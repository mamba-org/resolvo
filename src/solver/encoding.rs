use super::{SolverState, clause::WatchedLiterals};
use crate::{
    Candidates, Dependencies, DependencyProvider, NameId, Requirement, SolvableId, SolverCache,
    StringId, VersionSetId,
    internal::arena::ArenaId,
    internal::id::{ClauseId, SolvableOrRootId, VariableId},
};
use futures::{FutureExt, StreamExt, future::LocalBoxFuture, stream::FuturesUnordered};
use std::any::Any;

/// An object that is responsible for encoding information from the dependency
/// provider into rules and variables that are used by the solver.
///
/// This type allows concurrency in the dependency provider by concurrently
/// requesting information from the provider. This is achieved by recording all
/// futures in a [`FuturesUnordered`] and processing them as they become
/// available instead of waiting for individual futures to complete and
/// processing their response.
///
/// The encoder itself is completely single threaded (and not `Send`) but the
/// dependency provider is free to spawn tasks on other threads.
pub(crate) struct Encoder<'a, D: DependencyProvider> {
    state: &'a mut SolverState,
    cache: &'a SolverCache<D>,

    /// The dependencies of the root solvable.
    root_dependencies: &'a Dependencies,

    /// The set of futures that are pending to be resolved.
    pending_futures: FuturesUnordered<LocalBoxFuture<'a, Result<TaskResult<'a>, Box<dyn Any>>>>,

    /// A list of clauses that were introduced that are conflicting with the current state.
    conflicting_clauses: Vec<ClauseId>,
}

/// The result of a future that was queued for processing.
enum TaskResult<'a> {
    Dependencies(DependenciesAvailable<'a>),
    Candidates(CandidatesAvailable<'a>),
    RequirementCandidates(RequirementCandidatesAvailable<'a>),
    ConstraintCandidates(ConstraintCandidatesAvailable<'a>),
}

/// Result of requesting the dependencies for a certain solvable.
struct DependenciesAvailable<'a> {
    solvable_id: SolvableOrRootId,
    dependencies: &'a Dependencies,
}

/// Results of requesting the candidates for a certain package.
struct CandidatesAvailable<'a> {
    name_id: NameId,
    package_candidates: &'a Candidates,
}

/// Result of querying candidates for a particular requirement.
struct RequirementCandidatesAvailable<'a> {
    solvable_id: SolvableOrRootId,
    requirement: Requirement,
    candidates: Vec<&'a [SolvableId]>,
}

/// Result of querying candidates for a particular constraint.
struct ConstraintCandidatesAvailable<'a> {
    solvable_id: SolvableOrRootId,
    constraint: VersionSetId,
    candidates: &'a [SolvableId],
}

impl<'a, D: DependencyProvider> Encoder<'a, D> {
    pub fn new(
        state: &'a mut SolverState,
        cache: &'a SolverCache<D>,
        root_dependencies: &'a Dependencies,
    ) -> Self {
        Self {
            state,
            cache,
            root_dependencies,
            pending_futures: FuturesUnordered::new(),
            conflicting_clauses: Vec::new(),
        }
    }

    /// Encode rules and variables for the given solvables.
    pub async fn encode(
        mut self,
        solvable_ids: impl IntoIterator<Item = SolvableOrRootId>,
    ) -> Result<Vec<ClauseId>, Box<dyn Any>> {
        // Queue the initial solvables for processing.
        for solvable_id in solvable_ids {
            self.queue_solvable(solvable_id);
        }

        // Process all pending futures until there are no more.
        while let Some(future_result) = self.pending_futures.next().await {
            self.on_task_result(future_result?);
        }

        Ok(self.conflicting_clauses)
    }

    /// Called when the result of a future is available.
    fn on_task_result(&mut self, result: TaskResult<'a>) {
        match result {
            TaskResult::Dependencies(dependencies) => self.on_dependencies_available(dependencies),
            TaskResult::Candidates(candidates) => self.on_candidates_available(candidates),
            TaskResult::RequirementCandidates(candidates) => {
                self.on_requirement_candidates_available(candidates)
            }
            TaskResult::ConstraintCandidates(candidates) => {
                self.on_constraint_candidates_available(candidates)
            }
        }
    }

    /// Called when the dependencies of a solvable are available.
    ///
    /// Iterates over all the requirements and constraints and queues querying
    ///
    /// * the candidates for any new package that was encountered,
    /// * the matching candidates for each requirement,
    /// * the non-matching candidates for each constraint.
    fn on_dependencies_available(
        &mut self,
        DependenciesAvailable {
            solvable_id,
            dependencies,
        }: DependenciesAvailable<'a>,
    ) {
        tracing::trace!(
            "dependencies available for {}",
            solvable_id.display(self.cache.provider()),
        );

        // Extract the dependencies and constraints from the result.
        let (requirements, constraints) = match dependencies {
            Dependencies::Known(deps) => (&deps.requirements, &deps.constrains),
            Dependencies::Unknown(reason) => {
                // If the dependencies are unknown, we add an exclusion clause and stop processing.
                self.add_exclusion_clause(solvable_id, *reason);
                return;
            }
        };

        // Iterate over all requirements and find out to which packages they
        // refer. Make sure we have all candidates for a particular package.
        for version_set_id in requirements
            .iter()
            .flat_map(|requirement| requirement.version_sets(self.cache.provider()))
            .chain(constraints.iter().copied())
        {
            let package_name = self.cache.provider().version_set_name(version_set_id);
            self.queue_package(package_name);
        }

        // For each requirement request the matching candidates.
        for &requirement in requirements {
            self.queue_requirement(solvable_id, requirement);
        }

        // For each constraint, request the candidates that are non-matching
        // the version spec.
        for &constraint in constraints {
            self.queue_constraint(solvable_id, constraint);
        }
    }

    /// Called when all the solvable candidates for a package are available.
    fn on_candidates_available(
        &mut self,
        CandidatesAvailable {
            name_id,
            package_candidates,
        }: CandidatesAvailable<'a>,
    ) {
        tracing::trace!(
            "Package candidates available for {}",
            self.cache.provider().display_name(name_id)
        );

        // Resize the activity vector if needed
        if self.state.name_activity.len() <= name_id.to_usize() {
            self.state.name_activity.resize(name_id.to_usize() + 1, 0.0);
        }

        // If there is a locked solvable, forbid all other candidates
        if let Some(locked_solvable_id) = package_candidates.locked {
            self.add_locked_package_clauses(locked_solvable_id, &package_candidates.candidates);
        }

        // Add clauses for externally excluded candidates.
        for &(solvable, reason) in &package_candidates.excluded {
            let variable = self.add_exclusion_clause(solvable.into(), reason);
            debug_assert!(
                self.state.decision_tracker.assigned_value(variable) != Some(true),
                "it cannot be possible that the excluded candidate is already uninstallable"
            )
        }
    }

    /// Called when the candidates for a particular requirement are available.
    fn on_requirement_candidates_available(
        &mut self,
        RequirementCandidatesAvailable {
            solvable_id,
            requirement,
            candidates,
        }: RequirementCandidatesAvailable<'a>,
    ) {
        tracing::trace!(
            "Sorted candidates available for {}",
            requirement.display(self.cache.provider()),
        );

        let variable = self.state.variable_map.intern_solvable_or_root(solvable_id);

        // Get the variables associated with the individual candidates.
        let version_set_variables = candidates
            .iter()
            .map(|&candidates| {
                candidates
                    .iter()
                    .map(|&var| self.state.variable_map.intern_solvable(var))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // Queue requesting the dependencies of the candidates as well if they are
        // cheaply available from the dependency provider.
        for (candidate, candidate_var) in candidates
            .iter()
            .zip(version_set_variables.iter())
            .flat_map(|(&candidates, variable)| {
                candidates.iter().copied().zip(variable.iter().copied())
            })
        {
            // If the dependencies are already available for the
            // candidate, queue the candidate for processing.
            if self.cache.are_dependencies_available_for(candidate) {
                self.queue_solvable(candidate.into())
            }

            // Add forbid constraints for this solvable on all other
            // solvables that have been visited already for the same
            // version set name.
            let name_id = self.cache.provider().solvable_name(candidate);
            let other_solvables = self
                .state
                .forbidden_clauses_added
                .entry(name_id)
                .or_default();
            other_solvables.add(
                candidate_var,
                |a, b, positive| {
                    let (watched_literals, kind) = WatchedLiterals::forbid_multiple(
                        a,
                        if positive { b.positive() } else { b.negative() },
                        name_id,
                    );
                    let clause_id = self.state.clauses.alloc(watched_literals, kind);
                    let watched_literals = self.state.clauses.watched_literals
                        [clause_id.to_usize()]
                    .as_mut()
                    .expect("forbid clause must have watched literals");
                    self.state
                        .watches
                        .start_watching(watched_literals, clause_id);
                },
                || {
                    self.state
                        .variable_map
                        .alloc_forbid_multiple_variable(name_id)
                },
            );
        }

        // Add the requirements clause
        let no_candidates = candidates.iter().all(|candidates| candidates.is_empty());
        let (watched_literals, conflict, kind) = WatchedLiterals::requires(
            variable,
            requirement,
            version_set_variables.iter().flatten().copied(),
            &self.state.decision_tracker,
        );
        let clause_id = self.state.clauses.alloc(watched_literals, kind);

        let watched_literals = self.state.clauses.watched_literals[clause_id.to_usize()].as_mut();

        if let Some(watched_literals) = watched_literals {
            self.state
                .watches
                .start_watching(watched_literals, clause_id);
        }

        self.state
            .requires_clauses
            .entry(variable)
            .or_default()
            .push((requirement, clause_id));

        if conflict {
            self.conflicting_clauses.push(clause_id);
        } else if no_candidates {
            // Add assertions for unit clauses (i.e. those with no matching candidates)
            self.state.negative_assertions.push((variable, clause_id));
        }

        // Store resolved variables for later
        self.state
            .requirement_to_sorted_candidates
            .insert(requirement, version_set_variables);
    }

    /// Called when the candidates for a particular constraint are available.
    fn on_constraint_candidates_available(
        &mut self,
        ConstraintCandidatesAvailable {
            solvable_id,
            constraint,
            candidates,
        }: ConstraintCandidatesAvailable<'a>,
    ) {
        tracing::trace!(
            "non matching candidates available for {} {}",
            self.cache
                .provider()
                .display_name(self.cache.provider().version_set_name(constraint)),
            self.cache.provider().display_version_set(constraint),
        );

        let variable = self.state.variable_map.intern_solvable_or_root(solvable_id);
        for &forbidden_candidate in candidates {
            let forbidden_candidate_var =
                self.state.variable_map.intern_solvable(forbidden_candidate);
            let (watched_literals, conflict, kind) = WatchedLiterals::constrains(
                variable,
                forbidden_candidate_var,
                constraint,
                &self.state.decision_tracker,
            );

            // Allocate the clause for the constraint
            let clause_id = self.state.clauses.alloc(watched_literals, kind);

            // Start watching the clause
            let watched_literals = self.state.clauses.watched_literals[clause_id.to_usize()]
                .as_mut()
                .expect("a forbid clause must always have watched literals");
            self.state
                .watches
                .start_watching(watched_literals, clause_id);

            // Mark conflicting clauses
            if conflict {
                self.conflicting_clauses.push(clause_id);
            }
        }
    }

    /// Adds clauses to forbid any other clauses than the locked solvable to be installed.
    fn add_locked_package_clauses(
        &mut self,
        locked_solvable_id: SolvableId,
        all_candidate_ids: &[SolvableId],
    ) {
        let locked_solvable_var = self.state.variable_map.intern_solvable(locked_solvable_id);
        for &other_candidate in all_candidate_ids {
            if other_candidate == locked_solvable_id {
                // Don't add a clause for the locked solvable itself
                continue;
            }
            let other_candidate_var = self.state.variable_map.intern_solvable(other_candidate);

            // Allocated the clause for the exclusion
            let (watched_literals, kind) =
                WatchedLiterals::lock(locked_solvable_var, other_candidate_var);
            let clause_id = self.state.clauses.alloc(watched_literals, kind);

            // Start watching the clause.
            let watched_literals = self.state.clauses.watched_literals[clause_id.to_usize()]
                .as_mut()
                .expect("a forbid clause must always have watched literals");
            self.state
                .watches
                .start_watching(watched_literals, clause_id);
        }
    }

    /// Adds a clause to exclude a particular solvable
    fn add_exclusion_clause(
        &mut self,
        solvable_id: SolvableOrRootId,
        reason: StringId,
    ) -> VariableId {
        let variable = self.state.variable_map.intern_solvable_or_root(solvable_id);

        // Allocate a clause for the exclusion
        let (watched_literals, kind) = WatchedLiterals::exclude(variable, reason);
        let clause_id = self.state.clauses.alloc(watched_literals, kind);

        // Exclusions are negative assertions, tracked outside the watcher
        self.state.negative_assertions.push((variable, clause_id));

        // If the clause is already conflicting, e.g. we already decided that this
        // solvable must be installed, we add it to the list for later processing
        if self.state.decision_tracker.assigned_value(variable) == Some(true) {
            self.conflicting_clauses.push(clause_id)
        }

        variable
    }

    /// Enqueues retrieving the dependencies for a solvable.
    ///
    /// This method requests the dependencies for the given solvable in an
    /// async fashion and does not process the result itself. Instead, the
    /// future is queued for processing. When the future returns its result is
    /// processed by the [`Self::on_dependencies_available`] function.
    fn queue_solvable(&mut self, solvable_id: SolvableOrRootId) {
        // Early out if the solvable has already been processed
        if !self.state.clauses_added_for_solvable.insert(solvable_id) {
            return;
        }

        // Construct a future that queries the dependencies for the solvable
        let cache = self.cache;
        let root_dependencies = self.root_dependencies;
        let query_dependencies = async move {
            let dependencies = match solvable_id.solvable() {
                None => root_dependencies,
                Some(solvable_id) => cache.get_or_cache_dependencies(solvable_id).await?,
            };
            Ok(TaskResult::Dependencies(DependenciesAvailable {
                solvable_id,
                dependencies,
            }))
        };

        // Queue the future for processing
        self.pending_futures.push(query_dependencies.boxed_local());
    }

    /// Enqueues retrieving all candidates for a particular package name.
    fn queue_package(&mut self, name_id: NameId) {
        // Early out if the package has already been processed
        if !self.state.clauses_added_for_package.insert(name_id) {
            return;
        }

        // Construct a future that queries the candidates for the package
        let cache = self.cache;
        let query_candidates = async move {
            let package_candidates = cache.get_or_cache_candidates(name_id).await?;
            Ok(TaskResult::Candidates(CandidatesAvailable {
                name_id,
                package_candidates,
            }))
        };

        // Queue the future for processing
        self.pending_futures.push(query_candidates.boxed_local());
    }

    /// Enqueues retrieving the candidates for a particular requirement. These
    /// candidates are already filtered and sorted.
    fn queue_requirement(&mut self, solvable_id: SolvableOrRootId, requirement: Requirement) {
        let cache = self.cache;
        let query_requirements_candidates = async move {
            let candidates =
                futures::future::try_join_all(requirement.version_sets(cache.provider()).map(
                    |version_set| cache.get_or_cache_sorted_candidates_for_version_set(version_set),
                ))
                .await?;

            Ok(TaskResult::RequirementCandidates(
                RequirementCandidatesAvailable {
                    solvable_id,
                    requirement,
                    candidates,
                },
            ))
        };

        self.pending_futures
            .push(query_requirements_candidates.boxed_local());
    }

    /// Enqueues retrieving the candidates for a particular constraint. These
    /// are the candidates that do *not* match the version set.
    fn queue_constraint(&mut self, solvable_id: SolvableOrRootId, constraint: VersionSetId) {
        let cache = self.cache;
        let query_constraints_candidates = async move {
            let non_matching_candidates = cache
                .get_or_cache_non_matching_candidates(constraint)
                .await?;
            Ok(TaskResult::ConstraintCandidates(
                ConstraintCandidatesAvailable {
                    solvable_id,
                    constraint,
                    candidates: non_matching_candidates,
                },
            ))
        };

        self.pending_futures
            .push(query_constraints_candidates.boxed_local());
    }
}

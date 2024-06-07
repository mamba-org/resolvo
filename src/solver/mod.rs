use std::{any::Any, cell::RefCell, collections::HashSet, future::ready, ops::ControlFlow};

pub use cache::SolverCache;
use clause::{Clause, ClauseState, Literal};
use decision::Decision;
use decision_tracker::DecisionTracker;
use futures::{stream::FuturesUnordered, FutureExt, StreamExt};
use itertools::{chain, Itertools};
use watch_map::WatchMap;

use crate::{
    internal::{
        arena::Arena,
        id::{ClauseId, InternalSolvableId, LearntClauseId, NameId, SolvableId},
        mapping::Mapping,
    },
    problem::Problem,
    runtime::{AsyncRuntime, NowOrNeverRuntime},
    Candidates, Dependencies, DependencyProvider, KnownDependencies, VersionSetId,
};

mod cache;
pub(crate) mod clause;
mod decision;
mod decision_map;
mod decision_tracker;
mod watch_map;

#[derive(Default)]
struct AddClauseOutput {
    new_requires_clauses: Vec<(InternalSolvableId, VersionSetId, ClauseId)>,
    conflicting_clauses: Vec<ClauseId>,
    negative_assertions: Vec<(InternalSolvableId, ClauseId)>,
    clauses_to_watch: Vec<ClauseId>,
}

/// Drives the SAT solving process
pub struct Solver<D: DependencyProvider, RT: AsyncRuntime = NowOrNeverRuntime> {
    pub(crate) async_runtime: RT,
    pub(crate) cache: SolverCache<D>,

    pub(crate) clauses: RefCell<Arena<ClauseId, ClauseState>>,
    requires_clauses: Vec<(InternalSolvableId, VersionSetId, ClauseId)>,
    watches: WatchMap,

    negative_assertions: Vec<(InternalSolvableId, ClauseId)>,

    learnt_clauses: Arena<LearntClauseId, Vec<Literal>>,
    learnt_why: Mapping<LearntClauseId, Vec<ClauseId>>,
    learnt_clause_ids: Vec<ClauseId>,

    clauses_added_for_package: RefCell<HashSet<NameId>>,
    clauses_added_for_solvable: RefCell<HashSet<InternalSolvableId>>,

    decision_tracker: DecisionTracker,

    /// The version sets that must be installed as part of the solution.
    root_requirements: Vec<VersionSetId>,

    /// Additional constraints imposed by the root.
    root_constraints: Vec<VersionSetId>,
}

impl<D: DependencyProvider> Solver<D, NowOrNeverRuntime> {
    /// Creates a single threaded block solver, using the provided
    /// [`DependencyProvider`].
    pub fn new(provider: D) -> Self {
        Self {
            cache: SolverCache::new(provider),
            async_runtime: NowOrNeverRuntime,
            clauses: RefCell::new(Arena::new()),
            requires_clauses: Default::default(),
            watches: WatchMap::new(),
            negative_assertions: Default::default(),
            learnt_clauses: Arena::new(),
            learnt_why: Mapping::new(),
            learnt_clause_ids: Vec::new(),
            decision_tracker: DecisionTracker::new(),
            root_requirements: Default::default(),
            root_constraints: Default::default(),
            clauses_added_for_package: Default::default(),
            clauses_added_for_solvable: Default::default(),
        }
    }
}

/// The root cause of a solver error.
#[derive(Debug)]
pub enum UnsolvableOrCancelled {
    /// The problem was unsolvable.
    Unsolvable(Problem),
    /// The solving process was cancelled.
    Cancelled(Box<dyn Any>),
}

impl From<Problem> for UnsolvableOrCancelled {
    fn from(value: Problem) -> Self {
        UnsolvableOrCancelled::Unsolvable(value)
    }
}

impl From<Box<dyn Any>> for UnsolvableOrCancelled {
    fn from(value: Box<dyn Any>) -> Self {
        UnsolvableOrCancelled::Cancelled(value)
    }
}

/// An error during the propagation step
pub(crate) enum PropagationError {
    Conflict(InternalSolvableId, bool, ClauseId),
    Cancelled(Box<dyn Any>),
}

impl<D: DependencyProvider, RT: AsyncRuntime> Solver<D, RT> {
    /// Returns the dependency provider used by this instance.
    pub fn provider(&self) -> &D {
        self.cache.provider()
    }

    /// Set the runtime of the solver to `runtime`.
    pub fn with_runtime<RT2: AsyncRuntime>(self, runtime: RT2) -> Solver<D, RT2> {
        Solver {
            async_runtime: runtime,
            cache: self.cache,
            clauses: self.clauses,
            requires_clauses: self.requires_clauses,
            watches: self.watches,
            negative_assertions: self.negative_assertions,
            learnt_clauses: self.learnt_clauses,
            learnt_why: self.learnt_why,
            learnt_clause_ids: self.learnt_clause_ids,
            clauses_added_for_package: self.clauses_added_for_package,
            clauses_added_for_solvable: self.clauses_added_for_solvable,
            decision_tracker: self.decision_tracker,
            root_requirements: self.root_requirements,
            root_constraints: self.root_constraints,
        }
    }

    /// Solves for the provided `root_requirements` and `root_constraints`. The
    /// `root_requirements` are package that will be included in the
    /// solution. `root_constraints` are additional constrains which do not
    /// necesarily need to be included in the solution.
    ///
    /// Returns a [`Problem`] if no solution was found, which provides ways to
    /// inspect the causes and report them to the user.
    pub fn solve(
        &mut self,
        root_requirements: Vec<VersionSetId>,
        root_constraints: Vec<VersionSetId>,
    ) -> Result<Vec<SolvableId>, UnsolvableOrCancelled> {
        // Clear state
        self.decision_tracker.clear();
        self.negative_assertions.clear();
        self.learnt_clauses.clear();
        self.learnt_why = Mapping::new();
        self.clauses = Default::default();
        self.root_requirements = root_requirements;
        self.root_constraints = root_constraints;

        // The first clause will always be the install root clause. Here we verify that
        // this is indeed the case.
        let root_clause = self.clauses.borrow_mut().alloc(ClauseState::root());
        assert_eq!(root_clause, ClauseId::install_root());

        // Run SAT
        self.run_sat()?;

        let steps = self
            .decision_tracker
            .stack()
            .filter_map(|d| {
                if d.value {
                    d.solvable_id.as_solvable()
                } else {
                    // Ignore things that are set to false
                    None
                }
            })
            .collect();

        Ok(steps)
    }

    /// Adds clauses for a solvable. These clauses include requirements and
    /// constrains on other solvables.
    ///
    /// Returns the added clauses, and an additional list with conflicting
    /// clauses (if any).
    ///
    /// If the provider has requested the solving process to be cancelled, the
    /// cancellation value will be returned as an `Err(...)`.
    async fn add_clauses_for_solvables(
        &self,
        solvable_ids: impl IntoIterator<Item = InternalSolvableId>,
    ) -> Result<AddClauseOutput, Box<dyn Any>> {
        let mut output = AddClauseOutput::default();

        pub enum TaskResult<'i> {
            Dependencies {
                solvable_id: InternalSolvableId,
                dependencies: Dependencies,
            },
            SortedCandidates {
                solvable_id: InternalSolvableId,
                version_set_id: VersionSetId,
                candidates: &'i [SolvableId],
            },
            NonMatchingCandidates {
                solvable_id: InternalSolvableId,
                version_set_id: VersionSetId,
                non_matching_candidates: &'i [SolvableId],
            },
            Candidates {
                name_id: NameId,
                package_candidates: &'i Candidates,
            },
        }

        // Mark the initial seen solvables as seen
        let mut pending_solvables = vec![];
        {
            let mut clauses_added_for_solvable = self.clauses_added_for_solvable.borrow_mut();
            for solvable_id in solvable_ids {
                if clauses_added_for_solvable.insert(solvable_id) {
                    pending_solvables.push(solvable_id);
                }
            }
        }

        let mut seen = pending_solvables.iter().copied().collect::<HashSet<_>>();
        let mut pending_futures = FuturesUnordered::new();
        loop {
            // Iterate over all pending solvables and request their dependencies.
            for internal_solvable_id in pending_solvables.drain(..) {
                // Get the solvable information and request its requirements and constraints
                tracing::trace!(
                    "┝━ adding clauses for dependencies of {}",
                    internal_solvable_id.display(self.provider()),
                );

                // If the solvable is the root solvable, we can skip the dependency provider
                // and use the root requirements and constraints directly.
                let get_dependencies_fut =
                    if let Some(solvable_id) = internal_solvable_id.as_solvable() {
                        async move {
                            let deps = self.cache.get_or_cache_dependencies(solvable_id).await?;
                            Ok(TaskResult::Dependencies {
                                solvable_id: internal_solvable_id,
                                dependencies: deps.clone(),
                            })
                        }
                        .left_future()
                    } else {
                        ready(Ok(TaskResult::Dependencies {
                            solvable_id: internal_solvable_id,
                            dependencies: Dependencies::Known(KnownDependencies {
                                requirements: self.root_requirements.clone(),
                                constrains: self.root_constraints.clone(),
                            }),
                        }))
                        .right_future()
                    };

                pending_futures.push(get_dependencies_fut.boxed_local());
            }

            let Some(result) = pending_futures.next().await else {
                // No more pending results
                break;
            };

            let mut clauses_added_for_solvable = self.clauses_added_for_solvable.borrow_mut();
            let mut clauses_added_for_package = self.clauses_added_for_package.borrow_mut();

            match result? {
                TaskResult::Dependencies {
                    solvable_id,
                    dependencies,
                } => {
                    // Get the solvable information and request its requirements and constraints
                    tracing::trace!(
                        "dependencies available for {}",
                        solvable_id.display(self.provider()),
                    );

                    let (requirements, constrains) = match dependencies {
                        Dependencies::Known(deps) => (deps.requirements, deps.constrains),
                        Dependencies::Unknown(reason) => {
                            // There is no information about the solvable's dependencies, so we add
                            // an exclusion clause for it
                            let clause_id = self
                                .clauses
                                .borrow_mut()
                                .alloc(ClauseState::exclude(solvable_id, reason));

                            // Exclusions are negative assertions, tracked outside of the watcher
                            // system
                            output.negative_assertions.push((solvable_id, clause_id));

                            // There might be a conflict now
                            if self.decision_tracker.assigned_value(solvable_id) == Some(true) {
                                output.conflicting_clauses.push(clause_id);
                            }

                            continue;
                        }
                    };

                    for version_set_id in chain(requirements.iter(), constrains.iter()).copied() {
                        let dependency_name = self.provider().version_set_name(version_set_id);
                        if clauses_added_for_package.insert(dependency_name) {
                            tracing::trace!(
                                "┝━ adding clauses for package '{}'",
                                self.provider().display_name(dependency_name),
                            );

                            pending_futures.push(
                                async move {
                                    let package_candidates =
                                        self.cache.get_or_cache_candidates(dependency_name).await?;
                                    Ok(TaskResult::Candidates {
                                        name_id: dependency_name,
                                        package_candidates,
                                    })
                                }
                                .boxed_local(),
                            );
                        }
                    }

                    for version_set_id in requirements {
                        // Find all the solvable that match for the given version set
                        pending_futures.push(
                            async move {
                                let candidates = self
                                    .cache
                                    .get_or_cache_sorted_candidates(version_set_id)
                                    .await?;
                                Ok(TaskResult::SortedCandidates {
                                    solvable_id,
                                    version_set_id,
                                    candidates,
                                })
                            }
                            .boxed_local(),
                        );
                    }

                    for version_set_id in constrains {
                        // Find all the solvables that match for the given version set
                        pending_futures.push(
                            async move {
                                let non_matching_candidates = self
                                    .cache
                                    .get_or_cache_non_matching_candidates(version_set_id)
                                    .await?;
                                Ok(TaskResult::NonMatchingCandidates {
                                    solvable_id,
                                    version_set_id,
                                    non_matching_candidates,
                                })
                            }
                            .boxed_local(),
                        )
                    }
                }
                TaskResult::Candidates {
                    name_id,
                    package_candidates,
                } => {
                    // Get the solvable information and request its requirements and constraints
                    tracing::trace!(
                        "package candidates available for {}",
                        self.provider().display_name(name_id)
                    );

                    let locked_solvable_id = package_candidates.locked;
                    let candidates = &package_candidates.candidates;

                    // Check the assumption that no decision has been made about any of the
                    // solvables.
                    for &candidate in candidates {
                        debug_assert!(
                            self.decision_tracker.assigned_value(candidate.into()).is_none(),
                            "a decision has been made about a candidate of a package that was not properly added yet."
                        );
                    }

                    // Each candidate gets a clause to disallow other candidates.
                    for (i, &candidate) in candidates.iter().enumerate() {
                        for &other_candidate in &candidates[i + 1..] {
                            let clause_id =
                                self.clauses
                                    .borrow_mut()
                                    .alloc(ClauseState::forbid_multiple(
                                        candidate.into(),
                                        other_candidate.into(),
                                        name_id,
                                    ));

                            debug_assert!(self.clauses.borrow_mut()[clause_id].has_watches());
                            output.clauses_to_watch.push(clause_id);
                        }
                    }

                    // If there is a locked solvable, forbid other solvables.
                    if let Some(locked_solvable_id) = locked_solvable_id {
                        for &other_candidate in candidates {
                            if other_candidate != locked_solvable_id {
                                let clause_id = self.clauses.borrow_mut().alloc(ClauseState::lock(
                                    locked_solvable_id.into(),
                                    other_candidate.into(),
                                ));

                                debug_assert!(self.clauses.borrow_mut()[clause_id].has_watches());
                                output.clauses_to_watch.push(clause_id);
                            }
                        }
                    }

                    // Add a clause for solvables that are externally excluded.
                    for (solvable, reason) in package_candidates.excluded.iter().copied() {
                        let clause_id = self
                            .clauses
                            .borrow_mut()
                            .alloc(ClauseState::exclude(solvable.into(), reason));

                        // Exclusions are negative assertions, tracked outside of the watcher system
                        output
                            .negative_assertions
                            .push((solvable.into(), clause_id));

                        // Conflicts should be impossible here
                        debug_assert!(
                            self.decision_tracker.assigned_value(solvable.into()) != Some(true)
                        );
                    }
                }
                TaskResult::SortedCandidates {
                    solvable_id,
                    version_set_id,
                    candidates,
                } => {
                    tracing::trace!(
                        "sorted candidates available for {} {}",
                        self.provider()
                            .display_name(self.provider().version_set_name(version_set_id)),
                        self.provider().display_version_set(version_set_id),
                    );

                    // Queue requesting the dependencies of the candidates as well if they are
                    // cheaply available from the dependency provider.
                    for &candidate in candidates {
                        if seen.insert(candidate.into())
                            && self.cache.are_dependencies_available_for(candidate)
                            && clauses_added_for_solvable.insert(candidate.into())
                        {
                            pending_solvables.push(candidate.into());
                        }
                    }

                    // Add the requirements clause
                    let no_candidates = candidates.is_empty();
                    let (clause, conflict) = ClauseState::requires(
                        solvable_id,
                        version_set_id,
                        candidates,
                        &self.decision_tracker,
                    );

                    let clause_id = self.clauses.borrow_mut().alloc(clause);
                    let clause = &self.clauses.borrow()[clause_id];

                    let &Clause::Requires(solvable_id, version_set_id) = &clause.kind else {
                        unreachable!();
                    };

                    if clause.has_watches() {
                        output.clauses_to_watch.push(clause_id);
                    }

                    output
                        .new_requires_clauses
                        .push((solvable_id, version_set_id, clause_id));

                    if conflict {
                        output.conflicting_clauses.push(clause_id);
                    } else if no_candidates {
                        // Add assertions for unit clauses (i.e. those with no matching candidates)
                        output.negative_assertions.push((solvable_id, clause_id));
                    }
                }
                TaskResult::NonMatchingCandidates {
                    solvable_id,
                    version_set_id,
                    non_matching_candidates,
                } => {
                    tracing::trace!(
                        "non matching candidates available for {} {}",
                        self.provider()
                            .display_name(self.provider().version_set_name(version_set_id)),
                        self.provider().display_version_set(version_set_id),
                    );

                    // Add forbidden clauses for the candidates
                    for &forbidden_candidate in non_matching_candidates {
                        let (clause, conflict) = ClauseState::constrains(
                            solvable_id,
                            forbidden_candidate.into(),
                            version_set_id,
                            &self.decision_tracker,
                        );

                        let clause_id = self.clauses.borrow_mut().alloc(clause);
                        output.clauses_to_watch.push(clause_id);

                        if conflict {
                            output.conflicting_clauses.push(clause_id);
                        }
                    }
                }
            }
        }

        Ok(output)
    }

    /// Run the CDCL algorithm to solve the SAT problem
    ///
    /// The CDCL algorithm's job is to find a valid assignment to the variables
    /// involved in the provided clauses. It works in the following steps:
    ///
    /// 1. __Set__: Assign a value to a variable that hasn't been assigned yet.
    ///    An assignment in this step starts a new "level" (the first one being
    ///    level 1). If all variables have been assigned, then we are done.
    /// 2. __Propagate__: Perform [unit propagation](https://en.wikipedia.org/wiki/Unit_propagation).
    ///    Assignments in this step are associated to the same "level" as the
    ///    decision that triggered them. This "level" metadata is useful when it
    ///    comes to handling conflicts. See [`Solver::propagate`] for the
    ///    implementation of this step.
    /// 3. __Learn__: If propagation finishes without conflicts, go back to 1.
    ///    Otherwise find the combination of assignments that caused the
    ///    conflict and add a new clause to the solver to forbid that
    ///    combination of assignments (i.e. learn from this mistake so it is not
    ///    repeated in the future). Then backtrack and go back to step 1 or, if
    ///    the learnt clause is in conflict with existing clauses, declare the
    ///    problem to be unsolvable. See [`Solver::analyze`] for the
    ///    implementation of this step.
    ///
    /// The solver loop can be found in [`Solver::resolve_dependencies`].
    fn run_sat(&mut self) -> Result<(), UnsolvableOrCancelled> {
        assert!(self.decision_tracker.is_empty());
        let mut level = 0;

        loop {
            // A level of 0 means the decision loop has been completely reset because a
            // partial solution was invalidated by newly added clauses.
            if level == 0 {
                // Level 1 is the initial decision level
                level = 1;

                // Assign `true` to the root solvable. This must be installed to satisfy the
                // solution. The root solvable contains the dependencies that
                // were injected when calling `Solver::solve`. If we can find a
                // solution were the root is installable we found a
                // solution that satisfies the user requirements.
                tracing::info!("╤══ install <root> at level {level}",);
                self.decision_tracker
                    .try_add_decision(
                        Decision::new(InternalSolvableId::root(), true, ClauseId::install_root()),
                        level,
                    )
                    .expect("already decided");

                // Add the clauses for the root solvable.
                let output = self
                    .async_runtime
                    .block_on(self.add_clauses_for_solvables(vec![InternalSolvableId::root()]))?;
                if let Err(clause_id) = self.process_add_clause_output(output) {
                    return Err(UnsolvableOrCancelled::Unsolvable(
                        self.analyze_unsolvable(clause_id),
                    ));
                }
            }

            // Propagate decisions from assignments above
            let propagate_result = self.propagate(level);

            // Handle propagation errors
            match propagate_result {
                Ok(()) => {}
                Err(PropagationError::Conflict(_, _, clause_id)) => {
                    if level == 1 {
                        return Err(UnsolvableOrCancelled::Unsolvable(
                            self.analyze_unsolvable(clause_id),
                        ));
                    } else {
                        // The conflict was caused because new clauses have been added dynamically.
                        // We need to start over.
                        tracing::debug!("├─ added clause {clause} introduces a conflict which invalidates the partial solution",
                                clause=self.clauses.borrow()[clause_id].display(self.provider()));
                        level = 0;
                        self.decision_tracker.clear();
                        continue;
                    }
                }
                Err(PropagationError::Cancelled(value)) => {
                    // Propagation was cancelled
                    return Err(UnsolvableOrCancelled::Cancelled(value));
                }
            }

            // Enter the solver loop, return immediately if no new assignments have been
            // made.
            level = self.resolve_dependencies(level)?;

            // We have a partial solution. E.g. there is a solution that satisfies all the
            // clauses that have been added so far.

            // Determine which solvables are part of the solution for which we did not yet
            // get any dependencies. If we find any such solvable it means we
            // did not arrive at the full solution yet.
            let new_solvables: Vec<_> = self
                .decision_tracker
                .stack()
                // Filter only decisions that led to a positive assignment
                .filter(|d| d.value)
                // Select solvables for which we do not yet have dependencies
                .filter(|d| {
                    !self
                        .clauses_added_for_solvable
                        .borrow()
                        .contains(&d.solvable_id)
                })
                .map(|d| (d.solvable_id, d.derived_from))
                .collect();

            if new_solvables.is_empty() {
                // If no new literals were selected this solution is complete and we can return.
                return Ok(());
            }

            tracing::debug!(
                "====\n==Found newly selected solvables\n- {}\n====",
                new_solvables
                    .iter()
                    .copied()
                    .format_with("\n- ", |(id, derived_from), f| f(&format_args!(
                        "{} (derived from {})",
                        id.display(self.provider()),
                        self.clauses.borrow()[derived_from].display(self.provider()),
                    )))
            );

            // Concurrently get the solvable's clauses
            let output = self.async_runtime.block_on(self.add_clauses_for_solvables(
                new_solvables.iter().map(|(solvable_id, _)| *solvable_id),
            ))?;

            // Serially process the outputs, to reduce the need for synchronization
            for &clause_id in &output.conflicting_clauses {
                tracing::debug!("├─ added clause {clause} introduces a conflict which invalidates the partial solution",
                                        clause=self.clauses.borrow()[clause_id].display(self.provider()));
            }

            if let Err(_first_conflicting_clause_id) = self.process_add_clause_output(output) {
                self.decision_tracker.clear();
                level = 0;
            }
        }
    }

    fn process_add_clause_output(&mut self, mut output: AddClauseOutput) -> Result<(), ClauseId> {
        let mut clauses = self.clauses.borrow_mut();
        for clause_id in output.clauses_to_watch {
            debug_assert!(
                clauses[clause_id].has_watches(),
                "attempting to watch a clause without watches!"
            );
            self.watches
                .start_watching(&mut clauses[clause_id], clause_id);
        }

        self.requires_clauses
            .append(&mut output.new_requires_clauses);
        self.negative_assertions
            .append(&mut output.negative_assertions);

        if let Some(&clause_id) = output.conflicting_clauses.first() {
            return Err(clause_id);
        }

        Ok(())
    }

    /// Resolves all dependencies
    ///
    /// Repeatedly chooses the next variable to assign, and calls
    /// [`Solver::set_propagate_learn`] to drive the solving process (as you
    /// can see from the name, the method executes the set, propagate and
    /// learn steps described in the [`Solver::run_sat`] docs).
    ///
    /// The next variable to assign is obtained by finding the next dependency
    /// for which no concrete package has been picked yet. Then we pick the
    /// highest possible version for that package, or the favored version if
    /// it was provided by the user, and set its value to true.
    fn resolve_dependencies(&mut self, mut level: u32) -> Result<u32, UnsolvableOrCancelled> {
        loop {
            // Make a decision. If no decision could be made it means the problem is
            // satisfyable.
            let Some((candidate, required_by, clause_id)) = self.decide() else {
                break;
            };

            // Propagate the decision
            level = self.set_propagate_learn(level, candidate, required_by, clause_id)?;
        }

        // We just went through all clauses and there are no choices left to be made
        Ok(level)
    }

    /// Pick a solvable that we are going to assign true. This function uses a
    /// heuristic to determine to best decision to make. The function
    /// selects the requirement that has the least amount of working
    /// available candidates and selects the best candidate from that list. This
    /// ensures that if there are conflicts they are delt with as early as
    /// possible.
    fn decide(&mut self) -> Option<(InternalSolvableId, InternalSolvableId, ClauseId)> {
        let mut best_decision = None;
        for &(solvable_id, deps, clause_id) in &self.requires_clauses {
            // Consider only clauses in which we have decided to install the solvable
            if self.decision_tracker.assigned_value(solvable_id) != Some(true) {
                continue;
            }

            // Consider only clauses in which no candidates have been installed
            let candidates = &self.cache.version_set_to_sorted_candidates[&deps];

            // Either find the first assignable candidate or determine that one of the
            // candidates is already assigned in which case the clause has
            // already been satisfied.
            let candidate = candidates.iter().try_fold(
                (None, 0),
                |(first_selectable_candidate, selectable_candidates), &candidate| {
                    let assigned_value = self.decision_tracker.assigned_value(candidate.into());
                    match assigned_value {
                        Some(true) => ControlFlow::Break(()),
                        Some(false) => ControlFlow::Continue((
                            first_selectable_candidate,
                            selectable_candidates,
                        )),
                        None => ControlFlow::Continue((
                            first_selectable_candidate.or(Some(candidate)),
                            selectable_candidates + 1,
                        )),
                    }
                },
            );

            match candidate {
                ControlFlow::Continue((Some(candidate), count)) => {
                    let possible_decision = (candidate, solvable_id, clause_id);
                    best_decision = Some(match best_decision {
                        None => (count, possible_decision),
                        Some((best_count, _)) if count < best_count => {
                            (count, possible_decision)
                        }
                        Some(best_decision) => best_decision,
                    })
                }
                ControlFlow::Break(_) => continue,
                ControlFlow::Continue((None, _)) => unreachable!("when we get here it means that all candidates have been assigned false. This should not be able to happen at this point because during propagation the solvable should have been assigned false as well."),
            }
        }

        if let Some((count, (candidate, _solvable_id, clause_id))) = best_decision {
            tracing::info!(
                "deciding to assign {}, ({}, {} possible candidates)",
                self.provider().display_solvable(candidate),
                self.clauses.borrow()[clause_id].display(self.provider()),
                count,
            );
        }

        // Could not find a requirement that needs satisfying.
        best_decision.map(|(_best_count, (candidate, required_by, via))| {
            (candidate.into(), required_by, via)
        })
    }

    /// Executes one iteration of the CDCL loop
    ///
    /// A set-propagate-learn round is always initiated by a requirement clause
    /// (i.e. [`Clause::Requires`]). The parameters include the variable
    /// associated to the candidate for the dependency (`solvable`), the
    /// package that originates the dependency (`required_by`), and the
    /// id of the requires clause (`clause_id`).
    ///
    /// Refer to the documentation of [`Solver::run_sat`] for details on the
    /// CDCL algorithm.
    ///
    /// Returns the new level after this set-propagate-learn round, or a
    /// [`Problem`] if we discovered that the requested jobs are
    /// unsatisfiable.
    fn set_propagate_learn(
        &mut self,
        mut level: u32,
        solvable: InternalSolvableId,
        required_by: InternalSolvableId,
        clause_id: ClauseId,
    ) -> Result<u32, UnsolvableOrCancelled> {
        level += 1;

        tracing::info!(
            "╤══ Install {} at level {level} (required by {})",
            solvable.display(self.provider()),
            required_by.display(self.provider())
        );

        // Add the decision to the tracker
        self.decision_tracker
            .try_add_decision(Decision::new(solvable, true, clause_id), level)
            .expect("bug: solvable was already decided!");

        self.propagate_and_learn(level)
    }

    fn propagate_and_learn(&mut self, mut level: u32) -> Result<u32, UnsolvableOrCancelled> {
        loop {
            match self.propagate(level) {
                Ok(()) => {
                    // Propagation completed
                    tracing::debug!("╘══ Propagation completed");
                    return Ok(level);
                }
                Err(PropagationError::Cancelled(value)) => {
                    // Propagation cancelled
                    tracing::debug!("╘══ Propagation cancelled");
                    return Err(UnsolvableOrCancelled::Cancelled(value));
                }
                Err(PropagationError::Conflict(
                    conflicting_solvable,
                    attempted_value,
                    conflicting_clause,
                )) => {
                    level = self.learn_from_conflict(
                        level,
                        conflicting_solvable,
                        attempted_value,
                        conflicting_clause,
                    )?;
                }
            }
        }
    }

    fn learn_from_conflict(
        &mut self,
        mut level: u32,
        conflicting_solvable: InternalSolvableId,
        attempted_value: bool,
        conflicting_clause: ClauseId,
    ) -> Result<u32, Problem> {
        {
            tracing::info!(
                "├─ Propagation conflicted: could not set {solvable} to {attempted_value}",
                solvable = conflicting_solvable.display(self.provider()),
            );
            tracing::info!(
                "│  During unit propagation for clause: {}",
                self.clauses.borrow()[conflicting_clause].display(self.provider())
            );

            tracing::info!(
                "│  Previously decided value: {}. Derived from: {}",
                !attempted_value,
                self.clauses.borrow()[self
                    .decision_tracker
                    .find_clause_for_assignment(conflicting_solvable)
                    .unwrap()]
                .display(self.provider()),
            );
        }

        if level == 1 {
            tracing::info!("╘══ UNSOLVABLE");
            for decision in self.decision_tracker.stack() {
                let clause = &self.clauses.borrow()[decision.derived_from];
                let level = self.decision_tracker.level(decision.solvable_id);
                let action = if decision.value { "install" } else { "forbid" };

                if let Clause::ForbidMultipleInstances(..) = clause.kind {
                    // Skip forbids clauses, to reduce noise
                    continue;
                }

                tracing::info!(
                    "* ({level}) {action} {}. Reason: {}",
                    decision.solvable_id.display(self.provider()),
                    clause.display(self.provider()),
                );
            }

            return Err(self.analyze_unsolvable(conflicting_clause));
        }

        let (new_level, learned_clause_id, literal) =
            self.analyze(level, conflicting_solvable, conflicting_clause);
        level = new_level;

        tracing::debug!("├─ Backtracked to level {level}");

        // Optimization: propagate right now, since we know that the clause is a unit
        // clause
        let decision = literal.satisfying_value();
        self.decision_tracker
            .try_add_decision(
                Decision::new(literal.solvable_id, decision, learned_clause_id),
                level,
            )
            .expect("bug: solvable was already decided!");
        tracing::debug!(
            "├─ Propagate after learn: {} = {decision}",
            literal.solvable_id.display(self.provider()),
        );

        Ok(level)
    }

    /// The propagate step of the CDCL algorithm
    ///
    /// Propagation is implemented by means of watches: each clause that has two
    /// or more literals is "subscribed" to changes in the values of two
    /// solvables that appear in the clause. When a value is assigned to a
    /// solvable, each of the clauses tracking that solvable will be notified.
    /// That way, the clause can check whether the literal that is using the
    /// solvable has become false, in which case it picks a new solvable to
    /// watch (if available) or triggers an assignment.
    fn propagate(&mut self, level: u32) -> Result<(), PropagationError> {
        if let Some(value) = self.provider().should_cancel_with_value() {
            return Err(PropagationError::Cancelled(value));
        };

        // Negative assertions derived from other rules (assertions are clauses that
        // consist of a single literal, and therefore do not have watches)
        for &(solvable_id, clause_id) in &self.negative_assertions {
            let value = false;
            let decided = self
                .decision_tracker
                .try_add_decision(Decision::new(solvable_id, value, clause_id), level)
                .map_err(|_| PropagationError::Conflict(solvable_id, value, clause_id))?;

            if decided {
                tracing::trace!(
                    "├─ Propagate assertion {} = {}",
                    solvable_id.display(self.provider()),
                    value
                );
            }
        }

        // Assertions derived from learnt rules
        for learn_clause_idx in 0..self.learnt_clause_ids.len() {
            let clause_id = self.learnt_clause_ids[learn_clause_idx];
            let clause = &self.clauses.borrow()[clause_id];
            let Clause::Learnt(learnt_index) = clause.kind else {
                unreachable!();
            };

            let literals = &self.learnt_clauses[learnt_index];
            if literals.len() > 1 {
                continue;
            }

            debug_assert!(!literals.is_empty());

            let literal = literals[0];
            let decision = literal.satisfying_value();

            let decided = self
                .decision_tracker
                .try_add_decision(
                    Decision::new(literal.solvable_id, decision, clause_id),
                    level,
                )
                .map_err(|_| {
                    PropagationError::Conflict(literal.solvable_id, decision, clause_id)
                })?;

            if decided {
                tracing::trace!(
                    "├─ Propagate assertion {} = {}",
                    literal.solvable_id.display(self.provider()),
                    decision
                );
            }
        }

        // Watched solvables
        while let Some(decision) = self.decision_tracker.next_unpropagated() {
            let pkg = decision.solvable_id;

            // Propagate, iterating through the linked list of clauses that watch this
            // solvable
            let mut old_predecessor_clause_id: Option<ClauseId>;
            let mut predecessor_clause_id: Option<ClauseId> = None;
            let mut clause_id = self.watches.first_clause_watching_solvable(pkg);
            while !clause_id.is_null() {
                debug_assert!(
                    predecessor_clause_id != Some(clause_id),
                    "Linked list is circular!"
                );

                // Get mutable access to both clauses.
                let mut clauses = self.clauses.borrow_mut();
                let (predecessor_clause, clause) =
                    if let Some(prev_clause_id) = predecessor_clause_id {
                        let (predecessor_clause, clause) =
                            clauses.get_two_mut(prev_clause_id, clause_id);
                        (Some(predecessor_clause), clause)
                    } else {
                        (None, &mut clauses[clause_id])
                    };

                // Update the prev_clause_id for the next run
                old_predecessor_clause_id = predecessor_clause_id;
                predecessor_clause_id = Some(clause_id);

                // Configure the next clause to visit
                let this_clause_id = clause_id;
                clause_id = clause.next_watched_clause(pkg);

                if let Some((watched_literals, watch_index)) = clause.watch_turned_false(
                    pkg,
                    self.decision_tracker.map(),
                    &self.learnt_clauses,
                ) {
                    // One of the watched literals is now false
                    if let Some(variable) = clause.next_unwatched_variable(
                        &self.learnt_clauses,
                        &self.cache.version_set_to_sorted_candidates,
                        self.decision_tracker.map(),
                    ) {
                        debug_assert!(!clause.watched_literals.contains(&variable));

                        self.watches.update_watched(
                            predecessor_clause,
                            clause,
                            this_clause_id,
                            watch_index,
                            pkg,
                            variable,
                        );

                        // Make sure the right predecessor is kept for the next iteration (i.e. the
                        // current clause is no longer a predecessor of the next one; the current
                        // clause's predecessor is)
                        predecessor_clause_id = old_predecessor_clause_id;
                    } else {
                        // We could not find another literal to watch, which means the remaining
                        // watched literal can be set to true
                        let remaining_watch_index = match watch_index {
                            0 => 1,
                            1 => 0,
                            _ => unreachable!(),
                        };

                        let remaining_watch = watched_literals[remaining_watch_index];
                        let decided = self
                            .decision_tracker
                            .try_add_decision(
                                Decision::new(
                                    remaining_watch.solvable_id,
                                    remaining_watch.satisfying_value(),
                                    this_clause_id,
                                ),
                                level,
                            )
                            .map_err(|_| {
                                PropagationError::Conflict(
                                    remaining_watch.solvable_id,
                                    true,
                                    this_clause_id,
                                )
                            })?;

                        if decided {
                            match clause.kind {
                                // Skip logging for ForbidMultipleInstances, which is so noisy
                                Clause::ForbidMultipleInstances(..) => {}
                                _ => {
                                    tracing::debug!(
                                        "├─ Propagate {} = {}. {}",
                                        remaining_watch.solvable_id.display(self.provider()),
                                        remaining_watch.satisfying_value(),
                                        clause.display(self.provider()),
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Adds the clause with `clause_id` to the current `Problem`
    ///
    /// Because learnt clauses are not relevant for the user, they are not added
    /// to the `Problem`. Instead, we report the clauses that caused them.
    fn analyze_unsolvable_clause(
        clauses: &Arena<ClauseId, ClauseState>,
        learnt_why: &Mapping<LearntClauseId, Vec<ClauseId>>,
        clause_id: ClauseId,
        problem: &mut Problem,
        seen: &mut HashSet<ClauseId>,
    ) {
        let clause = &clauses[clause_id];
        match clause.kind {
            Clause::Learnt(learnt_clause_id) => {
                if !seen.insert(clause_id) {
                    return;
                }

                for &cause in learnt_why
                    .get(learnt_clause_id)
                    .expect("no cause for learnt clause available")
                {
                    Self::analyze_unsolvable_clause(clauses, learnt_why, cause, problem, seen);
                }
            }
            _ => problem.add_clause(clause_id),
        }
    }

    /// Create a [`Problem`] based on the id of the clause that triggered an
    /// unrecoverable conflict
    fn analyze_unsolvable(&mut self, clause_id: ClauseId) -> Problem {
        let last_decision = self.decision_tracker.stack().last().unwrap();
        let highest_level = self.decision_tracker.level(last_decision.solvable_id);
        debug_assert_eq!(highest_level, 1);

        let mut problem = Problem::default();

        tracing::info!("=== ANALYZE UNSOLVABLE");

        let mut involved = HashSet::new();
        self.clauses.borrow()[clause_id].kind.visit_literals(
            &self.learnt_clauses,
            &self.cache.version_set_to_sorted_candidates,
            |literal| {
                involved.insert(literal.solvable_id);
            },
        );

        let mut seen = HashSet::new();
        Self::analyze_unsolvable_clause(
            &self.clauses.borrow(),
            &self.learnt_why,
            clause_id,
            &mut problem,
            &mut seen,
        );

        for decision in self.decision_tracker.stack().rev() {
            if decision.solvable_id.is_root() {
                continue;
            }

            let why = decision.derived_from;

            if !involved.contains(&decision.solvable_id) {
                continue;
            }

            assert_ne!(why, ClauseId::install_root());

            Self::analyze_unsolvable_clause(
                &self.clauses.borrow(),
                &self.learnt_why,
                why,
                &mut problem,
                &mut seen,
            );

            self.clauses.borrow()[why].kind.visit_literals(
                &self.learnt_clauses,
                &self.cache.version_set_to_sorted_candidates,
                |literal| {
                    if literal.eval(self.decision_tracker.map()) == Some(true) {
                        assert_eq!(literal.solvable_id, decision.solvable_id);
                    } else {
                        involved.insert(literal.solvable_id);
                    }
                },
            );
        }

        problem
    }

    /// Analyze the causes of the conflict and learn from it
    ///
    /// This function finds the combination of assignments that caused the
    /// conflict and adds a new clause to the solver to forbid that
    /// combination of assignments (i.e. learn from this mistake
    /// so it is not repeated in the future). It corresponds to the
    /// `Solver.analyze` function from the MiniSAT paper.
    ///
    /// Returns the level to which we should backtrack, the id of the learnt
    /// clause and the literal that should be assigned (by definition, when
    /// we learn a clause, all its literals except one evaluate to false, so
    /// the value of the remaining literal must be assigned to make the clause
    /// become true)
    fn analyze(
        &mut self,
        mut current_level: u32,
        mut conflicting_solvable: InternalSolvableId,
        mut clause_id: ClauseId,
    ) -> (u32, ClauseId, Literal) {
        let mut seen = HashSet::new();
        let mut causes_at_current_level = 0u32;
        let mut learnt = Vec::new();
        let mut back_track_to = 0;

        let mut s_value;
        let mut learnt_why = Vec::new();
        let mut first_iteration = true;
        loop {
            learnt_why.push(clause_id);

            self.clauses.borrow()[clause_id].kind.visit_literals(
                &self.learnt_clauses,
                &self.cache.version_set_to_sorted_candidates,
                |literal| {
                    if !first_iteration && literal.solvable_id == conflicting_solvable {
                        // We are only interested in the causes of the conflict, so we ignore the
                        // solvable whose value was propagated
                        return;
                    }

                    if !seen.insert(literal.solvable_id) {
                        // Skip literals we have already seen
                        return;
                    }

                    let decision_level = self.decision_tracker.level(literal.solvable_id);
                    if decision_level == current_level {
                        causes_at_current_level += 1;
                    } else if current_level > 1 {
                        let learnt_literal = Literal {
                            solvable_id: literal.solvable_id,
                            negate: self
                                .decision_tracker
                                .assigned_value(literal.solvable_id)
                                .unwrap(),
                        };
                        learnt.push(learnt_literal);
                        back_track_to = back_track_to.max(decision_level);
                    } else {
                        unreachable!();
                    }
                },
            );

            first_iteration = false;

            // Select next literal to look at
            loop {
                let (last_decision, last_decision_level) = self.decision_tracker.undo_last();

                conflicting_solvable = last_decision.solvable_id;
                s_value = last_decision.value;
                clause_id = last_decision.derived_from;

                current_level = last_decision_level;

                // We are interested in the first literal we come across that caused the
                // conflicting assignment
                if seen.contains(&last_decision.solvable_id) {
                    break;
                }
            }

            causes_at_current_level = causes_at_current_level.saturating_sub(1);
            if causes_at_current_level == 0 {
                break;
            }
        }

        let last_literal = Literal {
            solvable_id: conflicting_solvable,
            negate: s_value,
        };
        learnt.push(last_literal);

        // Add the clause
        let learnt_id = self.learnt_clauses.alloc(learnt.clone());
        self.learnt_why.insert(learnt_id, learnt_why);

        let clause_id = self
            .clauses
            .borrow_mut()
            .alloc(ClauseState::learnt(learnt_id, &learnt));
        self.learnt_clause_ids.push(clause_id);

        let clause = &mut self.clauses.borrow_mut()[clause_id];
        if clause.has_watches() {
            self.watches.start_watching(clause, clause_id);
        }

        tracing::debug!("├─ Learnt disjunction:",);
        for lit in learnt {
            tracing::debug!(
                "│  - {}{}",
                if lit.negate { "NOT " } else { "" },
                lit.solvable_id.display(self.provider()),
            );
        }

        // Should revert at most to the root level
        let target_level = back_track_to.max(1);
        self.decision_tracker.undo_until(target_level);

        (target_level, clause_id, last_literal)
    }
}

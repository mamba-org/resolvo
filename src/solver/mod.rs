use crate::{
    internal::{
        arena::Arena,
        id::{ClauseId, LearntClauseId, NameId, SolvableId},
        mapping::Mapping,
    },
    pool::Pool,
    problem::Problem,
    solvable::SolvableInner,
    Dependencies, DependencyProvider, PackageName, VersionSet, VersionSetId,
};
use std::any::Any;
use std::collections::HashSet;
use std::fmt::Display;
use std::ops::ControlFlow;

use itertools::Itertools;

pub use cache::SolverCache;
use clause::{Clause, ClauseState, Literal};
use decision::Decision;
use decision_tracker::DecisionTracker;
use watch_map::WatchMap;

mod cache;
pub(crate) mod clause;
mod decision;
mod decision_map;
mod decision_tracker;
mod watch_map;

/// Drives the SAT solving process
pub struct Solver<VS: VersionSet, N: PackageName, D: DependencyProvider<VS, N>> {
    pub(crate) cache: SolverCache<VS, N, D>,

    pub(crate) clauses: Arena<ClauseId, ClauseState>,
    requires_clauses: Vec<(SolvableId, VersionSetId, ClauseId)>,
    watches: WatchMap,

    negative_assertions: Vec<(SolvableId, ClauseId)>,

    learnt_clauses: Arena<LearntClauseId, Vec<Literal>>,
    learnt_why: Mapping<LearntClauseId, Vec<ClauseId>>,
    learnt_clause_ids: Vec<ClauseId>,

    clauses_added_for_package: HashSet<NameId>,
    clauses_added_for_solvable: HashSet<SolvableId>,

    decision_tracker: DecisionTracker,

    /// The version sets that must be installed as part of the solution.
    root_requirements: Vec<VersionSetId>,
}

impl<VS: VersionSet, N: PackageName, D: DependencyProvider<VS, N>> Solver<VS, N, D> {
    /// Create a solver, using the provided pool
    pub fn new(provider: D) -> Self {
        Self {
            cache: SolverCache::new(provider),
            clauses: Arena::new(),
            requires_clauses: Default::default(),
            watches: WatchMap::new(),
            negative_assertions: Vec::new(),
            learnt_clauses: Arena::new(),
            learnt_why: Mapping::new(),
            learnt_clause_ids: Vec::new(),
            decision_tracker: DecisionTracker::new(),
            root_requirements: Default::default(),
            clauses_added_for_package: Default::default(),
            clauses_added_for_solvable: Default::default(),
        }
    }

    /// Returns a reference to the pool used by the solver
    pub fn pool(&self) -> &Pool<VS, N> {
        self.cache.pool()
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
    Conflict(SolvableId, bool, ClauseId),
    Cancelled(Box<dyn Any>),
}

impl<VS: VersionSet, N: PackageName + Display, D: DependencyProvider<VS, N>> Solver<VS, N, D> {
    /// Solves the provided `jobs` and returns a transaction from the found solution
    ///
    /// Returns a [`Problem`] if no solution was found, which provides ways to inspect the causes
    /// and report them to the user.
    pub fn solve(
        &mut self,
        root_requirements: Vec<VersionSetId>,
    ) -> Result<Vec<SolvableId>, UnsolvableOrCancelled> {
        // Clear state
        self.decision_tracker.clear();
        self.negative_assertions.clear();
        self.learnt_clauses.clear();
        self.learnt_why = Mapping::new();
        self.clauses = Default::default();
        self.root_requirements = root_requirements;

        // The first clause will always be the install root clause. Here we verify that this is
        // indeed the case.
        let root_clause = self.clauses.alloc(ClauseState::root());
        assert_eq!(root_clause, ClauseId::install_root());

        // Run SAT
        self.run_sat()?;

        let steps = self
            .decision_tracker
            .stack()
            .flat_map(|d| {
                if d.value && d.solvable_id != SolvableId::root() {
                    Some(d.solvable_id)
                } else {
                    // Ignore things that are set to false
                    None
                }
            })
            .collect();

        Ok(steps)
    }

    /// Adds a clause to the solver and immediately starts watching its literals.
    fn add_and_watch_clause(&mut self, clause: ClauseState) -> ClauseId {
        let clause_id = self.clauses.alloc(clause);
        let clause = &self.clauses[clause_id];

        // Add in requires clause lookup
        if let &Clause::Requires(solvable_id, version_set_id) = &clause.kind {
            self.requires_clauses
                .push((solvable_id, version_set_id, clause_id));
        }

        // Start watching the literals of the clause
        let clause = &mut self.clauses[clause_id];
        if clause.has_watches() {
            self.watches.start_watching(clause, clause_id);
        }

        clause_id
    }

    /// Adds clauses for a solvable. These clauses include requirements and constrains on other
    /// solvables.
    ///
    /// Returns the added clauses, and an additional list with conflicting clauses (if any).
    ///
    /// If the provider has requested the solving process to be cancelled, the cancellation value
    /// will be returned as an `Err(...)`.
    fn add_clauses_for_solvable(
        &mut self,
        solvable_id: SolvableId,
    ) -> Result<(Vec<ClauseId>, Vec<ClauseId>), Box<dyn Any>> {
        if self.clauses_added_for_solvable.contains(&solvable_id) {
            return Ok((Vec::new(), Vec::new()));
        }

        let mut new_clauses = Vec::new();
        let mut conflicting_clauses = Vec::new();
        let mut queue = vec![solvable_id];
        let mut seen = HashSet::new();
        seen.insert(solvable_id);

        while let Some(solvable_id) = queue.pop() {
            let solvable = self.pool().resolve_internal_solvable(solvable_id);
            tracing::trace!(
                "┝━ adding clauses for dependencies of {}",
                solvable.display(self.pool())
            );

            // Determine the dependencies of the current solvable. There are two cases here:
            // 1. The solvable is the root solvable which only provides required dependencies.
            // 2. The solvable is a package candidate in which case we request the corresponding
            //    dependencies from the `DependencyProvider`.
            let (requirements, constrains) = match solvable.inner {
                SolvableInner::Root => (self.root_requirements.clone(), Vec::new()),
                SolvableInner::Package(_) => {
                    let deps = self.cache.get_or_cache_dependencies(solvable_id)?;
                    match deps {
                        Dependencies::Known(deps) => {
                            (deps.requirements.clone(), deps.constrains.clone())
                        }
                        Dependencies::Unknown(reason) => {
                            // There is no information about the solvable's dependencies, so we add
                            // an exclusion clause for it
                            let clause_id = self
                                .clauses
                                .alloc(ClauseState::exclude(solvable_id, *reason));

                            // Exclusions are negative assertions, tracked outside of the watcher system
                            self.negative_assertions.push((solvable_id, clause_id));

                            // There might be a conflict now
                            let conflicts = if self.decision_tracker.assigned_value(solvable_id)
                                == Some(true)
                            {
                                vec![clause_id]
                            } else {
                                Vec::new()
                            };

                            // The new assertion should be kept in all cases (it is returned in the
                            // lhs of the tuple), and a conflicts should be reported if present (rhs
                            // of the tuple)
                            return Ok((vec![clause_id], conflicts));
                        }
                    }
                }
            };

            // Add clauses for the requirements
            for version_set_id in requirements {
                let dependency_name = self.pool().resolve_version_set_package_name(version_set_id);
                self.add_clauses_for_package(dependency_name)?;

                // Find all the solvables that match for the given version set
                let candidates = self.cache.get_or_cache_sorted_candidates(version_set_id)?;

                // Queue requesting the dependencies of the candidates as well if they are cheaply
                // available from the dependency provider.
                for &candidate in candidates {
                    if seen.insert(candidate)
                        && self.cache.are_dependencies_available_for(candidate)
                        && !self.clauses_added_for_solvable.contains(&candidate)
                    {
                        queue.push(candidate);
                    }
                }

                // Add the requires clause
                let no_candidates = candidates.is_empty();
                let (clause, conflict) = ClauseState::requires(
                    solvable_id,
                    version_set_id,
                    candidates,
                    &self.decision_tracker,
                );

                let clause_id = self.add_and_watch_clause(clause);

                if conflict {
                    conflicting_clauses.push(clause_id);
                } else if no_candidates {
                    // Add assertions for unit clauses (i.e. those with no matching candidates)
                    self.negative_assertions.push((solvable_id, clause_id));
                }

                new_clauses.push(clause_id);
            }

            // Add clauses for the constraints
            for version_set_id in constrains {
                let dependency_name = self.pool().resolve_version_set_package_name(version_set_id);
                self.add_clauses_for_package(dependency_name)?;

                // Find all the solvables that match for the given version set
                let constrained_candidates = self
                    .cache
                    .get_or_cache_non_matching_candidates(version_set_id)?;

                // Add forbidden clauses for the candidates
                for forbidden_candidate in constrained_candidates.iter().copied().collect_vec() {
                    let (clause, conflict) = ClauseState::constrains(
                        solvable_id,
                        forbidden_candidate,
                        version_set_id,
                        &self.decision_tracker,
                    );

                    let clause_id = self.add_and_watch_clause(clause);

                    if conflict {
                        conflicting_clauses.push(clause_id);
                    }

                    new_clauses.push(clause_id)
                }
            }

            // Start by stating the clauses have been added.
            self.clauses_added_for_solvable.insert(solvable_id);
        }

        Ok((new_clauses, conflicting_clauses))
    }

    /// Adds all clauses for a specific package name.
    ///
    /// These clauses include:
    ///
    /// 1. making sure that only a single candidate for the package is selected (forbid multiple)
    /// 2. if there is a locked candidate then that candidate is the only selectable candidate.
    ///
    /// If this function is called with the same package name twice, the clauses will only be added
    /// once.
    ///
    /// There is no need to propagate after adding these clauses because none of the clauses are
    /// assertions (only a single literal) and we assume that no decision has been made about any
    /// of the solvables involved. This assumption is checked when debug_assertions are enabled.
    ///
    /// If the provider has requested the solving process to be cancelled, the cancellation value
    /// will be returned as an `Err(...)`.
    fn add_clauses_for_package(&mut self, package_name: NameId) -> Result<(), Box<dyn Any>> {
        if self.clauses_added_for_package.contains(&package_name) {
            return Ok(());
        }

        tracing::trace!(
            "┝━ adding clauses for package '{}'",
            self.pool().resolve_package_name(package_name)
        );

        let package_candidates = self.cache.get_or_cache_candidates(package_name)?;
        let locked_solvable_id = package_candidates.locked;
        let candidates = &package_candidates.candidates;

        // Check the assumption that no decision has been made about any of the solvables.
        for &candidate in candidates {
            debug_assert!(
                self.decision_tracker.assigned_value(candidate).is_none(),
                "a decision has been made about a candidate of a package that was not properly added yet."
            );
        }

        // Each candidate gets a clause to disallow other candidates.
        for (i, &candidate) in candidates.iter().enumerate() {
            for &other_candidate in &candidates[i + 1..] {
                let clause_id = self
                    .clauses
                    .alloc(ClauseState::forbid_multiple(candidate, other_candidate));

                let clause = &mut self.clauses[clause_id];
                debug_assert!(clause.has_watches());
                self.watches.start_watching(clause, clause_id);
            }
        }

        // If there is a locked solvable, forbid other solvables.
        if let Some(locked_solvable_id) = locked_solvable_id {
            for &other_candidate in candidates {
                if other_candidate != locked_solvable_id {
                    let clause_id = self
                        .clauses
                        .alloc(ClauseState::lock(locked_solvable_id, other_candidate));

                    let clause = &mut self.clauses[clause_id];

                    debug_assert!(clause.has_watches());
                    self.watches.start_watching(clause, clause_id);
                }
            }
        }

        // Add a clause for solvables that are externally excluded.
        for (solvable, reason) in package_candidates.excluded.iter().copied() {
            let clause_id = self.clauses.alloc(ClauseState::exclude(solvable, reason));

            // Exclusions are negative assertions, tracked outside of the watcher system
            self.negative_assertions.push((solvable, clause_id));

            // Conflicts should be impossible here
            debug_assert!(self.decision_tracker.assigned_value(solvable) != Some(true));
        }

        self.clauses_added_for_package.insert(package_name);
        Ok(())
    }

    /// Run the CDCL algorithm to solve the SAT problem
    ///
    /// The CDCL algorithm's job is to find a valid assignment to the variables involved in the
    /// provided clauses. It works in the following steps:
    ///
    /// 1. __Set__: Assign a value to a variable that hasn't been assigned yet. An assignment in
    ///    this step starts a new "level" (the first one being level 1). If all variables have been
    ///    assigned, then we are done.
    /// 2. __Propagate__: Perform [unit
    ///    propagation](https://en.wikipedia.org/wiki/Unit_propagation). Assignments in this step
    ///    are associated to the same "level" as the decision that triggered them. This "level"
    ///    metadata is useful when it comes to handling conflicts. See [`Solver::propagate`] for the
    ///    implementation of this step.
    /// 3. __Learn__: If propagation finishes without conflicts, go back to 1. Otherwise find the
    ///    combination of assignments that caused the conflict and add a new clause to the solver to
    ///    forbid that combination of assignments (i.e. learn from this mistake so it is not
    ///    repeated in the future). Then backtrack and go back to step 1 or, if the learnt clause is
    ///    in conflict with existing clauses, declare the problem to be unsolvable. See
    ///    [`Solver::analyze`] for the implementation of this step.
    ///
    /// The solver loop can be found in [`Solver::resolve_dependencies`].
    fn run_sat(&mut self) -> Result<(), UnsolvableOrCancelled> {
        assert!(self.decision_tracker.is_empty());
        let mut level = 0;

        let mut new_clauses = Vec::new();
        loop {
            // A level of 0 means the decision loop has been completely reset because a partial
            // solution was invalidated by newly added clauses.
            if level == 0 {
                // Level 1 is the initial decision level
                level = 1;

                // Assign `true` to the root solvable. This must be installed to satisfy the solution.
                // The root solvable contains the dependencies that were injected when calling
                // `Solver::solve`. If we can find a solution were the root is installable we found a
                // solution that satisfies the user requirements.
                tracing::info!(
                    "╤══ install {} at level {level}",
                    SolvableId::root().display(self.pool())
                );
                self.decision_tracker
                    .try_add_decision(
                        Decision::new(SolvableId::root(), true, ClauseId::install_root()),
                        level,
                    )
                    .expect("already decided");

                // Add the clauses for the root solvable.
                let (mut clauses, conflicting_clauses) =
                    self.add_clauses_for_solvable(SolvableId::root())?;
                if let Some(clause_id) = conflicting_clauses.into_iter().next() {
                    return Err(UnsolvableOrCancelled::Unsolvable(
                        self.analyze_unsolvable(clause_id),
                    ));
                }
                new_clauses.append(&mut clauses);
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
                        tracing::debug!("├─ added clause {clause:?} introduces a conflict which invalidates the partial solution",
                                clause=self.clauses[clause_id].debug(self.pool()));
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

            // Enter the solver loop, return immediately if no new assignments have been made.
            level = self.resolve_dependencies(level)?;

            // We have a partial solution. E.g. there is a solution that satisfies all the clauses
            // that have been added so far.

            // Determine which solvables are part of the solution for which we did not yet get any
            // dependencies. If we find any such solvable it means we did not arrive at the full
            // solution yet.
            let new_solvables: Vec<_> = self
                .decision_tracker
                .stack()
                // Filter only decisions that led to a positive assignment
                .filter(|d| d.value)
                // Select solvables for which we do not yet have dependencies
                .filter(|d| !self.clauses_added_for_solvable.contains(&d.solvable_id))
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
                        "{} (derived from {:?})",
                        id.display(self.pool()),
                        self.clauses[derived_from].debug(self.pool()),
                    )))
            );

            for (solvable, _) in new_solvables {
                // Add the clauses for this particular solvable.
                let (mut clauses_for_solvable, conflicting_causes) =
                    self.add_clauses_for_solvable(solvable)?;
                new_clauses.append(&mut clauses_for_solvable);

                for &clause_id in &conflicting_causes {
                    // Backtrack in the case of conflicts
                    tracing::debug!("├─ added clause {clause:?} introduces a conflict which invalidates the partial solution",
                                clause=self.clauses[clause_id].debug(self.pool()));
                }

                if !conflicting_causes.is_empty() {
                    self.decision_tracker.clear();
                    level = 0;
                }
            }
        }
    }

    /// Resolves all dependencies
    ///
    /// Repeatedly chooses the next variable to assign, and calls [`Solver::set_propagate_learn`] to
    /// drive the solving process (as you can see from the name, the method executes the set,
    /// propagate and learn steps described in the [`Solver::run_sat`] docs).
    ///
    /// The next variable to assign is obtained by finding the next dependency for which no concrete
    /// package has been picked yet. Then we pick the highest possible version for that package, or
    /// the favored version if it was provided by the user, and set its value to true.
    fn resolve_dependencies(&mut self, mut level: u32) -> Result<u32, UnsolvableOrCancelled> {
        loop {
            // Make a decision. If no decision could be made it means the problem is satisfyable.
            let Some((candidate, required_by, clause_id)) = self.decide() else {
                break;
            };

            // Propagate the decision
            level = self.set_propagate_learn(level, candidate, required_by, clause_id)?;
        }

        // We just went through all clauses and there are no choices left to be made
        Ok(level)
    }

    /// Pick a solvable that we are going to assign true. This function uses a heuristic to
    /// determine to best decision to make. The function selects the requirement that has the least
    /// amount of working available candidates and selects the best candidate from that list. This
    /// ensures that if there are conflicts they are delt with as early as possible.
    fn decide(&mut self) -> Option<(SolvableId, SolvableId, ClauseId)> {
        let mut best_decision = None;
        for &(solvable_id, deps, clause_id) in self.requires_clauses.iter() {
            // Consider only clauses in which we have decided to install the solvable
            if self.decision_tracker.assigned_value(solvable_id) != Some(true) {
                continue;
            }

            // Consider only clauses in which no candidates have been installed
            let candidates = &self.cache.version_set_to_sorted_candidates[&deps];

            // Either find the first assignable candidate or determine that one of the candidates is
            // already assigned in which case the clause has already been satisfied.
            let candidate = candidates.iter().try_fold(
                (None, 0),
                |(first_selectable_candidate, selectable_candidates), &candidate| {
                    let assigned_value = self.decision_tracker.assigned_value(candidate);
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

        if let Some((count, (candidate, solvable_id, _clause_id))) = best_decision {
            tracing::info!(
                "deciding to assign {} with {} candidates (required by {})",
                candidate.display(self.pool()),
                count,
                solvable_id.display(self.pool())
            );
        }

        // Could not find a requirement that needs satisfying.
        best_decision.map(|d| d.1)
    }

    /// Executes one iteration of the CDCL loop
    ///
    /// A set-propagate-learn round is always initiated by a requirement clause (i.e.
    /// [`Clause::Requires`]). The parameters include the variable associated to the candidate for the
    /// dependency (`solvable`), the package that originates the dependency (`required_by`), and the
    /// id of the requires clause (`clause_id`).
    ///
    /// Refer to the documentation of [`Solver::run_sat`] for details on the CDCL algorithm.
    ///
    /// Returns the new level after this set-propagate-learn round, or a [`Problem`] if we
    /// discovered that the requested jobs are unsatisfiable.
    fn set_propagate_learn(
        &mut self,
        mut level: u32,
        solvable: SolvableId,
        required_by: SolvableId,
        clause_id: ClauseId,
    ) -> Result<u32, UnsolvableOrCancelled> {
        level += 1;

        tracing::info!(
            "╤══ Install {} at level {level} (required by {})",
            solvable.display(self.pool()),
            required_by.display(self.pool()),
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
        conflicting_solvable: SolvableId,
        attempted_value: bool,
        conflicting_clause: ClauseId,
    ) -> Result<u32, Problem> {
        {
            tracing::info!(
                "├─ Propagation conflicted: could not set {solvable} to {attempted_value}",
                solvable = conflicting_solvable.display(self.pool())
            );
            tracing::info!(
                "│  During unit propagation for clause: {:?}",
                self.clauses[conflicting_clause].debug(self.pool())
            );

            tracing::info!(
                "│  Previously decided value: {}. Derived from: {:?}",
                !attempted_value,
                self.clauses[self
                    .decision_tracker
                    .find_clause_for_assignment(conflicting_solvable)
                    .unwrap()]
                .debug(self.pool()),
            );
        }

        if level == 1 {
            tracing::info!("╘══ UNSOLVABLE");
            for decision in self.decision_tracker.stack() {
                let clause = &self.clauses[decision.derived_from];
                let level = self.decision_tracker.level(decision.solvable_id);
                let action = if decision.value { "install" } else { "forbid" };

                if let Clause::ForbidMultipleInstances(..) = clause.kind {
                    // Skip forbids clauses, to reduce noise
                    continue;
                }

                tracing::info!(
                    "* ({level}) {action} {}. Reason: {:?}",
                    decision.solvable_id.display(self.pool()),
                    clause.debug(self.pool()),
                );
            }

            return Err(self.analyze_unsolvable(conflicting_clause));
        }

        let (new_level, learned_clause_id, literal) =
            self.analyze(level, conflicting_solvable, conflicting_clause);
        level = new_level;

        tracing::debug!("├─ Backtracked to level {level}");

        // Optimization: propagate right now, since we know that the clause is a unit clause
        let decision = literal.satisfying_value();
        self.decision_tracker
            .try_add_decision(
                Decision::new(literal.solvable_id, decision, learned_clause_id),
                level,
            )
            .expect("bug: solvable was already decided!");
        tracing::debug!(
            "├─ Propagate after learn: {} = {decision}",
            literal.solvable_id.display(self.pool())
        );

        Ok(level)
    }

    /// The propagate step of the CDCL algorithm
    ///
    /// Propagation is implemented by means of watches: each clause that has two or more literals is
    /// "subscribed" to changes in the values of two solvables that appear in the clause. When a value
    /// is assigned to a solvable, each of the clauses tracking that solvable will be notified. That
    /// way, the clause can check whether the literal that is using the solvable has become false, in
    /// which case it picks a new solvable to watch (if available) or triggers an assignment.
    fn propagate(&mut self, level: u32) -> Result<(), PropagationError> {
        if let Some(value) = self.cache.provider.should_cancel_with_value() {
            return Err(PropagationError::Cancelled(value));
        };

        // Negative assertions derived from other rules (assertions are clauses that consist of a
        // single literal, and therefore do not have watches)
        for &(solvable_id, clause_id) in &self.negative_assertions {
            let value = false;
            let decided = self
                .decision_tracker
                .try_add_decision(Decision::new(solvable_id, value, clause_id), level)
                .map_err(|_| PropagationError::Conflict(solvable_id, value, clause_id))?;

            if decided {
                tracing::trace!(
                    "├─ Propagate assertion {} = {}",
                    solvable_id.display(self.pool()),
                    value
                );
            }
        }

        // Assertions derived from learnt rules
        for learn_clause_idx in 0..self.learnt_clause_ids.len() {
            let clause_id = self.learnt_clause_ids[learn_clause_idx];
            let clause = &self.clauses[clause_id];
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
                    literal.solvable_id.display(self.pool()),
                    decision
                );
            }
        }

        // Watched solvables
        while let Some(decision) = self.decision_tracker.next_unpropagated() {
            let pkg = decision.solvable_id;

            // Propagate, iterating through the linked list of clauses that watch this solvable
            let mut old_predecessor_clause_id: Option<ClauseId>;
            let mut predecessor_clause_id: Option<ClauseId> = None;
            let mut clause_id = self.watches.first_clause_watching_solvable(pkg);
            while !clause_id.is_null() {
                if predecessor_clause_id == Some(clause_id) {
                    panic!("Linked list is circular!");
                }

                // Get mutable access to both clauses.
                let (predecessor_clause, clause) =
                    if let Some(prev_clause_id) = predecessor_clause_id {
                        let (predecessor_clause, clause) =
                            self.clauses.get_two_mut(prev_clause_id, clause_id);
                        (Some(predecessor_clause), clause)
                    } else {
                        (None, &mut self.clauses[clause_id])
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
                                        "├─ Propagate {} = {}. {:?}",
                                        remaining_watch.solvable_id.display(self.cache.pool()),
                                        remaining_watch.satisfying_value(),
                                        clause.debug(self.cache.pool()),
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
    /// Because learnt clauses are not relevant for the user, they are not added to the `Problem`.
    /// Instead, we report the clauses that caused them.
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

    /// Create a [`Problem`] based on the id of the clause that triggered an unrecoverable conflict
    fn analyze_unsolvable(&mut self, clause_id: ClauseId) -> Problem {
        let last_decision = self.decision_tracker.stack().last().unwrap();
        let highest_level = self.decision_tracker.level(last_decision.solvable_id);
        debug_assert_eq!(highest_level, 1);

        let mut problem = Problem::default();

        tracing::info!("=== ANALYZE UNSOLVABLE");

        let mut involved = HashSet::new();
        self.clauses[clause_id].kind.visit_literals(
            &self.learnt_clauses,
            &self.cache.version_set_to_sorted_candidates,
            |literal| {
                involved.insert(literal.solvable_id);
            },
        );

        let mut seen = HashSet::new();
        Self::analyze_unsolvable_clause(
            &self.clauses,
            &self.learnt_why,
            clause_id,
            &mut problem,
            &mut seen,
        );

        for decision in self.decision_tracker.stack().rev() {
            if decision.solvable_id == SolvableId::root() {
                continue;
            }

            let why = decision.derived_from;

            if !involved.contains(&decision.solvable_id) {
                continue;
            }

            assert_ne!(why, ClauseId::install_root());

            Self::analyze_unsolvable_clause(
                &self.clauses,
                &self.learnt_why,
                why,
                &mut problem,
                &mut seen,
            );

            self.clauses[why].kind.visit_literals(
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
    /// This function finds the combination of assignments that caused the conflict and adds a new
    /// clause to the solver to forbid that combination of assignments (i.e. learn from this mistake
    /// so it is not repeated in the future). It corresponds to the `Solver.analyze` function from
    /// the MiniSAT paper.
    ///
    /// Returns the level to which we should backtrack, the id of the learnt clause and the literal
    /// that should be assigned (by definition, when we learn a clause, all its literals except one
    /// evaluate to false, so the value of the remaining literal must be assigned to make the clause
    /// become true)
    fn analyze(
        &mut self,
        mut current_level: u32,
        mut conflicting_solvable: SolvableId,
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

            self.clauses[clause_id].kind.visit_literals(
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

                // We are interested in the first literal we come across that caused the conflicting
                // assignment
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

        let clause_id = self.clauses.alloc(ClauseState::learnt(learnt_id, &learnt));
        self.learnt_clause_ids.push(clause_id);

        let clause = &mut self.clauses[clause_id];
        if clause.has_watches() {
            self.watches.start_watching(clause, clause_id);
        }

        tracing::debug!("├─ Learnt disjunction:",);
        for lit in learnt {
            tracing::debug!(
                "│  - {}{}",
                if lit.negate { "NOT " } else { "" },
                lit.solvable_id.display(self.pool())
            );
        }

        // Should revert at most to the root level
        let target_level = back_track_to.max(1);
        self.decision_tracker.undo_until(target_level);

        (target_level, clause_id, last_literal)
    }
}

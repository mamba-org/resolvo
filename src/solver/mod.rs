use std::{any::Any, cell::RefCell, fmt::Display, future::ready, ops::ControlFlow};

use ahash::{HashMap, HashSet};
pub use cache::SolverCache;
use clause::{Clause, ClauseState, Literal};
use decision::Decision;
use decision_tracker::DecisionTracker;
use futures::{stream::FuturesUnordered, FutureExt, StreamExt};
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use watch_map::WatchMap;

use crate::{
    conflict::Conflict,
    internal::{
        arena::{Arena, ArenaId},
        id::{ClauseId, InternalSolvableId, LearntClauseId, NameId, SolvableId},
        mapping::Mapping,
    },
    runtime::{AsyncRuntime, NowOrNeverRuntime},
    Candidates, Dependencies, DependencyProvider, KnownDependencies, Requirement, VersionSetId,
};

mod cache;
pub(crate) mod clause;
mod decision;
mod decision_map;
mod decision_tracker;
mod watch_map;

#[derive(Default)]
struct AddClauseOutput {
    new_requires_clauses: Vec<(InternalSolvableId, Requirement, ClauseId)>,
    conflicting_clauses: Vec<ClauseId>,
    negative_assertions: Vec<(InternalSolvableId, ClauseId)>,
    clauses_to_watch: Vec<ClauseId>,
    new_names: Vec<NameId>,
}

/// Describes the problem that is to be solved by the solver.
///
/// This struct is generic over the type `S` of the collection of soft
/// requirements passed to the solver, typically expected to be a type
/// implementing [`IntoIterator`].
///
/// This struct follows the builder pattern and can have its fields set by one
/// of the available setter methods.
pub struct Problem<S> {
    requirements: Vec<Requirement>,
    constraints: Vec<VersionSetId>,
    soft_requirements: S,
}

impl Default for Problem<std::iter::Empty<SolvableId>> {
    fn default() -> Self {
        Self::new()
    }
}

impl Problem<std::iter::Empty<SolvableId>> {
    /// Creates a new empty [`Problem`]. Use the setter methods to build the
    /// problem before passing it to the solver to be solved.
    pub fn new() -> Self {
        Self {
            requirements: Default::default(),
            constraints: Default::default(),
            soft_requirements: Default::default(),
        }
    }
}

impl<S: IntoIterator<Item = SolvableId>> Problem<S> {
    /// Sets the requirements that _must_ have one candidate solvable be
    /// included in the solution.
    ///
    /// Returns the [`Problem`] for further mutation or to pass to
    /// [`Solver::solve`].
    pub fn requirements(self, requirements: Vec<Requirement>) -> Self {
        Self {
            requirements,
            ..self
        }
    }

    /// Sets the additional constraints imposed on individual packages that the
    /// solvable (if any) chosen for that package _must_ adhere to.
    ///
    /// Returns the [`Problem`] for further mutation or to pass to
    /// [`Solver::solve`].
    pub fn constraints(self, constraints: Vec<VersionSetId>) -> Self {
        Self {
            constraints,
            ..self
        }
    }

    /// Sets the additional requirements that the solver should _try_ and
    /// fulfill once it has found a solution to the main problem.
    ///
    /// An unsatisfiable soft requirement does not cause a conflict; the solver
    /// will try and fulfill as many soft requirements as possible and skip
    /// the unsatisfiable ones.
    ///
    /// Soft requirements are currently only specified as individual solvables
    /// to be included in the solution, however in the future they will be
    /// able to be specified as version sets.
    ///
    /// # Returns
    ///
    /// Returns the [`Problem`] for further mutation or to pass to
    /// [`Solver::solve`].
    pub fn soft_requirements<I: IntoIterator<Item = SolvableId>>(
        self,
        soft_requirements: I,
    ) -> Problem<I> {
        Problem {
            requirements: self.requirements,
            constraints: self.constraints,
            soft_requirements,
        }
    }
}

#[derive(Default)]
pub(crate) struct Clauses {
    pub(crate) kinds: RefCell<Vec<Clause>>,
    states: RefCell<Vec<ClauseState>>,
}

impl Clauses {
    pub fn alloc(&self, state: ClauseState, kind: Clause) -> ClauseId {
        let mut kinds = self.kinds.borrow_mut();
        let mut states = self.states.borrow_mut();
        let id = ClauseId::from_usize(kinds.len());
        kinds.push(kind);
        states.push(state);
        id
    }
}

/// Drives the SAT solving process.
pub struct Solver<D: DependencyProvider, RT: AsyncRuntime = NowOrNeverRuntime> {
    pub(crate) async_runtime: RT,
    pub(crate) cache: SolverCache<D>,

    pub(crate) clauses: Clauses,
    requires_clauses:
        IndexMap<InternalSolvableId, Vec<(Requirement, ClauseId)>, ahash::RandomState>,
    watches: WatchMap,

    negative_assertions: Vec<(InternalSolvableId, ClauseId)>,

    learnt_clauses: Arena<LearntClauseId, Vec<Literal>>,
    learnt_why: Mapping<LearntClauseId, Vec<ClauseId>>,
    learnt_clause_ids: Vec<ClauseId>,

    clauses_added_for_package: RefCell<HashSet<NameId>>,
    clauses_added_for_solvable: RefCell<HashSet<InternalSolvableId>>,
    forbidden_clauses_added: RefCell<HashMap<NameId, IndexSet<InternalSolvableId>>>,

    decision_tracker: DecisionTracker,

    /// The [`Requirement`]s that must be installed as part of the solution.
    root_requirements: Vec<Requirement>,

    /// Additional constraints imposed by the root.
    root_constraints: Vec<VersionSetId>,

    /// Activity score per package.
    name_activity: Vec<f32>,

    /// The activity add factor. This is a value that is added to the activity
    /// score of each package that is part of a conflict.
    activity_add: f32,

    /// The activity decay factor. This is a value between 0 and 1 with which
    /// the activity scores of each package are multiplied when a conflict is
    /// detected.
    activity_decay: f32,
}

impl<D: DependencyProvider> Solver<D, NowOrNeverRuntime> {
    /// Creates a single threaded block solver, using the provided
    /// [`DependencyProvider`].
    pub fn new(provider: D) -> Self {
        Self {
            cache: SolverCache::new(provider),
            async_runtime: NowOrNeverRuntime,
            clauses: Clauses::default(),
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
            forbidden_clauses_added: Default::default(),
            name_activity: Default::default(),

            activity_add: 1.0,
            activity_decay: 0.95,
        }
    }
}

/// The root cause of a solver error.
#[derive(Debug)]
pub enum UnsolvableOrCancelled {
    /// The problem was unsolvable.
    Unsolvable(Conflict),
    /// The solving process was cancelled.
    Cancelled(Box<dyn Any>),
}

impl From<Conflict> for UnsolvableOrCancelled {
    fn from(value: Conflict) -> Self {
        UnsolvableOrCancelled::Unsolvable(value)
    }
}

impl From<Box<dyn Any>> for UnsolvableOrCancelled {
    fn from(value: Box<dyn Any>) -> Self {
        UnsolvableOrCancelled::Cancelled(value)
    }
}

/// An error during the propagation step
#[derive(Debug)]
pub(crate) enum PropagationError {
    Conflict(InternalSolvableId, bool, ClauseId),
    Cancelled(Box<dyn Any>),
}

impl Display for PropagationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PropagationError::Conflict(solvable, value, clause) => {
                write!(
                    f,
                    "conflict while propagating solvable {:?}, value {} caused by clause {:?}",
                    solvable, value, clause
                )
            }
            PropagationError::Cancelled(_) => {
                write!(f, "propagation was cancelled")
            }
        }
    }
}

impl<D: DependencyProvider, RT: AsyncRuntime> Solver<D, RT> {
    /// Returns the dependency provider used by this instance.
    pub fn provider(&self) -> &D {
        self.cache.provider()
    }

    /// Set the runtime of the solver to `runtime`.
    #[must_use]
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
            forbidden_clauses_added: self.forbidden_clauses_added,
            decision_tracker: self.decision_tracker,
            root_requirements: self.root_requirements,
            root_constraints: self.root_constraints,
            name_activity: self.name_activity,
            activity_add: self.activity_add,
            activity_decay: self.activity_decay,
        }
    }

    /// Configure activity andd and decay parameters. This enables tweaking
    /// these parameters.
    #[must_use]
    pub fn with_activity_params(self, add: f32, decay: f32) -> Self {
        Self {
            activity_add: add,
            activity_decay: decay,
            ..self
        }
    }

    /// Solves the given [`Problem`].
    ///
    /// The solver first solves for the root requirements and constraints, and
    /// then tries to include in the solution as many of the soft
    /// requirements as it can. Each soft requirement is subject to all the
    /// clauses and decisions introduced for all the previously decided
    /// solvables in the solution.
    ///
    /// Unless the corresponding package has been requested by a version set in
    /// another solvable's clauses, each soft requirement is _not_ subject
    /// to the package-level clauses introduced in
    /// [`DependencyProvider::get_candidates`] since the solvables have been
    /// requested specifically (not through a version set) in the solution.
    ///
    /// # Returns
    ///
    /// If a solution was found, returns a [`Vec`] of the solvables included in
    /// the solution.
    ///
    /// If no solution to the _root_ requirements and constraints was found,
    /// returns a [`Conflict`] wrapped in a
    /// [`UnsolvableOrCancelled::Unsolvable`], which provides ways to
    /// inspect the causes and report them to the user. If a soft requirement is
    /// unsolvable, it is simply not included in the solution.
    ///
    /// If the solution process is cancelled (see
    /// [`DependencyProvider::should_cancel_with_value`]), returns an
    /// [`UnsolvableOrCancelled::Cancelled`] containing the cancellation value.
    pub fn solve(
        &mut self,
        problem: Problem<impl IntoIterator<Item = SolvableId>>,
    ) -> Result<Vec<SolvableId>, UnsolvableOrCancelled> {
        self.decision_tracker.clear();
        self.negative_assertions.clear();
        self.learnt_clauses.clear();
        self.learnt_why = Mapping::new();
        self.clauses = Clauses::default();
        self.root_requirements = problem.requirements;
        self.root_constraints = problem.constraints;

        // The first clause will always be the install root clause. Here we verify that
        // this is indeed the case.
        let root_clause = {
            let (state, kind) = ClauseState::root();
            self.clauses.alloc(state, kind)
        };
        assert_eq!(root_clause, ClauseId::install_root());

        assert!(
            self.run_sat(InternalSolvableId::root())?,
            "bug: Since root is the first requested solvable, \
                  should have returned Err instead of Ok(false) if root is unsolvable"
        );

        for additional in problem.soft_requirements {
            let additional = additional.into();

            if self.decision_tracker.assigned_value(additional).is_none() {
                self.run_sat(additional)?;
            }
        }

        Ok(self.chosen_solvables().collect())
    }

    /// Returns the solvables that the solver has chosen to include in the
    /// solution so far.
    fn chosen_solvables(&self) -> impl Iterator<Item = SolvableId> + '_ {
        self.decision_tracker.stack().filter_map(|d| {
            if d.value {
                d.solvable_id.as_solvable()
            } else {
                // Ignore things that are set to false
                None
            }
        })
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

        tracing::trace!("Add clauses for solvables");

        pub enum TaskResult<'i> {
            Dependencies {
                solvable_id: InternalSolvableId,
                dependencies: Dependencies,
            },
            SortedCandidates {
                solvable_id: InternalSolvableId,
                requirement: Requirement,
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

                            let (state, kind) = ClauseState::exclude(solvable_id, reason);
                            let clause_id = self.clauses.alloc(state, kind);

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

                    for version_set_id in requirements
                        .iter()
                        .flat_map(|requirement| requirement.version_sets(self.provider()))
                        .chain(constrains.iter().copied())
                    {
                        let dependency_name = self.provider().version_set_name(version_set_id);
                        if clauses_added_for_package.insert(dependency_name) {
                            tracing::trace!(
                                "┝━ Adding clauses for package '{}'",
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

                    for requirement in requirements {
                        // Find all the solvable that match for the given version set
                        pending_futures.push(
                            async move {
                                let candidates = self
                                    .cache
                                    .get_or_cache_sorted_candidates(requirement)
                                    .await?;
                                Ok(TaskResult::SortedCandidates {
                                    solvable_id,
                                    requirement,
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
                        "Package candidates available for {}",
                        self.provider().display_name(name_id)
                    );

                    output.new_names.push(name_id);

                    let locked_solvable_id = package_candidates.locked;
                    let candidates = &package_candidates.candidates;

                    // If there is a locked solvable, forbid other solvables.
                    if let Some(locked_solvable_id) = locked_solvable_id {
                        for &other_candidate in candidates {
                            if other_candidate != locked_solvable_id {
                                let (state, kind) = ClauseState::lock(
                                    locked_solvable_id.into(),
                                    other_candidate.into(),
                                );
                                let clause_id = self.clauses.alloc(state, kind);

                                debug_assert!(self.clauses.states.borrow_mut()
                                    [clause_id.to_usize()]
                                .has_watches());
                                output.clauses_to_watch.push(clause_id);
                            }
                        }
                    }

                    // Add a clause for solvables that are externally excluded.
                    for (solvable, reason) in package_candidates.excluded.iter().copied() {
                        let (state, kind) = ClauseState::exclude(solvable.into(), reason);
                        let clause_id = self.clauses.alloc(state, kind);

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
                    requirement,
                    candidates,
                } => {
                    tracing::trace!(
                        "Sorted candidates available for {}",
                        requirement.display(self.provider()),
                    );

                    // Queue requesting the dependencies of the candidates as well if they are
                    // cheaply available from the dependency provider.
                    for &candidate in candidates {
                        if !seen.insert(candidate.into()) {
                            continue;
                        }

                        // If the dependencies are already available for the
                        // candidate, queue the candidate for processing.
                        if self.cache.are_dependencies_available_for(candidate)
                            && clauses_added_for_solvable.insert(candidate.into())
                        {
                            pending_solvables.push(candidate.into());
                        }

                        // Add forbid constraints for this solvable on all other
                        // solvables that have been visited already for the same
                        // version set name.
                        let name_id = self.provider().solvable_name(candidate);
                        let mut forbidden_clauses_added = self.forbidden_clauses_added.borrow_mut();
                        let other_solvables = forbidden_clauses_added.entry(name_id).or_default();
                        let candidate = InternalSolvableId::from(candidate);
                        if other_solvables.insert(candidate) {
                            for &other_candidate in other_solvables.iter() {
                                if candidate == other_candidate {
                                    continue;
                                }

                                let (state, kind) = ClauseState::forbid_multiple(
                                    candidate,
                                    other_candidate,
                                    name_id,
                                );
                                let clause_id = self.clauses.alloc(state, kind);

                                debug_assert!(self.clauses.states.borrow_mut()
                                    [clause_id.to_usize()]
                                .has_watches());
                                output.clauses_to_watch.push(clause_id);
                            }
                        }
                    }

                    // Add the requirements clause
                    let no_candidates = candidates.is_empty();
                    let (state, conflict, kind) = ClauseState::requires(
                        solvable_id,
                        requirement,
                        candidates,
                        &self.decision_tracker,
                    );
                    let has_watches = state.has_watches();
                    let clause_id = self.clauses.alloc(state, kind);

                    if has_watches {
                        output.clauses_to_watch.push(clause_id);
                    }

                    output
                        .new_requires_clauses
                        .push((solvable_id, requirement, clause_id));

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
                        let (state, conflict, kind) = ClauseState::constrains(
                            solvable_id,
                            forbidden_candidate.into(),
                            version_set_id,
                            &self.decision_tracker,
                        );

                        let clause_id = self.clauses.alloc(state, kind);
                        output.clauses_to_watch.push(clause_id);

                        if conflict {
                            output.conflicting_clauses.push(clause_id);
                        }
                    }
                }
            }
        }

        tracing::trace!("Done adding clauses for solvables");

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
    ///
    /// Returns `Ok(true)` if a solution was found for `solvable`. If a solution
    /// was not found, returns `Ok(false)` if some decisions have already
    /// been made by the solver (i.e. the decision tracker stack is not
    /// empty). Otherwise, returns [`UnsolvableOrCancelled::Unsolvable`] as
    /// an `Err` on no solution.
    ///
    /// If the solution process is cancelled (see
    /// [`DependencyProvider::should_cancel_with_value`]),
    /// returns [`UnsolvableOrCancelled::Cancelled`] as an `Err`.
    fn run_sat(&mut self, solvable: InternalSolvableId) -> Result<bool, UnsolvableOrCancelled> {
        let starting_level = self
            .decision_tracker
            .stack()
            .next_back()
            .map(|decision| self.decision_tracker.level(decision.solvable_id))
            .unwrap_or(0);

        let mut level = starting_level;

        loop {
            if level == starting_level {
                tracing::trace!("Level {starting_level}: Resetting the decision loop");
            } else {
                tracing::trace!("Level {}: Starting the decision loop", level);
            }

            // A level of starting_level means the decision loop has been completely reset
            // because a partial solution was invalidated by newly added clauses.
            if level == starting_level {
                // Level starting_level + 1 is the initial decision level
                level = starting_level + 1;

                // Assign `true` to the root solvable. This must be installed to satisfy the
                // solution. The root solvable contains the dependencies that
                // were injected when calling `Solver::solve`. If we can find a
                // solution were the root is installable we found a
                // solution that satisfies the user requirements.
                tracing::trace!(
                    "╤══ Install {} at level {level}",
                    solvable.display(self.provider())
                );
                self.decision_tracker
                    .try_add_decision(
                        Decision::new(solvable, true, ClauseId::install_root()),
                        level,
                    )
                    .expect("already decided");

                // Add the clauses for the root solvable.
                let output = self
                    .async_runtime
                    .block_on(self.add_clauses_for_solvables([solvable]))?;
                if let Err(clause_id) = self.process_add_clause_output(output) {
                    return self.run_sat_process_unsolvable(solvable, starting_level, clause_id);
                }
            }

            tracing::trace!("Level {}: Propagating", level);

            // Propagate decisions from assignments above
            let propagate_result = self.propagate(level);

            tracing::trace!("Propagate result: {:?}", propagate_result);

            // Handle propagation errors
            match propagate_result {
                Ok(()) => {}
                Err(PropagationError::Conflict(_, _, clause_id)) => {
                    if level == starting_level + 1 {
                        return self.run_sat_process_unsolvable(
                            solvable,
                            starting_level,
                            clause_id,
                        );
                    } else {
                        // The conflict was caused because new clauses have been added dynamically.
                        // We need to start over.
                        tracing::debug!("├─ added clause {clause} introduces a conflict which invalidates the partial solution",
                                clause=self.clauses.kinds.borrow()[clause_id.to_usize()].display(self.provider()));
                        level = starting_level;
                        self.decision_tracker.undo_until(starting_level);
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
            tracing::trace!("Level {}: Resolving dependencies", level);
            level = self.resolve_dependencies(level)?;
            tracing::trace!("Level {}: Done resolving dependencies", level);

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
                tracing::trace!(
                    "Level {}: No new solvables selected, solution is complete",
                    level
                );
                return Ok(true);
            }

            tracing::debug!("==== Found newly selected solvables");
            tracing::debug!(
                " - {}",
                new_solvables
                    .iter()
                    .copied()
                    .format_with("\n- ", |(id, derived_from), f| f(&format_args!(
                        "{} (derived from {})",
                        id.display(self.provider()),
                        self.clauses.kinds.borrow()[derived_from.to_usize()]
                            .display(self.provider()),
                    )))
            );
            tracing::debug!("====");

            // Concurrently get the solvable's clauses
            let output = self.async_runtime.block_on(self.add_clauses_for_solvables(
                new_solvables.iter().map(|(solvable_id, _)| *solvable_id),
            ))?;

            // Serially process the outputs, to reduce the need for synchronization
            for &clause_id in &output.conflicting_clauses {
                tracing::debug!("├─ Added clause {clause} introduces a conflict which invalidates the partial solution",
                                        clause=self.clauses.kinds.borrow()[clause_id.to_usize()].display(self.provider()));
            }

            if let Err(_first_conflicting_clause_id) = self.process_add_clause_output(output) {
                self.decision_tracker.undo_until(starting_level);
                level = starting_level;
            }
        }
    }

    /// Decides how to terminate the solver algorithm when the given `solvable`
    /// was deemed unsolvable by [`Solver::run_sat`].
    ///
    /// Returns an `Err` value of [`UnsolvableOrCancelled::Unsolvable`] only if
    /// `solvable` is the very first solvable we are solving for. Otherwise,
    /// undoes all the decisions made when trying to solve for `solvable`,
    /// sets it to `false` and returns `Ok(false)`.
    fn run_sat_process_unsolvable(
        &mut self,
        solvable: InternalSolvableId,
        starting_level: u32,
        clause_id: ClauseId,
    ) -> Result<bool, UnsolvableOrCancelled> {
        if starting_level == 0 {
            tracing::trace!("Unsolvable: {:?}", clause_id);
            Err(UnsolvableOrCancelled::Unsolvable(
                self.analyze_unsolvable(clause_id),
            ))
        } else {
            self.decision_tracker.undo_until(starting_level);
            self.decision_tracker
                .try_add_decision(
                    Decision::new(solvable, false, ClauseId::install_root()),
                    starting_level + 1,
                )
                .expect("bug: already decided - decision should have been undone");
            Ok(false)
        }
    }

    fn process_add_clause_output(&mut self, mut output: AddClauseOutput) -> Result<(), ClauseId> {
        let mut clauses = self.clauses.states.borrow_mut();
        for clause_id in output.clauses_to_watch {
            debug_assert!(
                clauses[clause_id.to_usize()].has_watches(),
                "attempting to watch a clause without watches!"
            );
            self.watches
                .start_watching(&mut clauses[clause_id.to_usize()], clause_id);
        }

        for (solvable_id, requirement, clause_id) in output.new_requires_clauses {
            self.requires_clauses
                .entry(solvable_id)
                .or_default()
                .push((requirement, clause_id));
        }
        self.negative_assertions
            .append(&mut output.negative_assertions);

        if let Some(max_name_idx) = output
            .new_names
            .into_iter()
            .map(|name_id| name_id.to_usize())
            .max()
        {
            if self.name_activity.len() <= max_name_idx {
                self.name_activity.resize(max_name_idx + 1, 0.0);
            }
        }

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

            tracing::info!(
                "╒══ Install {} at level {level} (derived from {})",
                candidate.display(self.provider()),
                self.clauses.kinds.borrow()[clause_id.to_usize()].display(self.provider())
            );

            // Propagate the decision
            match self.set_propagate_learn(level, candidate, required_by, clause_id) {
                Ok(new_level) => {
                    level = new_level;
                    tracing::info!("╘══ Propagation completed");
                }
                Err(UnsolvableOrCancelled::Cancelled(value)) => {
                    tracing::info!("╘══ Propagation cancelled");
                    return Err(UnsolvableOrCancelled::Cancelled(value));
                }
                Err(UnsolvableOrCancelled::Unsolvable(conflict)) => {
                    tracing::info!("╘══ Propagation resulted in a conflict");
                    return Err(UnsolvableOrCancelled::Unsolvable(conflict));
                }
            }
        }

        // We just went through all clauses and there are no choices left to be made
        Ok(level)
    }

    /// This function is responsible for selecting the next solvable to assign
    /// after all logical decisions have been propagated. Once this situation
    /// happens we need to take a guess to make progress in the solving process.
    /// This function tries to find the best guess to make based on several
    /// heuristics. These heuristics are tuned to find a solution that also
    /// maximizes the user's requirements.
    ///
    /// The heuristics are (in order of importance):
    /// 1. Prefer decisions on explicit requirements over non-explicit
    ///    requirements. This ensures that direct dependencies are maximized
    ///    over transitive dependencies.
    /// 2. Prefer decisions with a higher "package activity score". This score
    ///    is incremented everytime a package is involved in a conflict and the
    ///    score of all package is decreases on each conflict. This is similar
    ///    to the "activity score" of the VSIDS algorithm used in many modern
    ///    solvers.
    /// 3. Prefer decisions with the least amount of possible candidates. If
    ///    there are multiple requirements for the same package the requirement
    ///    with the least amount of possible candidates requires less
    ///    backtracking to determine unsatisfiability than a requirement with
    ///    more possible candidates.
    fn decide(&mut self) -> Option<(InternalSolvableId, InternalSolvableId, ClauseId)> {
        struct PossibleDecision {
            /// The activity of the package that is selected
            package_activity: f32,

            /// If this decision is based on a requirement that is explicitly
            /// requested by the user.
            is_explicit_requirement: bool,

            /// The total number of possible candidates that are available for
            /// this requirement.
            candidate_count: u32,

            /// The decision to make.
            decision: (SolvableId, InternalSolvableId, ClauseId),
        }

        let mut best_decision: Option<PossibleDecision> = None;
        for (&solvable_id, requirements) in self.requires_clauses.iter() {
            let is_explicit_requirement = solvable_id == InternalSolvableId::root();
            if let Some(best_decision) = &best_decision {
                // If we already have an explicit requirement, there is no need to evaluate
                // non-explicit requirements.
                if best_decision.is_explicit_requirement && !is_explicit_requirement {
                    continue;
                }
            }

            // Consider only clauses in which we have decided to install the solvable
            if self.decision_tracker.assigned_value(solvable_id) != Some(true) {
                continue;
            }

            for (deps, clause_id) in requirements.iter() {
                let mut candidate = ControlFlow::Break(());

                // Iterate over all version sets in the requirement and find the first version
                // set that we can act on, or if a single candidate (from any version set) makes
                // the clause true.
                for version_set in deps.version_sets(self.provider()) {
                    // Consider only clauses in which no candidates have been installed
                    let candidates = &self.cache.requirement_to_sorted_candidates
                        [&Requirement::Single(version_set)];

                    // Find the first candidate that is not yet assigned a value or find the first
                    // value that makes this clause true.
                    candidate = candidates.iter().try_fold(
                        match candidate {
                            ControlFlow::Continue(x) => x,
                            _ => None,
                        },
                        |first_candidate, &candidate| {
                            let assigned_value =
                                self.decision_tracker.assigned_value(candidate.into());
                            ControlFlow::Continue(match assigned_value {
                                Some(true) => {
                                    // This candidate has already been assigned so the clause is
                                    // already true. Skip it.
                                    return ControlFlow::Break(());
                                }
                                Some(false) => {
                                    // This candidate has already been assigned false, continue the
                                    // search.
                                    first_candidate
                                }
                                None => match first_candidate {
                                    Some((
                                        first_candidate,
                                        candidate_version_set,
                                        mut candidate_count,
                                        package_activity,
                                    )) => {
                                        // We found a candidate that has not been assigned yet, but
                                        // it is not the first candidate.
                                        if candidate_version_set == version_set {
                                            // Increment the candidate count if this is a candidate
                                            // in the same version set.
                                            candidate_count += 1u32;
                                        }
                                        Some((
                                            first_candidate,
                                            candidate_version_set,
                                            candidate_count,
                                            package_activity,
                                        ))
                                    }
                                    None => {
                                        // We found the first candidate that has not been assigned
                                        // yet.
                                        let package_activity = self.name_activity[self
                                            .provider()
                                            .version_set_name(version_set)
                                            .to_usize()];
                                        Some((candidate, version_set, 1, package_activity))
                                    }
                                },
                            })
                        },
                    );

                    // Stop searching if we found a candidate that makes the clause true.
                    if candidate.is_break() {
                        break;
                    }
                }

                match candidate {
                    ControlFlow::Break(_) => {
                        // A candidate has been assigned true which means the clause is already
                        // true, and we can skip it.
                        continue;
                    }
                    ControlFlow::Continue(None) => {
                        unreachable!("when we get here it means that all candidates have been assigned false. This should not be able to happen at this point because during propagation the solvable should have been assigned false as well.")
                    }
                    ControlFlow::Continue(Some((
                        candidate,
                        _version_set_id,
                        candidate_count,
                        package_activity,
                    ))) => {
                        let decision = (candidate, solvable_id, *clause_id);
                        best_decision = Some(match &best_decision {
                            None => PossibleDecision {
                                is_explicit_requirement,
                                package_activity,
                                candidate_count,
                                decision,
                            },
                            Some(best_decision) => {
                                // Prefer decisions on explicit requirements over non-explicit
                                // requirements. This optimizes direct dependencies over transitive
                                // dependencies.
                                if best_decision.is_explicit_requirement && !is_explicit_requirement
                                {
                                    continue;
                                }

                                // Prefer decisions with a higher package activity score to root out
                                // conflicts faster.
                                if best_decision.package_activity >= package_activity {
                                    continue;
                                }

                                if best_decision.candidate_count <= candidate_count {
                                    continue;
                                }

                                PossibleDecision {
                                    is_explicit_requirement,
                                    package_activity,
                                    candidate_count,
                                    decision,
                                }
                            }
                        })
                    }
                }
            }
        }

        if let Some(PossibleDecision {
            candidate_count,
            package_activity,
            decision: (candidate, _solvable_id, clause_id),
            ..
        }) = &best_decision
        {
            tracing::trace!(
                "deciding to assign {}, ({}, {} activity score, {} possible candidates)",
                self.provider().display_solvable(*candidate),
                self.clauses.kinds.borrow()[clause_id.to_usize()].display(self.provider()),
                package_activity,
                candidate_count,
            );
        }

        // Could not find a requirement that needs satisfying.
        best_decision.map(
            |PossibleDecision {
                 decision: (candidate, required_by, via),
                 ..
             }| { (candidate.into(), required_by, via) },
        )
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
    /// [`Conflict`] if we discovered that the requested jobs are
    /// unsatisfiable.
    fn set_propagate_learn(
        &mut self,
        mut level: u32,
        solvable: InternalSolvableId,
        _required_by: InternalSolvableId,
        clause_id: ClauseId,
    ) -> Result<u32, UnsolvableOrCancelled> {
        level += 1;

        self.decision_tracker
            .try_add_decision(Decision::new(solvable, true, clause_id), level)
            .expect("bug: solvable was already decided!");

        self.propagate_and_learn(level)
    }

    fn propagate_and_learn(&mut self, mut level: u32) -> Result<u32, UnsolvableOrCancelled> {
        loop {
            match self.propagate(level) {
                Ok(()) => {
                    return Ok(level);
                }
                Err(PropagationError::Cancelled(value)) => {
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
    ) -> Result<u32, Conflict> {
        {
            tracing::info!(
                "├┬ Propagation conflicted: could not set {solvable} to {attempted_value}",
                solvable = conflicting_solvable.display(self.provider()),
            );
            tracing::info!(
                "││ During unit propagation for clause: {}",
                self.clauses.kinds.borrow()[conflicting_clause.to_usize()].display(self.provider())
            );

            tracing::info!(
                "││ Previously decided value: {}. Derived from: {}",
                !attempted_value,
                self.clauses.kinds.borrow()[self
                    .decision_tracker
                    .find_clause_for_assignment(conflicting_solvable)
                    .unwrap()
                    .to_usize()]
                .display(self.provider()),
            );
        }

        if level == 1 {
            for decision in self.decision_tracker.stack() {
                let clause_id = decision.derived_from;
                let clause = self.clauses.kinds.borrow()[clause_id.to_usize()];
                let level = self.decision_tracker.level(decision.solvable_id);
                let action = if decision.value { "install" } else { "forbid" };

                if let Clause::ForbidMultipleInstances(..) = clause {
                    // Skip forbids clauses, to reduce noise
                    continue;
                }

                tracing::info!(
                    "* ({level}) {action} {}. Reason: {}",
                    decision.solvable_id.display(self.provider()),
                    self.clauses.kinds.borrow()[decision.derived_from.to_usize()]
                        .display(self.provider()),
                );
            }

            return Err(self.analyze_unsolvable(conflicting_clause));
        }

        let (new_level, learned_clause_id, literal) =
            self.analyze(level, conflicting_solvable, conflicting_clause);
        let old_level = level;
        level = new_level;

        // Optimization: propagate right now, since we know that the clause is a unit
        // clause
        let decision = literal.satisfying_value();
        self.decision_tracker
            .try_add_decision(
                Decision::new(literal.solvable_id(), decision, learned_clause_id),
                level,
            )
            .expect("bug: solvable was already decided!");
        tracing::debug!(
            "│├ Propagate after learn: {} = {decision}",
            literal.solvable_id().display(self.provider()),
        );

        tracing::info!("│└ Backtracked from {old_level} -> {level}");

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
                    "Negative assertions derived from other rules: Propagate assertion {} = {}",
                    solvable_id.display(self.provider()),
                    value
                );
            }
        }

        // Assertions derived from learnt rules
        for learn_clause_idx in 0..self.learnt_clause_ids.len() {
            let clause_id = self.learnt_clause_ids[learn_clause_idx];
            let clause = self.clauses.kinds.borrow()[clause_id.to_usize()];
            let Clause::Learnt(learnt_index) = clause else {
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
                    Decision::new(literal.solvable_id(), decision, clause_id),
                    level,
                )
                .map_err(|_| {
                    PropagationError::Conflict(literal.solvable_id(), decision, clause_id)
                })?;

            if decided {
                tracing::trace!(
                    "├─ Propagate assertion {} = {}",
                    literal.solvable_id().display(self.provider()),
                    decision
                );
            }
        }

        // Watched solvables
        let clauses = self.clauses.kinds.borrow();
        let mut clause_states = self.clauses.states.borrow_mut();
        while let Some(decision) = self.decision_tracker.next_unpropagated() {
            let watched_literal = Literal::new(decision.solvable_id, decision.value);

            // Propagate, iterating through the linked list of clauses that watch this
            // solvable
            let mut old_predecessor_clause_id: Option<ClauseId>;
            let mut predecessor_clause_id: Option<ClauseId> = None;
            let mut clause_id = self
                .watches
                .first_clause_watching_literal(watched_literal)
                .unwrap_or(ClauseId::null());
            while !clause_id.is_null() {
                debug_assert!(
                    predecessor_clause_id != Some(clause_id),
                    "Linked list is circular!"
                );

                // Get mutable access to both clauses.
                let (predecessor_clause_state, clause_state) =
                    if let Some(prev_clause_id) = predecessor_clause_id {
                        let prev_idx = prev_clause_id.to_usize();
                        let current_idx = clause_id.to_usize();
                        if prev_idx < current_idx {
                            let (left, right) = clause_states.split_at_mut(current_idx);
                            (Some(&mut left[prev_idx]), &mut right[0])
                        } else {
                            let (left, right) = clause_states.split_at_mut(prev_idx);
                            (Some(&mut right[0]), &mut left[current_idx])
                        }
                    } else {
                        (None, &mut clause_states[clause_id.to_usize()])
                    };

                // Update the prev_clause_id for the next run
                old_predecessor_clause_id = predecessor_clause_id;
                predecessor_clause_id = Some(clause_id);

                // Configure the next clause to visit
                let this_clause_id = clause_id;
                clause_id = clause_state.next_watched_clause(watched_literal.solvable_id());

                // Determine which watch turned false.
                let (watch_index, other_watch_index) = if clause_state.watched_literals[0]
                    .solvable_id()
                    == watched_literal.solvable_id()
                {
                    (0, 1)
                } else {
                    (1, 0)
                };
                debug_assert!(
                    clause_state.watched_literals[watch_index].eval(self.decision_tracker.map())
                        == Some(false)
                );

                // Find another literal to watch. If we can't find one, the other literal must
                // be set to true for the clause to still hold.
                if clause_state.watched_literals[other_watch_index]
                    .eval(self.decision_tracker.map())
                    == Some(true)
                {
                    // If the other watch is already true, we can simply skip
                    // this clause.
                } else if let Some(variable) = clause_state.next_unwatched_literal(
                    &clauses[this_clause_id.to_usize()],
                    &self.learnt_clauses,
                    &self.cache.requirement_to_sorted_candidates,
                    self.decision_tracker.map(),
                    watch_index,
                ) {
                    self.watches.update_watched(
                        predecessor_clause_state,
                        clause_state,
                        this_clause_id,
                        watch_index,
                        watched_literal,
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

                    let remaining_watch = clause_state.watched_literals[remaining_watch_index];
                    let decided = self
                        .decision_tracker
                        .try_add_decision(
                            Decision::new(
                                remaining_watch.solvable_id(),
                                remaining_watch.satisfying_value(),
                                this_clause_id,
                            ),
                            level,
                        )
                        .map_err(|_| {
                            PropagationError::Conflict(
                                remaining_watch.solvable_id(),
                                true,
                                this_clause_id,
                            )
                        })?;

                    if decided {
                        let clause = &clauses[this_clause_id.to_usize()];
                        match clause {
                            // Skip logging for ForbidMultipleInstances, which is so noisy
                            Clause::ForbidMultipleInstances(..) => {}
                            _ => {
                                tracing::debug!(
                                    "├ Propagate {} = {}. {}",
                                    remaining_watch.solvable_id().display(self.provider()),
                                    remaining_watch.satisfying_value(),
                                    clause.display(self.provider())
                                );
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Adds the clause with `clause_id` to the current [`Conflict`]
    ///
    /// Because learnt clauses are not relevant for the user, they are not added
    /// to the [`Conflict`]. Instead, we report the clauses that caused them.
    fn analyze_unsolvable_clause(
        clauses: &[Clause],
        learnt_why: &Mapping<LearntClauseId, Vec<ClauseId>>,
        clause_id: ClauseId,
        conflict: &mut Conflict,
        seen: &mut HashSet<ClauseId>,
    ) {
        let clause = &clauses[clause_id.to_usize()];
        match clause {
            Clause::Learnt(learnt_clause_id) => {
                if !seen.insert(clause_id) {
                    return;
                }

                for &cause in learnt_why
                    .get(*learnt_clause_id)
                    .expect("no cause for learnt clause available")
                {
                    Self::analyze_unsolvable_clause(clauses, learnt_why, cause, conflict, seen);
                }
            }
            _ => conflict.add_clause(clause_id),
        }
    }

    /// Create a [`Conflict`] based on the id of the clause that triggered an
    /// unrecoverable conflict
    fn analyze_unsolvable(&mut self, clause_id: ClauseId) -> Conflict {
        let last_decision = self.decision_tracker.stack().last().unwrap();
        let highest_level = self.decision_tracker.level(last_decision.solvable_id);
        debug_assert_eq!(highest_level, 1);

        let mut conflict = Conflict::default();

        tracing::info!("=== ANALYZE UNSOLVABLE");

        let mut involved = HashSet::default();
        self.clauses.kinds.borrow()[clause_id.to_usize()].visit_literals(
            &self.learnt_clauses,
            &self.cache.requirement_to_sorted_candidates,
            |literal| {
                involved.insert(literal.solvable_id());
            },
        );

        let mut seen = HashSet::default();
        Self::analyze_unsolvable_clause(
            &self.clauses.kinds.borrow(),
            &self.learnt_why,
            clause_id,
            &mut conflict,
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
                &self.clauses.kinds.borrow(),
                &self.learnt_why,
                why,
                &mut conflict,
                &mut seen,
            );

            self.clauses.kinds.borrow()[why.to_usize()].visit_literals(
                &self.learnt_clauses,
                &self.cache.requirement_to_sorted_candidates,
                |literal| {
                    if literal.eval(self.decision_tracker.map()) == Some(true) {
                        assert_eq!(literal.solvable_id(), decision.solvable_id);
                    } else {
                        involved.insert(literal.solvable_id());
                    }
                },
            );
        }

        conflict
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
        let mut seen = HashSet::default();
        let mut causes_at_current_level = 0u32;
        let mut learnt = Vec::new();
        let mut back_track_to = 0;

        let mut s_value;
        let mut learnt_why = Vec::new();
        let mut first_iteration = true;
        let clause_kinds = self.clauses.kinds.borrow();
        loop {
            learnt_why.push(clause_id);

            clause_kinds[clause_id.to_usize()].visit_literals(
                &self.learnt_clauses,
                &self.cache.requirement_to_sorted_candidates,
                |literal| {
                    if !first_iteration && literal.solvable_id() == conflicting_solvable {
                        // We are only interested in the causes of the conflict, so we ignore the
                        // solvable whose value was propagated
                        return;
                    }

                    if !seen.insert(literal.solvable_id()) {
                        // Skip literals we have already seen
                        return;
                    }

                    let decision_level = self.decision_tracker.level(literal.solvable_id());
                    if decision_level == current_level {
                        causes_at_current_level += 1;
                    } else if current_level > 1 {
                        let learnt_literal = Literal::new(
                            literal.solvable_id(),
                            self.decision_tracker
                                .assigned_value(literal.solvable_id())
                                .unwrap(),
                        );
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

        // No longer need the kinds
        drop(clause_kinds);

        let last_literal = Literal::new(conflicting_solvable, s_value);
        learnt.push(last_literal);

        // Increase the activity of the packages in the learned clause
        for literal in &learnt {
            let name_id = literal
                .solvable_id()
                .as_solvable()
                .map(|s| self.provider().solvable_name(s));
            if let Some(name_id) = name_id {
                self.name_activity[name_id.to_usize()] += self.activity_add;
            }
        }

        // Add the clause
        let learnt_id = self.learnt_clauses.alloc(learnt.clone());
        self.learnt_why.insert(learnt_id, learnt_why);

        let (state, kind) = ClauseState::learnt(learnt_id, &learnt);
        let has_watches = state.has_watches();
        let clause_id = self.clauses.alloc(state, kind);
        self.learnt_clause_ids.push(clause_id);
        if has_watches {
            self.watches.start_watching(
                &mut self.clauses.states.borrow_mut()[clause_id.to_usize()],
                clause_id,
            );
        }

        tracing::debug!("│├ Learnt disjunction:",);
        for lit in learnt {
            tracing::debug!(
                "││ - {}{}",
                if lit.negate() { "NOT " } else { "" },
                lit.solvable_id().display(self.provider()),
            );
        }

        // Should revert at most to the root level
        let target_level = back_track_to.max(1);
        self.decision_tracker.undo_until(target_level);

        self.decay_activity_scores();

        (target_level, clause_id, last_literal)
    }

    /// Decays the activity scores of all packages in the solver. This function
    /// is caleld after each conflict.
    fn decay_activity_scores(&mut self) {
        for activity in &mut self.name_activity {
            *activity *= self.activity_decay;
        }
    }
}

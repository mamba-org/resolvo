use crate::{
    internal::{
        arena::Arena,
        id::{ClauseId, LearntClauseId, SolvableId, VersionSetId},
    },
    pool::Pool,
    solver::decision_map::DecisionMap,
    PackageName, VersionSet,
};

use crate::internal::id::{StringId, VarId};
use crate::solver::decision_tracker::DecisionTracker;
use elsa::FrozenMap;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;

/// Represents a single clause in the SAT problem
///
/// # SAT terminology
///
/// Clauses consist of disjunctions of literals (i.e. a non-empty list of variables, potentially
/// negated, joined by the logical "or" operator). Here are some examples:
///
/// - (¬A ∨ ¬B)
/// - (¬A ∨ ¬B ∨ ¬C ∨ ¬D)
/// - (¬A ∨ B ∨ C)
/// - (root)
///
/// For additional clarity: if `(¬A ∨ ¬B)` is a clause, `¬A` and `¬B` are its literals, and `A` and
/// `B` are variables. In our implementation, variables are represented by [`SolvableId`], and
/// assignments are tracked in the [`DecisionMap`].
///
/// The solver will attempt to assign values to the variables involved in the problem in such a way
/// that all clauses become true. If that turns out to be impossible, the problem is unsatisfiable.
///
/// Since we are not interested in general-purpose SAT solving, but are targeting the specific
/// use-case of dependency resolution, we only support a limited set of clauses. There are thousands
/// of clauses for a particular dependency resolution problem, and we try to keep the [`Clause`] enum
/// small. A naive implementation would store a `Vec<Literal>`.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Clause {
    /// An assertion that the root solvable must be installed
    ///
    /// In SAT terms: (root)
    InstallRoot,
    /// The solvable requires the candidates associated with the version set
    ///
    /// In SAT terms: (¬A ∨ B1 ∨ B2 ∨ ... ∨ B99), where B1 to B99 represent the possible candidates
    /// for the provided version set
    Requires(SolvableId, VersionSetId),
    /// Ensures only a single version of a package is installed
    ///
    /// Usage: generate one [`Clause::ForbidMultipleInstances`] clause for each possible combination of
    /// packages under the same name. The clause itself forbids two solvables from being installed at
    /// the same time.
    ///
    /// In SAT terms: (¬A ∨ ¬B)
    ForbidMultipleInstances(SolvableId, Literal),
    /// Forbids packages that do not satisfy a solvable's constrains
    ///
    /// Usage: for each constrains relationship in a package, determine all the candidates that do
    /// _not_ satisfy it, and create one [`Clause::Constrains`]. The clause itself forbids two solvables
    /// from being installed at the same time, just as [`Clause::ForbidMultipleInstances`], but it
    /// pays off to have a separate variant for user-friendly error messages.
    ///
    /// In SAT terms: (¬A ∨ ¬B)
    Constrains(SolvableId, SolvableId, VersionSetId),
    /// Forbids the package on the right-hand side
    ///
    /// Note that the package on the left-hand side is not part of the clause, but just context to
    /// know which exact package was locked (necessary for user-friendly error messages)
    ///
    /// In SAT terms: (¬root ∨ ¬B). Note that we could encode this as an assertion (¬B), but that
    /// would require additional logic in the solver.
    Lock(SolvableId, SolvableId),
    /// A clause learnt during solving
    ///
    /// The learnt clause id can be used to retrieve the clause's literals, which are stored
    /// elsewhere to prevent the size of [`Clause`] from blowing up
    Learnt(LearntClauseId),

    /// A clause that forbids a package from being installed for an external reason.
    Excluded(SolvableId, StringId),
}

impl Clause {
    /// Returns the building blocks needed for a new [ClauseState] of the [Clause::Requires] kind.
    ///
    /// These building blocks are:
    ///
    /// - The [Clause] itself;
    /// - The ids of the solvables that will be watched (unless there are no candidates, i.e. the
    ///   clause is actually an assertion);
    /// - A boolean indicating whether the clause conflicts with existing decisions. This should
    ///   always be false when adding clauses before starting the solving process, but can be true
    ///   for clauses that are added dynamically.
    fn requires(
        parent: SolvableId,
        requirement: VersionSetId,
        candidates: &[SolvableId],
        decision_tracker: &DecisionTracker,
    ) -> (Self, Option<[VarId; 2]>, bool) {
        // It only makes sense to introduce a requires clause when the parent solvable is undecided
        // or going to be installed
        assert_ne!(decision_tracker.assigned_value(parent.into()), Some(false));

        let kind = Clause::Requires(parent, requirement);
        if candidates.is_empty() {
            (kind, None, false)
        } else {
            match candidates
                .iter()
                .find(|&&c| decision_tracker.assigned_value(c.into()) != Some(false))
            {
                // Watch any candidate that is not assigned to false
                Some(watched_candidate) => (
                    kind,
                    Some([parent.into(), (*watched_candidate).into()]),
                    false,
                ),

                // All candidates are assigned to false! Therefore the clause conflicts with the
                // current decisions. There are no valid watches for it at the moment, but we will
                // assign default ones nevertheless, because they will become valid after the solver
                // restarts.
                None => (kind, Some([parent.into(), candidates[0].into()]), true),
            }
        }
    }

    /// Returns the building blocks needed for a new [ClauseState] of the [Clause::Constrains] kind.
    ///
    /// These building blocks are:
    ///
    /// - The [Clause] itself;
    /// - The ids of the solvables that will be watched;
    /// - A boolean indicating whether the clause conflicts with existing decisions. This should
    ///   always be false when adding clauses before starting the solving process, but can be true
    ///   for clauses that are added dynamically.
    fn constrains(
        parent: SolvableId,
        forbidden_solvable: SolvableId,
        via: VersionSetId,
        decision_tracker: &DecisionTracker,
    ) -> (Self, Option<[VarId; 2]>, bool) {
        // It only makes sense to introduce a constrains clause when the parent solvable is
        // undecided or going to be installed
        assert_ne!(decision_tracker.assigned_value(parent.into()), Some(false));

        // If the forbidden solvable is already assigned to true, that means that there is a
        // conflict with current decisions, because it implies the parent solvable would be false
        // (and we just asserted that it is not)
        let conflict = decision_tracker.assigned_value(forbidden_solvable.into()) == Some(true);

        (
            Clause::Constrains(parent, forbidden_solvable, via),
            Some([parent.into(), forbidden_solvable.into()]),
            conflict,
        )
    }

    /// Returns the ids of the solvables that will be watched as well as the clause itself.
    fn forbid_multiple(
        candidate: SolvableId,
        constrained_candidate: Literal,
    ) -> (Self, Option<[VarId; 2]>) {
        (
            Clause::ForbidMultipleInstances(candidate, constrained_candidate),
            Some([candidate.into(), constrained_candidate.var_id]),
        )
    }

    fn root() -> (Self, Option<[VarId; 2]>) {
        (Clause::InstallRoot, None)
    }

    fn exclude(candidate: SolvableId, reason: StringId) -> (Self, Option<[VarId; 2]>) {
        (Clause::Excluded(candidate, reason), None)
    }

    fn lock(
        locked_candidate: SolvableId,
        other_candidate: SolvableId,
    ) -> (Self, Option<[VarId; 2]>) {
        (
            Clause::Lock(locked_candidate, other_candidate),
            Some([SolvableId::root().into(), other_candidate.into()]),
        )
    }

    fn learnt(
        learnt_clause_id: LearntClauseId,
        literals: &[Literal],
    ) -> (Self, Option<[VarId; 2]>) {
        debug_assert!(!literals.is_empty());
        (
            Clause::Learnt(learnt_clause_id),
            if literals.len() == 1 {
                // No need for watches, since we learned an assertion
                None
            } else {
                Some([
                    literals.first().unwrap().var_id,
                    literals.last().unwrap().var_id,
                ])
            },
        )
    }

    /// Visits each literal in the clause
    pub fn visit_literals(
        &self,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
        version_set_to_sorted_candidates: &FrozenMap<VersionSetId, Vec<SolvableId>>,
        mut visit: impl FnMut(Literal),
    ) {
        match *self {
            Clause::InstallRoot => unreachable!(),
            Clause::Excluded(solvable, _) => {
                visit(Literal {
                    var_id: solvable.into(),
                    negate: true,
                });
            }
            Clause::Learnt(learnt_id) => {
                for &literal in &learnt_clauses[learnt_id] {
                    visit(literal);
                }
            }
            Clause::Requires(solvable_id, match_spec_id) => {
                visit(Literal {
                    var_id: solvable_id.into(),
                    negate: true,
                });

                for &solvable_id in &version_set_to_sorted_candidates[&match_spec_id] {
                    visit(Literal {
                        var_id: solvable_id.into(),
                        negate: false,
                    });
                }
            }
            Clause::Constrains(s1, s2, _) => {
                visit(Literal {
                    var_id: s1.into(),
                    negate: true,
                });

                visit(Literal {
                    var_id: s2.into(),
                    negate: true,
                });
            }
            Clause::ForbidMultipleInstances(s1, s2) => {
                visit(Literal {
                    var_id: s1.into(),
                    negate: true,
                });

                visit(s2);
            }
            Clause::Lock(_, s) => {
                visit(Literal {
                    var_id: SolvableId::root().into(),
                    negate: true,
                });

                visit(Literal {
                    var_id: s.into(),
                    negate: true,
                });
            }
        }
    }
}

/// Keeps track of the literals watched by a [`Clause`] and the state associated to two linked lists
/// this clause is part of
///
/// In our SAT implementation, each clause tracks two literals present in its clause, to be notified
/// when the value assigned to the variable has changed (this technique is known as _watches_).
/// Clauses that are tracking the same variable are grouped together in a linked list, so it becomes
/// easy to notify them all.
#[derive(Clone)]
pub(crate) struct ClauseState {
    // The ids of the solvables this clause is watching
    pub watched_literals: [VarId; 2],
    // The ids of the next clause in each linked list that this clause is part of
    next_watches: [ClauseId; 2],
    // The clause itself
    pub(crate) kind: Clause,
}

impl ClauseState {
    /// Shorthand method to construct a [`Clause::InstallRoot`] without requiring complicated
    /// arguments.
    pub fn root() -> Self {
        let (kind, watched_literals) = Clause::root();
        Self::from_kind_and_initial_watches(kind, watched_literals)
    }

    /// Shorthand method to construct a [Clause::Requires] without requiring complicated arguments.
    ///
    /// The returned boolean value is true when adding the clause resulted in a conflict.
    pub fn requires(
        candidate: SolvableId,
        requirement: VersionSetId,
        matching_candidates: &[SolvableId],
        decision_tracker: &DecisionTracker,
    ) -> (Self, bool) {
        let (kind, watched_literals, conflict) = Clause::requires(
            candidate,
            requirement,
            matching_candidates,
            decision_tracker,
        );

        (
            Self::from_kind_and_initial_watches(kind, watched_literals),
            conflict,
        )
    }

    /// Shorthand method to construct a [Clause::Constrains] without requiring complicated arguments.
    ///
    /// The returned boolean value is true when adding the clause resulted in a conflict.
    pub fn constrains(
        candidate: SolvableId,
        constrained_package: SolvableId,
        requirement: VersionSetId,
        decision_tracker: &DecisionTracker,
    ) -> (Self, bool) {
        let (kind, watched_literals, conflict) = Clause::constrains(
            candidate,
            constrained_package,
            requirement,
            decision_tracker,
        );

        (
            Self::from_kind_and_initial_watches(kind, watched_literals),
            conflict,
        )
    }

    pub fn lock(locked_candidate: SolvableId, other_candidate: SolvableId) -> Self {
        let (kind, watched_literals) = Clause::lock(locked_candidate, other_candidate);
        Self::from_kind_and_initial_watches(kind, watched_literals)
    }

    pub fn forbid_multiple(candidate: SolvableId, other_candidate: Literal) -> Self {
        let (kind, watched_literals) = Clause::forbid_multiple(candidate, other_candidate);
        Self::from_kind_and_initial_watches(kind, watched_literals)
    }

    pub fn learnt(learnt_clause_id: LearntClauseId, literals: &[Literal]) -> Self {
        let (kind, watched_literals) = Clause::learnt(learnt_clause_id, literals);
        Self::from_kind_and_initial_watches(kind, watched_literals)
    }

    pub fn exclude(candidate: SolvableId, reason: StringId) -> Self {
        let (kind, watched_literals) = Clause::exclude(candidate, reason);
        Self::from_kind_and_initial_watches(kind, watched_literals)
    }

    fn from_kind_and_initial_watches(kind: Clause, watched_literals: Option<[VarId; 2]>) -> Self {
        let watched_literals = watched_literals.unwrap_or([VarId::null(), VarId::null()]);

        let clause = Self {
            watched_literals,
            next_watches: [ClauseId::null(), ClauseId::null()],
            kind,
        };

        debug_assert!(!clause.has_watches() || watched_literals[0] != watched_literals[1]);

        clause
    }

    pub fn debug<'a, VS: VersionSet, N: PackageName>(
        &self,
        pool: &'a Pool<VS, N>,
    ) -> ClauseDebug<'a, VS, N> {
        ClauseDebug {
            kind: self.kind,
            pool,
        }
    }

    pub fn link_to_clause(&mut self, watch_index: usize, linked_clause: ClauseId) {
        self.next_watches[watch_index] = linked_clause;
    }

    pub fn get_linked_clause(&self, watch_index: usize) -> ClauseId {
        self.next_watches[watch_index]
    }

    pub fn unlink_clause(
        &mut self,
        linked_clause: &ClauseState,
        watched_solvable: VarId,
        linked_clause_watch_index: usize,
    ) {
        if self.watched_literals[0] == watched_solvable {
            self.next_watches[0] = linked_clause.next_watches[linked_clause_watch_index];
        } else {
            debug_assert_eq!(self.watched_literals[1], watched_solvable);
            self.next_watches[1] = linked_clause.next_watches[linked_clause_watch_index];
        }
    }

    #[inline]
    pub fn next_watched_clause(&self, solvable_id: VarId) -> ClauseId {
        if solvable_id == self.watched_literals[0] {
            self.next_watches[0]
        } else {
            debug_assert_eq!(self.watched_literals[1], solvable_id);
            self.next_watches[1]
        }
    }

    // Returns the index of the watch that turned false, if any
    pub fn watch_turned_false(
        &self,
        var_id: VarId,
        decision_map: &DecisionMap,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
    ) -> Option<([Literal; 2], usize)> {
        debug_assert!(self.watched_literals.contains(&var_id));

        let literals @ [w1, w2] = self.watched_literals(learnt_clauses);

        if var_id == w1.var_id && w1.eval(decision_map) == Some(false) {
            Some((literals, 0))
        } else if var_id == w2.var_id && w2.eval(decision_map) == Some(false) {
            Some((literals, 1))
        } else {
            None
        }
    }

    pub fn has_watches(&self) -> bool {
        // If the first watch is not null, the second won't be either
        !self.watched_literals[0].is_null()
    }

    pub fn watched_literals(
        &self,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
    ) -> [Literal; 2] {
        let literals = |op1: bool, op2: bool| {
            [
                Literal {
                    var_id: self.watched_literals[0],
                    negate: !op1,
                },
                Literal {
                    var_id: self.watched_literals[1],
                    negate: !op2,
                },
            ]
        };

        match self.kind {
            Clause::InstallRoot => unreachable!(),
            Clause::Excluded(_, _) => unreachable!(),
            Clause::Learnt(learnt_id) => {
                // TODO: we might want to do something else for performance, like keeping the whole
                // literal in `self.watched_literals`, to avoid lookups... But first we should
                // benchmark!
                let &w1 = learnt_clauses[learnt_id]
                    .iter()
                    .find(|l| l.var_id == self.watched_literals[0])
                    .unwrap();
                let &w2 = learnt_clauses[learnt_id]
                    .iter()
                    .find(|l| l.var_id == self.watched_literals[1])
                    .unwrap();
                [w1, w2]
            }
            Clause::ForbidMultipleInstances(_a, lit) => literals(false, !lit.negate),
            Clause::Constrains(..) | Clause::Lock(..) => literals(false, false),
            Clause::Requires(solvable_id, _) => {
                if self.watched_literals[0] == solvable_id.into() {
                    literals(false, true)
                } else if self.watched_literals[1] == solvable_id.into() {
                    literals(true, false)
                } else {
                    literals(true, true)
                }
            }
        }
    }

    pub fn next_unwatched_variable(
        &self,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
        version_set_to_sorted_candidates: &FrozenMap<VersionSetId, Vec<SolvableId>>,
        decision_map: &DecisionMap,
    ) -> Option<VarId> {
        // The next unwatched variable (if available), is a variable that is:
        // * Not already being watched
        // * Not yet decided, or decided in such a way that the literal yields true
        let can_watch = |solvable_lit: Literal| {
            !self.watched_literals.contains(&solvable_lit.var_id)
                && solvable_lit.eval(decision_map).unwrap_or(true)
        };

        match self.kind {
            Clause::InstallRoot => unreachable!(),
            Clause::Excluded(_, _) => unreachable!(),
            Clause::Learnt(learnt_id) => learnt_clauses[learnt_id]
                .iter()
                .cloned()
                .find(|&l| can_watch(l))
                .map(|l| l.var_id),
            Clause::Constrains(..) | Clause::ForbidMultipleInstances(..) | Clause::Lock(..) => None,
            Clause::Requires(solvable_id, version_set_id) => {
                // The solvable that added this clause
                let solvable_lit = Literal {
                    var_id: solvable_id.into(),
                    negate: true,
                };
                if can_watch(solvable_lit) {
                    return Some(solvable_id.into());
                }

                // The available candidates
                for &candidate in &version_set_to_sorted_candidates[&version_set_id] {
                    let lit = Literal {
                        var_id: candidate.into(),
                        negate: false,
                    };
                    if can_watch(lit) {
                        return Some(candidate.into());
                    }
                }

                // No solvable available to watch
                None
            }
        }
    }
}

/// Represents a literal in a SAT clause (i.e. either A or ¬A)
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub(crate) struct Literal {
    pub(crate) var_id: VarId,
    pub(crate) negate: bool,
}

impl Literal {
    /// Returns the value that would make the literal evaluate to true if assigned to the literal's solvable
    pub(crate) fn satisfying_value(self) -> bool {
        !self.negate
    }

    /// Evaluates the literal, or returns `None` if no value has been assigned to the solvable
    pub(crate) fn eval(self, decision_map: &DecisionMap) -> Option<bool> {
        decision_map
            .value(self.var_id)
            .map(|value| self.eval_inner(value))
    }

    fn eval_inner(self, solvable_value: bool) -> bool {
        if self.negate {
            !solvable_value
        } else {
            solvable_value
        }
    }
}

/// A representation of a clause that implements [`Debug`]
pub(crate) struct ClauseDebug<'pool, VS: VersionSet, N: PackageName> {
    kind: Clause,
    pool: &'pool Pool<VS, N>,
}

impl<VS: VersionSet, N: PackageName + Display> Debug for ClauseDebug<'_, VS, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            Clause::InstallRoot => write!(f, "install root"),
            Clause::Excluded(solvable_id, reason) => {
                write!(
                    f,
                    "{} excluded because: {}",
                    solvable_id.display(self.pool),
                    self.pool.resolve_string(reason)
                )
            }
            Clause::Learnt(learnt_id) => write!(f, "learnt clause {learnt_id:?}"),
            Clause::Requires(solvable_id, match_spec_id) => {
                let match_spec = self.pool.resolve_version_set(match_spec_id).to_string();
                write!(
                    f,
                    "{} requires {} {match_spec}",
                    solvable_id.display(self.pool),
                    self.pool
                        .resolve_version_set_package_name(match_spec_id)
                        .display(self.pool)
                )
            }
            Clause::Constrains(s1, s2, vset_id) => {
                write!(
                    f,
                    "{} excludes {} by {}",
                    s1.display(self.pool),
                    s2.display(self.pool),
                    self.pool.resolve_version_set(vset_id)
                )
            }
            Clause::Lock(locked, forbidden) => {
                write!(
                    f,
                    "{} is locked, so {} is forbidden",
                    locked.display(self.pool),
                    forbidden.display(self.pool)
                )
            }
            Clause::ForbidMultipleInstances(s1, _) => {
                let name = self
                    .pool
                    .resolve_internal_solvable(s1)
                    .solvable()
                    .name
                    .display(self.pool);
                write!(f, "only one {name} allowed")
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::internal::arena::ArenaId;
    use crate::solver::decision::Decision;

    fn clause(next_clauses: [ClauseId; 2], watched_solvables: [VarId; 2]) -> ClauseState {
        ClauseState {
            watched_literals: watched_solvables,
            next_watches: next_clauses,

            // The kind is irrelevant here
            kind: Clause::InstallRoot,
        }
    }

    #[test]
    #[allow(clippy::bool_assert_comparison)]
    fn test_literal_satisfying_value() {
        let lit = Literal {
            var_id: SolvableId::root().into(),
            negate: true,
        };
        assert_eq!(lit.satisfying_value(), false);

        let lit = Literal {
            var_id: SolvableId::root().into(),
            negate: false,
        };
        assert_eq!(lit.satisfying_value(), true);
    }

    #[test]
    fn test_literal_eval() {
        let mut decision_map = DecisionMap::new();

        let literal = Literal {
            var_id: SolvableId::root().into(),
            negate: false,
        };
        let negated_literal = Literal {
            var_id: SolvableId::root().into(),
            negate: true,
        };

        // Undecided
        assert_eq!(literal.eval(&decision_map), None);
        assert_eq!(negated_literal.eval(&decision_map), None);

        // Decided
        decision_map.set(SolvableId::root().into(), true, 1);
        assert_eq!(literal.eval(&decision_map), Some(true));
        assert_eq!(negated_literal.eval(&decision_map), Some(false));

        decision_map.set(SolvableId::root().into(), false, 1);
        assert_eq!(literal.eval(&decision_map), Some(false));
        assert_eq!(negated_literal.eval(&decision_map), Some(true));
    }

    #[test]
    fn test_unlink_clause_different() {
        let clause1 = clause(
            [ClauseId::from_usize(2), ClauseId::from_usize(3)],
            [
                SolvableId::from_usize(1596).into(),
                SolvableId::from_usize(1211).into(),
            ],
        );
        let clause2 = clause(
            [ClauseId::null(), ClauseId::from_usize(3)],
            [
                SolvableId::from_usize(1596).into(),
                SolvableId::from_usize(1208).into(),
            ],
        );
        let clause3 = clause(
            [ClauseId::null(), ClauseId::null()],
            [
                SolvableId::from_usize(1211).into(),
                SolvableId::from_usize(42).into(),
            ],
        );

        // Unlink 0
        {
            let mut clause1 = clause1.clone();
            clause1.unlink_clause(&clause2, SolvableId::from_usize(1596).into(), 0);
            assert_eq!(
                clause1.watched_literals,
                [
                    SolvableId::from_usize(1596).into(),
                    SolvableId::from_usize(1211).into()
                ]
            );
            assert_eq!(
                clause1.next_watches,
                [ClauseId::null(), ClauseId::from_usize(3)]
            )
        }

        // Unlink 1
        {
            let mut clause1 = clause1;
            clause1.unlink_clause(&clause3, SolvableId::from_usize(1211).into(), 0);
            assert_eq!(
                clause1.watched_literals,
                [
                    SolvableId::from_usize(1596).into(),
                    SolvableId::from_usize(1211).into()
                ]
            );
            assert_eq!(
                clause1.next_watches,
                [ClauseId::from_usize(2), ClauseId::null()]
            )
        }
    }

    #[test]
    fn test_unlink_clause_same() {
        let clause1 = clause(
            [ClauseId::from_usize(2), ClauseId::from_usize(2)],
            [
                SolvableId::from_usize(1596).into(),
                SolvableId::from_usize(1211).into(),
            ],
        );
        let clause2 = clause(
            [ClauseId::null(), ClauseId::null()],
            [
                SolvableId::from_usize(1596).into(),
                SolvableId::from_usize(1211).into(),
            ],
        );

        // Unlink 0
        {
            let mut clause1 = clause1.clone();
            clause1.unlink_clause(&clause2, SolvableId::from_usize(1596).into(), 0);
            assert_eq!(
                clause1.watched_literals,
                [
                    SolvableId::from_usize(1596).into(),
                    SolvableId::from_usize(1211).into()
                ]
            );
            assert_eq!(
                clause1.next_watches,
                [ClauseId::null(), ClauseId::from_usize(2)]
            )
        }

        // Unlink 1
        {
            let mut clause1 = clause1;
            clause1.unlink_clause(&clause2, SolvableId::from_usize(1211).into(), 1);
            assert_eq!(
                clause1.watched_literals,
                [
                    SolvableId::from_usize(1596).into(),
                    SolvableId::from_usize(1211).into()
                ]
            );
            assert_eq!(
                clause1.next_watches,
                [ClauseId::from_usize(2), ClauseId::null()]
            )
        }
    }

    #[test]
    fn test_requires_with_and_without_conflict() {
        let mut decisions = DecisionTracker::new();

        let parent = SolvableId::from_usize(1);
        let candidate1 = SolvableId::from_usize(2);
        let candidate2 = SolvableId::from_usize(3);

        // No conflict, all candidates available
        let (clause, conflict) = ClauseState::requires(
            parent,
            VersionSetId::from_usize(0),
            &[candidate1, candidate2],
            &decisions,
        );
        assert!(!conflict);
        assert_eq!(clause.watched_literals[0], parent.into());
        assert_eq!(clause.watched_literals[1], candidate1.into());

        // No conflict, still one candidate available
        decisions
            .try_add_decision(Decision::new(candidate1.into(), false, ClauseId::null()), 1)
            .unwrap();
        let (clause, conflict) = ClauseState::requires(
            parent,
            VersionSetId::from_usize(0),
            &[candidate1, candidate2],
            &decisions,
        );
        assert!(!conflict);
        assert_eq!(clause.watched_literals[0], parent.into());
        assert_eq!(clause.watched_literals[1], candidate2.into());

        // Conflict, no candidates available
        decisions
            .try_add_decision(Decision::new(candidate2.into(), false, ClauseId::null()), 1)
            .unwrap();
        let (clause, conflict) = ClauseState::requires(
            parent,
            VersionSetId::from_usize(0),
            &[candidate1, candidate2],
            &decisions,
        );
        assert!(conflict);
        assert_eq!(clause.watched_literals[0], parent.into());
        assert_eq!(clause.watched_literals[1], candidate1.into());

        // Panic
        decisions
            .try_add_decision(Decision::new(parent.into(), false, ClauseId::null()), 1)
            .unwrap();
        let panicked = std::panic::catch_unwind(|| {
            ClauseState::requires(
                parent,
                VersionSetId::from_usize(0),
                &[candidate1, candidate2],
                &decisions,
            )
        })
        .is_err();
        assert!(panicked);
    }

    #[test]
    fn test_constrains_with_and_without_conflict() {
        let mut decisions = DecisionTracker::new();

        let parent = SolvableId::from_usize(1);
        let forbidden = SolvableId::from_usize(2);

        // No conflict, forbidden package not installed
        let (clause, conflict) =
            ClauseState::constrains(parent, forbidden, VersionSetId::from_usize(0), &decisions);
        assert!(!conflict);
        assert_eq!(clause.watched_literals[0], parent.into());
        assert_eq!(clause.watched_literals[1], forbidden.into());

        // Conflict, forbidden package installed
        decisions
            .try_add_decision(Decision::new(forbidden.into(), true, ClauseId::null()), 1)
            .unwrap();
        let (clause, conflict) =
            ClauseState::constrains(parent, forbidden, VersionSetId::from_usize(0), &decisions);
        assert!(conflict);
        assert_eq!(clause.watched_literals[0], parent.into());
        assert_eq!(clause.watched_literals[1], forbidden.into());

        // Panic
        decisions
            .try_add_decision(Decision::new(parent.into(), false, ClauseId::null()), 1)
            .unwrap();
        let panicked = std::panic::catch_unwind(|| {
            ClauseState::constrains(parent, forbidden, VersionSetId::from_usize(0), &decisions)
        })
        .is_err();
        assert!(panicked);
    }

    #[test]
    fn test_clause_size() {
        // This test is here to ensure we don't increase the size of `ClauseState` by accident, as
        // we are creating thousands of instances. Note: libsolv manages to bring down the size to
        // 24, so there is probably room for improvement.
        assert_eq!(std::mem::size_of::<ClauseState>(), 32);
    }
}

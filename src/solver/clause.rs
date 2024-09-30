use std::{
    fmt::{Debug, Display, Formatter},
    iter,
    ops::ControlFlow,
};

use elsa::FrozenMap;

use crate::{
    internal::{
        arena::{Arena, ArenaId},
        id::{ClauseId, InternalSolvableId, LearntClauseId, StringId, VersionSetId},
    },
    solver::{decision_map::DecisionMap, decision_tracker::DecisionTracker},
    Interner, NameId, Requirement, SolvableId,
};

/// Represents a single clause in the SAT problem
///
/// # SAT terminology
///
/// Clauses consist of disjunctions of literals (i.e. a non-empty list of
/// variables, potentially negated, joined by the logical "or" operator). Here
/// are some examples:
///
/// - (¬A ∨ ¬B)
/// - (¬A ∨ ¬B ∨ ¬C ∨ ¬D)
/// - (¬A ∨ B ∨ C)
/// - (root)
///
/// For additional clarity: if `(¬A ∨ ¬B)` is a clause, `¬A` and `¬B` are its
/// literals, and `A` and `B` are variables. In our implementation, variables
/// are represented by [`InternalSolvableId`], and assignments are tracked in
/// the [`DecisionMap`].
///
/// The solver will attempt to assign values to the variables involved in the
/// problem in such a way that all clauses become true. If that turns out to be
/// impossible, the problem is unsatisfiable.
///
/// Since we are not interested in general-purpose SAT solving, but are
/// targeting the specific use-case of dependency resolution, we only support a
/// limited set of clauses. There are thousands of clauses for a particular
/// dependency resolution problem, and we try to keep the [`Clause`] enum small.
/// A naive implementation would store a `Vec<Literal>`.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Clause {
    /// An assertion that the root solvable must be installed
    ///
    /// In SAT terms: (root)
    InstallRoot,
    /// Makes the solvable require the candidates associated with the
    /// [`Requirement`].
    ///
    /// In SAT terms: (¬A ∨ B1 ∨ B2 ∨ ... ∨ B99), where B1 to B99 represent the
    /// possible candidates for the provided [`Requirement`].
    Requires(InternalSolvableId, Requirement),
    /// Ensures only a single version of a package is installed
    ///
    /// Usage: generate one [`Clause::ForbidMultipleInstances`] clause for each
    /// possible combination of packages under the same name. The clause
    /// itself forbids two solvables from being installed at the same time.
    ///
    /// In SAT terms: (¬A ∨ ¬B)
    ForbidMultipleInstances(InternalSolvableId, InternalSolvableId, NameId),
    /// Forbids packages that do not satisfy a solvable's constrains
    ///
    /// Usage: for each constrains relationship in a package, determine all the
    /// candidates that do _not_ satisfy it, and create one
    /// [`Clause::Constrains`]. The clause itself forbids two solvables from
    /// being installed at the same time, just as
    /// [`Clause::ForbidMultipleInstances`], but it pays off to have a
    /// separate variant for user-friendly error messages.
    ///
    /// In SAT terms: (¬A ∨ ¬B)
    Constrains(InternalSolvableId, InternalSolvableId, VersionSetId),
    /// Forbids the package on the right-hand side
    ///
    /// Note that the package on the left-hand side is not part of the clause,
    /// but just context to know which exact package was locked (necessary
    /// for user-friendly error messages)
    ///
    /// In SAT terms: (¬root ∨ ¬B). Note that we could encode this as an
    /// assertion (¬B), but that would require additional logic in the
    /// solver.
    Lock(InternalSolvableId, InternalSolvableId),
    /// A clause learnt during solving
    ///
    /// The learnt clause id can be used to retrieve the clause's literals,
    /// which are stored elsewhere to prevent the size of [`Clause`] from
    /// blowing up
    Learnt(LearntClauseId),

    /// A clause that forbids a package from being installed for an external
    /// reason.
    Excluded(InternalSolvableId, StringId),
}

impl Clause {
    /// Returns the building blocks needed for a new [ClauseState] of the
    /// [Clause::Requires] kind.
    ///
    /// These building blocks are:
    ///
    /// - The [Clause] itself;
    /// - The ids of the solvables that will be watched (unless there are no
    ///   candidates, i.e. the clause is actually an assertion);
    /// - A boolean indicating whether the clause conflicts with existing
    ///   decisions. This should always be false when adding clauses before
    ///   starting the solving process, but can be true for clauses that are
    ///   added dynamically.
    fn requires(
        parent: InternalSolvableId,
        requirement: Requirement,
        candidates: &[SolvableId],
        decision_tracker: &DecisionTracker,
    ) -> (Self, Option<[Literal; 2]>, bool) {
        // It only makes sense to introduce a requires clause when the parent solvable
        // is undecided or going to be installed
        assert_ne!(decision_tracker.assigned_value(parent), Some(false));

        let kind = Clause::Requires(parent, requirement);
        if candidates.is_empty() {
            // If there are no candidates there is no need to watch anything.
            (kind, None, false)
        } else {
            match candidates
                .iter()
                .copied()
                .map(InternalSolvableId::from)
                .find(|&c| decision_tracker.assigned_value(c) != Some(false))
            {
                // Watch any candidate that is not assigned to false
                Some(watched_candidate) => (
                    kind,
                    Some([parent.negative(), watched_candidate.positive()]),
                    false,
                ),

                // All candidates are assigned to false! Therefore, the clause conflicts with the
                // current decisions. There are no valid watches for it at the moment, but we will
                // assign default ones nevertheless, because they will become valid after the solver
                // restarts.
                None => (
                    kind,
                    Some([
                        parent.negative(),
                        InternalSolvableId::from(candidates[0]).positive(),
                    ]),
                    true,
                ),
            }
        }
    }

    /// Returns the building blocks needed for a new [ClauseState] of the
    /// [Clause::Constrains] kind.
    ///
    /// These building blocks are:
    ///
    /// - The [Clause] itself;
    /// - The ids of the solvables that will be watched;
    /// - A boolean indicating whether the clause conflicts with existing
    ///   decisions. This should always be false when adding clauses before
    ///   starting the solving process, but can be true for clauses that are
    ///   added dynamically.
    fn constrains(
        parent: InternalSolvableId,
        forbidden_solvable: InternalSolvableId,
        via: VersionSetId,
        decision_tracker: &DecisionTracker,
    ) -> (Self, Option<[Literal; 2]>, bool) {
        // It only makes sense to introduce a constrains clause when the parent solvable
        // is undecided or going to be installed
        assert_ne!(decision_tracker.assigned_value(parent), Some(false));

        // If the forbidden solvable is already assigned to true, that means that there
        // is a conflict with current decisions, because it implies the parent
        // solvable would be false (and we just asserted that it is not)
        let conflict = decision_tracker.assigned_value(forbidden_solvable) == Some(true);

        (
            Clause::Constrains(parent, forbidden_solvable, via),
            Some([parent.negative(), forbidden_solvable.negative()]),
            conflict,
        )
    }

    /// Returns the ids of the solvables that will be watched as well as the
    /// clause itself.
    fn forbid_multiple(
        candidate: InternalSolvableId,
        constrained_candidate: InternalSolvableId,
        name: NameId,
    ) -> (Self, Option<[Literal; 2]>) {
        (
            Clause::ForbidMultipleInstances(candidate, constrained_candidate, name),
            Some([candidate.negative(), constrained_candidate.negative()]),
        )
    }

    fn root() -> (Self, Option<[Literal; 2]>) {
        (Clause::InstallRoot, None)
    }

    fn exclude(candidate: InternalSolvableId, reason: StringId) -> (Self, Option<[Literal; 2]>) {
        (Clause::Excluded(candidate, reason), None)
    }

    fn lock(
        locked_candidate: InternalSolvableId,
        other_candidate: InternalSolvableId,
    ) -> (Self, Option<[Literal; 2]>) {
        (
            Clause::Lock(locked_candidate, other_candidate),
            Some([
                InternalSolvableId::root().negative(),
                other_candidate.negative(),
            ]),
        )
    }

    fn learnt(
        learnt_clause_id: LearntClauseId,
        literals: &[Literal],
    ) -> (Self, Option<[Literal; 2]>) {
        debug_assert!(!literals.is_empty());
        (
            Clause::Learnt(learnt_clause_id),
            if literals.len() == 1 {
                // No need for watches, since we learned an assertion
                None
            } else {
                Some([*literals.first().unwrap(), *literals.last().unwrap()])
            },
        )
    }

    /// Tries to fold over all the literals in the clause.
    ///
    /// This function is useful to iterate, find, or filter the literals in a
    /// clause.
    pub fn try_fold_literals<B, C, F>(
        &self,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
        requirements_to_sorted_candidates: &FrozenMap<
            Requirement,
            Vec<SolvableId>,
            ahash::RandomState,
        >,
        init: C,
        mut visit: F,
    ) -> ControlFlow<B, C>
    where
        F: FnMut(C, Literal) -> ControlFlow<B, C>,
    {
        match *self {
            Clause::InstallRoot => unreachable!(),
            Clause::Excluded(solvable, _) => visit(init, solvable.negative()),
            Clause::Learnt(learnt_id) => learnt_clauses[learnt_id]
                .iter()
                .copied()
                .try_fold(init, visit),
            Clause::Requires(solvable_id, match_spec_id) => iter::once(solvable_id.negative())
                .chain(
                    requirements_to_sorted_candidates[&match_spec_id]
                        .iter()
                        .map(|&s| InternalSolvableId::from(s).positive()),
                )
                .try_fold(init, visit),
            Clause::Constrains(s1, s2, _) | Clause::ForbidMultipleInstances(s1, s2, _) => {
                [s1.negative(), s2.negative()]
                    .into_iter()
                    .try_fold(init, visit)
            }
            Clause::Lock(_, s) => [s.negative(), InternalSolvableId::root().negative()]
                .into_iter()
                .try_fold(init, visit),
        }
    }

    /// Visits each literal in the clause.
    ///
    /// If you need to exit early or return a value, use [`try_fold_literals`].
    pub fn visit_literals(
        &self,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
        requirements_to_sorted_candidates: &FrozenMap<
            Requirement,
            Vec<SolvableId>,
            ahash::RandomState,
        >,
        mut visit: impl FnMut(Literal),
    ) {
        self.try_fold_literals(
            learnt_clauses,
            requirements_to_sorted_candidates,
            (),
            |_, lit| {
                visit(lit);
                ControlFlow::<()>::Continue(())
            },
        );
    }

    /// Construct a [`ClauseDisplay`] to display the clause.
    pub fn display<'i, I: Interner>(&self, interner: &'i I) -> ClauseDisplay<'i, I> {
        ClauseDisplay {
            kind: *self,
            interner,
        }
    }
}

/// Keeps track of the literals watched by a [`Clause`] and the state associated
/// to two linked lists this clause is part of
///
/// In our SAT implementation, each clause tracks two literals present in its
/// clause, to be notified when the value assigned to the variable has changed
/// (this technique is known as _watches_). Clauses that are tracking the same
/// variable are grouped together in a linked list, so it becomes easy to notify
/// them all.
#[derive(Clone)]
pub(crate) struct ClauseState {
    // The ids of the solvables this clause is watching
    pub watched_literals: [Literal; 2],
    // The ids of the next clause in each linked list that this clause is part of
    pub(crate) next_watches: [ClauseId; 2],
}

impl ClauseState {
    /// Shorthand method to construct a [`Clause::InstallRoot`] without
    /// requiring complicated arguments.
    pub fn root() -> (Self, Clause) {
        let (kind, watched_literals) = Clause::root();
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    /// Shorthand method to construct a [Clause::Requires] without requiring
    /// complicated arguments.
    ///
    /// The returned boolean value is true when adding the clause resulted in a
    /// conflict.
    pub fn requires(
        candidate: InternalSolvableId,
        requirement: Requirement,
        matching_candidates: &[SolvableId],
        decision_tracker: &DecisionTracker,
    ) -> (Self, bool, Clause) {
        let (kind, watched_literals, conflict) = Clause::requires(
            candidate,
            requirement,
            matching_candidates,
            decision_tracker,
        );

        (
            Self::from_kind_and_initial_watches(watched_literals),
            conflict,
            kind,
        )
    }

    /// Shorthand method to construct a [Clause::Constrains] without requiring
    /// complicated arguments.
    ///
    /// The returned boolean value is true when adding the clause resulted in a
    /// conflict.
    pub fn constrains(
        candidate: InternalSolvableId,
        constrained_package: InternalSolvableId,
        requirement: VersionSetId,
        decision_tracker: &DecisionTracker,
    ) -> (Self, bool, Clause) {
        let (kind, watched_literals, conflict) = Clause::constrains(
            candidate,
            constrained_package,
            requirement,
            decision_tracker,
        );

        (
            Self::from_kind_and_initial_watches(watched_literals),
            conflict,
            kind,
        )
    }

    pub fn lock(
        locked_candidate: InternalSolvableId,
        other_candidate: InternalSolvableId,
    ) -> (Self, Clause) {
        let (kind, watched_literals) = Clause::lock(locked_candidate, other_candidate);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    pub fn forbid_multiple(
        candidate: InternalSolvableId,
        other_candidate: InternalSolvableId,
        name: NameId,
    ) -> (Self, Clause) {
        let (kind, watched_literals) = Clause::forbid_multiple(candidate, other_candidate, name);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    pub fn learnt(learnt_clause_id: LearntClauseId, literals: &[Literal]) -> (Self, Clause) {
        let (kind, watched_literals) = Clause::learnt(learnt_clause_id, literals);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    pub fn exclude(candidate: InternalSolvableId, reason: StringId) -> (Self, Clause) {
        let (kind, watched_literals) = Clause::exclude(candidate, reason);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    fn from_kind_and_initial_watches(watched_literals: Option<[Literal; 2]>) -> Self {
        let watched_literals = watched_literals.unwrap_or([Literal::null(), Literal::null()]);

        let clause = Self {
            watched_literals,
            next_watches: [ClauseId::null(), ClauseId::null()],
        };

        debug_assert!(!clause.has_watches() || watched_literals[0] != watched_literals[1]);

        clause
    }

    pub fn link_to_clause(&mut self, watch_index: usize, linked_clause: ClauseId) {
        self.next_watches[watch_index] = linked_clause;
    }

    pub fn unlink_clause(
        &mut self,
        linked_clause: &ClauseState,
        watched_solvable: InternalSolvableId,
        linked_clause_watch_index: usize,
    ) {
        if self.watched_literals[0].solvable_id() == watched_solvable {
            self.next_watches[0] = linked_clause.next_watches[linked_clause_watch_index];
        } else {
            debug_assert_eq!(self.watched_literals[1].solvable_id(), watched_solvable);
            self.next_watches[1] = linked_clause.next_watches[linked_clause_watch_index];
        }
    }

    #[inline]
    pub fn next_watched_clause(&self, solvable_id: InternalSolvableId) -> ClauseId {
        if solvable_id == self.watched_literals[0].solvable_id() {
            self.next_watches[0]
        } else {
            debug_assert_eq!(self.watched_literals[1].solvable_id(), solvable_id);
            self.next_watches[1]
        }
    }

    pub fn has_watches(&self) -> bool {
        // If the first watch is not null, the second won't be either
        !self.watched_literals[0].is_null()
    }

    pub fn next_unwatched_literal(
        &self,
        clause: &Clause,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
        requirement_to_sorted_candidates: &FrozenMap<
            Requirement,
            Vec<SolvableId>,
            ahash::RandomState,
        >,
        decision_map: &DecisionMap,
        for_watch_index: usize,
    ) -> Option<Literal> {
        let other_watch_index = 1 - for_watch_index;

        match clause {
            Clause::InstallRoot => unreachable!(),
            Clause::Excluded(_, _) => unreachable!(),
            Clause::Constrains(..) | Clause::ForbidMultipleInstances(..) | Clause::Lock(..) => {
                // We cannot move the watches in these clauses.
                None
            }
            clause => {
                let next = clause.try_fold_literals(
                    learnt_clauses,
                    requirement_to_sorted_candidates,
                    (),
                    |_, lit| {
                        // The next unwatched variable (if available), is a variable that is:
                        // * Not already being watched
                        // * Not yet decided, or decided in such a way that the literal yields true
                        if self.watched_literals[other_watch_index].solvable_id()
                            != lit.solvable_id()
                            && lit.eval(decision_map).unwrap_or(true)
                        {
                            ControlFlow::Break(lit)
                        } else {
                            ControlFlow::Continue(())
                        }
                    },
                );
                match next {
                    ControlFlow::Break(lit) => Some(lit),
                    ControlFlow::Continue(_) => None,
                }
            }
        }
    }
}

/// Represents a literal in a SAT clause (i.e. either A or ¬A)
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) struct Literal(u32);

impl Literal {
    /// Constructs a new [`Literal`] from a [`InternalSolvableId`] and a boolean
    /// indicating whether the literal should be negated.
    pub fn new(solvable_id: InternalSolvableId, negate: bool) -> Self {
        assert!(solvable_id.0 < (u32::MAX >> 1) - 1, "solvable id too big");
        Self(solvable_id.0 << 1 | negate as u32)
    }
}

impl ArenaId for Literal {
    fn from_usize(x: usize) -> Self {
        debug_assert!(x <= u32::MAX as usize, "watched literal id too big");
        Literal(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl Literal {
    pub fn null() -> Self {
        Self(u32::MAX)
    }

    pub fn is_null(&self) -> bool {
        self.0 == u32::MAX
    }

    pub fn negate(&self) -> bool {
        (self.0 & 1) == 1
    }

    /// Returns the value that would make the literal evaluate to true if
    /// assigned to the literal's solvable
    pub(crate) fn satisfying_value(self) -> bool {
        !self.negate()
    }

    /// Returns the value that would make the literal evaluate to true if
    /// assigned to the literal's solvable
    pub(crate) fn solvable_id(self) -> InternalSolvableId {
        InternalSolvableId(self.0 >> 1)
    }

    /// Evaluates the literal, or returns `None` if no value has been assigned
    /// to the solvable
    #[inline(always)]
    pub(crate) fn eval(self, decision_map: &DecisionMap) -> Option<bool> {
        decision_map
            .value(self.solvable_id())
            .map(|value| value != self.negate())
    }
}

impl InternalSolvableId {
    /// Constructs a [`Literal`] that indicates this solvable should be assigned
    /// a positive value.
    pub fn positive(self) -> Literal {
        Literal::new(self, false)
    }

    /// Constructs a [`Literal`] that indicates this solvable should be assigned
    /// a negative value.
    pub fn negative(self) -> Literal {
        Literal::new(self, true)
    }
}

/// A representation of a clause that implements [`Debug`]
pub(crate) struct ClauseDisplay<'i, I: Interner> {
    kind: Clause,
    interner: &'i I,
}

impl<'i, I: Interner> Display for ClauseDisplay<'i, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            Clause::InstallRoot => write!(f, "InstallRoot"),
            Clause::Excluded(solvable_id, reason) => {
                write!(
                    f,
                    "Excluded({}({:?}), {})",
                    solvable_id.display(self.interner),
                    solvable_id,
                    self.interner.display_string(reason)
                )
            }
            Clause::Learnt(learnt_id) => write!(f, "Learnt({learnt_id:?})"),
            Clause::Requires(solvable_id, requirement) => {
                write!(
                    f,
                    "Requires({}({:?}), {})",
                    solvable_id.display(self.interner),
                    solvable_id,
                    requirement.display(self.interner),
                )
            }
            Clause::Constrains(s1, s2, version_set_id) => {
                write!(
                    f,
                    "Constrains({}({:?}), {}({:?}), {})",
                    s1.display(self.interner),
                    s1,
                    s2.display(self.interner),
                    s2,
                    self.interner.display_version_set(version_set_id)
                )
            }
            Clause::ForbidMultipleInstances(s1, s2, name) => {
                write!(
                    f,
                    "ForbidMultipleInstances({}({:?}), {}({:?}), {})",
                    s1.display(self.interner),
                    s1,
                    s2.display(self.interner),
                    s2,
                    self.interner.display_name(name)
                )
            }
            Clause::Lock(locked, other) => {
                write!(
                    f,
                    "Lock({}({:?}), {}({:?}))",
                    locked.display(self.interner),
                    locked,
                    other.display(self.interner),
                    other,
                )
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{internal::arena::ArenaId, solver::decision::Decision};

    fn clause(next_clauses: [ClauseId; 2], watch_literals: [Literal; 2]) -> ClauseState {
        ClauseState {
            watched_literals: watch_literals,
            next_watches: next_clauses,
        }
    }

    #[test]
    #[allow(clippy::bool_assert_comparison)]
    fn test_literal_satisfying_value() {
        let lit = InternalSolvableId::root().negative();
        assert_eq!(lit.satisfying_value(), false);

        let lit = InternalSolvableId::root().positive();
        assert_eq!(lit.satisfying_value(), true);
    }

    #[test]
    fn test_literal_eval() {
        let mut decision_map = DecisionMap::new();

        let literal = InternalSolvableId::root().positive();
        let negated_literal = InternalSolvableId::root().negative();

        // Undecided
        assert_eq!(literal.eval(&decision_map), None);
        assert_eq!(negated_literal.eval(&decision_map), None);

        // Decided
        decision_map.set(InternalSolvableId::root(), true, 1);
        assert_eq!(literal.eval(&decision_map), Some(true));
        assert_eq!(negated_literal.eval(&decision_map), Some(false));

        decision_map.set(InternalSolvableId::root(), false, 1);
        assert_eq!(literal.eval(&decision_map), Some(false));
        assert_eq!(negated_literal.eval(&decision_map), Some(true));
    }

    #[test]
    fn test_unlink_clause_different() {
        let clause1 = clause(
            [ClauseId::from_usize(2), ClauseId::from_usize(3)],
            [
                InternalSolvableId::from_usize(1596).negative(),
                InternalSolvableId::from_usize(1211).negative(),
            ],
        );
        let clause2 = clause(
            [ClauseId::null(), ClauseId::from_usize(3)],
            [
                InternalSolvableId::from_usize(1596).negative(),
                InternalSolvableId::from_usize(1208).negative(),
            ],
        );
        let clause3 = clause(
            [ClauseId::null(), ClauseId::null()],
            [
                InternalSolvableId::from_usize(1211).negative(),
                InternalSolvableId::from_usize(42).negative(),
            ],
        );

        // Unlink 0
        {
            let mut clause1 = clause1.clone();
            clause1.unlink_clause(&clause2, InternalSolvableId::from_usize(1596), 0);
            assert_eq!(
                clause1.watched_literals,
                [
                    InternalSolvableId::from_usize(1596).negative(),
                    InternalSolvableId::from_usize(1211).negative()
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
            clause1.unlink_clause(&clause3, InternalSolvableId::from_usize(1211), 0);
            assert_eq!(
                clause1.watched_literals,
                [
                    InternalSolvableId::from_usize(1596).negative(),
                    InternalSolvableId::from_usize(1211).negative()
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
                InternalSolvableId::from_usize(1596).negative(),
                InternalSolvableId::from_usize(1211).negative(),
            ],
        );
        let clause2 = clause(
            [ClauseId::null(), ClauseId::null()],
            [
                InternalSolvableId::from_usize(1596).negative(),
                InternalSolvableId::from_usize(1211).negative(),
            ],
        );

        // Unlink 0
        {
            let mut clause1 = clause1.clone();
            clause1.unlink_clause(&clause2, InternalSolvableId::from_usize(1596), 0);
            assert_eq!(
                clause1.watched_literals,
                [
                    InternalSolvableId::from_usize(1596).negative(),
                    InternalSolvableId::from_usize(1211).negative()
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
            clause1.unlink_clause(&clause2, InternalSolvableId::from_usize(1211), 1);
            assert_eq!(
                clause1.watched_literals,
                [
                    InternalSolvableId::from_usize(1596).negative(),
                    InternalSolvableId::from_usize(1211).negative()
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

        let parent = InternalSolvableId::from_usize(1);
        let candidate1 = SolvableId::from_usize(2);
        let candidate2 = SolvableId::from_usize(3);

        // No conflict, all candidates available
        let (clause, conflict, _kind) = ClauseState::requires(
            parent,
            VersionSetId::from_usize(0).into(),
            &[candidate1, candidate2],
            &decisions,
        );
        assert!(!conflict);
        assert_eq!(clause.watched_literals[0].solvable_id(), parent);
        assert_eq!(clause.watched_literals[1].solvable_id(), candidate1.into());

        // No conflict, still one candidate available
        decisions
            .try_add_decision(Decision::new(candidate1.into(), false, ClauseId::null()), 1)
            .unwrap();
        let (clause, conflict, _kind) = ClauseState::requires(
            parent,
            VersionSetId::from_usize(0).into(),
            &[candidate1, candidate2],
            &decisions,
        );
        assert!(!conflict);
        assert_eq!(clause.watched_literals[0].solvable_id(), parent);
        assert_eq!(clause.watched_literals[1].solvable_id(), candidate2.into());

        // Conflict, no candidates available
        decisions
            .try_add_decision(Decision::new(candidate2.into(), false, ClauseId::null()), 1)
            .unwrap();
        let (clause, conflict, _kind) = ClauseState::requires(
            parent,
            VersionSetId::from_usize(0).into(),
            &[candidate1, candidate2],
            &decisions,
        );
        assert!(conflict);
        assert_eq!(clause.watched_literals[0].solvable_id(), parent);
        assert_eq!(clause.watched_literals[1].solvable_id(), candidate1.into());

        // Panic
        decisions
            .try_add_decision(Decision::new(parent, false, ClauseId::null()), 1)
            .unwrap();
        let panicked = std::panic::catch_unwind(|| {
            ClauseState::requires(
                parent,
                VersionSetId::from_usize(0).into(),
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

        let parent = InternalSolvableId::from_usize(1);
        let forbidden = InternalSolvableId::from_usize(2);

        // No conflict, forbidden package not installed
        let (clause, conflict, _kind) =
            ClauseState::constrains(parent, forbidden, VersionSetId::from_usize(0), &decisions);
        assert!(!conflict);
        assert_eq!(clause.watched_literals[0].solvable_id(), parent);
        assert_eq!(clause.watched_literals[1].solvable_id(), forbidden);

        // Conflict, forbidden package installed
        decisions
            .try_add_decision(Decision::new(forbidden, true, ClauseId::null()), 1)
            .unwrap();
        let (clause, conflict, _kind) =
            ClauseState::constrains(parent, forbidden, VersionSetId::from_usize(0), &decisions);
        assert!(conflict);
        assert_eq!(clause.watched_literals[0].solvable_id(), parent);
        assert_eq!(clause.watched_literals[1].solvable_id(), forbidden);

        // Panic
        decisions
            .try_add_decision(Decision::new(parent, false, ClauseId::null()), 1)
            .unwrap();
        let panicked = std::panic::catch_unwind(|| {
            ClauseState::constrains(parent, forbidden, VersionSetId::from_usize(0), &decisions)
        })
        .is_err();
        assert!(panicked);
    }

    #[test]
    fn test_clause_size() {
        // This test is here to ensure we don't increase the size of `ClauseState` by
        // accident, as we are creating thousands of instances.
        // libsolv: 24 bytes
        assert_eq!(std::mem::size_of::<ClauseState>(), 16);
    }
}

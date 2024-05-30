use crate::{
    internal::{
        arena::Arena,
        id::{ClauseId, LearntClauseId, SolvableId, VersionSetId},
    },
    pool::Pool,
    solver::decision_map::DecisionMap,
    PackageName, VersionSet,
};

use crate::internal::id::StringId;
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
    Requires(RequiresClause),
    /// Ensures only a single version of a package is installed
    ///
    /// Usage: generate one [`Clause::ForbidMultipleInstances`] clause for each possible combination of
    /// packages under the same name. The clause itself forbids two solvables from being installed at
    /// the same time.
    ///
    /// In SAT terms: (¬A ∨ ¬B)
    ForbidMultipleInstances(ForbidMultipleInstancesClause),
    /// Forbids packages that do not satisfy a solvable's constrains
    ///
    /// Usage: for each constrains relationship in a package, determine all the candidates that do
    /// _not_ satisfy it, and create one [`Clause::Constrains`]. The clause itself forbids two solvables
    /// from being installed at the same time, just as [`Clause::ForbidMultipleInstances`], but it
    /// pays off to have a separate variant for user-friendly error messages.
    ///
    /// In SAT terms: (¬A ∨ ¬B)
    Constrains(ConstrainsClause),
    /// Forbids the package on the right-hand side
    ///
    /// Note that the package on the left-hand side is not part of the clause, but just context to
    /// know which exact package was locked (necessary for user-friendly error messages)
    ///
    /// In SAT terms: (¬root ∨ ¬B). Note that we could encode this as an assertion (¬B), but that
    /// would require additional logic in the solver.
    Lock(LockClause),
    /// A clause learnt during solving
    ///
    /// The learnt clause id can be used to retrieve the clause's literals, which are stored
    /// elsewhere to prevent the size of [`Clause`] from blowing up
    Learnt(LearntClauseId),

    /// A clause that forbids a package from being installed for an external reason.
    Excluded(ExcludeClause),
}

#[derive(Copy, Clone, Debug)]
pub struct RequiresClause {
    pub candidate: SolvableId,
    pub requirement: VersionSetId,
}

#[derive(Copy, Clone, Debug)]
pub struct ForbidMultipleInstancesClause {
    pub from: SolvableId,
    pub to: SolvableId,
}

#[derive(Copy, Clone, Debug)]
pub struct ConstrainsClause {
    pub candidate: SolvableId,
    pub constrained_candidate: SolvableId,
    pub via: VersionSetId,
}

#[derive(Copy, Clone, Debug)]
pub struct LockClause {
    pub locked_candidate: SolvableId,
    pub forbidden_candidate: SolvableId,
}

#[derive(Copy, Clone, Debug)]
pub struct ExcludeClause {
    pub candidate: SolvableId,
    pub reason: StringId,
}

impl From<RequiresClause> for Clause {
    fn from(requires: RequiresClause) -> Self {
        Clause::Requires(requires)
    }
}

impl From<ForbidMultipleInstancesClause> for Clause {
    fn from(forbid_multiple: ForbidMultipleInstancesClause) -> Self {
        Clause::ForbidMultipleInstances(forbid_multiple)
    }
}

impl From<ConstrainsClause> for Clause {
    fn from(constrains: ConstrainsClause) -> Self {
        Clause::Constrains(constrains)
    }
}

impl From<LockClause> for Clause {
    fn from(lock: LockClause) -> Self {
        Clause::Lock(lock)
    }
}

impl From<LearntClauseId> for Clause {
    fn from(value: LearntClauseId) -> Self {
        Clause::Learnt(value)
    }
}

impl From<ExcludeClause> for Clause {
    fn from(value: ExcludeClause) -> Self {
        Clause::Excluded(value)
    }
}

impl ExcludeClause {
    pub fn visit_literal(&self, mut visit: impl FnMut(Literal)) {
        visit(Literal {
            solvable_id: self.candidate,
            negate: true,
        });
    }
}

impl RequiresClause {
    pub fn visit_literal(
        &self,
        version_set_to_sorted_candidates: &FrozenMap<VersionSetId, Vec<SolvableId>>,
        mut visit: impl FnMut(Literal),
    ) {
        visit(Literal {
            solvable_id: self.candidate,
            negate: true,
        });

        for &solvable_id in &version_set_to_sorted_candidates[&self.requirement] {
            visit(Literal {
                solvable_id,
                negate: false,
            });
        }
    }
}

impl ForbidMultipleInstancesClause {
    pub fn visit_literal(&self, mut visit: impl FnMut(Literal)) {
        visit(Literal {
            solvable_id: self.from,
            negate: true,
        });

        visit(Literal {
            solvable_id: self.to,
            negate: true,
        });
    }
}

impl ConstrainsClause {
    pub fn visit_literal(&self, mut visit: impl FnMut(Literal)) {
        visit(Literal {
            solvable_id: self.candidate,
            negate: true,
        });

        visit(Literal {
            solvable_id: self.constrained_candidate,
            negate: true,
        });
    }
}

impl LockClause {
    pub fn visit_literal(&self, mut visit: impl FnMut(Literal)) {
        visit(Literal {
            solvable_id: SolvableId::root(),
            negate: true,
        });

        visit(Literal {
            solvable_id: self.forbidden_candidate,
            negate: true,
        });
    }
}

impl Clause {
    /// Visits each literal in the clause
    pub fn visit_literals(
        &self,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
        version_set_to_sorted_candidates: &FrozenMap<VersionSetId, Vec<SolvableId>>,
        mut visit: impl FnMut(Literal),
    ) {
        match *self {
            Clause::InstallRoot => unreachable!(),
            Clause::Excluded(clause) => clause.visit_literal(visit),
            Clause::Learnt(learnt_id) => {
                for &literal in &learnt_clauses[learnt_id] {
                    visit(literal);
                }
            }
            Clause::Requires(clause) => {
                clause.visit_literal(version_set_to_sorted_candidates, visit)
            }
            Clause::Constrains(clause) => clause.visit_literal(visit),
            Clause::ForbidMultipleInstances(clause) => clause.visit_literal(visit),
            Clause::Lock(clause) => clause.visit_literal(visit),
        }
    }

    /// Returns an object that implements `Debug` to debug the clause.
    pub fn debug<'pool, VS: VersionSet, N: PackageName + Display>(
        &self,
        pool: &'pool Pool<VS, N>,
    ) -> impl Debug + 'pool {
        ClauseDebug {
            clause: *self,
            pool,
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
    pub watched_literals: [SolvableId; 2],
    // The ids of the next clause in each linked list that this clause is part of
    next_watches: [ClauseId; 2],
    // The clause itself
    pub(crate) clause: Clause,
}

impl ClauseState {
    pub fn debug<'a, VS: VersionSet, N: PackageName>(
        &self,
        pool: &'a Pool<VS, N>,
    ) -> ClauseDebug<'a, VS, N> {
        ClauseDebug {
            clause: self.clause,
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
        watched_solvable: SolvableId,
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
    pub fn next_watched_clause(&self, solvable_id: SolvableId) -> ClauseId {
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
        solvable_id: SolvableId,
        decision_map: &DecisionMap,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
    ) -> Option<([Literal; 2], usize)> {
        debug_assert!(self.watched_literals.contains(&solvable_id));

        let literals @ [w1, w2] = self.watched_literals(learnt_clauses);

        if solvable_id == w1.solvable_id && w1.eval(decision_map) == Some(false) {
            Some((literals, 0))
        } else if solvable_id == w2.solvable_id && w2.eval(decision_map) == Some(false) {
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
                    solvable_id: self.watched_literals[0],
                    negate: !op1,
                },
                Literal {
                    solvable_id: self.watched_literals[1],
                    negate: !op2,
                },
            ]
        };

        match self.clause {
            Clause::InstallRoot | Clause::Excluded(..) => unreachable!(),
            Clause::Learnt(learnt_id) => {
                // TODO: we might want to do something else for performance, like keeping the whole
                // literal in `self.watched_literals`, to avoid lookups... But first we should
                // benchmark!
                let &w1 = learnt_clauses[learnt_id]
                    .iter()
                    .find(|l| l.solvable_id == self.watched_literals[0])
                    .unwrap();
                let &w2 = learnt_clauses[learnt_id]
                    .iter()
                    .find(|l| l.solvable_id == self.watched_literals[1])
                    .unwrap();
                [w1, w2]
            }
            Clause::Constrains(..) | Clause::ForbidMultipleInstances(..) | Clause::Lock(..) => {
                literals(false, false)
            }
            Clause::Requires(RequiresClause { candidate, .. }) => {
                if self.watched_literals[0] == candidate {
                    literals(false, true)
                } else if self.watched_literals[1] == candidate {
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
    ) -> Option<SolvableId> {
        // The next unwatched variable (if available), is a variable that is:
        // * Not already being watched
        // * Not yet decided, or decided in such a way that the literal yields true
        let can_watch = |solvable_lit: Literal| {
            !self.watched_literals.contains(&solvable_lit.solvable_id)
                && solvable_lit.eval(decision_map).unwrap_or(true)
        };

        match self.clause {
            Clause::InstallRoot => unreachable!(),
            Clause::Excluded(_) => unreachable!(),
            Clause::Learnt(learnt_id) => learnt_clauses[learnt_id]
                .iter()
                .cloned()
                .find(|&l| can_watch(l))
                .map(|l| l.solvable_id),
            Clause::Constrains(..) | Clause::ForbidMultipleInstances(..) | Clause::Lock(..) => None,
            Clause::Requires(clause) => {
                // The solvable that added this clause
                let solvable_lit = Literal {
                    solvable_id: clause.candidate,
                    negate: true,
                };
                if can_watch(solvable_lit) {
                    return Some(clause.candidate);
                }

                // The available candidates
                for &candidate in &version_set_to_sorted_candidates[&clause.requirement] {
                    let lit = Literal {
                        solvable_id: candidate,
                        negate: false,
                    };
                    if can_watch(lit) {
                        return Some(candidate);
                    }
                }

                // No solvable available to watch
                None
            }
        }
    }
}

/// Represents a literal in a SAT clause (i.e. either A or ¬A)
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub(crate) struct Literal {
    pub(crate) solvable_id: SolvableId,
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
            .value(self.solvable_id)
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
    clause: Clause,
    pool: &'pool Pool<VS, N>,
}

impl<VS: VersionSet, N: PackageName + Display> Debug for ClauseDebug<'_, VS, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.clause {
            Clause::InstallRoot => write!(f, "install root"),
            Clause::Excluded(ExcludeClause { candidate, reason }) => {
                write!(
                    f,
                    "{} excluded because: {}",
                    candidate.display(self.pool),
                    self.pool.resolve_string(reason)
                )
            }
            Clause::Learnt(learnt_id) => write!(f, "learnt clause {learnt_id:?}"),
            Clause::Requires(RequiresClause {
                candidate,
                requirement,
            }) => {
                let match_spec = self.pool.resolve_version_set(requirement).to_string();
                write!(
                    f,
                    "{} requires {} {match_spec}",
                    candidate.display(self.pool),
                    self.pool
                        .resolve_version_set_package_name(requirement)
                        .display(self.pool)
                )
            }
            Clause::Constrains(ConstrainsClause {
                candidate,
                constrained_candidate,
                via,
            }) => {
                write!(
                    f,
                    "{} excludes {} by {}",
                    candidate.display(self.pool),
                    constrained_candidate.display(self.pool),
                    self.pool.resolve_version_set(via)
                )
            }
            Clause::Lock(LockClause {
                locked_candidate,
                forbidden_candidate: other_candidate,
            }) => {
                write!(
                    f,
                    "{} is locked, so {} is forbidden",
                    locked_candidate.display(self.pool),
                    other_candidate.display(self.pool)
                )
            }
            Clause::ForbidMultipleInstances(ForbidMultipleInstancesClause { from, .. }) => {
                let name = self
                    .pool
                    .resolve_internal_solvable(from)
                    .solvable()
                    .name
                    .display(self.pool);
                write!(f, "only one {name} allowed")
            }
        }
    }
}

#[derive(Default)]
pub struct Clauses {
    clauses: Arena<ClauseId, ClauseState>,
}

impl Clauses {
    /// Allocates a new [`Clause::Requires`] clause.
    pub fn alloc_requires(
        &mut self,
        candidate: SolvableId,
        requirement: VersionSetId,
        resolved_candidates: &[SolvableId],
        decision_tracker: &DecisionTracker,
    ) -> (ClauseId, bool) {
        // It only makes sense to introduce a requires clause when the parent solvable is undecided
        // or going to be installed
        assert_ne!(decision_tracker.assigned_value(candidate), Some(false));

        let clause = RequiresClause {
            candidate,
            requirement,
        };
        let (watched_literals, conflict) = if resolved_candidates.is_empty() {
            (None, false)
        } else {
            match resolved_candidates
                .iter()
                .find(|&&c| decision_tracker.assigned_value(c) != Some(false))
            {
                // Watch any candidate that is not assigned to false
                Some(watched_candidate) => (Some([candidate, *watched_candidate]), false),

                // All candidates are assigned to false! Therefore the clause conflicts with the
                // current decisions. There are no valid watches for it at the moment, but we will
                // assign default ones nevertheless, because they will become valid after the solver
                // restarts.
                None => (Some([candidate, resolved_candidates[0]]), true),
            }
        };

        let clause_id = self.alloc(clause, watched_literals);
        (clause_id, conflict)
    }

    /// Allocates a new [`Clause::Constrains`] clause.
    pub fn alloc_constrains(
        &mut self,
        candidate: SolvableId,
        constrained_candidate: SolvableId,
        requires_clause: VersionSetId,
        decision_tracker: &DecisionTracker,
    ) -> (ClauseId, bool) {
        // It only makes sense to introduce a constrains clause when the parent solvable is
        // undecided or going to be installed
        assert_ne!(decision_tracker.assigned_value(candidate), Some(false));

        // If the forbidden solvable is already assigned to true, that means that there is a
        // conflict with current decisions, because it implies the parent solvable would be false
        // (and we just asserted that it is not)
        let conflict = decision_tracker.assigned_value(constrained_candidate) == Some(true);

        let clause_id = self.alloc(
            ConstrainsClause {
                candidate,
                constrained_candidate,
                via: requires_clause,
            },
            Some([candidate, constrained_candidate]),
        );

        (clause_id, conflict)
    }

    /// Allocates a new [`Clause::ForbidMultipleInstances`] clause.
    pub fn alloc_forbid_multiple(
        &mut self,
        candidates: SolvableId,
        constrained_candidate: SolvableId,
    ) -> ClauseId {
        let clause = ForbidMultipleInstancesClause {
            from: candidates,
            to: constrained_candidate,
        };

        self.alloc(clause, Some([candidates, constrained_candidate]))
    }

    /// Allocates a new [`Clause::InstallRoot`] clause.
    pub fn alloc_root(&mut self) -> ClauseId {
        self.alloc(Clause::InstallRoot, None)
    }

    /// Allocates a new [`Clause::Excluded`] clause.
    pub fn alloc_exclude(&mut self, candidate: SolvableId, reason: StringId) -> ClauseId {
        self.alloc(Clause::Excluded(ExcludeClause { candidate, reason }), None)
    }

    /// Allocates a new [`Clause::Learnt`] clause.
    pub fn alloc_learnt(
        &mut self,
        learnt_clause_id: LearntClauseId,
        literals: &[Literal],
    ) -> ClauseId {
        debug_assert!(!literals.is_empty());
        let watched_literals = if literals.len() == 1 {
            // Not need for watches, since we learned an assertion
            None
        } else {
            Some([literals[0].solvable_id, literals[1].solvable_id])
        };

        self.alloc(Clause::Learnt(learnt_clause_id), watched_literals)
    }

    /// Allocates a new [`Clause::Lock`] clause.
    pub fn alloc_lock(
        &mut self,
        locked_candidate: SolvableId,
        other_candidate: SolvableId,
    ) -> ClauseId {
        self.alloc(
            Clause::Lock(LockClause {
                locked_candidate,
                forbidden_candidate: other_candidate,
            }),
            Some([SolvableId::root(), other_candidate]),
        )
    }

    fn alloc(
        &mut self,
        clause: impl Into<Clause>,
        watched_literals: Option<[SolvableId; 2]>,
    ) -> ClauseId {
        let watched_literals = watched_literals.unwrap_or([SolvableId::null(), SolvableId::null()]);

        let clause = ClauseState {
            watched_literals,
            next_watches: [ClauseId::null(), ClauseId::null()],
            clause: clause.into(),
        };

        debug_assert!(!clause.has_watches() || watched_literals[0] != watched_literals[1]);

        self.clauses.alloc(clause)
    }

    /// Returns the clause with the given id.
    pub fn clause(&self, id: ClauseId) -> Clause {
        self.clauses[id].clause
    }

    /// Returns the clause with the given id.
    pub fn clause_state_mut(&mut self, id: ClauseId) -> &mut ClauseState {
        &mut self.clauses[id]
    }

    /// Returns two clause states with the given ids.
    pub fn two_clause_state_mut(&mut self, a: ClauseId, b: ClauseId) -> (&mut ClauseState, &mut ClauseState) {
        self.clauses.get_two_mut(a, b)
    }

    pub fn has_watches(&self, id: ClauseId) -> bool {
        self.clauses[id].has_watches()
    }
}

// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::internal::arena::ArenaId;
//     use crate::solver::decision::Decision;
//
//     fn clause(next_clauses: [ClauseId; 2], watched_solvables: [SolvableId; 2]) -> ClauseState {
//         ClauseState {
//             watched_literals: watched_solvables,
//             next_watches: next_clauses,
//
//             // The kind is irrelevant here
//             clause: Clause::InstallRoot,
//         }
//     }
//
//     #[test]
//     #[allow(clippy::bool_assert_comparison)]
//     fn test_literal_satisfying_value() {
//         let lit = Literal {
//             solvable_id: SolvableId::root(),
//             negate: true,
//         };
//         assert_eq!(lit.satisfying_value(), false);
//
//         let lit = Literal {
//             solvable_id: SolvableId::root(),
//             negate: false,
//         };
//         assert_eq!(lit.satisfying_value(), true);
//     }
//
//     #[test]
//     fn test_literal_eval() {
//         let mut decision_map = DecisionMap::new();
//
//         let literal = Literal {
//             solvable_id: SolvableId::root(),
//             negate: false,
//         };
//         let negated_literal = Literal {
//             solvable_id: SolvableId::root(),
//             negate: true,
//         };
//
//         // Undecided
//         assert_eq!(literal.eval(&decision_map), None);
//         assert_eq!(negated_literal.eval(&decision_map), None);
//
//         // Decided
//         decision_map.set(SolvableId::root(), true, 1);
//         assert_eq!(literal.eval(&decision_map), Some(true));
//         assert_eq!(negated_literal.eval(&decision_map), Some(false));
//
//         decision_map.set(SolvableId::root(), false, 1);
//         assert_eq!(literal.eval(&decision_map), Some(false));
//         assert_eq!(negated_literal.eval(&decision_map), Some(true));
//     }
//
//     #[test]
//     fn test_unlink_clause_different() {
//         let clause1 = clause(
//             [ClauseId::from_usize(2), ClauseId::from_usize(3)],
//             [SolvableId::from_usize(1596), SolvableId::from_usize(1211)],
//         );
//         let clause2 = clause(
//             [ClauseId::null(), ClauseId::from_usize(3)],
//             [SolvableId::from_usize(1596), SolvableId::from_usize(1208)],
//         );
//         let clause3 = clause(
//             [ClauseId::null(), ClauseId::null()],
//             [SolvableId::from_usize(1211), SolvableId::from_usize(42)],
//         );
//
//         // Unlink 0
//         {
//             let mut clause1 = clause1.clone();
//             clause1.unlink_clause(&clause2, SolvableId::from_usize(1596), 0);
//             assert_eq!(
//                 clause1.watched_literals,
//                 [SolvableId::from_usize(1596), SolvableId::from_usize(1211)]
//             );
//             assert_eq!(
//                 clause1.next_watches,
//                 [ClauseId::null(), ClauseId::from_usize(3)]
//             )
//         }
//
//         // Unlink 1
//         {
//             let mut clause1 = clause1;
//             clause1.unlink_clause(&clause3, SolvableId::from_usize(1211), 0);
//             assert_eq!(
//                 clause1.watched_literals,
//                 [SolvableId::from_usize(1596), SolvableId::from_usize(1211)]
//             );
//             assert_eq!(
//                 clause1.next_watches,
//                 [ClauseId::from_usize(2), ClauseId::null()]
//             )
//         }
//     }
//
//     #[test]
//     fn test_unlink_clause_same() {
//         let clause1 = clause(
//             [ClauseId::from_usize(2), ClauseId::from_usize(2)],
//             [SolvableId::from_usize(1596), SolvableId::from_usize(1211)],
//         );
//         let clause2 = clause(
//             [ClauseId::null(), ClauseId::null()],
//             [SolvableId::from_usize(1596), SolvableId::from_usize(1211)],
//         );
//
//         // Unlink 0
//         {
//             let mut clause1 = clause1.clone();
//             clause1.unlink_clause(&clause2, SolvableId::from_usize(1596), 0);
//             assert_eq!(
//                 clause1.watched_literals,
//                 [SolvableId::from_usize(1596), SolvableId::from_usize(1211)]
//             );
//             assert_eq!(
//                 clause1.next_watches,
//                 [ClauseId::null(), ClauseId::from_usize(2)]
//             )
//         }
//
//         // Unlink 1
//         {
//             let mut clause1 = clause1;
//             clause1.unlink_clause(&clause2, SolvableId::from_usize(1211), 1);
//             assert_eq!(
//                 clause1.watched_literals,
//                 [SolvableId::from_usize(1596), SolvableId::from_usize(1211)]
//             );
//             assert_eq!(
//                 clause1.next_watches,
//                 [ClauseId::from_usize(2), ClauseId::null()]
//             )
//         }
//     }
//
//     #[test]
//     fn test_requires_with_and_without_conflict() {
//         let mut decisions = DecisionTracker::new();
//
//         let parent = SolvableId::from_usize(1);
//         let candidate1 = SolvableId::from_usize(2);
//         let candidate2 = SolvableId::from_usize(3);
//
//         // No conflict, all candidates available
//         let (clause, conflict) = ClauseState::requires(
//             parent,
//             VersionSetId::from_usize(0),
//             &[candidate1, candidate2],
//             &decisions,
//         );
//         assert!(!conflict);
//         assert_eq!(clause.watched_literals[0], parent);
//         assert_eq!(clause.watched_literals[1], candidate1);
//
//         // No conflict, still one candidate available
//         decisions
//             .try_add_decision(Decision::new(candidate1, false, ClauseId::null()), 1)
//             .unwrap();
//         let (clause, conflict) = ClauseState::requires(
//             parent,
//             VersionSetId::from_usize(0),
//             &[candidate1, candidate2],
//             &decisions,
//         );
//         assert!(!conflict);
//         assert_eq!(clause.watched_literals[0], parent);
//         assert_eq!(clause.watched_literals[1], candidate2);
//
//         // Conflict, no candidates available
//         decisions
//             .try_add_decision(Decision::new(candidate2, false, ClauseId::null()), 1)
//             .unwrap();
//         let (clause, conflict) = ClauseState::requires(
//             parent,
//             VersionSetId::from_usize(0),
//             &[candidate1, candidate2],
//             &decisions,
//         );
//         assert!(conflict);
//         assert_eq!(clause.watched_literals[0], parent);
//         assert_eq!(clause.watched_literals[1], candidate1);
//
//         // Panic
//         decisions
//             .try_add_decision(Decision::new(parent, false, ClauseId::null()), 1)
//             .unwrap();
//         let panicked = std::panic::catch_unwind(|| {
//             ClauseState::requires(
//                 parent,
//                 VersionSetId::from_usize(0),
//                 &[candidate1, candidate2],
//                 &decisions,
//             )
//         })
//         .is_err();
//         assert!(panicked);
//     }
//
//     #[test]
//     fn test_constrains_with_and_without_conflict() {
//         let mut decisions = DecisionTracker::new();
//
//         let parent = SolvableId::from_usize(1);
//         let forbidden = SolvableId::from_usize(2);
//
//         // No conflict, forbidden package not installed
//         let (clause, conflict) =
//             ClauseState::constrains(parent, forbidden, VersionSetId::from_usize(0), &decisions);
//         assert!(!conflict);
//         assert_eq!(clause.watched_literals[0], parent);
//         assert_eq!(clause.watched_literals[1], forbidden);
//
//         // Conflict, forbidden package installed
//         decisions
//             .try_add_decision(Decision::new(forbidden, true, ClauseId::null()), 1)
//             .unwrap();
//         let (clause, conflict) =
//             ClauseState::constrains(parent, forbidden, VersionSetId::from_usize(0), &decisions);
//         assert!(conflict);
//         assert_eq!(clause.watched_literals[0], parent);
//         assert_eq!(clause.watched_literals[1], forbidden);
//
//         // Panic
//         decisions
//             .try_add_decision(Decision::new(parent, false, ClauseId::null()), 1)
//             .unwrap();
//         let panicked = std::panic::catch_unwind(|| {
//             ClauseState::constrains(parent, forbidden, VersionSetId::from_usize(0), &decisions)
//         })
//         .is_err();
//         assert!(panicked);
//     }
//
//     #[test]
//     fn test_clause_size() {
//         // This test is here to ensure we don't increase the size of `ClauseState` by accident, as
//         // we are creating thousands of instances. Note: libsolv manages to bring down the size to
//         // 24, so there is probably room for improvement.
//         assert_eq!(std::mem::size_of::<ClauseState>(), 32);
//     }
// }

use crate::internal::arena::ArenaId;
use crate::solver::clause::Literal;
use crate::{
    internal::{id::ClauseId, mapping::Mapping},
    solver::clause::ClauseState,
};

/// A map from solvables to the clauses that are watching them
pub(crate) struct WatchMap {
    /// Note: the map is to a single clause, but clauses form a linked list, so
    /// it is possible to go from one to the next
    map: Mapping<WatchedLiteralId, ClauseId>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) struct WatchedLiteralId(u32);

impl From<Literal> for WatchedLiteralId {
    fn from(value: Literal) -> Self {
        debug_assert!(!value.solvable_id.is_root());
        assert!(value.solvable_id.0 < (u32::MAX >> 1), "solvable id too big");
        WatchedLiteralId(value.solvable_id.0 * 2 + if value.negate { 1 } else { 0 })
    }
}

impl ArenaId for WatchedLiteralId {
    fn from_usize(x: usize) -> Self {
        debug_assert!(x <= u32::MAX as usize, "watched literal id too big");
        WatchedLiteralId(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl WatchMap {
    pub(crate) fn new() -> Self {
        Self {
            map: Mapping::new(),
        }
    }

    pub(crate) fn start_watching(&mut self, clause: &mut ClauseState, clause_id: ClauseId) {
        for (watch_index, watched_literal) in clause.watched_literals.into_iter().enumerate() {
            let already_watching = self
                .first_clause_watching_literal(watched_literal)
                .unwrap_or(ClauseId::null());
            clause.link_to_clause(watch_index, already_watching);
            self.watch_literal(watched_literal, clause_id);
        }
    }

    pub(crate) fn update_watched(
        &mut self,
        predecessor_clause: Option<&mut ClauseState>,
        clause: &mut ClauseState,
        clause_id: ClauseId,
        watch_index: usize,
        previous_watch: Literal,
        new_watch: Literal,
    ) {
        // Remove this clause from its current place in the linked list, because we
        // are no longer watching what brought us here
        if let Some(predecessor_clause) = predecessor_clause {
            // Unlink the clause
            predecessor_clause.unlink_clause(clause, previous_watch.solvable_id, watch_index);
        } else {
            // This was the first clause in the chain
            self.map
                .insert(previous_watch.into(), clause.next_watches[watch_index]);
        }

        // Set the new watch
        clause.watched_literals[watch_index] = new_watch;
        let previous_clause_id = self
            .map
            .insert(new_watch.into(), clause_id)
            .unwrap_or(ClauseId::null());
        clause.next_watches[watch_index] = previous_clause_id;
    }

    pub(crate) fn first_clause_watching_literal(
        &mut self,
        watched_literal: Literal,
    ) -> Option<ClauseId> {
        self.map.get(watched_literal.into()).copied()
    }

    pub(crate) fn watch_literal(&mut self, watched_literal: Literal, id: ClauseId) {
        self.map.insert(watched_literal.into(), id);
    }
}

use crate::{
    internal::{id::ClauseId, mapping::Mapping},
    solver::clause::{ClauseState, Literal},
};

/// A map from solvables to the clauses that are watching them
pub(crate) struct WatchMap {
    /// Note: the map is to a single clause, but clauses form a linked list, so
    /// it is possible to go from one to the next
    map: Mapping<Literal, ClauseId>,
}

impl WatchMap {
    pub(crate) fn new() -> Self {
        Self {
            map: Mapping::new(),
        }
    }

    pub(crate) fn start_watching(&mut self, clause: &mut ClauseState, clause_id: ClauseId) {
        for (watch_index, watched_literal) in clause.watched_literals.into_iter().enumerate() {
            let already_watching = self.first_clause_watching_literal(watched_literal);
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
            predecessor_clause.unlink_clause(clause, previous_watch.solvable_id(), watch_index);
        } else if let Some(next_watch) = clause.next_watches[watch_index] {
            // This was the first clause in the chain
            self.map.insert(previous_watch, next_watch);
        } else {
            self.map.unset(previous_watch);
        }

        // Set the new watch
        clause.watched_literals[watch_index] = new_watch;
        let previous_clause_id = self.map.insert(new_watch, clause_id);
        clause.next_watches[watch_index] = previous_clause_id;
    }

    pub(crate) fn first_clause_watching_literal(
        &mut self,
        watched_literal: Literal,
    ) -> Option<ClauseId> {
        self.map.get(watched_literal).copied()
    }

    pub(crate) fn watch_literal(&mut self, watched_literal: Literal, id: ClauseId) {
        self.map.insert(watched_literal, id);
    }
}

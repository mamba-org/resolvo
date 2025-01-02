use crate::{
    internal::{id::ClauseId, mapping::Mapping},
    solver::clause::{ClauseState, Literal},
};

/// A map from literals to the clauses that are watching them. Each literal
/// forms a linked list of clauses that are all watching that literal.
pub(crate) struct WatchMap {
    // Note: the map is to a single clause, but clauses form a linked list, so
    // it is possible to go from one to the next
    map: Mapping<Literal, ClauseId>,
}

impl WatchMap {
    pub(crate) fn new() -> Self {
        Self {
            map: Mapping::new(),
        }
    }

    /// Add the clause to the linked list of the literals that the clause is
    /// watching.
    pub(crate) fn start_watching(&mut self, clause: &mut ClauseState, clause_id: ClauseId) {
        for (watch_index, watched_literal) in clause.watched_literals.into_iter().enumerate() {
            // Construct a linked list by adding the clause to the start of the linked list
            // and setting the previous head of the chain as the next element in the linked
            // list.
            let current_head = self.map.get(watched_literal).copied();
            clause.next_watches[watch_index] = current_head;
            self.map.insert(watched_literal, clause_id);
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
            predecessor_clause.unlink_clause(clause, previous_watch.variable(), watch_index);
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

    /// Returns the id of the first clause that is watching the specified
    /// literal.
    pub(crate) fn first_clause_watching_literal(
        &mut self,
        watched_literal: Literal,
    ) -> Option<ClauseId> {
        self.map.get(watched_literal).copied()
    }
}

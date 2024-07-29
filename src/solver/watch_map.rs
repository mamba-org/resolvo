use crate::internal::id::{ExpandedVar, VarId};
use crate::{
    internal::{
        id::{ClauseId, InternalSolvableId},
        mapping::Mapping,
    },
    solver::clause::ClauseState,
};

/// A map from solvables to the clauses that are watching them
pub(crate) struct WatchMap {
    /// Note: the map is to a single clause, but clauses form a linked list, so it is possible to go
    /// from one to the next
    solvables: Mapping<InternalSolvableId, ClauseId>,
    variables: Mapping<u32, ClauseId>,
}

impl WatchMap {
    pub(crate) fn new() -> Self {
        Self {
            solvables: Mapping::new(),
            variables: Mapping::new(),
        }
    }

    pub(crate) fn start_watching(&mut self, clause: &mut ClauseState, clause_id: ClauseId) {
        for (watch_index, watched_solvable) in clause.watched_literals.into_iter().enumerate() {
            let already_watching = self.first_clause_watching_var(watched_solvable);
            clause.link_to_clause(watch_index, already_watching);
            self.watch_solvable(watched_solvable, clause_id);
        }
    }

    pub(crate) fn update_watched(
        &mut self,
        predecessor_clause: Option<&mut ClauseState>,
        clause: &mut ClauseState,
        clause_id: ClauseId,
        watch_index: usize,
        previous_watch: VarId,
        new_watch: VarId,
    ) {
        // Remove this clause from its current place in the linked list, because we
        // are no longer watching what brought us here
        if let Some(predecessor_clause) = predecessor_clause {
            // Unlink the clause
            predecessor_clause.unlink_clause(clause, previous_watch, watch_index);
        } else {
            // This was the first clause in the chain
            let linked_clause = clause.get_linked_clause(watch_index);
            match previous_watch.expand() {
                ExpandedVar::Solvable(s) => {
                    self.solvables.insert(s, linked_clause);
                }
                ExpandedVar::Variable(v) => {
                    self.variables.insert(v, linked_clause);
                }
            }
        }

        let new_watch_clause = match new_watch.expand() {
            ExpandedVar::Solvable(s) => self.solvables.get(s),
            ExpandedVar::Variable(v) => self.variables.get(v),
        };

        // Set the new watch
        clause.watched_literals[watch_index] = new_watch;
        clause.link_to_clause(
            watch_index,
            *new_watch_clause.expect("linking to unknown variable"),
        );
        match new_watch.expand() {
            ExpandedVar::Solvable(s) => self.solvables.insert(s, clause_id),
            ExpandedVar::Variable(v) => self.variables.insert(v, clause_id),
        };
    }

    pub(crate) fn first_clause_watching_var(&mut self, watched_var: VarId) -> ClauseId {
        match watched_var.expand() {
            ExpandedVar::Solvable(s) => self.solvables.get(s),
            ExpandedVar::Variable(v) => self.variables.get(v),
        }
        .copied()
        .unwrap_or(ClauseId::null())
    }

    pub(crate) fn watch_solvable(&mut self, watched_var: VarId, id: ClauseId) {
        match watched_var.expand() {
            ExpandedVar::Solvable(s) => self.solvables.insert(s, id),
            ExpandedVar::Variable(v) => self.variables.insert(v, id),
        }
    }
}

use crate::{
    internal::{arena::ArenaId, id::ClauseId, mapping::Mapping},
    solver::clause::{ClauseWatches, Literal},
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
    pub(crate) fn start_watching(&mut self, clause: &mut ClauseWatches, clause_id: ClauseId) {
        for (watch_index, watched_literal) in
            clause.watched_literals.into_iter().flatten().enumerate()
        {
            // Construct a linked list by adding the clause to the start of the linked list
            // and setting the previous head of the chain as the next element in the linked
            // list.
            let current_head = self.map.get(watched_literal).copied();
            clause.next_watches[watch_index] = current_head;
            self.map.insert(watched_literal, clause_id);
        }
    }

    /// Returns a [`WatchMapCursor`] that can be used to navigate and manipulate
    /// the linked list of the clauses that are watching the specified
    /// literal.
    pub fn cursor<'a>(
        &'a mut self,
        watches: &'a mut [ClauseWatches],
        literal: Literal,
    ) -> Option<WatchMapCursor<'a>> {
        let clause_id = *self.map.get(literal)?;
        let watch_index = if watches[clause_id.to_usize()].watched_literals[0] == Some(literal) {
            0
        } else {
            debug_assert_eq!(
                watches[clause_id.to_usize()].watched_literals[1],
                Some(literal),
                "the clause is not actually watching the literal"
            );
            1
        };

        Some(WatchMapCursor {
            watch_map: self,
            watches,
            literal,
            previous: None,
            current: WatchNode {
                clause_id,
                watch_index,
            },
        })
    }
}

struct WatchNode {
    /// The index of the [`ClauseWatches`]
    clause_id: ClauseId,

    /// A [`ClauseWatches`] contains the state for two linked lists. This index
    /// indicates which of the two linked-list nodes is referenced.
    watch_index: usize,
}

/// The watchmap contains a linked-list of clauses that are watching a certain
/// literal. This linked-list is a singly linked list, which requires some
/// administration when trying to modify the list. The [`WatchMapCursor`] is a
/// utility that allows navigating the linked-list and manipulate it.
///
/// A cursor is created using [`WatchMap::cursor`]. The cursor can iterate
/// through all the clauses using [`WatchMapCursor::next`] and a single watch
/// can be updated using the [`WatchMapCursor::update`] method.
pub struct WatchMapCursor<'a> {
    /// The watchmap that is being navigated.
    watch_map: &'a mut WatchMap,

    /// The nodes of the linked list.
    watches: &'a mut [ClauseWatches],

    /// The literal who's linked list is being navigated.
    literal: Literal,

    /// The previous node we iterated or `None` if this is the head.
    previous: Option<WatchNode>,

    /// The current node.
    current: WatchNode,
}

impl<'a> WatchMapCursor<'a> {
    /// Skip to the next node in the linked list. Returns `None` if there is no
    /// next node.
    pub fn next(mut self) -> Option<Self> {
        let next = self.next_node()?;

        self.previous = Some(self.current);
        self.current = next;

        Some(self)
    }

    /// Returns the next node in the linked list or `None` if there is no next.
    fn next_node(&self) -> Option<WatchNode> {
        let next_clause_id =
            self.watches[self.current.clause_id.to_usize()].next_watches[self.current.watch_index]?;
        let next_clause_watch_index =
            if self.watches[next_clause_id.to_usize()].watched_literals[0] == Some(self.literal) {
                0
            } else {
                debug_assert_eq!(
                    self.watches[next_clause_id.to_usize()].watched_literals[1],
                    Some(self.literal),
                    "the clause is not actually watching the literal"
                );
                1
            };

        Some(WatchNode {
            clause_id: next_clause_id,
            watch_index: next_clause_watch_index,
        })
    }

    /// Returns the other literal that the current clause is watching.
    pub fn other_literal(&self) -> Literal {
        self.watches[self.current.clause_id.to_usize()].watched_literals
            [1 - self.current.watch_index]
            .expect("clauses never watch just one literal")
    }

    /// The current clause that is being navigated.
    pub fn clause_id(&self) -> ClauseId {
        self.current.clause_id
    }

    /// Returns the watches of the current clause.
    pub fn watches(&mut self) -> &mut ClauseWatches {
        &mut self.watches[self.current.clause_id.to_usize()]
    }

    /// Returns the index of the current watch in the current clause.
    pub fn watch_index(&self) -> usize {
        self.current.watch_index
    }

    /// Update the current watch to a new literal. This removes the current node
    /// from the linked-list and sets up a watch on the new literal.
    ///
    /// Returns a cursor that points to the next node in the linked list or
    /// `None` if there is no next.
    pub fn update(mut self, new_watch: Literal) -> Option<Self> {
        debug_assert_ne!(
            new_watch, self.literal,
            "cannot update watch to the same literal"
        );

        let clause_idx = self.current.clause_id.to_usize();
        let next_node = self.next_node();

        // Update the previous node to point to the next node in the linked list
        // (effectively removing this one).
        if let Some(previous) = &self.previous {
            // If there is a previous node we update that node to point to the next.
            self.watches[previous.clause_id.to_usize()].next_watches[previous.watch_index] =
                next_node.as_ref().map(|node| node.clause_id);
        } else if let Some(next_clause_id) = next_node.as_ref().map(|node| node.clause_id) {
            // If there is no previous node, we are the head of the linked list.
            self.watch_map.map.insert(self.literal, next_clause_id);
        } else {
            self.watch_map.map.unset(self.literal);
        }

        // Set the new watch for the current clause.
        let watch = &mut self.watches[clause_idx];
        watch.watched_literals[self.current.watch_index] = Some(new_watch);
        let previous_clause_id = self.watch_map.map.insert(new_watch, self.current.clause_id);
        watch.next_watches[self.current.watch_index] = previous_clause_id;

        // Update the current
        self.current = next_node?;

        Some(self)
    }
}

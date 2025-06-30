use std::{collections::hash_map::Entry, fmt::Display};

use ahash::HashMap;

use crate::{
    Interner, NameId, SolvableId,
    internal::{
        arena::ArenaId,
        id::{SolvableOrRootId, VariableId},
    },
};

/// All variables in the solver are stored in a `VariableMap`. This map is used
/// to keep track of the semantics of a variable, e.g. what a specific variable
/// represents.
///
/// The `VariableMap` is responsible for assigning unique identifiers to each
/// variable represented by [`VariableId`].
pub struct VariableMap {
    /// The id of the next variable to be allocated.
    next_id: usize,

    /// A map from solvable id to variable id.
    solvable_to_variable: HashMap<SolvableId, VariableId>,

    /// Records the origins of all variables.
    origins: HashMap<VariableId, VariableOrigin>,
}

/// Describes the origin of a variable.
#[derive(Clone, Debug)]
pub enum VariableOrigin {
    /// The variable is the root of the decision tree.
    Root,

    /// The variable represents a specific solvable.
    Solvable(SolvableId),

    /// A variable that helps encode an at most one constraint.
    ForbidMultiple(NameId),

    /// A variable that indicates that any solvable of a particular package is
    /// part of the solution.
    AtLeastOne(NameId),
}

impl Default for VariableMap {
    fn default() -> Self {
        let mut origins = HashMap::default();
        origins.insert(VariableId::root(), VariableOrigin::Root);

        Self {
            next_id: 1, // The first variable id is 1 because 0 is reserved for the root.
            solvable_to_variable: HashMap::default(),
            origins,
        }
    }
}

impl VariableMap {
    /// Allocate a variable for a new variable or reuse an existing one.
    pub fn intern_solvable(&mut self, solvable_id: SolvableId) -> VariableId {
        match self.solvable_to_variable.entry(solvable_id) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let id = self.next_id;
                self.next_id += 1;
                let variable_id = VariableId::from_usize(id);
                entry.insert(variable_id);
                self.origins
                    .insert(variable_id, VariableOrigin::Solvable(solvable_id));
                variable_id
            }
        }
    }

    #[cfg(feature = "diagnostics")]
    pub fn count(&self) -> usize {
        self.next_id
    }

    #[cfg(feature = "diagnostics")]
    pub fn size_in_bytes(&self) -> usize {
        self.origins.capacity() * std::mem::size_of::<(VariableId, VariableOrigin)>()
            + self.solvable_to_variable.capacity() * std::mem::size_of::<(SolvableId, VariableId)>()
    }

    /// Allocate a variable for a solvable or the root.
    pub fn intern_solvable_or_root(&mut self, solvable_or_root_id: SolvableOrRootId) -> VariableId {
        match solvable_or_root_id.solvable() {
            Some(solvable_id) => self.intern_solvable(solvable_id),
            None => VariableId::root(),
        }
    }

    /// Allocate a variable that helps encode an at most one constraint.
    pub fn alloc_forbid_multiple_variable(&mut self, name: NameId) -> VariableId {
        let id = self.next_id;
        self.next_id += 1;
        let variable_id = VariableId::from_usize(id);
        self.origins
            .insert(variable_id, VariableOrigin::ForbidMultiple(name));
        variable_id
    }

    /// Allocate a variable helps encode whether at least one solvable for a
    /// particular package is selected.
    pub fn alloc_at_least_one_variable(&mut self, name: NameId) -> VariableId {
        let id = self.next_id;
        self.next_id += 1;
        let variable_id = VariableId::from_usize(id);
        self.origins
            .insert(variable_id, VariableOrigin::AtLeastOne(name));
        variable_id
    }

    /// Returns the origin of a variable. The origin describes the semantics of
    /// a variable.
    pub fn origin(&self, variable_id: VariableId) -> VariableOrigin {
        self.origins[&variable_id].clone()
    }
}

impl VariableId {
    /// Returns the solvable id associated with the variable if it represents a
    /// solvable.
    pub fn as_solvable(self, variable_map: &VariableMap) -> Option<SolvableId> {
        variable_map.origin(self).as_solvable()
    }

    pub fn as_solvable_or_root(self, variable_map: &VariableMap) -> Option<SolvableOrRootId> {
        variable_map.origin(self).as_solvable_or_root()
    }

    /// Returns an object that can be used to format the variable.
    pub fn display<'i, I: Interner>(
        self,
        variable_map: &'i VariableMap,
        interner: &'i I,
    ) -> VariableDisplay<'i, I> {
        VariableDisplay {
            variable: self,
            interner,
            variable_map,
        }
    }
}

pub struct VariableDisplay<'i, I: Interner> {
    variable: VariableId,
    interner: &'i I,
    variable_map: &'i VariableMap,
}

impl<I: Interner> Display for VariableDisplay<'_, I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.variable_map.origin(self.variable) {
            VariableOrigin::Root => write!(f, "root"),
            VariableOrigin::Solvable(solvable_id) => {
                write!(f, "{}", self.interner.display_solvable(solvable_id))
            }
            VariableOrigin::ForbidMultiple(name) => {
                write!(f, "forbid-multiple({})", self.interner.display_name(name))
            }
            VariableOrigin::AtLeastOne(name) => {
                write!(f, "any-of({})", self.interner.display_name(name))
            }
        }
    }
}

impl VariableOrigin {
    pub fn as_solvable(&self) -> Option<SolvableId> {
        match self {
            VariableOrigin::Solvable(solvable_id) => Some(*solvable_id),
            _ => None,
        }
    }

    pub fn as_solvable_or_root(&self) -> Option<SolvableOrRootId> {
        match self {
            VariableOrigin::Solvable(solvable_id) => Some((*solvable_id).into()),
            VariableOrigin::Root => Some(SolvableOrRootId::root()),
            _ => None,
        }
    }
}

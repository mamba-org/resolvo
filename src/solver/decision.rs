use crate::internal::id::{ClauseId, InternalSolvableId};

/// Represents an assignment to a variable
#[derive(Copy, Clone, Eq, PartialEq)]
pub(crate) struct Decision {
    pub(crate) solvable_id: InternalSolvableId,
    pub(crate) value: bool,
    pub(crate) derived_from: ClauseId,
}

impl Decision {
    pub(crate) fn new(solvable: InternalSolvableId, value: bool, derived_from: ClauseId) -> Self {
        Self {
            solvable_id: solvable,
            value,
            derived_from,
        }
    }
}

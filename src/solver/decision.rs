use crate::internal::id::{ClauseId, VarId};

/// Represents an assignment to a variable
#[derive(Copy, Clone, Eq, PartialEq)]
pub(crate) struct Decision {
    pub(crate) var_id: VarId,
    pub(crate) value: bool,
    pub(crate) derived_from: ClauseId,
}

impl Decision {
    pub(crate) fn new(variable: VarId, value: bool, derived_from: ClauseId) -> Self {
        Self {
            var_id: variable,
            value,
            derived_from,
        }
    }
}

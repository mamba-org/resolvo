use crate::internal::id::ConditionId;
use crate::{Requirement, VersionSetId};

/// A [`ConditionalRequirement`] is a requirement that is only enforced when a
/// certain condition holds.
#[derive(Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConditionalRequirement {
    /// The requirement is enforced only when the condition evaluates to true.
    pub condition: Option<ConditionId>,

    /// A requirement on another package.
    pub requirement: Requirement,
}

/// A condition defines a boolean expression that evaluates to true or false
/// based on whether one or more other requirements are true or false.
#[derive(Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Condition {
    /// Defines a combination of conditions using logical operators.
    Binary(LogicalOperator, ConditionId, ConditionId),

    /// The condition is only true if the requirement is true.
    Requirement(VersionSetId),
}

/// A [`LogicalOperator`] defines how multiple conditions are compared to each other.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum LogicalOperator {
    /// The condition is true if both operands are true.
    And,

    /// The condition is true if either operand is true.
    Or,
}

// Constructs a `ConditionalRequirement` from a `Requirement` without a
// condition.
impl From<Requirement> for ConditionalRequirement {
    fn from(value: Requirement) -> Self {
        Self {
            condition: None,
            requirement: value,
        }
    }
}

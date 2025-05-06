use std::num::NonZero;

use crate::{
    Condition, ConditionId, Interner, LogicalOperator, VersionSetId,
    internal::{
        arena::{Arena, ArenaId},
        small_vec::SmallVec,
    },
};

/// An identifier that describes a group of version sets that are combined using
/// AND logical operators.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct DisjunctionId(NonZero<u32>);

impl ArenaId for DisjunctionId {
    fn from_usize(x: usize) -> Self {
        // Safe because we are guaranteed that the id is non-zero by adding 1.
        DisjunctionId(unsafe { NonZero::new_unchecked((x + 1) as u32) })
    }

    fn to_usize(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

pub struct Disjunction {
    /// The top-level condition to which this disjunction belongs.
    pub condition: ConditionId,
}

/// Converts from a boolean expression tree as described by `condition` to a
/// boolean formula in disjunctive normal form (DNF). Each inner Vec represents
/// a conjunction (AND group) and the outer Vec represents the disjunction (OR
/// group).
pub fn convert_conditions_to_dnf<I: Interner>(
    condition: ConditionId,
    interner: &I,
) -> Vec<Vec<VersionSetId>> {
    match interner.resolve_condition(condition) {
        Condition::Requirement(version_set) => vec![vec![version_set]],
        Condition::Binary(LogicalOperator::Or, lhs, rhs) => {
            let mut left_dnf = convert_conditions_to_dnf(lhs, interner);
            let mut right_dnf = convert_conditions_to_dnf(rhs, interner);
            left_dnf.append(&mut right_dnf);
            left_dnf
        }
        Condition::Binary(LogicalOperator::And, lhs, rhs) => {
            let left_dnf = convert_conditions_to_dnf(lhs, interner);
            let right_dnf = convert_conditions_to_dnf(rhs, interner);

            // Distribute AND over OR
            let mut result = Vec::new();
            for l in &left_dnf {
                for r in &right_dnf {
                    let mut merged = l.clone();
                    merged.extend(r.clone());
                    result.push(merged);
                }
            }
            result
        }
    }
}

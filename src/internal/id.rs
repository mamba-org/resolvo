use std::{
    fmt::{Display, Formatter},
    num::NonZeroU32,
};

use crate::{internal::arena::ArenaId, Interner};

/// The id associated to a package name
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct NameId(pub u32);

impl ArenaId for NameId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a generic string
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct StringId(pub u32);

impl ArenaId for StringId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a VersionSet.
#[repr(transparent)]
#[derive(Clone, Default, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct VersionSetId(pub u32);

impl ArenaId for VersionSetId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a union (logical OR) of two or more version sets.
#[repr(transparent)]
#[derive(Clone, Default, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct VersionSetUnionId(pub u32);

impl ArenaId for VersionSetUnionId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to a solvable
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct SolvableId(pub u32);

/// Internally used id for solvables that can also represent the root.
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub(crate) struct InternalSolvableId(pub u32);
const INTERNAL_SOLVABLE_ROOT: u32 = 0;

impl InternalSolvableId {
    /// Returns the id of the "root" solvable. This is a special solvable that
    /// is always present when solving.
    pub const fn root() -> Self {
        Self(0)
    }

    /// Returns if this id represents the root solvable.
    pub const fn is_root(self) -> bool {
        self.0 == 0
    }

    pub const fn as_solvable(self) -> Option<SolvableId> {
        match self.0 {
            INTERNAL_SOLVABLE_ROOT => None,
            x => Some(SolvableId(x - 1)),
        }
    }

    pub fn display<I: Interner>(self, interner: &I) -> impl std::fmt::Display + '_ {
        DisplayInternalSolvable { interner, id: self }
    }
}

pub struct DisplayInternalSolvable<'i, I: Interner> {
    interner: &'i I,
    id: InternalSolvableId,
}

impl<'i, I: Interner> Display for DisplayInternalSolvable<'i, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.id.0 {
            INTERNAL_SOLVABLE_ROOT => write!(f, "<root>"),
            x => {
                write!(f, "{}", self.interner.display_solvable(SolvableId(x - 1)))
            }
        }
    }
}

impl From<SolvableId> for InternalSolvableId {
    fn from(value: SolvableId) -> Self {
        Self(value.0 + 1)
    }
}

impl TryFrom<InternalSolvableId> for SolvableId {
    type Error = ();

    fn try_from(value: InternalSolvableId) -> Result<Self, Self::Error> {
        value.as_solvable().ok_or(())
    }
}

impl ArenaId for InternalSolvableId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl ArenaId for SolvableId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl From<SolvableId> for u32 {
    fn from(value: SolvableId) -> Self {
        value.0
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq, Debug, Hash)]
pub(crate) struct ClauseId(NonZeroU32);

impl ClauseId {
    /// There is a guarentee that ClauseId(1) will always be
    /// "Clause::InstallRoot". This assumption is verified by the solver.
    pub(crate) fn install_root() -> Self {
        Self(unsafe { NonZeroU32::new_unchecked(1) })
    }
}

impl ArenaId for ClauseId {
    fn from_usize(x: usize) -> Self {
        // SAFETY: Safe because we always add 1 to the index
        Self(unsafe { NonZeroU32::new_unchecked((x + 1).try_into().expect("clause id too big")) })
    }

    fn to_usize(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct LearntClauseId(u32);

impl ArenaId for LearntClauseId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to an arena of Candidates
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CandidatesId(u32);

impl ArenaId for CandidatesId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to an arena of PackageRequirements
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DependenciesId(u32);

impl ArenaId for DependenciesId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clause_id_size() {
        // Verify that the size of a ClauseId is the same as an Option<ClauseId>.
        assert_eq!(
            std::mem::size_of::<ClauseId>(),
            std::mem::size_of::<Option<ClauseId>>()
        );
    }
}

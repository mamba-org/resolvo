use std::fmt::{Display, Formatter};
use std::str::FromStr;

/// This is `Pack` which is a unique version and name in our bespoke packaging
/// system
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
pub struct Pack {
    pub version: u32,
    pub unknown_deps: bool,
    pub cancel_during_get_dependencies: bool,
}

impl Pack {
    pub fn new(version: u32) -> Pack {
        Pack {
            version,
            unknown_deps: false,
            cancel_during_get_dependencies: false,
        }
    }

    pub fn with_unknown_deps(mut self) -> Pack {
        self.unknown_deps = true;
        self
    }

    pub fn cancel_during_get_dependencies(mut self) -> Pack {
        self.cancel_during_get_dependencies = true;
        self
    }
}

impl From<u32> for Pack {
    fn from(value: u32) -> Self {
        Pack::new(value)
    }
}

impl From<i32> for Pack {
    fn from(value: i32) -> Self {
        Pack::new(value as u32)
    }
}

impl Display for Pack {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.version)
    }
}

impl FromStr for Pack {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        u32::from_str(s).map(Pack::new)
    }
}

//! Defines several helper functions and structs that make it easier to
//! implement a custom dependency provider.

mod pool;
mod range;

pub use pool::{PackageName, Pool, VersionSet};
pub use range::Range;

use super::Pack;
use chumsky::{Parser, error};
use version_ranges::Ranges;

/// We can use this to see if a `Pack` is contained in a range of package
/// versions or a `Spec`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Spec {
    pub name: String,
    pub versions: Ranges<Pack>,
}

impl Spec {
    pub fn new(name: String, versions: Ranges<Pack>) -> Self {
        Self { name, versions }
    }
}

impl Spec {
    pub fn from_str(s: &str) -> Result<Self, Vec<error::Simple<'_, char>>> {
        super::parser::spec().parse(s).into_result()
    }
}

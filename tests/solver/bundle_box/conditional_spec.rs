use super::Spec;
use chumsky::{Parser, error};
use resolvo::LogicalOperator;

#[derive(Debug, Clone)]
pub struct ConditionalSpec {
    pub condition: Option<SpecCondition>,
    pub specs: Vec<Spec>,
}

impl ConditionalSpec {
    pub fn from_str(s: &str) -> Result<Self, Vec<error::Simple<'_, char>>> {
        super::parser::conditional_spec().parse(s).into_result()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum SpecCondition {
    Binary(LogicalOperator, Box<[SpecCondition; 2]>),
    Requirement(Spec),
}

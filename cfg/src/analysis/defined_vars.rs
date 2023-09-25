use bril_rs::Function;

use super::*;
use std::collections::HashSet;

/// Variables that *may* be defined at a given program point
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct DefinedVars {
    vars: HashSet<String>,
}

impl DefinedVars {
    /// Returns true if the variable is defined
    #[must_use]
    pub fn is_defined(&self, var: &str) -> bool {
        self.vars.contains(var)
    }

    #[must_use]
    pub fn top(f: &Function) -> Self {
        Self {
            vars: f.args.iter().map(|a| a.name.clone()).collect(),
        }
    }
}

impl Fact for DefinedVars {
    fn meet(&self, b: &Self) -> Self {
        let mut vars = self.vars.clone();
        for v in &b.vars {
            vars.insert(v.clone());
        }
        Self { vars }
    }

    fn transfer(&self, instr: &(u64, Instruction), _: usize) -> Vec<Self>
    where
        Self: std::marker::Sized,
    {
        let instr = &instr.1;
        let mut res = self.clone();
        if let Some(dest) = instr.get_dest() {
            res.vars.insert(dest);
        }
        vec![res]
    }

    type Dir = Forwards;
}

impl std::fmt::Display for DefinedVars {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // sort for deterministic output
        let mut vars = self.vars.iter().collect::<Vec<_>>();
        vars.sort();
        write!(f, "[")?;
        for (i, v) in vars.iter().enumerate() {
            write!(f, "{v}")?;
            if i != self.vars.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "]")
    }
}

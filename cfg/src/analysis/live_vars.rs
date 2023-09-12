use super::*;
use std::collections::HashSet;

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct LiveVars {
    vars: HashSet<String>,
}

impl Fact for LiveVars {
    fn top() -> Self {
        Self {
            vars: HashSet::new(),
        }
    }

    fn meet(&self, b: &Self) -> Self {
        let mut vars = self.vars.clone();
        for v in &b.vars {
            vars.insert(v.clone());
        }
        Self { vars }
    }

    fn transfer(&self, instr: &Instruction) -> Vec<Self>
    where
        Self: std::marker::Sized,
    {
        let mut res = self.clone();
        if let Some(dest) = instr.get_dest() {
            res.vars.remove(&dest);
        }
        if let Some(args) = instr.get_args() {
            for a in args {
                res.vars.insert(a.to_string());
            }
        }
        vec![res]
    }
}

impl std::fmt::Display for LiveVars {
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

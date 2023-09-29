use std::collections::{HashMap, HashSet};

use bril_rs::{Function, Instruction, ValueOps};

use super::{Fact, Forwards};

/// Dataflow analysis for available copies
/// Top: set of all copies
/// Meet: intersection of copies
///
/// We do this with an inverted lattice where the top element is the empty set
/// and the meet is union of `not_copies`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AvailableCopies {
    /// Map from variable to variable it was copied from
    copies: HashMap<String, String>,
    /// Set of variables that are not copies
    /// The top element is represented by an empty set of not copies
    not_copies: HashSet<String>,
}

impl AvailableCopies {
    #[must_use]
    pub fn top(f: &Function) -> Self {
        Self {
            copies: HashMap::new(),
            not_copies: f.args.iter().map(|a| a.name.clone()).collect(),
        }
    }

    /// If `var` is a copy, returns the variable it was copied from
    /// Otherwise returns None
    #[must_use]
    pub fn get_copy(&self, var: &str) -> Option<&String> {
        self.copies.get(var)
    }
}

impl std::fmt::Display for AvailableCopies {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (idx, (k, v)) in self.copies.iter().enumerate() {
            write!(f, "{k} = {v}")?;
            if idx < self.copies.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "]")
    }
}

impl Fact for AvailableCopies {
    fn meet(&self, b: &Self) -> Self {
        let mut copies = self.copies.clone();
        let mut not_copies = self.not_copies.clone();
        for (var, copy) in &b.copies {
            if let Some(c) = self.copies.get(var) {
                if c != copy {
                    // meeting of two copies, but they are copies
                    // of different variables, so this is not a copy
                    copies.remove(var);
                    not_copies.insert(var.clone());
                }
            } else {
                copies.insert(var.clone(), copy.clone());
            }
        }
        not_copies = not_copies.union(&b.not_copies).cloned().collect();
        for nc in &not_copies {
            copies.remove(nc);
        }
        Self { copies, not_copies }
    }

    fn transfer(
        &self,
        instr: &(u64, bril_rs::Instruction),
        _: usize,
    ) -> Vec<Self>
    where
        Self: std::marker::Sized,
    {
        if let Instruction::Value {
            op: ValueOps::Id,
            dest,
            args,
            ..
        } = &instr.1
        {
            let mut not_copies = self.not_copies.clone();
            not_copies.remove(dest);
            let mut copies = self.copies.clone();
            copies.insert(dest.clone(), args[0].clone());
            vec![Self { copies, not_copies }]
        } else if let Some(dest) = instr.1.get_dest() {
            let mut not_copies = self.not_copies.clone();
            not_copies.insert(dest.clone());
            let mut copies = self.copies.clone();
            copies.remove(&dest);
            vec![Self { copies, not_copies }]
        } else {
            vec![self.clone()]
        }
    }

    type Dir = Forwards;
}

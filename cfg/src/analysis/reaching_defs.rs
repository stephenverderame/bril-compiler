use super::*;
use std::collections::{HashMap, HashSet};

#[derive(PartialEq, Clone, Debug)]
pub struct ReachingDefs {
    /// map from instruction pointer/id to (block id, instruction)
    instrs: HashMap<u64, (usize, Instruction)>,
    /// the instructions that define a variable
    defs: HashMap<String, HashSet<u64>>,
}

impl ReachingDefs {
    /// Returns the blocks that define the given variable
    #[must_use]
    pub fn blocks_defining(&self, arg: &str) -> Vec<usize> {
        self.defs
            .get(arg)
            .map(|v| v.iter().map(|i| self.instrs[i].0).collect())
            .unwrap_or_default()
    }

    /// Returns the instructions that define the given variable
    #[must_use]
    pub fn instrs_defining(&self, var: &str) -> Vec<u64> {
        self.defs
            .get(var)
            .map(|v| v.iter().copied().collect())
            .unwrap_or_default()
    }

    /// Returns the variables that are defined
    #[must_use]
    pub fn definied_vars(&self) -> HashSet<String> {
        self.defs.keys().cloned().collect()
    }

    /// Returns true if `instr` is a definition that reaches this program point
    #[must_use]
    pub fn reached_by(&self, instr_id: u64) -> bool {
        self.instrs.contains_key(&instr_id)
    }
}

impl Fact for ReachingDefs {
    fn top() -> Self {
        Self {
            defs: HashMap::new(),
            instrs: HashMap::new(),
        }
    }

    fn meet(&self, b: &Self) -> Self {
        let mut defs = self.defs.clone();
        let mut instrs = self.instrs.clone();
        instrs.extend(b.instrs.iter().map(|(k, v)| (*k, v.clone())));
        for (k, v) in &b.defs {
            defs.entry(k.to_string()).or_default().extend(v);
        }
        Self { instrs, defs }
    }

    fn transfer(&self, instr: &(u64, Instruction), block_id: usize) -> Vec<Self>
    where
        Self: std::marker::Sized,
    {
        let (instr_id, instr) = instr;
        let mut res = self.clone();
        if let Instruction::Value { dest, .. } = instr {
            if let Some(existing_defs) = res.defs.get(dest) {
                res.instrs.retain(|ptr, _| !existing_defs.contains(ptr));
            }
            let mut hs = HashSet::new();
            hs.insert(*instr_id);
            res.defs.insert(dest.to_string(), hs);
            res.instrs.insert(*instr_id, (block_id, instr.clone()));
        }
        vec![res]
    }
}

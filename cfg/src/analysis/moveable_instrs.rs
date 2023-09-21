use std::{
    collections::{HashSet, VecDeque},
    rc::Rc,
};

use bril_rs::Instruction;

use crate::{Cfg, CfgNode};

use super::{
    live_vars::LiveVars, loops::NaturalLoop, reaching_defs::ReachingDefs,
    AnalysisResult, Fact,
};

/// An ordered instruction is an instruction with an order
/// that keeps track of the order in which it was marked as
/// loop invariant
///
/// Lower orders are more recent (later)
// #[derive(Clone, Debug)]
// struct OrderedInstruction {
//     instr: Instruction,
//     id: *const Instruction,
//     order: i64,
// }
// impl PartialOrd for OrderedInstruction {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         Some(self.order.cmp(&other.order))
//     }
// }
// impl Ord for OrderedInstruction {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         self.order.cmp(&other.order)
//     }
// }

// impl PartialEq for OrderedInstruction {
//     fn eq(&self, other: &Self) -> bool {
//         self.id == other.id
//     }
// }

// impl Eq for OrderedInstruction {}

/// Set of variables which are not loop invariant
#[derive(Clone)]
pub struct MoveableInstrs {
    not_invariant: HashSet<u64>,
    reaching_defs: Rc<AnalysisResult<ReachingDefs>>,
    lp: Rc<NaturalLoop>,
    /// The set of variables that are live out of the loop
    live_exit_vars: Rc<HashSet<String>>,
}

impl PartialEq for MoveableInstrs {
    fn eq(&self, other: &Self) -> bool {
        self.not_invariant == other.not_invariant
    }
}

impl MoveableInstrs {
    /// Constructs a new top element of the data flow
    #[must_use]
    pub fn new(
        reaching_defs: Rc<AnalysisResult<ReachingDefs>>,
        lp: Rc<NaturalLoop>,
        live_vars: &AnalysisResult<LiveVars>,
    ) -> Self {
        let mut live_exit_vars = HashSet::new();
        for n in &lp.exits {
            for f in &live_vars.block_out_facts[n] {
                live_exit_vars.extend(f.vars.iter().cloned());
            }
        }
        Self {
            not_invariant: HashSet::new(),
            reaching_defs,
            lp,
            live_exit_vars: Rc::new(live_exit_vars),
        }
    }

    #[must_use]
    pub fn is_loop_invariant(&self, instr: &(u64, Instruction)) -> bool {
        instr.1.is_pure() && !self.not_invariant.contains(&instr.0)
    }
}

impl Fact for MoveableInstrs {
    fn top() -> Self {
        unimplemented!()
    }

    fn meet(&self, b: &Self) -> Self {
        let not_inv = self.not_invariant.union(&b.not_invariant);
        Self {
            not_invariant: not_inv.copied().collect(),
            reaching_defs: self.reaching_defs.clone(),
            lp: self.lp.clone(),
            live_exit_vars: self.live_exit_vars.clone(),
        }
    }

    fn transfer(&self, instr: &(u64, Instruction), _: usize) -> Vec<Self>
    where
        Self: std::marker::Sized,
    {
        let (instr_id, instr) = instr;
        let mut not_inv = self.not_invariant.clone();
        if let Some(args) = instr.get_args() {
            for arg in args {
                if self.reaching_defs.in_facts[instr_id]
                    .instrs_defining(arg)
                    .iter()
                    .any(|instr| self.not_invariant.contains(instr))
                    || self.live_exit_vars.contains(arg)
                    || self.reaching_defs.in_facts[instr_id]
                        .blocks_defining(arg)
                        .iter()
                        .any(|block| self.lp.nodes.contains(block))
                        && self.reaching_defs.in_facts[instr_id]
                            .blocks_defining(arg)
                            .len()
                            > 1
                {
                    // argument uses a varying instruction OR
                    // argument is live-in to a loop exit node OR
                    // argument is defined in the loop and has more than one definition
                    not_inv.insert(*instr_id);
                }
            }
        }
        vec![Self {
            not_invariant: not_inv,
            reaching_defs: self.reaching_defs.clone(),
            lp: self.lp.clone(),
            live_exit_vars: self.live_exit_vars.clone(),
        }]
    }
}

/// Returns the set of loop invariant instructions
/// in the given loop
/// # Arguments
/// * `cfg` - The CFG
/// * `nodes` - The nodes in the loop
/// * `header` - The header of the loop
/// * `res` - The analysis result
/// # Returns
/// * The set of loop invariant instructions
/// # Panics
/// Empty block output facts
#[must_use]
pub fn get_loop_invariant_instrs(
    cfg: &Cfg,
    nodes: &[usize],
    header: usize,
    res: &AnalysisResult<MoveableInstrs>,
) -> Vec<(u64, Instruction)> {
    let mut queue = VecDeque::new();
    queue.push_back(header);
    let mut visited = HashSet::new();
    let mut instrs = Vec::new();
    while let Some(n) = queue.pop_front() {
        if visited.contains(&n) {
            continue;
        }
        visited.insert(n);
        if let CfgNode::Block(block) = &cfg.blocks[&n] {
            for instr in &block.instrs {
                assert!(res.block_out_facts[&n].len() == 1);
                if res.block_out_facts[&n][0].is_loop_invariant(instr) {
                    instrs.push(instr.clone());
                }
            }
        }
        for succ in cfg.adj_lst[&n].nodes().iter().filter(|x| nodes.contains(x))
        {
            queue.push_back(*succ);
        }
    }
    instrs
}

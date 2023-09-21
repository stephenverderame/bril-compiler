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

/// Set of variables which are not loop invariant
#[derive(Clone)]
pub struct MoveableInstrs {
    not_invariant: HashSet<u64>,
    not_inv_vars: HashSet<String>,
    reaching_defs: Rc<AnalysisResult<ReachingDefs>>,
    f_args: Rc<Vec<String>>,
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
        f_args: Rc<Vec<String>>,
    ) -> Self {
        let mut live_exit_vars = HashSet::new();
        for n in &lp.exits {
            for f in &live_vars.block_out_facts[n] {
                live_exit_vars.extend(f.vars.iter().cloned());
            }
        }
        Self {
            not_invariant: HashSet::new(),
            not_inv_vars: HashSet::new(),
            reaching_defs,
            lp,
            live_exit_vars: Rc::new(live_exit_vars),
            f_args,
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
        let not_inv_vars = self.not_inv_vars.union(&b.not_inv_vars);
        Self {
            not_invariant: not_inv.copied().collect(),
            not_inv_vars: not_inv_vars.map(String::to_string).collect(),
            reaching_defs: self.reaching_defs.clone(),
            lp: self.lp.clone(),
            live_exit_vars: self.live_exit_vars.clone(),
            f_args: self.f_args.clone(),
        }
    }

    fn transfer(&self, instr: &(u64, Instruction), _: usize) -> Vec<Self>
    where
        Self: std::marker::Sized,
    {
        let (instr_id, instr) = instr;
        let mut not_inv = self.not_invariant.clone();
        let mut not_inv_vars = self.not_inv_vars.clone();
        if let Some(dest) = instr.get_dest() {
            if self.live_exit_vars.contains(&dest)
                || self.not_inv_vars.contains(&dest)
            {
                // variable is live-in to an exit node
                not_inv.insert(*instr_id);
            }
        }
        if let Some(args) = instr.get_args() {
            for arg in args {
                // max definitions of an argument
                // 0 if the argument is a function argument (bc we imagine function
                // arguments to be defined at the beginning of the function), so
                // if there is 1 other definition, that would be two separate blocks
                let arg_max_defs = usize::from(!self.f_args.contains(arg));
                if self.reaching_defs.in_facts[instr_id]
                    .instrs_defining(arg)
                    .iter()
                    .any(|instr| self.not_invariant.contains(instr))
                    || self.reaching_defs.in_facts[instr_id]
                        .blocks_defining(arg)
                        .iter()
                        .any(|block| self.lp.nodes.contains(block))
                        && self.reaching_defs.in_facts[instr_id]
                            .blocks_defining(arg)
                            .len()
                            > arg_max_defs
                    || self.not_inv_vars.contains(arg)
                {
                    // argument uses a varying instruction OR
                    // argument is defined in the loop and has more than one definition
                    not_inv.insert(*instr_id);
                    instr.get_dest().map(|d| not_inv_vars.insert(d));
                }
            }
        }
        vec![Self {
            not_invariant: not_inv,
            not_inv_vars,
            reaching_defs: self.reaching_defs.clone(),
            lp: self.lp.clone(),
            live_exit_vars: self.live_exit_vars.clone(),
            f_args: self.f_args.clone(),
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

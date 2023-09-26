#![warn(clippy::pedantic, clippy::nursery)]
#![allow(clippy::enum_glob_use)]
use std::collections::HashMap;

use bril_rs::{Code, Function, Instruction, ValueOps};
use cfg::CfgNode;
use common_cli::{cli_args, compiler_pass};

#[cli_args]
struct ExtraArgs {
    /// Instead of asserting that the code is in SSA form, if this flag is
    /// present, we will assert that the code does not contain a phi node.
    #[arg(long, short, default_value_t = false)]
    not: bool,
}

#[compiler_pass(all_labels)]
fn is_ssa(cfg: Cfg, a: &CLIArgs, _: &Function) -> Cfg {
    let mut def_count = HashMap::new();
    for blk in cfg.blocks.values() {
        if let CfgNode::Block(blk) = blk {
            for (_, instr) in &blk.instrs {
                if let Instruction::Value {
                    op: ValueOps::Phi, ..
                } = instr
                {
                    assert!(!a.not, "Phi node found in code");
                }
                if let Some(dest) = instr.get_dest() {
                    *def_count.entry(dest).or_insert(0) += 1;
                }
            }
        }
    }
    let max_defs = def_count
        .iter()
        .max_by(|(_, a), (_, b)| a.cmp(b))
        .map(|(_, v)| *v)
        .unwrap_or_default();
    assert!(a.not || max_defs <= 1, "Code is not in SSA form");
    cfg
}

const fn is_ssa_post(instrs: Vec<Code>) -> Vec<Code> {
    instrs
}

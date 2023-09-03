use bril_rs::{EffectOps, Instruction};
use cfg::{BasicBlock, CfgNode};
use common_cli::{cli_args, compiler_pass};
use std::collections::HashMap;

#[cli_args]
struct ExtraArgs {}

/// Invokes local dead code elimination on the cfg
#[compiler_pass(true)]
fn ldce(mut cfg: Cfg, _args: &CLIArgs) -> Cfg {
    for block in &mut cfg.blocks.iter_mut().filter_map(|(_, node)| match node {
        CfgNode::Block(block) => Some(block),
        _ => None,
    }) {
        block_dce(block);
    }
    cfg
}

/// Returns the set of arguments to the instruction
/// or None if the instruction is a constant
fn instr_args(instr: &Instruction) -> Option<&[String]> {
    match instr {
        Instruction::Value { args, .. } => Some(args),
        Instruction::Effect { args, .. } => Some(args),
        Instruction::Constant { .. } => None,
    }
}

/// Returns the destination of the instruction
/// or None if the instruction is an effect
fn instr_dest(instr: &Instruction) -> Option<&String> {
    match instr {
        Instruction::Value { dest, .. } => Some(dest),
        Instruction::Effect { .. } => None,
        Instruction::Constant { dest, .. } => Some(dest),
    }
}

/// Conservative dead code elimination on a basic block
/// Any variables not overwritten are assumed to be read in another block
fn block_dce(block: &mut BasicBlock) {
    // we can ignore the terminator since it is only a jump or branch
    assert!(
        block.terminator.is_none()
            || matches!(
                block.terminator,
                Some(Instruction::Effect {
                    op: EffectOps::Jump | EffectOps::Branch | EffectOps::Return,
                    ..
                })
            )
    );
    loop {
        let mut can_remove = vec![];
        // need to use pointer equality since there could be duplicate instructions
        let mut potentially_unused: HashMap<&String, *const Instruction> =
            HashMap::new();
        for instr in block.instrs.iter() {
            if let Some(args) = instr_args(instr) {
                potentially_unused.retain(|k, _| !args.contains(*k));
            }
            if let Some(dest) = instr_dest(instr) {
                if let Some(instr) = potentially_unused.get(dest) {
                    can_remove.push(*instr);
                }
                potentially_unused.insert(dest, instr);
            }
        }
        let old_size = block.instrs.len();
        block
            .instrs
            .retain(|instr| !can_remove.contains(&(instr as *const _)));
        if block.instrs.len() == old_size || old_size == 0 {
            break;
        }
    }
}

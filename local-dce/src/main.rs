use bril_rs::{Code, EffectOps, Instruction};
use cfg::{BasicBlock, CfgNode};
use common_cli::{cli_args, compiler_pass};
use std::collections::{HashMap, HashSet};

#[cli_args]
struct ExtraArgs {}

/// Invokes local dead code elimination on the cfg
#[compiler_pass(true)]
fn dce(mut cfg: Cfg, _args: &CLIArgs, _f: &bril_rs::Function) -> Cfg {
    for block in &mut cfg.blocks.iter_mut().filter_map(|(_, node)| match node {
        CfgNode::Block(block) => Some(block),
        _ => None,
    }) {
        block_dce(block);
    }
    cfg.clean()
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
                Some((
                    _,
                    Instruction::Effect {
                        op: EffectOps::Jump
                            | EffectOps::Branch
                            | EffectOps::Return,
                        ..
                    }
                ))
            )
    );
    loop {
        let mut can_remove = vec![];
        // need to use pointer equality since there could be duplicate instructions
        let mut potentially_unused: HashMap<&String, u64> = HashMap::new();
        for (instr_id, instr) in block.instrs.iter() {
            if let Some(args) = instr_args(instr) {
                potentially_unused.retain(|k, _| !args.contains(*k));
            }
            if let Some(dest) = instr_dest(instr) {
                if let Some(instr) = potentially_unused.get(dest) {
                    can_remove.push(*instr);
                }
                potentially_unused.insert(dest, *instr_id);
            }
        }
        let old_size = block.instrs.len();
        block
            .instrs
            .retain(|(instr_id, _)| !can_remove.contains(instr_id));
        if block.instrs.len() == old_size || old_size == 0 {
            break;
        }
    }
}

/// Performs trvial global dead code elimination
fn dce_post(mut instrs: Vec<Code>) -> Vec<Code> {
    loop {
        let mut can_remove = HashSet::new();
        let mut used_args = HashSet::new();
        // identify all args
        for i in &instrs {
            if let Code::Instruction(instr) = i {
                if let Some(args) = instr_args(instr) {
                    used_args.extend(args.iter().cloned());
                }
            }
        }
        // identify destinations that aren't used (non-effects)
        for i in &instrs {
            if let Code::Instruction(
                instr @ (Instruction::Constant { .. }
                | Instruction::Value { .. }),
            ) = i
            {
                if let Some(dest) = instr_dest(instr) {
                    if !used_args.contains(dest) {
                        can_remove.insert(instr as *const _);
                    }
                }
            }
        }
        // remove instructions that compute results that aren't used
        instrs.retain(|k| match k {
            Code::Instruction(k) => !can_remove.contains(&(k as *const _)),
            _ => true,
        });
        if can_remove.is_empty() {
            break;
        }
    }
    instrs
}

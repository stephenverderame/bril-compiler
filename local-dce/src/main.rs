use atty::Stream;
use bril_rs::{
    load_program, load_program_from_read, EffectOps, Instruction, Program,
};
use cfg::{BasicBlock, Cfg, CfgNode};
use clap::{command, Parser};
use std::{collections::HashMap, fs::File};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct CLIArgs {
    /// The optional file to read from, if not specified a bril program
    /// is expected on stdin
    #[arg(short, long)]
    file: Option<String>,
}

fn main() {
    let args = CLIArgs::parse();
    if args.file.is_some() {
        let prog =
            load_program_from_read(File::open(args.file.unwrap()).unwrap());
        println!("{}", serde_json::to_string(&transform_prog(prog)).unwrap());
    } else if !atty::is(Stream::Stdin) {
        println!(
            "{}",
            serde_json::to_string(&transform_prog(load_program())).unwrap()
        );
    } else {
        eprintln!("Either specify a file or pipe in a bril program.");
        eprintln!("See `local-dce --help` for more information.");
    }
}

fn transform_prog(mut prog: Program) -> Program {
    for f in &mut prog.functions {
        let cfg = Cfg::from(f, false);
        let new_body = ldce(cfg).to_src();
        f.instrs = new_body;
    }
    prog
}

/// Invokes local dead code elimination on the cfg
fn ldce(mut cfg: Cfg) -> Cfg {
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

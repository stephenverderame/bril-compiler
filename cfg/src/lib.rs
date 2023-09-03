#![warn(clippy::pedantic, clippy::nursery)]
#![allow(clippy::wildcard_imports)]
use std::collections::{BTreeMap, HashMap, VecDeque};

use bril_rs::{Code, EffectOps, Function, Instruction, ValueOps};

mod cfg2src;
mod src2cfg;
pub use cfg2src::to_src;

/// Id of the start node in the CFG
pub const CFG_START_ID: usize = 0;
/// Id of the end node in the CFG
pub const CFG_END_ID: usize = CFG_START_ID + 1;

/// A basic block in the CFG
#[derive(Clone, Debug, PartialEq, Default)]
pub struct BasicBlock {
    pub instrs: Vec<Instruction>,
    pub terminator: Option<Instruction>,
}

impl BasicBlock {
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.instrs.is_empty() && self.terminator.is_none()
    }
}

/// A node in the CFG
#[derive(Clone, Debug, PartialEq)]
pub enum CfgNode {
    Start,
    Block(BasicBlock),
    End,
}

impl CfgNode {
    /// Returns true if the node is a branch node
    #[must_use]
    pub const fn is_branch(&self) -> bool {
        matches!(
            self,
            Self::Block(BasicBlock {
                terminator: Some(Instruction::Effect {
                    op: EffectOps::Branch,
                    ..
                }),
                ..
            })
        )
    }
}

/// The destination of an edge in the CFG
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgEdgeTo {
    Next(usize),
    Branch { true_node: usize, false_node: usize },
    Terminal,
}

/// The control flow graph of a function
#[derive(Clone, Debug)]
pub struct Cfg {
    pub blocks: BTreeMap<usize, CfgNode>,
    pub adj_lst: HashMap<usize, CfgEdgeTo>,
    pub labels: HashMap<usize, Vec<String>>,
}

/// Returns true if the instruction is a terminator instruction
/// # Arguments
/// * `instr` - The instruction
/// * `single_mode` - If true, then a basic block is a single instruction
const fn is_terminator(instr: &Instruction) -> bool {
    matches!(
        instr,
        Instruction::Effect {
            op: EffectOps::Jump | EffectOps::Branch | EffectOps::Return,
            ..
        }
    )
}

impl CfgNode {
    /// Format a value instruction
    #[allow(clippy::too_many_lines)]
    fn fmt_val(
        args: &[String],
        dest: &str,
        funcs: &[String],
        labels: &[String],
        op: ValueOps,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let empty = String::new();
        let arg_0 = args.get(0).unwrap();
        let arg_1 = args.get(1).unwrap_or(&empty);
        let func_0 = funcs.get(0).unwrap_or(&empty);
        match op {
            ValueOps::Add | ValueOps::Fadd | ValueOps::PtrAdd => {
                write!(f, "{dest} := {arg_0} + {arg_1}")
            }
            ValueOps::Sub | ValueOps::Fsub => {
                write!(f, "{dest} := {arg_0} - {arg_1}")
            }
            ValueOps::Mul | ValueOps::Fmul => {
                write!(f, "{dest} := {arg_0} * {arg_1}")
            }
            ValueOps::Div | ValueOps::Fdiv => {
                write!(f, "{dest} := {arg_0} / {arg_1}")
            }
            ValueOps::Eq | ValueOps::Feq | ValueOps::Ceq => {
                write!(f, "{dest} := {arg_0} == {arg_1}")
            }
            ValueOps::Lt | ValueOps::Flt | ValueOps::Clt => {
                write!(f, "{dest} := {arg_0} < {arg_1}")
            }
            ValueOps::Gt | ValueOps::Fgt | ValueOps::Cgt => {
                write!(f, "{dest} := {arg_0} > {arg_1}")
            }
            ValueOps::Le | ValueOps::Fle | ValueOps::Cle => {
                write!(f, "{dest} := {arg_0} <= {arg_1}")
            }
            ValueOps::Ge | ValueOps::Fge | ValueOps::Cge => {
                write!(f, "{dest} := {arg_0} >= {arg_1}")
            }
            ValueOps::Not => write!(f, "{dest} := !{arg_0}"),
            ValueOps::And => write!(f, "{dest} := {arg_0} && {arg_1}"),
            ValueOps::Or => write!(f, "{dest} := {arg_0} || {arg_1}"),
            ValueOps::Id => write!(f, "{dest} := {arg_0}"),
            ValueOps::Call => {
                Self::fmt_call(Some(dest.to_string()), func_0, args, f)
            }
            ValueOps::Phi => {
                writeln!(f, "{dest} := phi {{")?;
                for (lbl, arg) in labels.iter().zip(args.iter()) {
                    writeln!(f, "   | {lbl} => {arg},")?;
                }
                write!(f, "}}")
            }
            ValueOps::Char2int => write!(f, "{dest} := (int){arg_0}"),
            ValueOps::Int2char => write!(f, "{dest} := (char){arg_0}"),
            ValueOps::Alloc => write!(f, "{dest} := alloc {arg_0}"),
            ValueOps::Load => write!(f, "{dest} := *{arg_0}"),
        }
    }

    /// Format a call instruction
    /// Can be used for both value and effect calls
    /// If `dest` is `None`, then this is an effect call
    fn fmt_call(
        dest: Option<String>,
        func: &str,
        args: &[String],
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        if let Some(dest) = dest {
            write!(f, "{dest} := ")?;
        }
        write!(f, "{func}(")?;
        for (idx, a) in args.iter().enumerate() {
            write!(f, "{a}")?;
            if idx < args.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }

    /// Format an effect instruction
    fn fmt_effect(
        op: EffectOps,
        funcs: &[String],
        args: &[String],
        labels: &[String],
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match op {
            EffectOps::Jump => Ok(()),
            EffectOps::Branch => {
                let cond = args.get(0).unwrap();
                write!(f, "if {cond}")
            }
            EffectOps::Call => {
                Self::fmt_call(None, funcs.get(0).unwrap(), args, f)
            }
            EffectOps::Return => {
                write!(f, "return")?;
                if let Some(arg) = args.get(0) {
                    write!(f, " {arg}")?;
                }
                write!(f, "")
            }
            EffectOps::Print => write!(f, "print {}", args.get(0).unwrap()),
            EffectOps::Nop => panic!("Nop should not be in CFG"),
            EffectOps::Store => {
                write!(
                    f,
                    "*{} := {}",
                    args.get(0).unwrap(),
                    args.get(1).unwrap()
                )
            }
            EffectOps::Free => write!(f, "free {}", args.get(0).unwrap()),
            EffectOps::Speculate => write!(f, "speculate"),
            EffectOps::Commit => write!(f, "commit"),
            EffectOps::Guard => write!(
                f,
                "guard {} {}",
                args.get(0).unwrap(),
                labels.get(0).unwrap()
            ),
        }
    }

    fn fmt_instruction(
        instr: &Instruction,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match instr {
            Instruction::Constant { dest, value, .. } => {
                write!(f, "{dest} := {value}")
            }
            Instruction::Value {
                args,
                dest,
                op,
                funcs,
                labels,
                ..
            } => Self::fmt_val(args, dest, funcs, labels, *op, f),
            Instruction::Effect {
                args,
                funcs,
                labels,
                op,
                ..
            } => Self::fmt_effect(*op, funcs, args, labels, f),
        }
    }
}

impl std::fmt::Display for CfgNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Start => write!(f, "START"),
            Self::End => write!(f, "END"),
            Self::Block(BasicBlock { instrs, terminator }) => {
                for (idx, instr) in instrs.iter().chain(terminator).enumerate()
                {
                    Self::fmt_instruction(instr, f)?;
                    if idx < instrs.len() {
                        write!(f, "\\n")?;
                    }
                }
                Ok(())
            }
        }
    }
}

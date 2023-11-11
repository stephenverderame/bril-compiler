#![warn(clippy::pedantic, clippy::nursery)]
#![allow(clippy::wildcard_imports)]
use std::collections::{BTreeMap, HashMap, VecDeque};

use bril_rs::{Code, EffectOps, Function, Instruction, ValueOps};

pub mod analysis;
mod cfg2src;
mod src2cfg;
pub use cfg2src::to_src;

/// Id of the start node in the CFG
pub const CFG_START_ID: usize = 0;
/// Id of the end node in the CFG
pub const CFG_END_ID: usize = CFG_START_ID + 1;
/// Id of the first free block in the CFG
pub const CFG_FIRST_FREE_ID: usize = CFG_END_ID + 1;

/// A basic block in the CFG
#[derive(Clone, Debug, PartialEq, Default)]
pub struct BasicBlock {
    pub instrs: Vec<(u64, Instruction)>,
    pub terminator: Option<(u64, Instruction)>,
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
                terminator: Some((
                    _,
                    Instruction::Effect {
                        op: EffectOps::Branch,
                        ..
                    }
                )),
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

impl CfgEdgeTo {
    /// Returns the nodes that this edge points to
    #[must_use]
    pub fn nodes(&self) -> Vec<usize> {
        match self {
            Self::Next(n) => vec![*n],
            Self::Branch {
                true_node: t,
                false_node: f,
            } => vec![*t, *f],
            Self::Terminal => vec![],
        }
    }
}

/// The control flow graph of a function
#[derive(Clone, Debug)]
pub struct Cfg {
    pub blocks: BTreeMap<usize, CfgNode>,
    pub adj_lst: HashMap<usize, CfgEdgeTo>,
    pub block_labels: HashMap<usize, Vec<String>>,
    pub labels: HashMap<String, usize>,
    /// The next instruction id to be used
    pub next_instr_id: u64,
}

impl Cfg {
    /// Returns a map from block id to the block's predecessors.
    pub fn preds(&self) -> HashMap<usize, Vec<usize>> {
        let mut preds = HashMap::new();
        for (id, edge_to) in &self.adj_lst {
            match edge_to {
                CfgEdgeTo::Branch {
                    true_node,
                    false_node,
                } => {
                    preds.entry(*true_node).or_insert_with(Vec::new).push(*id);
                    preds.entry(*false_node).or_insert_with(Vec::new).push(*id);
                }
                CfgEdgeTo::Next(next_node) => {
                    preds.entry(*next_node).or_insert_with(Vec::new).push(*id);
                }
                CfgEdgeTo::Terminal => {}
            }
        }
        preds
    }
}

impl Default for Cfg {
    fn default() -> Self {
        let mut blocks = BTreeMap::new();
        blocks.insert(CFG_START_ID, CfgNode::Start);
        blocks.insert(CFG_END_ID, CfgNode::End);
        let mut adj_lst = HashMap::new();
        adj_lst.insert(CFG_START_ID, CfgEdgeTo::Next(CFG_END_ID));
        adj_lst.insert(CFG_END_ID, CfgEdgeTo::Terminal);
        Self {
            blocks,
            adj_lst,
            block_labels: HashMap::new(),
            labels: HashMap::new(),
            next_instr_id: 0,
        }
    }
}

/// Returns true if the instruction is a terminator instruction
/// # Arguments
/// * `instr` - The instruction
#[must_use]
pub const fn is_terminator(instr: &Instruction) -> bool {
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
        let arg_0 = args.get(0).unwrap_or(&empty);
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
                write!(f, "{dest} := phi {{\\n")?;
                for (lbl, arg) in labels.iter().zip(args.iter()) {
                    write!(f, "   | {lbl} => {arg},\\n")?;
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
            EffectOps::Print => {
                let mut args_str = String::new();
                for (idx, arg) in args.iter().enumerate() {
                    args_str.push_str(arg);
                    if idx < args.len() - 1 {
                        args_str.push_str(", ");
                    }
                }
                write!(f, "print {args_str}")
            }
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
                let hide_terminator = matches!(
                    terminator,
                    Some((
                        _,
                        Instruction::Effect {
                            op: EffectOps::Jump,
                            ..
                        }
                    ))
                );
                let total_size =
                    instrs.len() + terminator.as_ref().map_or(0, |_| 1);
                for (idx, (_, instr)) in
                    instrs.iter().chain(terminator).enumerate()
                {
                    Self::fmt_instruction(instr, f)?;
                    if idx < total_size.max(2) - 2 && hide_terminator
                        || !hide_terminator && idx < total_size - 1
                    {
                        write!(f, "\\n")?;
                    }
                }
                Ok(())
            }
        }
    }
}

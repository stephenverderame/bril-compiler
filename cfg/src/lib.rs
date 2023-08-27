#![warn(clippy::pedantic, clippy::nursery)]
use std::collections::{BTreeMap, HashMap, VecDeque};

use bril_rs::{Code, EffectOps, Function, Instruction, ValueOps};

/// Id of the start node in the CFG
pub const CFG_START_ID: usize = 0;
/// Id of the end node in the CFG
pub const CFG_END_ID: usize = CFG_START_ID + 1;

/// A node in the CFG
#[derive(Clone, Debug, PartialEq)]
pub enum CfgNode {
    Start,
    Instr(Instruction),
    End,
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
}

impl Cfg {
    #[must_use]
    pub fn from(f: &Function) -> Self {
        // map from label to node id
        let mut labels = HashMap::new();
        // the labels we encounter before the next instruction
        let mut active_labels = Vec::new();
        // map from node id to instruction
        let mut blocks = BTreeMap::new();
        // node id counter
        let mut i = CFG_END_ID + 1;
        blocks.insert(CFG_START_ID, CfgNode::Start);
        blocks.insert(CFG_END_ID, CfgNode::End);
        for code in &f.instrs {
            match code {
                Code::Label { label, .. } => {
                    active_labels.push(label.clone());
                }
                Code::Instruction(instr) => {
                    blocks.insert(i, CfgNode::Instr(instr.clone()));
                    for lbl in &active_labels {
                        labels.insert(lbl.clone(), i);
                    }
                    i += 1;
                    active_labels.clear();
                }
            }
        }
        // any labels that are still active are at the end of the function
        for lbl in &active_labels {
            labels.insert(lbl.clone(), CFG_END_ID);
        }
        Self::gen_cfg_from_lbls_and_blocks(&labels, blocks)
    }

    /// Generate a CFG from a map from label to node id and a map from node id to instruction
    ///
    /// # Arguments
    /// * `labels_map` - A map from label to node id
    /// * `blocks` - A map from node id to instruction
    /// * `labels_rev` - A map from node id to labels
    #[must_use]
    fn gen_cfg_from_lbls_and_blocks(
        labels_map: &HashMap<String, usize>,
        blocks: BTreeMap<usize, CfgNode>,
    ) -> Self {
        // cfg adjacency list
        let mut adj_lst = HashMap::new();
        // the last id of an instruction included in the CFG
        // this is to keep track of a sequential stream of instructions
        let mut last_id = Some(CFG_START_ID);
        adj_lst.insert(CFG_END_ID, CfgEdgeTo::Terminal);
        for (id, instr) in blocks.iter().filter_map(|(id, instr)| match instr {
            CfgNode::Instr(instr) => Some((id, instr)),
            CfgNode::Start | CfgNode::End => None,
        }) {
            if !Self::handle_effects(
                instr,
                *id,
                labels_map,
                &mut adj_lst,
                &mut last_id,
            ) {
                Self::add_edge(&mut adj_lst, &last_id, *id);
                last_id = Some(*id);
            }
        }
        // make the transition from the last sequntial instruction to be
        // to the end node.
        if let Some(last_id) = last_id {
            adj_lst.insert(last_id, CfgEdgeTo::Next(CFG_END_ID));
        }
        Self::splice_out_goto_and_make_self(adj_lst, blocks, labels_map)
    }

    /// Splice out jumps from the `adj_list`, constructs and CFG with
    /// the resulant `adj_list` and blocks, and then cleans the CFG
    /// which removes unreachable nodes
    fn splice_out_goto_and_make_self(
        mut adj_lst: HashMap<usize, CfgEdgeTo>,
        blocks: BTreeMap<usize, CfgNode>,
        labels_map: &HashMap<String, usize>,
    ) -> Self {
        for (self_id, edge) in &mut adj_lst {
            match edge {
                CfgEdgeTo::Branch {
                    true_node,
                    false_node,
                } => {
                    *true_node = Self::get_next_real_node(
                        &blocks, *true_node, labels_map, None,
                    )
                    .unwrap_or(*self_id);
                    *false_node = Self::get_next_real_node(
                        &blocks,
                        *false_node,
                        labels_map,
                        None,
                    )
                    .unwrap_or(*self_id);
                }
                CfgEdgeTo::Next(next) => {
                    *next = Self::get_next_real_node(
                        &blocks, *next, labels_map, None,
                    )
                    .unwrap_or(*self_id);
                }
                CfgEdgeTo::Terminal => {}
            }
        }
        Self { blocks, adj_lst }.clean()
    }

    /// If `id` is a jump instruction, return the id of the next real (non-jump)
    /// node by following the chain of jumps.
    /// Otherwise, return `id`
    ///
    /// If `id` is the starting id, then we have an infinite loop
    /// and we return `None`
    /// # Arguments
    /// * `blocks` - A map from node id to instruction
    /// * `id` - The id of the jump instruction
    /// * `labels_map` - A map from label to node id
    /// * `starting_id` - The id of the first jump instruction in the chain or
    /// `None` if this is the first jump instruction in the chain
    ///
    /// # Returns
    /// * `Some(id)` where `id` is the id of the next real node or `None` if
    ///  there is an infinite loop
    fn get_next_real_node(
        blocks: &BTreeMap<usize, CfgNode>,
        id: usize,
        labels_map: &HashMap<String, usize>,
        starting_id: Option<usize>,
    ) -> Option<usize> {
        if starting_id.map_or(false, |first_id| id == first_id) {
            // infinite loop
            return None;
        }
        if let Some(CfgNode::Instr(Instruction::Effect {
            op: EffectOps::Jump,
            labels,
            ..
        })) = blocks.get(&id)
        {
            Self::get_next_real_node(
                blocks,
                *labels_map.get(labels.get(0).unwrap()).unwrap(),
                labels_map,
                starting_id.or(Some(id)),
            )
        } else {
            Some(id)
        }
    }

    /// Remove unreachable nodes from the CFG
    /// Unreachable nodes occur when we splice out jumps when
    /// constructing the cfg. Prior to cleaning, the
    /// adjacency list may contain such jumps that have
    /// been spliced out. Cleaning will remove these jumps
    fn clean(mut self) -> Self {
        let mut keeps = vec![];
        let mut q = VecDeque::new();
        q.push_back(CFG_START_ID);
        while !q.is_empty() {
            let reachable = q.pop_front().unwrap();
            if keeps.contains(&reachable) {
                continue;
            }
            keeps.push(reachable);
            match self.adj_lst.get(&reachable) {
                Some(CfgEdgeTo::Next(next)) => {
                    if !keeps.contains(next) {
                        q.push_back(*next);
                    }
                }
                Some(CfgEdgeTo::Branch {
                    true_node,
                    false_node,
                }) => {
                    if !keeps.contains(true_node) {
                        q.push_back(*true_node);
                    }
                    if !keeps.contains(false_node) {
                        q.push_back(*false_node);
                    }
                }
                Some(CfgEdgeTo::Terminal) | None => {}
            }
        }
        self.adj_lst.retain(|id, _| keeps.contains(id));
        self.blocks.retain(|id, _| self.adj_lst.contains_key(id));
        self
    }

    /// Add an edge from each node in `froms` to `to`.
    fn add_edge(
        adj_lst: &mut HashMap<usize, CfgEdgeTo>,
        froms: &Option<usize>,
        to: usize,
    ) {
        if let Some(from) = froms {
            adj_lst.insert(*from, CfgEdgeTo::Next(to));
        }
    }

    /// Handles adding effect instructions to the CFG
    /// Adds `Effect { op, labels, }` to the CFG `adj_lst`
    /// Updates `last_id` accordingly
    ///
    /// # Arguments
    /// * `instr` - The effect instruction
    /// * `id` - The id of the effect instruction
    /// * `labels_map` - A map from label to node id
    /// * `adj_lst` - The adjacency list of the CFG
    /// * `last_id` - The last id of an instruction included in the CFG
    ///
    /// # Returns
    /// * `true` if the instruction was an effect instruction and was handled
    fn handle_effects(
        instr: &Instruction,
        id: usize,
        labels_map: &HashMap<String, usize>,
        adj_lst: &mut HashMap<usize, CfgEdgeTo>,
        last_id: &mut Option<usize>,
    ) -> bool {
        if let Instruction::Effect {
            op,
            args: _,
            labels,
            ..
        } = instr
        {
            match op {
                EffectOps::Branch => {
                    assert_eq!(labels.len(), 2);
                    let true_node = *labels_map.get(&labels[0]).unwrap();
                    let false_node = *labels_map.get(&labels[1]).unwrap();
                    adj_lst.insert(
                        id,
                        CfgEdgeTo::Branch {
                            true_node,
                            false_node,
                        },
                    );
                    Self::add_edge(adj_lst, last_id, id);
                    *last_id = None;
                    true
                }
                EffectOps::Jump => {
                    let next = *labels_map.get(&labels[0]).unwrap();
                    Self::add_edge(adj_lst, last_id, id);
                    Self::add_edge(adj_lst, &Some(id), next);
                    *last_id = None;
                    true
                }
                EffectOps::Return => {
                    Self::add_edge(adj_lst, last_id, id);
                    Self::add_edge(adj_lst, &Some(id), CFG_END_ID);
                    *last_id = None;
                    true
                }
                // do not change last_id
                EffectOps::Nop => true,
                _ => false,
            }
        } else {
            false
        }
    }
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
            EffectOps::Jump => write!(f, "goto {}", labels.get(0).unwrap()),
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
}

impl std::fmt::Display for CfgNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Start => write!(f, "START"),
            Self::End => write!(f, "END"),
            Self::Instr(instr) => match instr {
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
            },
        }
    }
}

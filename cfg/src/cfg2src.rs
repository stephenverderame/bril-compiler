use super::*;
use std::collections::{HashSet, VecDeque};

/// The base name (non-unique) of a block label.
const BLOCK_LABEL_BASE: &str = "block.";

/// Returns a map from block id to the block's predecessors.
fn cfg_preds(cfg: &Cfg) -> HashMap<usize, Vec<usize>> {
    let mut preds = HashMap::new();
    for (id, edge_to) in &cfg.adj_lst {
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

/// Returns true if current block needs a label.
fn need_label(
    cfg: &Cfg,
    last_block_id: usize,
    preds: &HashMap<usize, Vec<usize>>,
    cur_block_id: usize,
) -> bool {
    // more than one predecessor OR
    // the only predecessor is not the last block OR
    // a predecessor is a branch
    preds.get(&cur_block_id).map_or(0, Vec::len) > 1
        || preds
            .get(&cur_block_id)
            .map_or(false, |v| !v.is_empty() && v[0] != last_block_id)
        || preds.get(&cur_block_id).map_or(false, |v| {
            v.iter()
                .any(|e| cfg.blocks.get(e).map_or(false, CfgNode::is_branch))
        })
}

/// Fixes jumps on blocks that branch and
/// sets the next block to be visited by pushing
/// it to the stack.
fn fix_branch_jumps_and_set_next(
    true_node: usize,
    false_node: usize,
    block: &BasicBlock,
    mut src: Vec<Code>,
    mut stack: VecDeque<usize>,
) -> (Vec<Code>, VecDeque<usize>) {
    if let Instruction::Effect {
        args: terminator_args,
        funcs: terminator_funcs,
        pos: terminator_pos,
        ..
    } = block.terminator.as_ref().unwrap()
    {
        src.push(Code::Instruction(Instruction::Effect {
            op: EffectOps::Branch,
            args: terminator_args.clone(),
            funcs: terminator_funcs.clone(),
            labels: vec![
                format!("{BLOCK_LABEL_BASE}{true_node}"),
                format!("{BLOCK_LABEL_BASE}{false_node}"),
            ],
            pos: terminator_pos.clone(),
        }));
    } else {
        panic!("Unexpected terminator of branching block");
    }
    stack.push_front(true_node);
    stack.push_back(false_node);
    (src, stack)
}

/// Fixes jumps on blocks that transition to the end block.
/// # Arguments
/// * `block` - The block transitioning to the end
/// * `src` - The source code
/// * `last_block` - True if the block is the last block
/// # Returns
/// The source code with `block` instructions added
fn fix_goto_epilogue(
    block: &BasicBlock,
    mut src: Vec<Code>,
    last_block: bool,
) -> Vec<Code> {
    // jump or return
    match block.terminator.as_ref() {
        Some(
            instr @ Instruction::Effect {
                op: EffectOps::Return,
                ..
            },
        ) => src.push(Code::Instruction(instr.clone())),
        Some(Instruction::Effect {
            op: EffectOps::Jump,
            ..
        }) => {
            // jump to end
            src.push(Code::Instruction(Instruction::Effect {
                op: EffectOps::Jump,
                args: vec![],
                funcs: vec![],
                labels: vec![format!("{BLOCK_LABEL_BASE}{CFG_END_ID}")],
                pos: None,
            }));
        }
        None if last_block => {}
        None => src.push(Code::Instruction(Instruction::Effect {
            op: EffectOps::Jump,
            args: vec![],
            funcs: vec![],
            labels: vec![format!("{BLOCK_LABEL_BASE}{CFG_END_ID}")],
            pos: None,
        })),
        t => panic!(
            "Unexpected terminator {t:?} of block transitioning to the end"
        ),
    }
    src
}

/// Fixes jumps on blocks that don't fall through to the next block.
/// # Arguments
/// * `cfg` - The CFG
/// * `block_id` - The block id
/// * `block` - The block to add to the source code
/// * `src` - The source code
/// * `visited` - The visited blocks
/// * `stack` - The stack of blocks to visit
/// * `last_block` - True if the block is the last block
/// # Returns
/// A tuple of the source code with `block` instructions added and
/// the stack of blocks to visit next
fn fix_jumps_and_set_next(
    cfg: &Cfg,
    block_id: usize,
    block: &BasicBlock,
    mut src: Vec<Code>,
    visited: &HashSet<usize>,
    mut stack: VecDeque<usize>,
    last_block: bool,
) -> (Vec<Code>, VecDeque<usize>) {
    match cfg.adj_lst.get(&block_id).unwrap() {
        CfgEdgeTo::Branch {
            true_node,
            false_node,
        } => {
            (src, stack) = fix_branch_jumps_and_set_next(
                *true_node,
                *false_node,
                block,
                src,
                stack,
            );
        }
        CfgEdgeTo::Next(next_node) if *next_node == CFG_END_ID => {
            src = fix_goto_epilogue(block, src, last_block);
        }
        CfgEdgeTo::Next(next_node) if visited.contains(next_node) => {
            src.push(Code::Instruction(Instruction::Effect {
                op: EffectOps::Jump,
                args: vec![],
                funcs: vec![],
                labels: vec![format!("{BLOCK_LABEL_BASE}{}", next_node)],
                pos: None,
            }));
        }
        CfgEdgeTo::Next(next_node) => {
            // fallthrough
            stack.push_front(*next_node);
        }
        CfgEdgeTo::Terminal => {
            if let Some(t) = block.terminator.as_ref() {
                src.push(Code::Instruction(t.clone()));
            }
        }
    }
    (src, stack)
}

/// Converts a CFG to a vector of Bril instructions and labels.
///
/// # Panics
/// Panics if the CFG is malformed.
#[must_use]
pub fn to_src(cfg: &Cfg) -> Vec<Code> {
    let mut src = Vec::new();
    let mut visited = HashSet::new();
    visited.insert(CFG_START_ID);
    visited.insert(CFG_END_ID);
    let mut stack = VecDeque::new();
    let preds = cfg_preds(cfg);
    if let Some(CfgEdgeTo::Next(nxt)) = cfg.adj_lst.get(&CFG_START_ID) {
        stack.push_front(*nxt);
    } else {
        panic!("Unexpected transition from start node");
    }
    let mut last_block_id = CFG_START_ID;
    while let Some(id) = stack.pop_front() {
        if visited.contains(&id) {
            continue;
        }
        visited.insert(id);
        let last_node = visited.len() == cfg.blocks.len();
        if let Some(CfgNode::Block(block)) = cfg.blocks.get(&id) {
            if need_label(cfg, last_block_id, &preds, id) {
                // we relabel everything to avoid potential conflicts
                src.push(Code::Label {
                    pos: None,
                    label: format!("{BLOCK_LABEL_BASE}{id}"),
                });
            }
            for instr in &block.instrs {
                src.push(Code::Instruction(instr.clone()));
            }
            (src, stack) = fix_jumps_and_set_next(
                cfg, id, block, src, &visited, stack, last_node,
            );
            last_block_id = id;
        }
    }
    if need_label(cfg, last_block_id, &preds, CFG_END_ID) {
        src.push(Code::Label {
            pos: None,
            label: format!("{BLOCK_LABEL_BASE}{CFG_END_ID}"),
        });
    }
    src
}

impl Cfg {
    #[must_use]
    pub fn to_src(&self) -> Vec<Code> {
        to_src(self)
    }
}

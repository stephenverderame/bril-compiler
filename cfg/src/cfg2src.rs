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
fn fix_branch_jumps(
    true_node: usize,
    false_node: usize,
    block: &BasicBlock,
    mut src: Vec<Code>,
) -> Vec<Code> {
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
    src
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
        _ if last_block => {}
        Some(Instruction::Effect {
            op: EffectOps::Jump,
            pos,
            ..
        }) => {
            // jump to end
            src.push(Code::Instruction(Instruction::Effect {
                op: EffectOps::Jump,
                args: vec![],
                funcs: vec![],
                labels: vec![format!("{BLOCK_LABEL_BASE}{CFG_END_ID}")],
                pos: pos.clone(),
            }));
        }
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
/// * `next_code_block` - The next basic block that will come after this one
///     in the source code
/// # Returns
/// A tuple of the source code with `block` instructions added and
/// the stack of blocks to visit next
fn fix_jumps(
    cfg: &Cfg,
    block_id: usize,
    block: &BasicBlock,
    mut src: Vec<Code>,
    visited: &HashSet<usize>,
    next_code_block: Option<&usize>,
) -> Vec<Code> {
    let terminator_pos =
        block.terminator.as_ref().and_then(|p| p.get_pos().or(None));
    match cfg.adj_lst.get(&block_id).unwrap() {
        CfgEdgeTo::Branch {
            true_node,
            false_node,
        } => {
            src = fix_branch_jumps(*true_node, *false_node, block, src);
        }
        CfgEdgeTo::Next(next_node) if *next_node == CFG_END_ID => {
            let is_last_block = next_code_block.is_none()
                || matches!(next_code_block, Some(&CFG_END_ID));
            src = fix_goto_epilogue(block, src, is_last_block);
        }
        CfgEdgeTo::Next(next_node) if visited.contains(next_node) => {
            src.push(Code::Instruction(Instruction::Effect {
                op: EffectOps::Jump,
                args: vec![],
                funcs: vec![],
                labels: vec![format!("{BLOCK_LABEL_BASE}{next_node}")],
                pos: terminator_pos,
            }));
        }
        CfgEdgeTo::Next(next_node) => {
            if next_code_block == Some(next_node) {
                // fallthrough to next block
            } else {
                src.push(Code::Instruction(Instruction::Effect {
                    op: EffectOps::Jump,
                    args: vec![],
                    funcs: vec![],
                    labels: vec![format!("{BLOCK_LABEL_BASE}{next_node}")],
                    pos: terminator_pos,
                }));
            }
        }
        CfgEdgeTo::Terminal => {
            if let Some(t) = block.terminator.as_ref() {
                src.push(Code::Instruction(t.clone()));
            }
        }
    }
    src
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
    let mut order = order_blocks(cfg, &cfg_preds(cfg));
    let preds = cfg_preds(cfg);
    let mut last_block_id = CFG_START_ID;
    while let Some(id) = order.pop_front() {
        assert!(!visited.contains(&id));
        visited.insert(id);
        let next_code_block = order.front();
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
            src = fix_jumps(cfg, id, block, src, &visited, next_code_block);
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

/// Returns false if the node has unmarked predecessors.
fn all_marked_preds(
    node: usize,
    preds: &HashMap<usize, Vec<usize>>,
    unmarked: &HashSet<usize>,
) -> bool {
    preds
        .get(&node)
        .map_or(true, |v| v.iter().all(|e| !unmarked.contains(e)))
}

/// Returns an order of blocks to output via Greedy Reordering
/// The order starts with the first real (non-start) node and ends with the end node
fn order_blocks(
    cfg: &Cfg,
    preds: &HashMap<usize, Vec<usize>>,
) -> VecDeque<usize> {
    let mut order = VecDeque::new();
    let mut unmarked = cfg.blocks.keys().copied().collect::<HashSet<_>>();
    unmarked.remove(&CFG_START_ID);
    unmarked.remove(&CFG_END_ID);
    let mut n = CFG_START_ID;
    while !unmarked.is_empty() {
        unmarked.remove(&n);
        order.push_back(n);
        // set default next node
        match cfg.adj_lst.get(&n) {
            // maximal unmarked trace
            Some(CfgEdgeTo::Next(next_node))
                if unmarked.contains(next_node) && *next_node != CFG_END_ID =>
            {
                n = *next_node;
            }
            _ => {
                n = *unmarked.iter().next().unwrap_or(&n);
            }
        }

        if !all_marked_preds(n, preds, &unmarked) {
            // heuristic: pick the first unmarked node with no unmarked predecessors
            // if there are no such nodes, prefer the next node in the current trace
            // or pick the first node in the unmarked set if the current trace is ending
            // if there are multiple such nodes, pick the next one in the current trace
            for u in &unmarked {
                // first iteration: always set the next node in case
                // there are no nodes with no unmarked predecessors
                if all_marked_preds(*u, preds, &unmarked) {
                    n = *u;
                    break;
                }
            }
        }
    }
    // remove START_ID
    assert!(order.pop_front() == Some(CFG_START_ID));
    order.push_back(CFG_END_ID);
    order
}

impl Cfg {
    #[must_use]
    pub fn to_src(&self) -> Vec<Code> {
        to_src(self)
    }
}

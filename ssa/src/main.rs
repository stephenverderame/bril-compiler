use std::collections::HashMap;

use bril_rs::{Code, Function, Instruction, Type};
use cfg::{
    analysis::{
        analyze,
        defined_vars::{self, DefinedVars},
        dominators,
        live_vars::{self, LiveVars},
        AnalysisResult,
    },
    CfgNode, CFG_START_ID,
};
use common_cli::{cli_args, compiler_pass};

#[cli_args]
struct ExtraArgs {
    /// Pass this flag to transform out of SSA form instead of transforming
    /// into SSA form
    #[arg(long, short, default_value_t = false)]
    out: bool,
}

/// Invokes global dead code elimination on the cfg
#[compiler_pass(true)]
fn ssa(cfg: Cfg, args: &CLIArgs, f: &Function) -> Cfg {
    (if args.out { cfg } else { add_phi_nodes(cfg, f) }).clean()
}

/// Inserts a phi node as the first instruction of a block if one with the
/// same destination does not already exist. If one does exist, it will be
/// replaced with the new phi node
/// # Arguments
/// * `cfg` - The cfg
/// * `block` - The block to insert the phi node into
/// * `phi` - The phi node to insert
/// # Returns
/// * The cfg with the phi node inserted
fn add_phi_to_block(mut cfg: Cfg, block: usize, phi: Instruction) -> Cfg {
    if let Some(CfgNode::Block(block)) = cfg.blocks.get_mut(&block) {
        if let Some(existing_pos) = block
            .instrs
            .iter()
            .position(|(_, instr)| instr.get_dest() == phi.get_dest())
        {
            block.instrs[existing_pos] = (cfg.last_instr_id, phi);
        } else {
            block.instrs.insert(0, (cfg.last_instr_id, phi));
        }
        cfg.last_instr_id += 1;
    }
    cfg
}

/// Gets the labels of predecessor blocks of `frontier_blk` that have `var` live out
/// # Arguments
/// * `preds` - Inverse cfg adjacency list
/// * `live_vars` - The live variables analysis result
/// * `cfg` - The cfg
/// * `var` - The defined variable that an SSA node is being constructed for
/// * `frontier_blk` - The block in the dominance frontier of the definition that
/// we are constructing an phi node for
/// # Returns
/// * The labels of the predecessor blocks that have `var` live out (and therefore)
/// need to be merged in a phi node
fn get_ssa_pred_labels(
    preds: &HashMap<usize, Vec<usize>>,
    live_vars: &AnalysisResult<LiveVars>,
    defined_vars: &AnalysisResult<DefinedVars>,
    cfg: &Cfg,
    var: &str,
    frontier_blk: usize,
) -> Vec<String> {
    preds[&frontier_blk]
        .iter()
        .filter_map(|blk| {
            if let CfgNode::Block(block) = &cfg.blocks[blk] {
                if live_vars.block_facts(block, *blk).0.is_live_out(var)
                    && defined_vars
                        .block_facts(block, *blk)
                        .1
                        .iter()
                        .any(|x| x.is_defined(var))
                {
                    Some(format!("block.{blk}"))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect()
}

/// Adds phi nodes to all blocks in the dominance frontier of a definition
/// The phi nodes will be inserted as the first instructions of the block
/// and will use the same variable names as the definition
/// # Arguments
/// * `cfg` - The cfg
/// * `f` - The function
/// # Returns
/// * The cfg with phi nodes inserted
fn add_phi_nodes(mut cfg: Cfg, f: &Function) -> Cfg {
    let mut vars = find_vars(&cfg, f);
    let dom_tree = dominators::compute_dominators(&cfg);
    let mut added_phi_nodes: HashMap<(String, usize), Vec<String>> =
        HashMap::new();
    let preds = cfg.preds();
    let mut changed = true;
    let empty_preds = vec![];
    let live_vars = analyze(&cfg, &live_vars::LiveVars::top(), None);
    let defined_vars = analyze(&cfg, &defined_vars::DefinedVars::top(f), None);
    while changed {
        changed = false;
        for (var, def_blocks) in vars.iter_mut() {
            for (def_blk, def_type) in def_blocks {
                for frontier_blk in dom_tree.dom_frontier(*def_blk, &cfg) {
                    let existing_phi = added_phi_nodes
                        .get(&(var.to_string(), frontier_blk))
                        .unwrap_or(&empty_preds);
                    let pred_labels = get_ssa_pred_labels(
                        &preds,
                        &live_vars,
                        &defined_vars,
                        &cfg,
                        var,
                        frontier_blk,
                    );
                    if existing_phi != &pred_labels {
                        added_phi_nodes.insert(
                            (var.to_string(), frontier_blk),
                            pred_labels.clone(),
                        );
                        let phi = bril_rs::Instruction::Value {
                            op: bril_rs::ValueOps::Phi,
                            args: pred_labels
                                .iter()
                                .map(|_| var.to_string())
                                .collect(),
                            dest: var.to_string(),
                            funcs: vec![],
                            labels: pred_labels,
                            pos: None,
                            op_type: def_type.clone(),
                        };
                        cfg = add_phi_to_block(cfg, frontier_blk, phi);
                        changed = true;
                    }
                }
            }
        }
    }
    cfg
}

/// Gets a map from variable name to the blocks that define it
/// Function arguments are considered to be defined in the ghost start block
/// # Arguments
/// * `cfg` - The cfg
/// * `f` - The function
/// # Returns
/// * A map from variable name to a vector of tuples of (block id, type)
fn find_vars(
    cfg: &Cfg,
    f: &bril_rs::Function,
) -> HashMap<String, Vec<(usize, Type)>> {
    let mut vars: HashMap<_, _> = f
        .args
        .iter()
        .map(|x| (x.name.clone(), vec![(CFG_START_ID, x.arg_type.clone())]))
        .collect();
    for (blk_id, block) in &cfg.blocks {
        if let CfgNode::Block(block) = block {
            for (_, instr) in block.instrs.iter() {
                if let (Some(dest), Some(typ)) =
                    (instr.get_dest(), instr.get_type())
                {
                    vars.entry(dest).or_default().push((*blk_id, typ));
                }
            }
        }
    }
    vars
}

fn ssa_post(instrs: Vec<Code>) -> Vec<Code> {
    instrs
}

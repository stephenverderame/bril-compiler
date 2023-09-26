use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use bril_rs::{Code, Instruction};
use cfg::{
    analysis::{
        analyze, dominators,
        live_vars::LiveVars,
        loops::{self, NaturalLoop},
        moveable_instrs::{get_loop_invariant_instrs, MoveableInstrs},
        reaching_defs::ReachingDefs,
        AnalysisResult,
    },
    BasicBlock, CfgEdgeTo, CfgNode,
};
use common_cli::{cli_args, compiler_pass};
use rand::Rng;

#[cli_args]
struct ExtraArgs {}

/// Invokes global dead code elimination on the cfg
#[compiler_pass]
fn licm(mut cfg: Cfg, _args: &CLIArgs, f: &bril_rs::Function) -> Cfg {
    let domtree = dominators::compute_dominators(&cfg);
    let loops = loops::find_natural_loops(&cfg, &domtree);
    let args =
        Rc::new(f.args.iter().map(|a| a.name.clone()).collect::<Vec<_>>());
    for lp in loops {
        cfg = licm_loop(cfg, Rc::new(lp), args.clone());
    }
    cfg
}

/// Performs LICM on a loop
/// # Arguments
/// * `cfg` - The cfg
/// * `lp` - The loop
/// * `live_vars` - The live variables analysis result
/// * `reaching_defs` - The reaching definitions analysis result
/// # Returns
/// The cfg with the loop invariant code moved out of the loop
fn licm_loop(
    mut cfg: Cfg,
    lp: Rc<NaturalLoop>,
    f_args: Rc<Vec<String>>,
) -> Cfg {
    #![allow(clippy::manual_retain)]
    // reanalyze bc the CFG is changing
    let reaching_defs =
        Rc::new(analyze(&cfg, &ReachingDefs::top(&f_args), None));
    let live_vars = analyze(&cfg, &LiveVars::top(), None);
    let moveable_instrs = loop_invariant_instrs(
        &cfg,
        reaching_defs.clone(),
        lp.clone(),
        &live_vars,
    );
    let moveable_instrs =
        hoist_and_rewrite(moveable_instrs, &mut cfg, &reaching_defs, &lp);
    let _ = insert_preheader(&mut cfg, lp.header, moveable_instrs.clone(), &lp);
    for n in &lp.nodes {
        if let Some(CfgNode::Block(block)) = &mut cfg.blocks.get_mut(n) {
            block.instrs = block
                .instrs
                .iter()
                .filter(|i| !moveable_instrs.iter().any(|instr| instr.0 == i.0))
                .cloned()
                .collect();
        }
    }
    for nest in &lp.nested {
        cfg = licm_loop(cfg, Rc::new(nest.clone()), f_args.clone());
    }
    cfg
}

/// Returns a set of all variables whose definition reaches any part of
/// the loop or any loop exit node
fn used_variables(
    reaching_defs: &AnalysisResult<ReachingDefs>,
    lp: &NaturalLoop,
    cfg: &Cfg,
) -> HashSet<String> {
    let mut vars = HashSet::new();
    for n in lp.nodes.iter().chain(lp.exits.iter()) {
        if let CfgNode::Block(block) = &cfg.blocks[n] {
            let (in_facts, _) = reaching_defs.block_facts(block, *n);
            vars = vars.union(&in_facts.definied_vars()).cloned().collect();
        }
    }
    vars
}

/// Creates a new, unused variable name
fn generate_fresh_var(
    used_vars: &mut HashSet<String>,
    base_name: &str,
) -> String {
    let mut i = 0;
    let stem: String = rand::thread_rng()
        .sample_iter(&rand::distributions::Alphanumeric)
        .take(3)
        .map(char::from)
        .collect();
    let mut name = format!("{base_name}_{stem}");
    while used_vars.contains(&name) {
        name = format!("{base_name}_{stem}{i}");
        i += 1;
    }
    used_vars.insert(name.clone());
    name
}

/// Rewrites all usages of the given moveable instructions to use different
/// variable names which prevent errors due to moving the instructions
fn hoist_and_rewrite(
    mut moveable_instrs: Vec<(u64, Instruction)>,
    cfg: &mut Cfg,
    reaching_defs: &AnalysisResult<ReachingDefs>,
    lp: &NaturalLoop,
) -> Vec<(u64, Instruction)> {
    let mut updated_vars = HashMap::new();
    let mut used_vars = used_variables(reaching_defs, lp, cfg);
    for i in 0..moveable_instrs.len() {
        if let Some(old) = moveable_instrs[i].1.get_dest() {
            let new_dest = generate_fresh_var(&mut used_vars, &old);
            // variable name to replace in instructions in `moveable_instrs`
            let old_var = updated_vars.get(&old).unwrap_or(&old).clone();
            for instr in moveable_instrs.iter_mut().skip(i + 1) {
                // replace all succeeding moveable instructions with the new variable name
                // regardless if they actually use the definition from the changing
                // instruction

                // if they do not, a later instruction will update the variable name
                // again
                instr.1.replace_args(&old_var, &new_dest);
            }
            rewrite_cfg(
                cfg,
                &old,
                &new_dest,
                moveable_instrs[i].0,
                reaching_defs,
                lp,
            );
            updated_vars.insert(old_var, new_dest.clone());
            moveable_instrs[i].1.set_dest(new_dest);
        }
    }
    moveable_instrs
}

/// Rewrites all the uses of the given instruction in the loop
/// to use `new_use` instead of `old_use`
/// # Arguments
/// * `cfg` - The cfg
/// * `old_use` - The old use
/// * `new_use` - The new use
/// * `changing_instr` - The instruction that is changing
/// * `reaching_defs` - The reaching definitions analysis result
/// * `lp` - The loop to rewrite instructions in
fn rewrite_cfg(
    cfg: &mut Cfg,
    old_use: &str,
    new_use: &str,
    changing_instr: u64,
    reaching_defs: &AnalysisResult<ReachingDefs>,
    lp: &NaturalLoop,
) {
    for (_, blk) in cfg
        .blocks
        .iter_mut()
        .filter(|(id, _)| lp.nodes.contains(id))
    {
        if let CfgNode::Block(blk) = blk {
            for (instr_id, instr) in
                blk.instrs.iter_mut().chain(blk.terminator.as_mut())
            {
                if reaching_defs.in_facts[instr_id].reached_by(changing_instr) {
                    instr.replace_args(old_use, new_use);
                }
            }
        }
    }
}

/// Gets the next available block id for a new block
fn next_block_id(cfg: &Cfg) -> usize {
    let mut next = 0;
    for k in cfg.blocks.keys() {
        if *k >= next {
            next = k + 1;
        }
    }
    next
}

/// Creates a new preheader block for the given header
/// and inserts it into the cfg
fn insert_preheader(
    cfg: &mut Cfg,
    header: usize,
    instrs: Vec<(u64, Instruction)>,
    lp: &NaturalLoop,
) -> usize {
    let preheader_id = next_block_id(cfg);
    for (n, edge) in cfg.adj_lst.iter_mut() {
        if lp.nodes.contains(n) {
            continue;
        }
        match edge {
            CfgEdgeTo::Next(n) if *n == header => {
                *n = preheader_id;
            }
            CfgEdgeTo::Branch {
                true_node: t,
                false_node: f,
            } => {
                if *t == header {
                    *t = preheader_id;
                }
                if *f == header {
                    *f = preheader_id;
                }
            }
            _ => (),
        }
    }
    cfg.blocks.insert(
        preheader_id,
        CfgNode::Block(BasicBlock {
            instrs,
            terminator: None,
        }),
    );
    cfg.adj_lst.insert(preheader_id, CfgEdgeTo::Next(header));
    preheader_id
}

fn loop_invariant_instrs(
    cfg: &Cfg,
    reaching_defs: Rc<AnalysisResult<ReachingDefs>>,
    lp: Rc<NaturalLoop>,
    live_vars: &AnalysisResult<LiveVars>,
) -> Vec<(u64, Instruction)> {
    let nodes = Rc::new(lp.nodes.iter().copied().collect::<Vec<usize>>());
    let loop_inv = analyze(
        cfg,
        &MoveableInstrs::top(reaching_defs, lp.clone(), live_vars),
        Some(&nodes),
    );
    get_loop_invariant_instrs(cfg, &nodes, lp.header, &loop_inv)
}

fn licm_post(instrs: Vec<Code>) -> Vec<Code> {
    instrs
}

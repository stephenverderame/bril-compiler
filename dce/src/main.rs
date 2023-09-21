use bril_rs::Code;
use cfg::{
    analysis::{analyze, live_vars::LiveVars, AnalysisResult, Backwards},
    BasicBlock, CfgNode,
};
use common_cli::{cli_args, compiler_pass};

#[cli_args]
struct ExtraArgs {}

/// Invokes global dead code elimination on the cfg
#[compiler_pass(true)]
fn dce(mut cfg: Cfg, _args: &CLIArgs, _f: &bril_rs::Function) -> Cfg {
    let mut changed = true;
    while changed {
        changed = false;
        let analysis_res = analyze::<LiveVars, Backwards>(&cfg, None, None);
        for block in
            &mut cfg.blocks.iter_mut().filter_map(|(_, node)| match node {
                CfgNode::Block(block) => Some(block),
                _ => None,
            })
        {
            changed |= block_dce(block, &analysis_res);
        }
    }
    cfg.clean()
}

/// Performs dead code elimination on a basic block using global analysis results
/// Returns true if the block was changed
fn block_dce(
    block: &mut BasicBlock,
    analysis_res: &AnalysisResult<LiveVars>,
) -> bool {
    let mut can_remove = vec![];
    for (instr_id, instr) in block.instrs.iter() {
        if let Some(dest) = instr.get_dest() {
            if instr.is_semi_pure()
                && !analysis_res.in_facts[instr_id].is_live_out(&dest)
            {
                can_remove.push(*instr_id);
            }
        }
    }
    block.instrs.retain(|(id, _)| !can_remove.contains(id));
    !can_remove.is_empty()
}

fn dce_post(instrs: Vec<Code>) -> Vec<Code> {
    instrs
}

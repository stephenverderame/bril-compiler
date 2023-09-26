use bril_rs::Code;
use common_cli::{cli_args, compiler_pass};

#[cli_args]
struct ExtraArgs {}

#[compiler_pass]
fn dummy_pass(graph: Cfg, _args: &CLIArgs, _f: &bril_rs::Function) -> Cfg {
    graph
}

fn dummy_pass_post(instrs: Vec<Code>) -> Vec<Code> {
    instrs
}

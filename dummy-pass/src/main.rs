use common_cli::{cli_args, compiler_pass};

#[cli_args]
struct ExtraArgs {}

#[compiler_pass(true)]
fn dummy_pass(graph: Cfg, _args: &CLIArgs) -> Cfg {
    graph
}

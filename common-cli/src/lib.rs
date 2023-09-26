use proc_macro::Delimiter;
use proc_macro::Group;
use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;
use syn::Ident;
use syn::ItemFn;
use syn::ItemStruct;
use syn::__private::Span;

/// A macro that decorates a struct which stores extra arguments to the program
#[proc_macro_attribute]
pub fn cli_args(_: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemStruct);
    let mut output: TokenStream = quote! {
        use clap::Parser;

        #[derive(Parser, Debug)]
        #[command(author, version, about, long_about = None)]
        struct CLIArgs
    }
    .into();

    let mut struct_fields = TokenStream::new();
    struct_fields.extend(Into::<proc_macro::TokenStream>::into(quote! {
            /// The optional file to read from, if not specified a bril program
            /// is expected on stdin
            #[arg(short, long)]
            file: Option<String>,

            /// Whether to use basic blocks for the analysis or not
            /// A pass that operates on basic blocks will do nothing
            /// if this is set to false.
            /// Defaults to true.
            #[arg(long)]
            use_blocks: Option<bool>,

    }));
    for f in input.fields.iter() {
        struct_fields.extend(Into::<proc_macro::TokenStream>::into(quote! {
            #f,
        }));
    }
    output.extend(vec![proc_macro::TokenTree::Group(Group::new(
        Delimiter::Brace,
        struct_fields,
    ))]);
    output
}

struct CompilerPassArgs {
    /// Whether to use basic blocks for the analysis or not
    block_cfg: bool,
    /// Whether to generate all labels or not
    all_labels: bool,
}

impl Default for CompilerPassArgs {
    fn default() -> Self {
        Self {
            block_cfg: true,
            all_labels: false,
        }
    }
}

fn parse_compiler_pass_args(arr: TokenStream) -> CompilerPassArgs {
    let mut args: CompilerPassArgs = Default::default();
    for tok in arr {
        match tok {
            proc_macro::TokenTree::Ident(ident)
                if ident.to_string() == "instruction_cfg" =>
            {
                args.block_cfg = false;
            }
            proc_macro::TokenTree::Ident(ident)
                if ident.to_string() == "all_labels" =>
            {
                args.all_labels = true;
            }
            _ => (),
        }
    }
    args
}

/// A compiler pass that decorates a function that takes in a `Cfg` and `&CLIArgs`
/// and returns a `Cfg`
///
/// A function with the same name as the decorated function with `_post` appended
/// is expected to exist and will be called after the decorated function. It
/// is expected to take in a `Vec<Code>` and return a `Vec<Code>`
/// # Arguments
/// * `all_labels` - Whether to generate all labels or not
/// * `instruction_cfg` - Whether to use instruction-level blocks for the analysis
/// # Example
///
/// ```
/// #[compiler_pass(all_labels, instruction_cfg)]
/// fn my_pass(graph: Cfg, _args: &CLIArgs, _f: &bril_rs::Function) -> Cfg {
///    // ...
///    graph
/// }
/// ```
///
///
/// ```
/// #[compiler_pass(instruction_cfg)]
/// fn my_pass(graph: Cfg, _args: &CLIArgs, _f: &bril_rs::Function) -> Cfg {
///    // ...
///    graph
/// }
/// ```
///
///
/// ```
/// #[compiler_pass]
/// fn my_pass(graph: Cfg, _args: &CLIArgs, _f: &bril_rs::Function) -> Cfg {
///    // ...
///    graph
/// }
/// ```
#[proc_macro_attribute]
pub fn compiler_pass(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let name = input.sig.ident.to_string();
    let postprocess_name =
        Ident::new(&format!("{}_post", name), Span::call_site());
    let name = Ident::new(&name, Span::call_site());
    let pass_args = parse_compiler_pass_args(attr);
    let block_cfg = pass_args.block_cfg;
    let all_labels = pass_args.all_labels;
    let output = quote! {
        use atty::Stream;
        use bril_rs::{load_program, load_program_from_read, Program};
        use cfg::Cfg;
        use std::fs::File;

        #input

        fn main() {
            let args = CLIArgs::parse();
            if args.file.is_some() {
                let prog =
                    load_program_from_read(File::open(args.file.as_ref().unwrap()).unwrap());
                println!("{}", serde_json::to_string(&transform_prog(prog, &args)).unwrap());
            } else if !atty::is(Stream::Stdin) {
                println!(
                    "{}",
                    serde_json::to_string(&transform_prog(load_program(), &args)).unwrap()
                );
            } else {
                eprintln!("Either specify a file or pipe in a bril program.");
                eprintln!("See `--help` for more information.");
            }
        }

        fn transform_prog(mut prog: Program, args: &CLIArgs) -> Program {
            for f in &mut prog.functions {
                let cfg = Cfg::from(f, !args.use_blocks.unwrap_or(#block_cfg));
                let new_body = #name(cfg, args, f).to_src(#all_labels);
                f.instrs = #postprocess_name(new_body);
            }
            prog
        }
    };
    output.into()
}

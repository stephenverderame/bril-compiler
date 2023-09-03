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
            #[arg(long)]
            #f,
        }));
    }
    output.extend(vec![proc_macro::TokenTree::Group(Group::new(
        Delimiter::Brace,
        struct_fields,
    ))]);
    output
}

/// A compiler pass that decorates a function that takes in a `Cfg` and `&CLIArgs`
/// and returns a `Cfg`
/// # Arguments
/// * `default_use_cfg` - Whether to use basic blocks for the analysis or not
///     if not specified in the CLI args
///     Must be a boolean literal
#[proc_macro_attribute]
pub fn compiler_pass(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let name = input.sig.ident.to_string();
    let name = Ident::new(&name, Span::call_site());
    let default_use_cfg = parse_macro_input!(attr as syn::LitBool).value;
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
                let cfg = Cfg::from(f, !args.use_blocks.unwrap_or(#default_use_cfg));
                let new_body = #name(cfg, args).to_src();
                f.instrs = new_body;
            }
            prog
        }
    };
    output.into()
}

use proc_macro::TokenStream;
use syn::parse_macro_input;

use crate::{
    ast::{DefineCtxInput, DefineCtxViewInput, RegisterDepInput},
    codegen::{
        define_ctx::gen_define_ctx, define_ctx_view::gen_define_ctx_view,
        register_ctx_factory::gen_register_factory, register_ctx_singleton::gen_register_singleton,
    },
};

mod ast;
mod helpers;
mod codegen {
    pub mod define_ctx;
    pub mod define_ctx_view;
    pub mod register_ctx_factory;
    pub mod register_ctx_singleton;
    mod shared;
}

#[proc_macro]
pub fn define_ctx(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as DefineCtxInput);
    gen_define_ctx(parsed).into()
}

#[proc_macro]
pub fn define_ctx_view(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as DefineCtxViewInput);
    gen_define_ctx_view(parsed).into()
}

#[proc_macro]
pub fn register_ctx_singleton(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as RegisterDepInput);
    gen_register_singleton(parsed).into()
}

#[proc_macro]
pub fn register_ctx_factory(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as RegisterDepInput);
    gen_register_factory(parsed).into()
}

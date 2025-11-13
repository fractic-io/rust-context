use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens as _};
use syn::{Expr, Ident, Type, TypeParamBound};
use syn::{ExprClosure, Pat, PatIdent, PatType};

use crate::ast::RegisterDepInput;
use crate::helpers::{chain_to_pascal, dep_kind, type_ident_chain, DepKind};

pub fn gen_register_factory(input: RegisterDepInput) -> TokenStream2 {
    let RegisterDepInput {
        ctx_ty,
        type_ty,
        builder,
    } = input;

    // ── inspect the supplied builder closure ──────────────────────────────
    fn fallback_arg_ident(idx: usize) -> Ident {
        format_ident!("arg{}", idx)
    }
    let (is_async, arg_idents, arg_types): (bool, Vec<Ident>, Vec<TokenStream2>) = match &builder {
        Expr::Closure(ExprClosure {
            asyncness,
            inputs,
            body,
            ..
        }) => {
            // async |..| { … }  ➜ asyncness.is_some()
            // |..| async { … } ➜ body is Expr::Async
            let body_is_async_block = matches!(body.as_ref(), Expr::Async(_));
            let is_async = asyncness.is_some() || body_is_async_block;

            let mut ids = Vec::new();
            let mut tys = Vec::new();

            // inputs: (ctx, arg0, arg1, …)  → skip ctx
            for (idx, p) in inputs.iter().skip(1).enumerate() {
                match p {
                    // e.g.   |db: &Db|
                    Pat::Type(PatType { pat, ty, .. }) => {
                        if let Pat::Ident(PatIdent { ident, .. }) = pat.as_ref() {
                            ids.push(ident.clone());
                        } else {
                            ids.push(fallback_arg_ident(idx));
                        }
                        tys.push(ty.to_token_stream());
                    }
                    // e.g.   |db|
                    Pat::Ident(PatIdent { ident, .. }) => {
                        ids.push(ident.clone());
                        tys.push(quote! { _ });
                    }
                    // anything else: `|_|`, `|&(x, y)|`, …
                    _ => {
                        ids.push(fallback_arg_ident(idx));
                        tys.push(quote! { _ });
                    }
                }
            }

            (is_async, ids, tys)
        }
        _ => (true, Vec::new(), Vec::new()),
    };

    // ── helper identifiers ───────────────────────────────────────────────
    let chain = type_ident_chain(&type_ty);
    let stem_pascal = chain_to_pascal(&chain);
    let factory_id = format_ident!("{stem_pascal}Factory");

    // ── return-type tokens for the public API ────────────────────────────
    let (arc_ret_ty, bound_trait_path, is_trait_dep) = match dep_kind(&type_ty) {
        DepKind::Trait => {
            // Extract the first trait path from `dyn …`.
            let trait_path = if let Type::TraitObject(obj) = &type_ty {
                obj.bounds
                    .iter()
                    .find_map(|b| match b {
                        TypeParamBound::Trait(tb) => Some(quote! { #tb }),
                        _ => None,
                    })
                    .expect("empty trait object")
            } else {
                quote! {}
            };
            (
                quote! { std::sync::Arc<#type_ty + Send + Sync> },
                trait_path,
                true,
            )
        }
        DepKind::Struct => (
            quote! { std::sync::Arc<#type_ty> },
            quote! {}, // no extra bound needed
            false,
        ),
    };

    // ---------------------------------------------------------------------
    // 1.  The stored builder type
    // ---------------------------------------------------------------------
    let builder_field_ty = if is_async {
        quote! {
            std::sync::Arc<
                dyn Fn(
                    std::sync::Arc<#ctx_ty>, #( #arg_types ),*
                ) -> std::pin::Pin<
                    Box<
                        dyn std::future::Future<
                                Output = ::std::result::Result<#arc_ret_ty, ::fractic_server_error::ServerError>
                        > + Send
                    >
                > + Send + Sync
            >
        }
    } else {
        quote! {
            std::sync::Arc<
                dyn Fn(
                    std::sync::Arc<#ctx_ty>, #( #arg_types ),*
                ) -> ::std::result::Result<#arc_ret_ty, ::fractic_server_error::ServerError>
                + Send + Sync
            >
        }
    };

    // ---------------------------------------------------------------------
    // 2.  new(ctx, builder):  wraps the user closure to return an Arc
    // ---------------------------------------------------------------------
    let new_fn = if is_async {
        if is_trait_dep {
            quote! {
                pub fn new<B, Fut, R>(
                    ctx: std::sync::Arc<#ctx_ty>,
                    builder: B
                ) -> Self
                where
                    B  : Fn(std::sync::Arc<#ctx_ty>, #( #arg_types ),*) -> Fut
                         + Send + Sync + 'static,
                    Fut: std::future::Future<Output =
                            ::std::result::Result<R, ::fractic_server_error::ServerError>>
                         + Send + 'static,
                    R  : #bound_trait_path + Send + Sync + 'static,
                {
                    let wrapped = move |ctx: std::sync::Arc<#ctx_ty>, #( #arg_idents : #arg_types ),*| {
                        let fut = builder(ctx, #( #arg_idents ),*);
                        Box::pin(async move {
                            let concrete: R = fut.await?;
                            let arc_concrete = std::sync::Arc::new(concrete);
                            let arc: #arc_ret_ty = arc_concrete; // unsize coercion
                            ::std::result::Result::Ok(arc)
                        }) as std::pin::Pin<
                                Box<
                                    dyn std::future::Future<
                                        Output = ::std::result::Result<#arc_ret_ty,
                                                                       ::fractic_server_error::ServerError>
                                    > + Send
                                >
                            >
                    };
                    Self { ctx, builder: std::sync::Arc::new(wrapped) }
                }
            }
        } else {
            quote! {
                pub fn new<B, Fut>(
                    ctx: std::sync::Arc<#ctx_ty>,
                    builder: B
                ) -> Self
                where
                    B: Fn(std::sync::Arc<#ctx_ty>, #( #arg_types ),*) -> Fut
                        + Send + Sync + 'static,
                    Fut: std::future::Future<Output =
                        ::std::result::Result<#type_ty, ::fractic_server_error::ServerError>
                    > + Send + 'static,
                {
                    let wrapped = move |ctx: std::sync::Arc<#ctx_ty>, #( #arg_idents : #arg_types ),*| {
                        let fut = builder(ctx, #( #arg_idents ),*);
                        Box::pin(async move {
                            let concrete = fut.await?;
                            let arc = std::sync::Arc::new(concrete);
                            ::std::result::Result::Ok(arc)
                        }) as std::pin::Pin<
                                Box<
                                    dyn std::future::Future<
                                        Output =
                                            ::std::result::Result<#arc_ret_ty,
                                                                       ::fractic_server_error::ServerError>
                                    > + Send
                                >
                            >
                    };
                    Self { ctx, builder: std::sync::Arc::new(wrapped) }
                }
            }
        }
    } else {
        if is_trait_dep {
            quote! {
                pub fn new<B, R>(
                    ctx: std::sync::Arc<#ctx_ty>,
                    builder: B
                ) -> Self
                where
                    B: Fn(std::sync::Arc<#ctx_ty>, #( #arg_types ),*)
                         -> ::std::result::Result<R, ::fractic_server_error::ServerError>
                         + Send + Sync + 'static,
                    R: #bound_trait_path + Send + Sync + 'static,
                {
                    let wrapped = move |ctx: std::sync::Arc<#ctx_ty>, #( #arg_idents : #arg_types ),*| {
                        builder(ctx, #( #arg_idents ),*).map(|concrete: R| {
                            let arc_concrete = std::sync::Arc::new(concrete);
                            let arc: #arc_ret_ty = arc_concrete; // unsize coercion
                            arc
                        })
                    };
                    Self { ctx, builder: std::sync::Arc::new(wrapped) }
                }
            }
        } else {
            quote! {
                pub fn new<B>(
                    ctx: std::sync::Arc<#ctx_ty>,
                    builder: B
                ) -> Self
                where
                    B: Fn(std::sync::Arc<#ctx_ty>, #( #arg_types ),*)
                         -> ::std::result::Result<#type_ty, ::fractic_server_error::ServerError>
                         + Send + Sync + 'static,
                {
                    let wrapped = move |ctx: std::sync::Arc<#ctx_ty>, #( #arg_idents : #arg_types ),*| {
                        builder(ctx, #( #arg_idents ),*).map(|concrete| {
                            std::sync::Arc::new(concrete)
                        })
                    };
                    Self { ctx, builder: std::sync::Arc::new(wrapped) }
                }
            }
        }
    };

    // ---------------------------------------------------------------------
    // 3.  build(&self, …)
    // ---------------------------------------------------------------------
    let build_fn = if is_async {
        quote! {
            pub async fn build(&self #( , #arg_idents : #arg_types )* )
                -> ::std::result::Result<#arc_ret_ty, ::fractic_server_error::ServerError>
            {
                (self.builder)(self.ctx.clone(), #( #arg_idents ),*).await
            }
        }
    } else {
        quote! {
            pub fn build(&self #( , #arg_idents : #arg_types )* )
                -> ::std::result::Result<#arc_ret_ty, ::fractic_server_error::ServerError>
            {
                (self.builder)(self.ctx.clone(), #( #arg_idents ),* )
            }
        }
    };

    // ---------------------------------------------------------------------
    // 4.  final expansion
    // ---------------------------------------------------------------------
    quote! {
        #[derive(Clone)]
        pub struct #factory_id {
            ctx:     std::sync::Arc<#ctx_ty>,
            builder: #builder_field_ty,
        }

        impl #factory_id {
            #new_fn
            #build_fn
        }

        // Register the factory as the lazy singleton.
        ::fractic_context::register_ctx_singleton!(
            #ctx_ty,
            #factory_id,
            |ctx: std::sync::Arc<#ctx_ty>| async move {
                ::std::result::Result::Ok(#factory_id::new(ctx.clone(), #builder))
            }
        );
    }
}

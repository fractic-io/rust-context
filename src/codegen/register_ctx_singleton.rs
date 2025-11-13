use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};

use crate::ast::RegisterDepInput;
use crate::helpers::{chain_to_pascal, chain_to_snake, dep_kind, type_ident_chain, DepKind};

pub fn gen_register_singleton(input: RegisterDepInput) -> TokenStream2 {
    let RegisterDepInput {
        ctx_ty,
        type_ty,
        builder,
    } = input;

    let chain = type_ident_chain(&type_ty);
    let field_snake = chain_to_snake(&chain);
    let trait_pascal = chain_to_pascal(&chain);

    let trait_name = format_ident!("CtxHas{}", trait_pascal);
    let getter = field_snake.clone();
    let default_fn = format_ident!("__default_{}", field_snake);

    let wrapped_type_ty = match dep_kind(&type_ty) {
        // written as `dyn crate::Foo`  → keep it
        DepKind::Trait => quote! { #type_ty + Send + Sync },
        // any plain path (struct or trait)  → treat as concrete type
        DepKind::Struct => quote! { #type_ty },
    };

    quote! {
        #[doc(hidden)]
        #[async_trait::async_trait]
        pub trait #trait_name {
            async fn #getter(&self) -> ::std::result::Result<
                std::sync::Arc<#wrapped_type_ty>,
                ::fractic_server_error::ServerError
            >;
        }

        #[doc(hidden)]
        pub async fn #default_fn(
            ctx: std::sync::Arc<#ctx_ty>
        ) -> ::std::result::Result<
            std::sync::Arc<#wrapped_type_ty>,
            ::fractic_server_error::ServerError
        > {
            let concrete = (#builder)(ctx).await?;
            Ok(std::sync::Arc::new(concrete))
        }
    }
}

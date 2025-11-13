use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{Ident, Type};

use crate::helpers::{
    chain_to_pascal, chain_to_snake, dep_kind, type_ident_chain, type_is_local, type_path_prefix,
    DepKind,
};

/// Shared artifact generation (fields / getters / overrides / CtxHas impls) for
/// both top-level deps (define_ctx) and overlay deps (define_ctx_view).
pub fn gen_dep_artifacts(
    ctx_name: &Ident,
    dep_tys: &[Type],
) -> (
    Vec<TokenStream2>, // field defs
    Vec<TokenStream2>, // field inits
    Vec<TokenStream2>, // inherent getters + overrides
    Vec<TokenStream2>,
) // `impl CtxHas… for Ctx`
{
    let mut field_defs = Vec::new();
    let mut field_inits = Vec::new();
    let mut getters = Vec::new();
    let mut trait_impls = Vec::new();

    for trait_ty in dep_tys {
        // ---------- absolute-path validation ----------
        if type_is_local(trait_ty) {
            let ident = type_ident_chain(trait_ty)
                .first()
                .cloned()
                .unwrap_or_else(|| format_ident!("_"));
            let msg = format!(
                "dependency path `{}` must be an absolute path (e.g. `crate::{}::{}`), not a \
                 local identifier or re-export.",
                ident, ident, ident
            );
            field_defs.push(quote! { compile_error!(#msg); });
            continue;
        }

        // ---------- identifiers ----------
        let chain = type_ident_chain(trait_ty);
        if chain.is_empty() {
            field_defs.push(quote! { compile_error!("unsupported dependency type"); });
            continue;
        }

        let field_ident = chain_to_snake(&chain); // `tts_repository`
        let getter_ident = field_ident.clone(); // same as field
        let override_ident = format_ident!("override_{}", field_ident);

        // helpers that already existed
        let default_fn_ident = format_ident!("__default_{}", field_ident);
        let ctxhas_ident = format_ident!("CtxHas{}", chain_to_pascal(&chain));
        let prefix = type_path_prefix(trait_ty);

        let default_fn_path = if !prefix.is_empty() {
            quote! { #prefix :: #default_fn_ident }
        } else {
            quote! { #default_fn_ident }
        };
        let ctxhas_path = if !prefix.is_empty() {
            quote! { #prefix :: #ctxhas_ident }
        } else {
            quote! { #ctxhas_ident }
        };

        // ---------- kind-specific code ----------
        let kind = dep_kind(trait_ty);

        // 1.  Field definition
        let field_ty_tokens = match kind {
            DepKind::Trait => quote! { std::sync::Arc<#trait_ty + Send + Sync> },
            DepKind::Struct => quote! { std::sync::Arc<#trait_ty> },
        };
        field_defs.push(quote! {
            #[doc(hidden)]
            pub #field_ident: ::tokio::sync::RwLock<Option<#field_ty_tokens>>
        });

        // 2.  Field init (always `None`)
        field_inits.push(quote! {
            #field_ident: ::tokio::sync::RwLock::new(None)
        });

        // 3.  Getter + override on the context itself
        let getter_ret_ty = field_ty_tokens.clone(); // same as field type
        getters.push(quote! {
            pub async fn #getter_ident(&self) -> ::std::result::Result<
                #getter_ret_ty,
                ::fractic_server_error::ServerError
            > {
                if let Some(existing) = {
                    let read = self.#field_ident.read().await;
                    (*read).clone()
                } {
                    return ::std::result::Result::Ok(existing);
                }
                // build outside any lock
                let ctx_arc = self.__weak_self
                    .upgrade()
                    .expect("Ctx weak ptr lost – this should never happen");
                let built = #default_fn_path(ctx_arc).await?;

                // store – be race-aware
                let mut write = self.#field_ident.write().await;
                let arc = if let Some(ref arc) = *write {
                    arc.clone()
                } else {
                    write.replace(built.clone());
                    built
                };
                ::std::result::Result::Ok(arc)
            }

            #[cfg(test)]
            pub async fn #override_ident(&self, new_impl: #getter_ret_ty) {
                let mut lock = self.#field_ident.write().await;
                *lock = Some(new_impl);
            }
        });

        // 4.  Blanket `CtxHas…` impl
        trait_impls.push(quote! {
            #[async_trait::async_trait]
            impl #ctxhas_path for #ctx_name {
                async fn #getter_ident(&self) -> ::std::result::Result<
                    #getter_ret_ty,
                    ::fractic_server_error::ServerError
                > {
                    self.#getter_ident().await
                }
            }
        });
    }

    (field_defs, field_inits, getters, trait_impls)
}

use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};

use crate::{
    ast::DefineCtxViewInput,
    helpers::{
        chain_to_pascal, chain_to_snake, collect_valid_dep_tys, dep_kind, last_ident, to_snake,
        type_ident_chain, type_is_local, type_path_prefix, DepKind,
    },
};

pub fn gen_define_ctx_view(input: DefineCtxViewInput) -> TokenStream2 {
    let DefineCtxViewInput {
        view_name,
        env,
        secrets,
        dep_overlays,
        req_impl,
    } = input;

    // -- Dependency aliases ───────────────────────────────────────
    let mut alias_reexports = Vec::<TokenStream2>::new();
    // Dependency overlays – keep only well-formed absolute paths.
    let mut overlay_error_tokens = Vec::<TokenStream2>::new();
    let dep_overlay_tys = collect_valid_dep_tys(
        dep_overlays.iter().map(|d| &d.trait_ty),
        &mut overlay_error_tokens,
    );

    for trait_ty in &dep_overlay_tys {
        // absolute-path validation
        if type_is_local(trait_ty) {
            let bad = type_ident_chain(trait_ty)
                .first()
                .cloned()
                .unwrap_or_else(|| format_ident!("_"));
            let msg = format!(
                "`define_ctx_view!`: overlay dep path `{}` must be an absolute path (e.g. \
                 `crate::{}::{}`)",
                bad, bad, bad
            );
            alias_reexports.push(quote! { compile_error!(#msg); });
            continue;
        }

        // identifiers for naming
        let chain = type_ident_chain(trait_ty);
        if chain.is_empty() {
            alias_reexports.push(quote! { compile_error!("unsupported dependency type"); });
            continue;
        }

        // 1. deterministic "stem" for every alias we create
        let alias_snake = chain_to_snake(&chain);

        // 2. the three symbols we have to re-export from the **parent module**
        let trait_ident = &last_ident(trait_ty).ident; // e.g. `TtsRepository`
        let default_fn_ident = format_ident!("__default_{}", alias_snake); // e.g. `__default_tts_repository`
        let ctxhas_ident = format_ident!("CtxHas{}", chain_to_pascal(&chain));

        // 3. names the rest of the macro will point at
        let trait_alias_ident = format_ident!("__{}_trait", alias_snake); // `__tts_repository_trait`
        let default_fn_alias = format_ident!("__{}_default", alias_snake); // `__tts_repository_default`
        let ctxhas_alias = format_ident!("__{}_ctxhas", alias_snake); // `__tts_repository_ctxhas`

        // Parent path == everything except the last segment.
        let parent_path = type_path_prefix(trait_ty);

        alias_reexports.push(quote! {
            #[doc(hidden)]
            pub use #parent_path::#trait_ident      as #trait_alias_ident;
            #[doc(hidden)]
            pub use #parent_path::#default_fn_ident as #default_fn_alias;
            #[doc(hidden)]
            pub use #parent_path::#ctxhas_ident     as #ctxhas_alias;
        });
    }

    // -- Signatures only ──────────────────────────────────────────
    let env_sigs: Vec<_> = env
        .iter()
        .map(|kv| {
            let fn_name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { fn #fn_name(&self) -> &#ty; }
        })
        .collect();

    let secret_sigs: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let fn_name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { fn #fn_name(&self) -> &#ty; }
        })
        .collect();

    // Overlay deps signatures: use full Type (trait).
    let dep_sigs: Vec<_> = dep_overlay_tys
        .iter()
        .map(|trait_ty| {
            let chain = type_ident_chain(trait_ty);
            let fn_name = chain_to_snake(&chain);
            let inner_ty = match dep_kind(trait_ty) {
                DepKind::Trait => quote! { std::sync::Arc<#trait_ty + Send + Sync> },
                DepKind::Struct => quote! { std::sync::Arc<#trait_ty> },
            };
            quote! {
                async fn #fn_name(&self) -> ::std::result::Result<#inner_ty, ::fractic_server_error::ServerError>;
            }
        })
        .collect();

    // -- Implementations for the helper macro ─────────────────────
    let env_impls: Vec<_> = env
        .iter()
        .map(|kv| {
            let fn_name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! {
                fn #fn_name(&self) -> &#ty {
                    &self.#fn_name
                }
            }
        })
        .collect();

    let secret_impls: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let fn_name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! {
                fn #fn_name(&self) -> &#ty {
                    &self.#fn_name
                }
            }
        })
        .collect();

    // Generate impls only for *valid* overlays.
    let dep_impls: Vec<_> = dep_overlay_tys
        .iter()
        .map(|trait_ty| {
            let chain = type_ident_chain(trait_ty);
            let fn_name = chain_to_snake(&chain);
            let alias_snake = chain_to_snake(&chain);
            let trait_alias_ident = format_ident!("__{}_trait", alias_snake);

            // trait_args is just the generic argument list (if any):
            let trait_args = match &last_ident(trait_ty).arguments {
                syn::PathArguments::AngleBracketed(g) => quote! { #g },
                _ => quote! {},
            };

            let inner_ty = match dep_kind(trait_ty) {
                DepKind::Trait  => quote! { std::sync::Arc<dyn $crate::#trait_alias_ident #trait_args + Send + Sync> },
                DepKind::Struct => quote! { std::sync::Arc<$crate::#trait_alias_ident #trait_args> },
            };

            quote! {
                async fn #fn_name(&self) -> ::std::result::Result<#inner_ty, ::fractic_server_error::ServerError> {
                    self.#fn_name().await
                }
            }
        })
        .collect();

    // Super-trait list.
    let super_traits: TokenStream2 = if !req_impl.is_empty() {
        quote! { + #( #req_impl )+* }
    } else {
        TokenStream2::new()
    };

    // Macro/struct identifiers.
    let impl_macro = format_ident!("__impl_{}_for", view_name);
    let overlay_impls_macro = format_ident!("__overlay_impls_{}_for", view_name);
    // Per-view overlay struct + its field on the parent ctx.
    let overlay_struct_name = format_ident!("__{}DepsOverlay", view_name);
    let overlay_field_ident = format_ident!("__{}_deps", to_snake(&view_name));

    // Generate struct field defs, getters, etc.
    let overlay_field_defs: Vec<_> = dep_overlay_tys
        .iter()
        .map(|trait_ty| {
            // identifiers for naming
            let chain = type_ident_chain(trait_ty);
            if chain.is_empty() {
                return quote! { compile_error!("unsupported dependency type"); };
            }
            let field = chain_to_snake(&chain);

            // alias module
            let alias_snake = chain_to_snake(&chain);
            let trait_alias_ident = format_ident!("__{}_trait", alias_snake);

            // keep generic args
            let trait_args = match &last_ident(trait_ty).arguments {
                syn::PathArguments::AngleBracketed(g) => quote! { #g },
                _ => quote! {},
            };

            let inner_ty = match dep_kind(trait_ty) {
                DepKind::Trait => {
                    quote! { std::sync::Arc<dyn crate::#trait_alias_ident #trait_args + Send + Sync> }
                }
                DepKind::Struct => quote! { std::sync::Arc<crate::#trait_alias_ident #trait_args> },
            };

            quote! {
                #[doc(hidden)]
                pub #field: ::tokio::sync::RwLock<Option<#inner_ty>>,
            }
        })
        .collect();
    // No explicit init: `Default` sets each lock to `None`.

    let overlay_getters_impls: Vec<_> = dep_overlay_tys
        .iter()
        .map(|trait_ty| {
            let chain = type_ident_chain(trait_ty);
            let field = chain_to_snake(&chain);
            let getter = field.clone();
            let override_fn = format_ident!("override_{}", field);
            let alias_snake = chain_to_snake(&chain);
            let trait_alias_ident = format_ident!("__{}_trait", alias_snake);
            let default_fn_alias = format_ident!("__{}_default", alias_snake);

            // keep generic args
            let trait_args = match &last_ident(trait_ty).arguments {
                syn::PathArguments::AngleBracketed(g) => quote! { #g },
                _ => quote! {},
            };

            let return_ty = match dep_kind(trait_ty) {
                DepKind::Trait  => quote! { std::sync::Arc<dyn $crate::#trait_alias_ident #trait_args + Send + Sync> },
                DepKind::Struct => quote! { std::sync::Arc<$crate::#trait_alias_ident #trait_args> },
            };

            let default_fn_path = quote! { $crate::#default_fn_alias };

            quote! {
                pub async fn #getter(&self) -> ::std::result::Result<#return_ty, ::fractic_server_error::ServerError> {
                    if let Some(existing) = {
                        let read = self.#overlay_field_ident.#field.read().await;
                        (*read).clone()
                    } {
                        return ::std::result::Result::Ok(existing);
                    }
                    let ctx_arc = self.__weak_self
                        .upgrade()
                        .expect("Ctx weak ptr lost – this should never happen");
                    let built = #default_fn_path(ctx_arc).await?;
                    let mut write = self.#overlay_field_ident.#field.write().await;
                    let arc = if let Some(ref arc) = *write {
                        arc.clone()
                    } else {
                        write.replace(built.clone());
                        built
                    };
                    ::std::result::Result::Ok(arc)
                }

                #[cfg(test)]
                pub async fn #override_fn(&self, new_impl: #return_ty) {
                    let mut lock = self.#overlay_field_ident.#field.write().await;
                    *lock = Some(new_impl);
                }
            }
        })
        .collect();

    let overlay_trait_impls: Vec<_> = dep_overlay_tys
        .iter()
        .map(|trait_ty| {
            let chain = type_ident_chain(trait_ty);
            let getter = chain_to_snake(&chain);
            let alias_snake = chain_to_snake(&chain);
            let trait_alias_ident = format_ident!("__{}_trait", alias_snake);
            let ctxhas_alias = format_ident!("__{}_ctxhas", alias_snake);

            // keep generic args
            let trait_args = match &last_ident(trait_ty).arguments {
                syn::PathArguments::AngleBracketed(g) => quote! { #g },
                _ => quote! {},
            };

            let return_ty = match dep_kind(trait_ty) {
                DepKind::Trait  => quote! { std::sync::Arc<dyn $crate::#trait_alias_ident #trait_args + Send + Sync> },
                DepKind::Struct => quote! { std::sync::Arc<$crate::#trait_alias_ident #trait_args> },
            };

            let ctxhas_path = quote! { $crate::#ctxhas_alias };

            quote! {
                #[async_trait::async_trait]
                impl #ctxhas_path for $ctx {
                    async fn #getter(&self) -> ::std::result::Result<#return_ty, ::fractic_server_error::ServerError> {
                        self.#getter().await
                    }
                }
            }
        })
        .collect();

    // Assembly ────────────────────────────────────────────────
    quote! {
        #(#alias_reexports)*

        // View trait.
        #[async_trait::async_trait]
        pub trait #view_name : Send + Sync + std::fmt::Debug #super_traits {
            #(#env_sigs)*
            #(#secret_sigs)*
            #(#dep_sigs)*
        }

        // View trait impl helper.
        #[doc(hidden)]
        #[macro_export]
        macro_rules! #impl_macro {
            ($ctx:ty) => {
                #[async_trait::async_trait]
                impl $crate::#view_name for $ctx {
                    #(#env_impls)*
                    #(#secret_impls)*
                    #(#dep_impls)*
                }
            };
        }

        // Hidden per-view overlay struct; parent ctx keeps a single field of this.
        #[derive(Default)]
        #[doc(hidden)]
        pub struct #overlay_struct_name {
            #(#overlay_field_defs)*
        }

        // Overlay impl helper.
        #[doc(hidden)]
        #[macro_export]
        macro_rules! #overlay_impls_macro {
            ($ctx:ty) => {
                impl $ctx {
                    #(#overlay_getters_impls)*
                }
                #(#overlay_trait_impls)*
            };
        }

        // Propagate compile errors for invalid overlay deps.
        #(#overlay_error_tokens)*
    }
}

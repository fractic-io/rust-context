use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};

use crate::ast::DefineCtxInput;
use crate::codegen::shared::gen_dep_artifacts;
use crate::helpers::{chain_to_snake, collect_valid_dep_tys, to_snake, type_ident_chain};

pub fn gen_define_ctx(input: DefineCtxInput) -> TokenStream2 {
    let DefineCtxInput {
        ctx_name,
        env,
        secrets_region_ident,
        secrets_id_ident,
        secrets,
        deps,
        views,
    } = input;

    // ── ENV vars ─────────────────────────────────────────────────────────
    let env_field_defs: Vec<_> = env
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { pub #ident: #ty }
        })
        .collect();

    let env_inits: Vec<_> = env
        .iter()
        .map(|kv| {
            let var_name = kv.key.to_string();
            let ident = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! {
                let #ident: #ty = std::env::var(#var_name)
                    .map_err(|_| ::fractic_server_error::InitError::new(
                        concat!("missing env var `", #var_name, "`")
                    ).into())?
                    .parse()
                    .map_err(|e| ::fractic_server_error::InitError::with_debug(
                        concat!("failed to parse env var `", #var_name, "`"), &e
                    ).into())?;
            }
        })
        .collect();

    let env_getters: Vec<_> = env
        .iter()
        .map(|kv| {
            let fn_name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { pub fn #fn_name(&self) -> &#ty { &self.#fn_name } }
        })
        .collect();

    let env_idents: Vec<_> = env
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            quote! { #ident }
        })
        .collect();

    // Test-only init: argument definitions for env variables.
    let test_init_env_args: Vec<_> = env
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { #ident: #ty }
        })
        .collect();

    // ── Secrets ──────────────────────────────────────────────────────────
    let secret_field_defs: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { pub #ident: #ty }
        })
        .collect();

    let secret_key_strs: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let key_name = kv.key.to_string();
            quote! { #key_name }
        })
        .collect();

    let secret_fetch: TokenStream2 = if !secrets.is_empty() {
        quote! {
            let __secrets_util =
                ::fractic_aws_secrets::SecretsUtil::new(secrets_fetch_region.clone()).await;
            let __secret_map = __secrets_util
                .load_secrets(&secrets_fetch_id, &[#(#secret_key_strs),*])
                .await
                .map_err(|e| ::fractic_server_error::InitError::with_debug("failed to load secrets", &e).into())?;
        }
    } else {
        TokenStream2::new()
    };

    let secret_inits: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            let ty = &kv.ty;
            let key_name = kv.key.to_string();
            quote! {
                let #ident: #ty = __secret_map
                    .get(#key_name)
                    .ok_or_else(|| ::fractic_server_error::InitError::new(
                        concat!("missing secret key `", #key_name, "`")
                    ).into())?
                    .parse()
                    .map_err(|e| ::fractic_server_error::InitError::with_debug(
                        concat!("failed to parse secret `", #key_name, "`"), &e
                    ).into())?;
            }
        })
        .collect();

    let secret_getters: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let fn_name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { pub fn #fn_name(&self) -> &#ty { &self.#fn_name } }
        })
        .collect();

    let secret_idents: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            quote! { #ident }
        })
        .collect();

    // Test-only init: argument definitions for secret variables.
    let test_init_secret_args: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { #ident: #ty }
        })
        .collect();

    // ── Top-level Dependencies ──────────────────────────────────────────
    let mut dep_error_tokens = Vec::<TokenStream2>::new();
    let dep_tys = collect_valid_dep_tys(deps.iter().map(|d| &d.trait_ty), &mut dep_error_tokens);
    let (dep_field_defs, dep_field_inits, dep_getters, dep_trait_impls) =
        gen_dep_artifacts(&ctx_name, &dep_tys);

    // ── View invocations ─────────────────────────────────────────────────
    let mut view_overlay_field_defs = Vec::<TokenStream2>::new();
    let mut view_overlay_field_inits = Vec::<TokenStream2>::new();
    let mut view_overlay_impl_macro_calls = Vec::<TokenStream2>::new();
    let mut view_impl_macro_calls = Vec::<TokenStream2>::new();

    for path in &views {
        if path.segments.len() < 2 {
            let view_ident = &path.segments.first().unwrap().ident;
            let msg = format!(
                "`define_ctx!`: view path `{}` must be an absolute path (e.g. `my_crate::{}`), \
                 not a local identifier or brought into scope with a `use` statement.",
                view_ident, view_ident
            );
            view_impl_macro_calls.push(quote! { compile_error!(#msg); });
            continue;
        }
        // Split into crate-root and final segment.
        let crate_root = &path.segments.first().unwrap().ident;
        let view_ident = &path.segments.last().unwrap().ident;

        let impl_macro = format_ident!("__impl_{}_for", view_ident);
        let overlay_impls_macro = format_ident!("__overlay_impls_{}_for", view_ident);
        let overlay_struct_name = format_ident!("__{}DepsOverlay", view_ident);
        let overlay_field_ident = format_ident!("__{}_deps", to_snake(&view_ident));

        view_overlay_field_defs.push(quote! {
            #[doc(hidden)]
            pub #overlay_field_ident: #crate_root::#overlay_struct_name,
        });

        view_overlay_field_inits.push(quote! {
            #overlay_field_ident: ::std::default::Default::default(),
        });

        // If the view lives in *this* crate (`crate::…`) new versions of Rust
        // don't allow calling it by its fully qualified path
        // `crate::macro_name!(…)`. A unqualified `macro_name!(…)` is required
        // instead (no further path specification is needed because
        // `#[macro_export]` puts macros in the global namespace).
        //
        // Overlay implementation:
        let overlay_call = if crate_root == "crate" {
            quote! { #overlay_impls_macro!(#ctx_name); }
        } else {
            quote! { #crate_root::#overlay_impls_macro!(#ctx_name); }
        };
        view_overlay_impl_macro_calls.push(overlay_call);
        //
        // View implementation:
        let impl_call = if crate_root == "crate" {
            quote! { #impl_macro!(#ctx_name); }
        } else {
            quote! { #crate_root::#impl_macro!(#ctx_name); }
        };
        view_impl_macro_calls.push(impl_call);
    }

    // `compile_error!`s for any invalid deps we filtered out above.
    view_impl_macro_calls.extend(dep_error_tokens);

    // ── Custom std::fmt::Debug implementation ────────────────────────────
    let debug_env_fields: Vec<_> = env.iter().map(|kv| to_snake(&kv.key)).collect();
    let debug_secret_fields: Vec<_> = secrets.iter().map(|kv| to_snake(&kv.key)).collect();
    let debug_dep_fields: Vec<_> = dep_tys
        .iter()
        .map(|ty| chain_to_snake(&type_ident_chain(ty)))
        .collect();

    quote! {
        pub struct #ctx_name {
            // Runtime settings.
            #(#env_field_defs,)*
            #(#secret_field_defs,)*
            pub secrets_fetch_region: String,
            pub secrets_fetch_id: String,
            // Dependency slots (top-level).
            #(#dep_field_defs,)*
            // Dependency overlays injected by views.
            #(#view_overlay_field_defs)*
            // Weak self-reference for lazy builders.
            #[doc(hidden)]
            pub __weak_self: std::sync::Weak<Self>,
        }

        impl #ctx_name {
            /// Build an async-initialised, reference-counted context *without* eagerly creating deps.
            pub async fn init() -> ::std::result::Result<std::sync::Arc<Self>, ::fractic_server_error::ServerError> {
                use std::sync::Arc;

                // Mandatory runtime configuration.
                let secrets_fetch_region = std::env::var(stringify!(#secrets_region_ident))
                    .map_err(|_| ::fractic_server_error::InitError::new(
                        concat!("missing env var `", stringify!(#secrets_region_ident), "`")
                    ).into())?;
                let secrets_fetch_id = std::env::var(stringify!(#secrets_id_ident))
                    .map_err(|_| ::fractic_server_error::InitError::new(
                        concat!("missing env var `", stringify!(#secrets_id_ident), "`")
                    ).into())?;

                #(#env_inits)*
                #secret_fetch
                #(#secret_inits)*

                // Create `Arc` cyclically to embed Weak<Self>.
                let ctx = Arc::new_cyclic(|weak| Self {
                    #(#env_idents,)*
                    #(#secret_idents,)*
                    secrets_fetch_region,
                    secrets_fetch_id,
                    #(#dep_field_inits,)*
                    // Overlay fields initialised to None inside macro expansion.
                    #(#view_overlay_field_inits)*
                    __weak_self: weak.clone(),
                });

                ::std::result::Result::Ok(ctx)
            }
        }

        // Test-only init: bypass external env and secrets by providing values directly.
        #[cfg(test)]
        impl #ctx_name {
            pub fn init_test(
                #(#test_init_env_args),*,
                #(#test_init_secret_args),*
            ) -> ::std::sync::Arc<Self> {
                use std::sync::Arc;
                let ctx = Arc::new_cyclic(|weak| Self {
                    #(#env_idents,)*
                    #(#secret_idents,)*
                    secrets_fetch_region: String::new(),
                    secrets_fetch_id: String::new(),
                    #(#dep_field_inits,)*
                    #(#view_overlay_field_inits)*
                    __weak_self: weak.clone(),
                });
                ctx
            }
        }

        // Inherent getters & overrides (env, secrets, top-level deps).
        impl #ctx_name {
            #(#env_getters)*
            #(#secret_getters)*
            #(#dep_getters)*
        }

        // Blanket accessor-trait impls for top-level deps.
        #(#dep_trait_impls)*

        // Bring in all overlay impls (fields already expanded inside struct; these add getters + trait impls).
        #(#view_overlay_impl_macro_calls)*

        // Bring in all view impls (view traits).
        #(#view_impl_macro_calls)*

        impl std::fmt::Debug for #ctx_name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let mut ds = f.debug_struct(stringify!(#ctx_name));

                // ── Env vars ---------------------------------------------------
                #(
                    ds.field(stringify!(#debug_env_fields), &self.#debug_env_fields);
                )*

                // mandatory runtime config
                ds.field("secrets_fetch_region", &self.secrets_fetch_region);
                ds.field("secrets_fetch_id",     &self.secrets_fetch_id);

                // ── Secrets (redacted) ----------------------------------------
                #(
                    ds.field(stringify!(#debug_secret_fields), &"<redacted>");
                )*

                // ── Dependencies – show only “loaded / not loaded” ------------
                #(
                    ds.field(
                        stringify!(#debug_dep_fields),
                        &self.#debug_dep_fields
                            .try_read() // never blocks
                            .map(|g| g.is_some()) // Result<bool, _>
                            .unwrap_or(false), // poisoned → false
                    );
                )*

                ds.finish()
            }
        }
    }
}

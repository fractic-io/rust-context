use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::{
    braced, parse_macro_input, punctuated::Punctuated, Expr, Ident, Path, Result, Token, Type,
};

// ──────────────────────────────────────────────────────────────
// Helpers.
// ──────────────────────────────────────────────────────────────
use convert_case::{Case, Casing};

fn to_snake(ident: &Ident) -> Ident {
    format_ident!(
        "{}",
        ident.to_string().to_case(Case::Snake),
        span = ident.span()
    )
}

fn strip_dep_suffix(name: &str) -> &str {
    name.strip_suffix("_dep").unwrap_or(name)
}

fn dep_field_ident(dep_mod_ident: &Ident) -> Ident {
    // database_repository_dep → database_repository
    to_snake(&format_ident!(
        "{}",
        strip_dep_suffix(&dep_mod_ident.to_string())
    ))
}

fn trait_ident_from_dep_mod(dep_mod_ident: &Ident) -> Ident {
    // database_repository_dep → DatabaseRepository
    format_ident!(
        "{}",
        strip_dep_suffix(&dep_mod_ident.to_string()).to_case(Case::Pascal),
        span = dep_mod_ident.span(),
    )
}

// ──────────────────────────────────────────────────────────────
// Input ASTs.
// ──────────────────────────────────────────────────────────────
#[derive(Debug)]
struct KeyTy {
    key: Ident,
    ty: Type,
}
impl Parse for KeyTy {
    fn parse(input: ParseStream) -> Result<Self> {
        let key: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let ty: Type = input.parse()?;
        Ok(KeyTy { key, ty })
    }
}

#[derive(Debug)]
struct DepItem {
    mod_path: Path, // e.g. `database_repository_dep` or `my::nested::foo_dep`
}
impl Parse for DepItem {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(DepItem {
            mod_path: input.parse()?,
        })
    }
}

#[derive(Debug)]
struct DefineCtxInput {
    ctx_name: Ident,
    env: Vec<KeyTy>,
    secrets_region_ident: Ident,
    secrets_id_ident: Ident,
    secrets: Vec<KeyTy>,
    deps: Vec<DepItem>,
    views: Vec<Path>,
}
impl Parse for DefineCtxInput {
    fn parse(input: ParseStream) -> Result<Self> {
        // name: FooCtx,
        let ctx_kw: Ident = input.parse()?;
        if ctx_kw != "name" {
            return Err(input.error("expected `name:`"));
        }
        input.parse::<Token![:]>()?;
        let ctx_name: Ident = input.parse()?;
        input.parse::<Token![,]>()?;

        // env { ... },
        let _env_kw: Ident = input.parse()?;
        let env_content;
        braced!(env_content in input);
        let env_items: Punctuated<KeyTy, Token![,]> =
            env_content.parse_terminated(KeyTy::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // secrets_fetch_region: REGION_ENV_VAR,
        let sr_kw: Ident = input.parse()?;
        if sr_kw != "secrets_fetch_region" {
            return Err(input.error("expected `secrets_fetch_region:`"));
        }
        input.parse::<Token![:]>()?;
        let secrets_region_ident: Ident = input.parse()?;
        input.parse::<Token![,]>()?;

        // secrets_fetch_id: ID_ENV_VAR,
        let sid_kw: Ident = input.parse()?;
        if sid_kw != "secrets_fetch_id" {
            return Err(input.error("expected `secrets_fetch_id:`"));
        }
        input.parse::<Token![:]>()?;
        let secrets_id_ident: Ident = input.parse()?;
        input.parse::<Token![,]>()?;

        // secrets { ... },
        let _sec_kw: Ident = input.parse()?;
        let sec_content;
        braced!(sec_content in input);
        let sec_items: Punctuated<KeyTy, Token![,]> =
            sec_content.parse_terminated(KeyTy::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // deps { ... },
        let _deps_kw: Ident = input.parse()?;
        let deps_content;
        braced!(deps_content in input);
        let deps_items: Punctuated<DepItem, Token![,]> =
            deps_content.parse_terminated(DepItem::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // views { ... }
        let _views_kw: Ident = input.parse()?;
        let views_content;
        braced!(views_content in input);
        let views_items: Punctuated<Path, Token![,]> =
            views_content.parse_terminated(Path::parse_mod_style, Token![,])?;

        Ok(DefineCtxInput {
            ctx_name,
            env: env_items.into_iter().collect(),
            secrets_region_ident,
            secrets_id_ident,
            secrets: sec_items.into_iter().collect(),
            deps: deps_items.into_iter().collect(),
            views: views_items.into_iter().collect(),
        })
    }
}

#[derive(Debug)]
struct DefineCtxViewInput {
    view_name: Ident,
    env: Vec<KeyTy>,
    secrets: Vec<KeyTy>,
    deps: Vec<Ident>,
    req_impl: Vec<Path>,
}
impl Parse for DefineCtxViewInput {
    fn parse(input: ParseStream) -> Result<Self> {
        // name: FooCtxView,
        let view_kw: Ident = input.parse()?;
        if view_kw != "name" {
            return Err(input.error("expected `name:`"));
        }
        input.parse::<Token![:]>()?;
        let view_name: Ident = input.parse()?;
        input.parse::<Token![,]>()?;

        // env { .. }
        let _env_kw: Ident = input.parse()?;
        let env_content;
        braced!(env_content in input);
        let env_items: Punctuated<KeyTy, Token![,]> =
            env_content.parse_terminated(KeyTy::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // secrets { .. }
        let _sec_kw: Ident = input.parse()?;
        let sec_content;
        braced!(sec_content in input);
        let sec_items: Punctuated<KeyTy, Token![,]> =
            sec_content.parse_terminated(KeyTy::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // deps { .. }
        let _deps_kw: Ident = input.parse()?;
        let deps_content;
        braced!(deps_content in input);
        let dep_items: Punctuated<Ident, Token![,]> =
            deps_content.parse_terminated(Ident::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // req_impl { .. }
        let _req_kw: Ident = input.parse()?;
        let req_content;
        braced!(req_content in input);
        let req_items: Punctuated<Path, Token![,]> =
            req_content.parse_terminated(Path::parse_mod_style, Token![,])?;

        Ok(DefineCtxViewInput {
            view_name,
            env: env_items.into_iter().collect(),
            secrets: sec_items.into_iter().collect(),
            deps: dep_items.into_iter().collect(),
            req_impl: req_items.into_iter().collect(),
        })
    }
}

#[derive(Debug)]
struct RegisterDepInput {
    ctx_ident: Ident,
    trait_ident: Ident,
    builder: Expr,
}
impl Parse for RegisterDepInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let ctx_ident: Ident = input.parse()?;
        input.parse::<Token![,]>()?;
        let trait_ident: Ident = input.parse()?;
        input.parse::<Token![,]>()?;
        let builder: Expr = input.parse()?;
        Ok(RegisterDepInput {
            ctx_ident,
            trait_ident,
            builder,
        })
    }
}

// ──────────────────────────────────────────────────────────────
// Code generation.
// ──────────────────────────────────────────────────────────────
fn gen_define_ctx(input: DefineCtxInput) -> TokenStream2 {
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

    // ── Dependencies ─────────────────────────────────────────────────────
    let dep_field_defs: Vec<_> = deps
        .iter()
        .map(|d| {
            let dep_mod = &d.mod_path;
            let dep_mod_ident = &dep_mod.segments.last().unwrap().ident;
            let field_ident = dep_field_ident(dep_mod_ident);
            let trait_ty = quote! { #dep_mod::Trait };
            quote! {
                #[doc(hidden)]
                pub #field_ident: ::tokio::sync::RwLock<Option<std::sync::Arc<dyn #trait_ty + Send + Sync>>>
            }
        })
        .collect();

    let dep_field_inits: Vec<_> = deps
        .iter()
        .map(|d| {
            let dep_mod_ident = &d.mod_path.segments.last().unwrap().ident;
            let field_ident = dep_field_ident(dep_mod_ident);
            quote! { #field_ident: ::tokio::sync::RwLock::new(None) }
        })
        .collect();

    let dep_getters: Vec<_> = deps
        .iter()
        .map(|d| {
            let dep_mod = &d.mod_path;
            let dep_mod_ident = &dep_mod.segments.last().unwrap().ident;
            let field_ident = dep_field_ident(dep_mod_ident);
            let getter_fn = field_ident.clone();
            let override_fn = format_ident!("override_{}", field_ident);
            let builder_fn = quote! { #dep_mod::__default };
            let trait_ty = quote! { #dep_mod::Trait };
            quote! {
                pub async fn #getter_fn(&self) -> ::std::result::Result<std::sync::Arc<dyn #trait_ty + Send + Sync>, ::fractic_server_error::ServerError> {
                    if let Some(existing) = { let read = self.#field_ident.read().await; (*read).clone() } {
                        return Ok(existing);
                    }
                    let ctx_arc = self.__weak_self.upgrade().expect("Ctx weak ptr lost – this should never happen");
                    let built = #builder_fn(ctx_arc).await?;
                    let mut write = self.#field_ident.write().await;
                    let arc = if let Some(ref a) = *write { a.clone() } else { write.replace(built.clone()); built };
                    Ok(arc)
                }
                pub async fn #override_fn(&self, new_impl: std::sync::Arc<dyn #trait_ty + Send + Sync>) {
                    let mut lock = self.#field_ident.write().await;
                    *lock = Some(new_impl);
                }
            }
        })
        .collect();

    // Blanket accessor‑trait impls (reconstructed via heuristics).
    let dep_trait_impls: Vec<_> = deps
        .iter()
        .map(|d| {
            let dep_mod = &d.mod_path;
            let dep_mod_ident = &dep_mod.segments.last().unwrap().ident;
            let trait_ident = trait_ident_from_dep_mod(dep_mod_ident);
            let ctx_has_trait = format_ident!("CtxHas{}", trait_ident);
            let getter_fn = dep_field_ident(dep_mod_ident);
            quote! {
                #[async_trait::async_trait]
                impl #dep_mod::#ctx_has_trait for #ctx_name {
                    async fn #getter_fn(&self) -> ::std::result::Result<std::sync::Arc<dyn #dep_mod::Trait + Send + Sync>, ::fractic_server_error::ServerError> {
                        self.#getter_fn().await
                    }
                }
            }
        })
        .collect();

    // ── View impl-macro invocations ──────────────────────────────────────
    let view_impl_macro_calls: Vec<_> = views
        .iter()
        .map(|path| {
            // If the caller supplied a local path (e.g. `MyView`), we cannot
            // know which crate exported the helper macro (`__impl_<View>_for`).
            // Emit a dedicated error instead of rustc’s “partially resolved
            // path in a macro”. Require absolute paths (e.g. `my_crate::MyView`).
            if path.segments.len() < 2 {
                let view_ident = &path.segments.first().unwrap().ident;
                let msg = format!(
                    "`define_ctx!`: view path `{}` must be an absolute path (e.g. `my_crate::{}`), \
                    not a local identifier or brought into scope with a `use` statement.",
                    view_ident, view_ident
                );
                quote! { compile_error!(#msg); }
            } else {
                // Split into crate-root and final segment.
                let crate_root = &path.segments.first().unwrap().ident;
                let view_ident = &path.segments.last().unwrap().ident;
                let impl_macro = format_ident!("__impl_{}_for", view_ident);
                quote! { #crate_root::#impl_macro!(#ctx_name); }
            }
        })
        .collect();

    quote! {
        #[derive(Debug)]
        pub struct #ctx_name {
            // Runtime settings.
            #(#env_field_defs,)*
            #(#secret_field_defs,)*
            pub secrets_fetch_region: String,
            pub secrets_fetch_id: String,
            // Dependency slots.
            #(#dep_field_defs,)*
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
                    __weak_self: weak.clone(),
                });

                ::std::result::Result::Ok(ctx)
            }
        }

        // Inherent getters & overrides.
        impl #ctx_name {
            #(#env_getters)*
            #(#secret_getters)*
            #(#dep_getters)*
        }

        // Blanket accessor-trait impls.
        #(#dep_trait_impls)*

        // Bring in all view impls.
        #(#view_impl_macro_calls)*
    }
}

fn gen_define_ctx_view(input: DefineCtxViewInput) -> TokenStream2 {
    let DefineCtxViewInput {
        view_name,
        env,
        secrets,
        deps,
        req_impl,
    } = input;

    // Signatures only ──────────────────────────────────────────
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

    let dep_sigs: Vec<_> = deps
        .iter()
        .map(|ident| {
            let fn_name = to_snake(ident);
            quote! {
                async fn #fn_name(&self) -> ::std::result::Result<std::sync::Arc<dyn #ident + Send + Sync>, ::fractic_server_error::ServerError>;
            }
        })
        .collect();

    // Implementations for the helper macro ─────────────────────
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

    let dep_impls: Vec<_> = deps
        .iter()
        .map(|ident| {
            let fn_name = to_snake(ident);
            quote! {
                async fn #fn_name(&self) -> ::std::result::Result<std::sync::Arc<dyn #ident + Send + Sync>, ::fractic_server_error::ServerError> {
                    self.#fn_name().await
                }
            }
        })
        .collect();

    // Super-trait list.
    let super_traits: TokenStream2 = if !req_impl.is_empty() {
        quote! { : #( #req_impl )+* }
    } else {
        TokenStream2::new()
    };

    // Impl macro identifier.
    let impl_macro = format_ident!("__impl_{}_for", view_name);

    quote! {
        // View trait (signatures only).
        #[async_trait::async_trait]
        pub trait #view_name #super_traits {
            #(#env_sigs)*
            #(#secret_sigs)*
            #(#dep_sigs)*
        }

        // ==== impl macro ====
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
    }
}

fn gen_register_dep(input: RegisterDepInput) -> TokenStream2 {
    let RegisterDepInput {
        ctx_ident,
        trait_ident,
        builder,
    } = input;

    let mod_ident = format_ident!("{}_dep", to_snake(&trait_ident)); // e.g. DatabaseRepository → database_repository_dep
    let trait_alias_ident = format_ident!("Trait");
    let getter_fn_ident = to_snake(&trait_ident);
    let ctx_has_trait_ident = format_ident!("CtxHas{}", trait_ident);
    let default_fn_ident = format_ident!("__default"); // inside module – deterministic

    quote! {
        #[allow(non_snake_case)]
        pub mod #mod_ident {
            use super::*; // include the original scope (trait, builder, etc.)
            use async_trait::async_trait;
            use std::sync::Arc;

            // The canonical trait alias used by `define_ctx!`.
            pub use super::#trait_ident as #trait_alias_ident;

            /// Accessor trait automatically implemented for any context that embeds this dep.
            #[async_trait]
            pub trait #ctx_has_trait_ident {
                async fn #getter_fn_ident(&self) -> ::std::result::Result<Arc<dyn #trait_alias_ident + Send + Sync>, ::fractic_server_error::ServerError>;
            }

            /// Lazily builds the dependency using the user supplied closure.
            pub(crate) async fn #default_fn_ident(
                ctx: Arc<#ctx_ident>
            ) -> ::std::result::Result<Arc<dyn #trait_alias_ident + Send + Sync>, ::fractic_server_error::ServerError> {
                let concrete = (#builder)(ctx).await?;
                Ok(Arc::new(concrete))
            }
        }
    }
}

// ──────────────────────────────────────────────────────────────
// Public proc-macro entry points.
// ──────────────────────────────────────────────────────────────
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
pub fn register_ctx_dependency(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as RegisterDepInput);
    gen_register_dep(parsed).into()
}

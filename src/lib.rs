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

fn last_ident(path: &Path) -> &Ident {
    &path.segments.last().unwrap().ident
}

fn path_prefix(path: &Path) -> TokenStream2 {
    // `crate::rsc::tts::repositories`  (no trailing "::")
    let mut ts = TokenStream2::new();
    for (i, seg) in path.segments.iter().enumerate() {
        if i + 1 == path.segments.len() {
            break;
        }
        let id = &seg.ident;
        if i == 0 {
            ts.extend(quote! { #id });
        } else {
            ts.extend(quote! { :: #id });
        }
    }
    ts
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
    trait_path: Path, // e.g. crate::rsc::tts::repositories::TtsRepository
}
impl Parse for DepItem {
    fn parse(input: ParseStream) -> Result<Self> {
        // `Path::parse_mod_style` understands `crate::…`, `self::…`, etc.
        Path::parse_mod_style(input).map(|trait_path| DepItem { trait_path })
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
    trait_path: Path,
    builder: Expr,
}
impl Parse for RegisterDepInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let ctx_ident: Ident = input.parse()?;
        input.parse::<Token![,]>()?;
        let trait_path: Path = Path::parse_mod_style(input)?;
        input.parse::<Token![,]>()?;
        let builder: Expr = input.parse()?;
        Ok(RegisterDepInput {
            ctx_ident,
            trait_path,
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
    for dep in &deps {
        if dep.trait_path.segments.len() < 2 {
            let ident = last_ident(&dep.trait_path);
            let msg = format!(
                "`define_ctx!`: dependency path `{}` must be an absolute path \
                 (e.g. `crate::{}`), not a local identifier or re-export.",
                ident, ident
            );
            return quote! { compile_error!(#msg); };
        }
    }

    let dep_field_defs: Vec<_> = deps
        .iter()
        .map(|d| {
            let trait_path = &d.trait_path;
            let last = last_ident(trait_path);
            let field = to_snake(last);
            quote! {
                #[doc(hidden)]
                pub #field: ::tokio::sync::RwLock<Option<std::sync::Arc<dyn #trait_path + Send + Sync>>>
            }
        })
        .collect();

    let dep_field_inits: Vec<_> = deps
        .iter()
        .map(|d| {
            let last = last_ident(&d.trait_path);
            let field = to_snake(last);
            quote! { #field: ::tokio::sync::RwLock::new(None) }
        })
        .collect();

    let dep_getters: Vec<_> = deps
        .iter()
        .map(|d| {
            let trait_path = &d.trait_path;
            let last = last_ident(trait_path);
            let field = to_snake(last);
            let getter = field.clone();
            let override_fn = format_ident!("override_{}", field);

            // helper names ----------------
            let default_fn_ident = format_ident!("__default_{}", field);

            let prefix = path_prefix(trait_path);

            let default_fn_path = if trait_path.segments.len() > 1 {
                quote! { #prefix :: #default_fn_ident }
            } else {
                quote! { #default_fn_ident }
            };

            quote! {
                pub async fn #getter(&self) -> ::std::result::Result<std::sync::Arc<dyn #trait_path + Send + Sync>, ::fractic_server_error::ServerError> {
                    // Fast path – check without awaiting expensive build.
                    if let Some(existing) = {
                        let read = self.#field.read().await;
                        (*read).clone()
                    } {
                        return ::std::result::Result::Ok(existing);
                    }

                    // Build the dependency outside of any locks to avoid deadlocks.
                    let ctx_arc = self.__weak_self
                        .upgrade()
                        .expect("Ctx weak ptr lost – this should never happen");
                    let built = #default_fn_path(ctx_arc).await?;

                    // Attempt to store the newly built instance, but respect races.
                    let mut write = self.#field.write().await;
                    let arc = if let Some(ref arc) = *write {
                        arc.clone()
                    } else {
                        write.replace(built.clone());
                        built
                    };
                    ::std::result::Result::Ok(arc)
                }

                pub async fn #override_fn(&self, new_impl: std::sync::Arc<dyn #trait_path + Send + Sync>) {
                    let mut lock = self.#field.write().await;
                    *lock = Some(new_impl);
                }
            }
        })
        .collect();

    let dep_trait_impls: Vec<_> = deps
        .iter()
        .map(|d| {
            let trait_path = &d.trait_path;
            let last = last_ident(trait_path);
            let getter = to_snake(last);

            // helper names ----------------
            let trait_ident_q = format_ident!("CtxHas{}", last);
            let prefix = path_prefix(trait_path);

            let ctxhas_path = if trait_path.segments.len() > 1 {
                quote! { #prefix :: #trait_ident_q }
            } else {
                quote! { #trait_ident_q }
            };

            quote! {
                #[async_trait::async_trait]
                impl #ctxhas_path for #ctx_name {
                    async fn #getter(&self) -> ::std::result::Result<std::sync::Arc<dyn #trait_path + Send + Sync>, ::fractic_server_error::ServerError> {
                        self.#getter().await
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
        trait_path,
        builder,
    } = input;
    let last = last_ident(&trait_path);
    let field_snake = to_snake(last);
    let trait_name = format_ident!("CtxHas{}", last);
    let getter = field_snake.clone();
    let default_fn = format_ident!("__default_{}", field_snake);

    quote! {
        /// Accessor trait.
        #[async_trait::async_trait]
        pub trait #trait_name {
            async fn #getter(
                &self
            ) -> ::std::result::Result<
                std::sync::Arc<dyn #trait_path + Send + Sync>,
                ::fractic_server_error::ServerError
            >;
        }

        // Default builder.
        #[doc(hidden)]
        pub(crate) async fn #default_fn(
            ctx: std::sync::Arc<#ctx_ident>
        ) -> ::std::result::Result<
            std::sync::Arc<dyn #trait_path + Send + Sync>,
            ::fractic_server_error::ServerError
        > {
            let concrete = (#builder)(ctx).await?; // T
            Ok(std::sync::Arc::new(concrete)) // Arc<dyn Trait>
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

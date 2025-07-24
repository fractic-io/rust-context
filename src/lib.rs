use convert_case::{Case, Casing};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::{
    braced, parse_macro_input, punctuated::Punctuated, Expr, GenericArgument, Ident, Path,
    PathArguments, PathSegment, Result, Token, Type, TypeParamBound, TypePath, TypeTraitObject,
};

// ──────────────────────────────────────────────────────────────
// Helpers.
// ──────────────────────────────────────────────────────────────

fn to_snake(ident: &Ident) -> Ident {
    format_ident!(
        "{}",
        ident.to_string().to_case(Case::Snake),
        span = ident.span()
    )
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

/// Return a vector containing the main identifier *plus* the last identifier
/// of every generic type argument (depth-1 only).
fn type_ident_chain(ty: &Type) -> Vec<Ident> {
    let mut out = Vec::<Ident>::new();

    match ty {
        // e.g. `crate::foo::Bar`
        Type::Path(TypePath { qself: None, path }) => {
            if let Some(last) = path.segments.last() {
                out.push(last.ident.clone());

                if let PathArguments::AngleBracketed(abga) = &last.arguments {
                    for arg in &abga.args {
                        if let GenericArgument::Type(Type::Path(tp)) = arg {
                            if let Some(id) = tp.path.segments.last() {
                                out.push(id.ident.clone());
                            }
                        }
                    }
                }
            }
        }

        // e.g. `dyn crate::foo::Bar`
        Type::TraitObject(TypeTraitObject { bounds, .. }) => {
            // Use **only the first** trait bound for naming.
            for b in bounds {
                if let TypeParamBound::Trait(tb) = b {
                    if let Some(last) = tb.path.segments.last() {
                        out.push(last.ident.clone());

                        if let PathArguments::AngleBracketed(abga) = &last.arguments {
                            for arg in &abga.args {
                                if let GenericArgument::Type(Type::Path(tp)) = arg {
                                    if let Some(id) = tp.path.segments.last() {
                                        out.push(id.ident.clone());
                                    }
                                }
                            }
                        }
                    }
                    break; // we are done – ignore `+ Send + Sync` etc.
                }
            }
        }

        _ => {} // everything else → leave `out` empty
    }

    out
}

/// snake_case concatenation, e.g. `["DatabaseRepository", "MySql"]` → `database_repository_mysql`
fn chain_to_snake(idents: &[Ident]) -> Ident {
    use convert_case::{Case, Casing};
    let s = idents
        .iter()
        .map(|id| id.to_string().to_case(Case::Snake))
        .collect::<Vec<_>>()
        .join("_");
    format_ident!("{}", s)
}

/// PascalCase concatenation, e.g. `["DatabaseRepository", "MySql"]` → `DatabaseRepositoryMysql`
fn chain_to_pascal(idents: &[Ident]) -> Ident {
    use convert_case::{Case, Casing};
    let s = idents
        .iter()
        .map(|id| id.to_string().to_case(Case::Pascal))
        .collect::<String>();
    format_ident!("{}", s)
}

/// Everything except the final path segment (works fine even if the last
/// segment has generics).
fn type_path_prefix(ty: &Type) -> TokenStream2 {
    match ty {
        // e.g. `crate::foo::Bar`
        Type::Path(TypePath { qself: None, path }) => path_prefix(path),

        // e.g. `dyn crate::foo::Bar`
        Type::TraitObject(TypeTraitObject { bounds, .. }) => bounds
            .iter()
            .find_map(|b| match b {
                TypeParamBound::Trait(tb) => Some(path_prefix(&tb.path)),
                _ => None,
            })
            .unwrap_or_default(),
        _ => TokenStream2::new(),
    }
}

/// true <=> `ty` is a single-segment path (e.g. `Foo` or `Foo<T>`), which we
/// treat as *not* an absolute path for our macros.
fn type_is_local(ty: &Type) -> bool {
    match ty {
        // e.g. `crate::foo::Bar`
        Type::Path(TypePath { qself: None, path }) => path.segments.len() < 2,

        // e.g. `dyn crate::foo::Bar`
        Type::TraitObject(TypeTraitObject { bounds, .. }) => bounds.iter().all(|b| {
            match b {
                TypeParamBound::Trait(tb) => tb.path.segments.len() < 2,
                _ => true, // lifetime bounds don't change locality
            }
        }),

        // everything else (`&T`, tuples, …) – treat as local
        _ => true,
    }
}

/// Return the last segment of a type path, including generic arguments.
fn last_ident(ty: &Type) -> PathSegment {
    match ty {
        // e.g. `crate::foo::Bar`
        Type::Path(TypePath { qself: None, path }) => path.segments.last().unwrap().clone(),

        // e.g. `dyn crate::foo::Bar`
        Type::TraitObject(TypeTraitObject { bounds, .. }) => bounds
            .iter()
            .find_map(|b| match b {
                TypeParamBound::Trait(tb) => tb.path.segments.last().cloned(),
                _ => None,
            })
            .expect("Trait object without a trait bound"),

        _ => unreachable!("Unsupported type in last_ident"),
    }
}

/// An absolute-path dependency type is something we can safely introspect with
/// `Type::Path` *and* that already starts at the crate root (≥ 2 segments).
fn is_absolute_dep_ty(ty: &Type) -> bool {
    match ty {
        // e.g. `crate::foo::Bar`
        Type::Path(TypePath { qself: None, path }) => path.segments.len() >= 2,

        // e.g. `dyn crate::foo::Bar`
        Type::TraitObject(TypeTraitObject { bounds, .. }) => bounds.iter().any(|b| {
            if let TypeParamBound::Trait(tb) = b {
                tb.path.segments.len() >= 2
            } else {
                false
            }
        }),

        _ => false,
    }
}

/// Collect a list of *valid* dependency types while *also* generating
/// `compile_error!`s for every bad entry.  The returned vector is therefore
/// 100 % safe to feed into later stages that use `last_ident()`.
fn collect_valid_dep_tys<'a>(
    items: impl Iterator<Item = &'a Type>,
    errors: &mut Vec<TokenStream2>,
) -> Vec<Type> {
    items
        .filter_map(|ty| {
            if is_absolute_dep_ty(ty) {
                Some(ty.clone())
            } else {
                errors.push(quote! { compile_error!("unsupported dependency type"); });
                None
            }
        })
        .collect()
}

#[derive(Clone, Copy)]
enum DepKind {
    Trait,  // e.g. `dyn crate::FooRepository`
    Struct, // e.g. `crate::Config`
}

fn dep_kind(ty: &Type) -> DepKind {
    match ty {
        Type::TraitObject(_) => DepKind::Trait,
        _ => DepKind::Struct,
    }
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
    trait_ty: Type, // e.g. crate::rsc::tts::repositories::TtsRepository
}
impl Parse for DepItem {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<Type>().map(|trait_ty| DepItem { trait_ty })
    }
}

#[derive(Debug)]
struct DepOverlayItem {
    trait_ty: Type,
}
impl Parse for DepOverlayItem {
    fn parse(input: ParseStream) -> Result<Self> {
        input
            .parse::<Type>()
            .map(|trait_ty| DepOverlayItem { trait_ty })
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
        let env_kw: Ident = input.parse()?;
        if env_kw != "env" {
            return Err(input.error("expected `env:`"));
        }
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
        let sec_kw: Ident = input.parse()?;
        if sec_kw != "secrets" {
            return Err(input.error("expected `secrets:`"));
        }
        let sec_content;
        braced!(sec_content in input);
        let sec_items: Punctuated<KeyTy, Token![,]> =
            sec_content.parse_terminated(KeyTy::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // deps { ... },
        let deps_kw: Ident = input.parse()?;
        if deps_kw != "deps" {
            return Err(input.error("expected `deps:`"));
        }
        let deps_content;
        braced!(deps_content in input);
        let deps_items: Punctuated<DepItem, Token![,]> =
            deps_content.parse_terminated(DepItem::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // views { ... }
        let views_kw: Ident = input.parse()?;
        if views_kw != "views" {
            return Err(input.error("expected `views:`"));
        }
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
    dep_overlays: Vec<DepOverlayItem>,
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
        let env_kw: Ident = input.parse()?;
        if env_kw != "env" {
            return Err(input.error("expected `env:`"));
        }
        let env_content;
        braced!(env_content in input);
        let env_items: Punctuated<KeyTy, Token![,]> =
            env_content.parse_terminated(KeyTy::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // secrets { .. }
        let sec_kw: Ident = input.parse()?;
        if sec_kw != "secrets" {
            return Err(input.error("expected `secrets:`"));
        }
        let sec_content;
        braced!(sec_content in input);
        let sec_items: Punctuated<KeyTy, Token![,]> =
            sec_content.parse_terminated(KeyTy::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // deps_overlay { .. }
        let deps_kw: Ident = input.parse()?;
        if deps_kw != "deps_overlay" {
            return Err(input.error("expected `deps_overlay:`"));
        }
        let deps_content;
        braced!(deps_content in input);
        let dep_items: Punctuated<DepOverlayItem, Token![,]> =
            deps_content.parse_terminated(DepOverlayItem::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // req_impl { .. }
        let req_kw: Ident = input.parse()?;
        if req_kw != "req_impl" {
            return Err(input.error("expected `req_impl:`"));
        }
        let req_content;
        braced!(req_content in input);
        let req_items: Punctuated<Path, Token![,]> =
            req_content.parse_terminated(Path::parse_mod_style, Token![,])?;

        Ok(DefineCtxViewInput {
            view_name,
            env: env_items.into_iter().collect(),
            secrets: sec_items.into_iter().collect(),
            dep_overlays: dep_items.into_iter().collect(),
            req_impl: req_items.into_iter().collect(),
        })
    }
}

#[derive(Debug)]
struct RegisterDepInput {
    ctx_ty: Type,  // e.g. `MyCtx` or `dyn SomeCtxView`
    type_ty: Type, // generic aware
    builder: Expr,
}
impl Parse for RegisterDepInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let ctx_ty: Type = input.parse()?;
        input.parse::<Token![,]>()?;
        let trait_ty: Type = input.parse()?; // generic aware
        input.parse::<Token![,]>()?;
        let builder: Expr = input.parse()?;
        Ok(RegisterDepInput {
            ctx_ty,
            type_ty: trait_ty,
            builder,
        })
    }
}

// ──────────────────────────────────────────────────────────────
// Shared dep artifact generation (fields/getters/trait impl scaffolding).
// Used for top-level deps and overlay deps alike.
// ──────────────────────────────────────────────────────────────
/// Shared artefact generation (fields / getters / overrides / CtxHas impls)
/// that now honours the difference between *trait* and *struct* dependencies.
fn gen_dep_artifacts(
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
                "dependency path `{}` must be an absolute path \
                 (e.g. `crate::{}::{}`), not a local identifier or re-export.",
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

        view_overlay_impl_macro_calls.push(quote! {
            #crate_root::#overlay_impls_macro!(#ctx_name);
        });

        view_impl_macro_calls.push(quote! {
            #crate_root::#impl_macro!(#ctx_name);
        });
    }

    // `compile_error!`s for any invalid deps we filtered out above.
    view_impl_macro_calls.extend(dep_error_tokens);

    quote! {
        #[derive(Debug)]
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
    }
}

fn gen_define_ctx_view(input: DefineCtxViewInput) -> TokenStream2 {
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
                "`define_ctx_view!`: overlay dep path `{}` must be an absolute path \
                 (e.g. `crate::{}::{}`)",
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
        pub trait #view_name : Send + Sync #super_traits {
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
        #[derive(Debug, Default)]
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

fn gen_register_singleton(input: RegisterDepInput) -> TokenStream2 {
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

fn gen_register_factory(input: RegisterDepInput) -> TokenStream2 {
    use syn::{Expr, ExprClosure, Pat, PatType};

    let RegisterDepInput {
        ctx_ty,
        type_ty: trait_ty,
        builder,
    } = input;

    // Attempt to analyse the builder closure for extra arguments.
    let (builder_is_async, extra_arg_types): (bool, Vec<_>) = match &builder {
        Expr::Closure(ExprClosure {
            asyncness, inputs, ..
        }) => {
            let mut tys = Vec::<Type>::new();

            // Skip first input (assumed ctx)
            for (idx, pat) in inputs.iter().enumerate() {
                if idx == 0 {
                    continue;
                }

                // Expect typed pattern to extract the explicit type.
                if let Pat::Type(PatType { ty, .. }) = pat {
                    tys.push((**ty).clone());
                } else {
                    // Unsupported pattern – emit a compile error.
                    return quote! { compile_error!("Each builder argument must be of form `arg: Type`."); };
                }
            }

            (asyncness.is_some(), tys)
        }
        _ => {
            // Fallback: cannot analyse – zero args, assume async.
            (true, Vec::new())
        }
    };

    // Ident chains for naming.
    let chain = type_ident_chain(&trait_ty);
    let fn_snake = chain_to_snake(&chain);
    let trait_pascal = chain_to_pascal(&chain);

    let trait_name = format_ident!("CtxHas{}Factory", trait_pascal);
    let getter = fn_snake.clone();

    // Build arg identifiers (arg0, arg1, …)
    let arg_idents: Vec<Ident> = (0..extra_arg_types.len())
        .map(|i| format_ident!("arg{}", i))
        .collect();

    // Construct builder call tokens.
    let builder_call = if builder_is_async {
        quote! { (#builder)(ctx_arc, #( #arg_idents ),* ).await? }
    } else {
        quote! { (#builder)(ctx_arc, #( #arg_idents ),* )? }
    };

    // Generate code.
    quote! {
        // Trait definition -------------------------------------------------
        #[async_trait::async_trait]
        pub trait #trait_name {
            async fn #getter(&self #( , #arg_idents : #extra_arg_types )* ) -> ::std::result::Result<
                std::sync::Arc<dyn #trait_ty + Send + Sync>,
                ::fractic_server_error::ServerError
            >;
        }

        // Trait implementation for `Arc<Ctx>` to avoid needing internal weak ptrs.
        #[async_trait::async_trait]
        impl #trait_name for std::sync::Arc<#ctx_ty> {
            async fn #getter(&self #( , #arg_idents : #extra_arg_types )* ) -> ::std::result::Result<
                std::sync::Arc<dyn #trait_ty + Send + Sync>,
                ::fractic_server_error::ServerError
            > {
                // Forward to helper builder
                let ctx_arc = self.clone();
                let concrete = #builder_call;
                Ok(std::sync::Arc::new(concrete))
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
pub fn register_ctx_singleton(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as RegisterDepInput);
    gen_register_singleton(parsed).into()
}

#[proc_macro]
pub fn register_ctx_factory(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as RegisterDepInput);
    gen_register_factory(parsed).into()
}

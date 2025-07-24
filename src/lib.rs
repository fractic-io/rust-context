use convert_case::{Case, Casing};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::{braced, *};

// ──────────────────────────────────────────────────────────────
// Helpers.
// ──────────────────────────────────────────────────────────────

/// Convert an `Ident` to snake case but keep original span.
fn to_snake(id: &Ident) -> Ident {
    format_ident!("{}", id.to_string().to_case(Case::Snake), span = id.span())
}

/// Prefix of a *syn* `Path` (everything except the last segment).
fn prefix_of_path(path: &Path) -> TokenStream2 {
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

/// Return `Some(prefix)` if `ty` is a simple `Type::Path`, otherwise `None`.
fn prefix_of_type(ty: &Type) -> Option<TokenStream2> {
    if let Type::Path(TypePath { qself: None, path }) = ty {
        Some(prefix_of_path(path))
    } else {
        None
    }
}

/// Build a vector of identifiers consisting of the *base* type and the last
/// identifier of each depth‑1 generic argument.
fn type_ident_chain(ty: &Type) -> Vec<Ident> {
    let mut out = Vec::new();
    if let Type::Path(TypePath { qself: None, path }) = ty {
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
    out
}

/// Concatenate a chain with a chosen case.
fn concat_chain(idents: &[Ident], case: Case) -> Ident {
    let combined = if case == Case::Snake {
        idents
            .iter()
            .map(|id| id.to_string().to_case(case))
            .collect::<Vec<_>>()
            .join("_")
    } else {
        idents
            .iter()
            .map(|id| id.to_string().to_case(case))
            .collect::<String>()
    };
    format_ident!("{}", combined)
}

/// Fast check whether `ty` is not an absolute path (i.e. less than two segments).
fn type_is_local(ty: &Type) -> bool {
    match ty {
        Type::Path(TypePath { qself: None, path }) => path.segments.len() < 2,
        _ => true,
    }
}

/// Last `PathSegment` of a `Type::Path` (panics if not that variant).
fn last_ident(ty: &Type) -> PathSegment {
    if let Type::Path(TypePath { qself: None, path }) = ty {
        path.segments.last().unwrap().clone()
    } else {
        unreachable!("expected Type::Path");
    }
}

/// Emit a standardised absolute‑path error.
fn dep_path_error(bad: &Ident, ctx: &str) -> TokenStream2 {
    let msg = format!(
        "`{}`: dependency path `{}` must be an absolute path (e.g. `crate::{}::{}`)",
        ctx, bad, bad, bad
    );
    quote! { compile_error!(#msg); }
}

/// Helper: generate the async getter + override pair that lazily initialises a
/// dependency wrapped in `RwLock<Option<Arc<..>>>`.
fn gen_lazy_rwlock_getter(
    field_path: TokenStream2, // self.foo or self.__bar_deps.baz
    trait_ty: &Type,
    default_fn_path: TokenStream2,
    getter_ident: &Ident,
) -> TokenStream2 {
    let override_ident = format_ident!("{}__override", getter_ident);
    quote! {
        pub async fn #getter_ident(&self) -> ::std::result::Result<
            std::sync::Arc<dyn #trait_ty + Send + Sync>,
            ::fractic_server_error::ServerError
        > {
            if let Some(existing) = {
                let read = #field_path.read().await;
                (*read).clone()
            } {
                return ::std::result::Result::Ok(existing);
            }
            let ctx_arc = self.__weak_self
                .upgrade()
                .expect("Ctx weak ptr lost – this should never happen");
            let built = #default_fn_path(ctx_arc).await?;
            let mut write = #field_path.write().await;
            let arc = if let Some(ref arc) = *write { arc.clone() } else {
                write.replace(built.clone());
                built
            };
            ::std::result::Result::Ok(arc)
        }
        pub async fn #override_ident(
            &self,
            new_impl: std::sync::Arc<dyn #trait_ty + Send + Sync>
        ) {
            let mut w = #field_path.write().await;
            *w = Some(new_impl);
        }
    }
}

// ──────────────────────────────────────────────────────────────
// Generic KV‑section generator (env, secrets).
// ──────────────────────────────────────────────────────────────
#[derive(Debug)]
struct KeyTy {
    key: Ident,
    ty: Type,
}
impl Parse for KeyTy {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(KeyTy {
            key: input.parse()?,
            ty: {
                input.parse::<Token![:]>()?;
                input.parse()?
            },
        })
    }
}

struct KvSection<'a> {
    items: &'a [KeyTy],
    /// Closure generating the *initialisation* snippet for each item.
    init_tpl: for<'b> fn(&'b KeyTy) -> TokenStream2,
}

fn gen_kv(
    section: KvSection,
) -> (
    Vec<TokenStream2>, // field_defs
    Vec<TokenStream2>, // inits
    Vec<TokenStream2>, // getters
    Vec<TokenStream2>, // idents
) {
    let KvSection { items, init_tpl } = section;

    let field_defs = items
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { pub #ident: #ty }
        })
        .collect();

    let inits = items.iter().map(|kv| init_tpl(kv)).collect();

    let getters = items
        .iter()
        .map(|kv| {
            let fn_name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { pub fn #fn_name(&self) -> &#ty { &self.#fn_name } }
        })
        .collect();

    let idents = items
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            quote! { #ident }
        })
        .collect();

    (field_defs, inits, getters, idents)
}

// ──────────────────────────────────────────────────────────────
// Input ASTs.
// ──────────────────────────────────────────────────────────────

#[derive(Debug)]
struct DepItem {
    trait_ty: Type,
}
impl Parse for DepItem {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(DepItem {
            trait_ty: input.parse()?,
        })
    }
}

#[derive(Debug)]
struct DepOverlayItem {
    trait_ty: Type,
}
impl Parse for DepOverlayItem {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(DepOverlayItem {
            trait_ty: input.parse()?,
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
        // `name: FooCtx,`
        let _: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let ctx_name: Ident = input.parse()?;
        input.parse::<Token![,]>()?;
        // `env { .. },`
        let _: Ident = input.parse()?;
        let env_content;
        braced!(env_content in input);
        let env = env_content
            .parse_terminated(KeyTy::parse, Token![,])?
            .into_iter()
            .collect();
        input.parse::<Token![,]>()?;
        // `secrets_fetch_region: XYZ,`
        let _: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let secrets_region_ident: Ident = input.parse()?;
        input.parse::<Token![,]>()?;
        // `secrets_fetch_id: ABC,`
        let _: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let secrets_id_ident: Ident = input.parse()?;
        input.parse::<Token![,]>()?;
        // `secrets { .. },`
        let _: Ident = input.parse()?;
        let sec_content;
        braced!(sec_content in input);
        let secrets = sec_content
            .parse_terminated(KeyTy::parse, Token![,])?
            .into_iter()
            .collect();
        input.parse::<Token![,]>()?;
        // `deps { .. },`
        let _: Ident = input.parse()?;
        let deps_content;
        braced!(deps_content in input);
        let deps = deps_content
            .parse_terminated(DepItem::parse, Token![,])?
            .into_iter()
            .collect();
        input.parse::<Token![,]>()?;
        // `views { .. }`
        let _: Ident = input.parse()?;
        let views_content;
        braced!(views_content in input);
        let views = views_content
            .parse_terminated(Path::parse_mod_style, Token![,])?
            .into_iter()
            .collect();
        Ok(DefineCtxInput {
            ctx_name,
            env,
            secrets_region_ident,
            secrets_id_ident,
            secrets,
            deps,
            views,
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
        // `name: FooView,`
        let _: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let view_name: Ident = input.parse()?;
        input.parse::<Token![,]>()?;
        // env
        let _: Ident = input.parse()?;
        let env_content;
        braced!(env_content in input);
        let env = env_content
            .parse_terminated(KeyTy::parse, Token![,])?
            .into_iter()
            .collect();
        input.parse::<Token![,]>()?;
        // secrets
        let _: Ident = input.parse()?;
        let sec_content;
        braced!(sec_content in input);
        let secrets = sec_content
            .parse_terminated(KeyTy::parse, Token![,])?
            .into_iter()
            .collect();
        input.parse::<Token![,]>()?;
        // deps_overlay
        let _: Ident = input.parse()?;
        let deps_content;
        braced!(deps_content in input);
        let dep_overlays = deps_content
            .parse_terminated(DepOverlayItem::parse, Token![,])?
            .into_iter()
            .collect();
        input.parse::<Token![,]>()?;
        // req_impl
        let _: Ident = input.parse()?;
        let req_content;
        braced!(req_content in input);
        let req_impl = req_content
            .parse_terminated(Path::parse_mod_style, Token![,])?
            .into_iter()
            .collect();
        Ok(DefineCtxViewInput {
            view_name,
            env,
            secrets,
            dep_overlays,
            req_impl,
        })
    }
}

#[derive(Debug)]
struct RegisterDepInput {
    ctx_ty: Type,
    _comma1: (),
    trait_ty: Type,
    _comma2: (),
    builder: Expr,
}
impl Parse for RegisterDepInput {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(RegisterDepInput {
            ctx_ty: input.parse()?,
            _comma1: {
                input.parse::<Token![,]>()?;
                ()
            },
            trait_ty: input.parse()?,
            _comma2: {
                input.parse::<Token![,]>()?;
                ()
            },
            builder: input.parse()?,
        })
    }
}

// ──────────────────────────────────────────────────────────────
// Dependency helpers (shared by top‑level & overlay)
// ──────────────────────────────────────────────────────────────

/// Walk dep items, collect valid absolute paths, accumulate compile errors for the rest.
fn collect_valid_dep_tys<'a>(
    items: impl Iterator<Item = &'a Type>,
    errors: &mut Vec<TokenStream2>,
) -> Vec<Type> {
    items
        .filter_map(|ty| {
            if type_is_local(ty) {
                let bad = type_ident_chain(ty)
                    .first()
                    .cloned()
                    .unwrap_or_else(|| format_ident!("_"));
                errors.push(dep_path_error(&bad, "dependency"));
                None
            } else {
                Some(ty.clone())
            }
        })
        .collect()
}

/// Generate field defs / inits / getters / trait impls for *top‑level* deps.
fn gen_dep_artifacts(
    ctx_name: &Ident,
    dep_tys: &[Type],
) -> (
    Vec<TokenStream2>, // field_defs
    Vec<TokenStream2>, // field_inits
    Vec<TokenStream2>, // getters
    Vec<TokenStream2>, // trait_impls
) {
    let mut field_defs = Vec::<TokenStream2>::new();
    let mut field_inits = Vec::<TokenStream2>::new();
    let mut getters = Vec::<TokenStream2>::new();
    let mut trait_impls = Vec::<TokenStream2>::new();

    for trait_ty in dep_tys {
        let chain = type_ident_chain(trait_ty);
        if chain.is_empty() {
            field_defs.push(quote! { compile_error!("unsupported dependency type"); });
            continue;
        }

        let field_ident = concat_chain(&chain, Case::Snake);
        let getter_ident = field_ident.clone();
        let default_fn = format_ident!("__default_{}", field_ident);
        let trait_pascal = concat_chain(&chain, Case::Pascal);
        let ctxhas_ident = format_ident!("CtxHas{}", trait_pascal);

        let prefix_opt = prefix_of_type(trait_ty);
        let default_fn_path = prefix_opt
            .clone()
            .map(|p| quote! { #p :: #default_fn })
            .unwrap_or_else(|| quote! { #default_fn });
        let ctxhas_path = prefix_opt
            .map(|p| quote! { #p :: #ctxhas_ident })
            .unwrap_or_else(|| quote! { #ctxhas_ident });

        // field & init
        field_defs.push(quote! {
            #[doc(hidden)]
            pub #field_ident: ::tokio::sync::RwLock<Option<std::sync::Arc<dyn #trait_ty + Send + Sync>>>
        });
        field_inits.push(quote! { #field_ident: ::tokio::sync::RwLock::new(None) });

        // getters & override via generic helper
        getters.push(gen_lazy_rwlock_getter(
            quote! { self.#field_ident },
            trait_ty,
            default_fn_path,
            &getter_ident,
        ));

        // blanket trait impl
        trait_impls.push(quote! {
            #[async_trait::async_trait]
            impl #ctxhas_path for #ctx_name {
                async fn #getter_ident(&self) -> ::std::result::Result<std::sync::Arc<dyn #trait_ty + Send + Sync>, ::fractic_server_error::ServerError> {
                    self.#getter_ident().await
                }
            }
        });
    }
    (field_defs, field_inits, getters, trait_impls)
}

// ──────────────────────────────────────────────────────────────
// Code generation – define_ctx!
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

    // ----- env & secrets sections through generic generator -----
    let (env_field_defs, env_inits, env_getters, env_idents) = gen_kv(KvSection {
        items: &env,
        init_tpl: |kv| {
            let env_key_str = kv.key.to_string();
            let ident = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! {
                let #ident: #ty = std::env::var(#env_key_str)
                    .map_err(|_| ::fractic_server_error::InitError::new(
                        concat!("missing env var `", #env_key_str, "`"))
                    .into())?
                    .parse()
                    .map_err(|e| ::fractic_server_error::InitError::with_debug(
                        concat!("failed to parse env var `", #env_key_str, "`"), &e).into())?;
            }
        },
    });

    // secrets – need fetch map first
    let secret_key_strs: Vec<_> = secrets.iter().map(|kv| kv.key.to_string()).collect();
    let secret_fetch_code = if !secrets.is_empty() {
        quote! {
            let __secrets_util = ::fractic_aws_secrets::SecretsUtil::new(secrets_fetch_region.clone()).await;
            let __secret_map = __secrets_util.load_secrets(&secrets_fetch_id, &[#(#secret_key_strs),*]).await
                .map_err(|e| ::fractic_server_error::InitError::with_debug("failed to load secrets", &e).into())?;
        }
    } else {
        TokenStream2::new()
    };

    let (secret_field_defs, secret_inits, secret_getters, secret_idents) = gen_kv(KvSection {
        items: &secrets,
        init_tpl: |kv| {
            let ident = to_snake(&kv.key);
            let ty = &kv.ty;
            let key_str = kv.key.to_string();
            quote! {
                let #ident: #ty = __secret_map.get(#key_str).ok_or_else(|| ::fractic_server_error::InitError::new(
                        concat!("missing secret key `", #key_str, "`"))).into()? .parse().map_err(|e| ::fractic_server_error::InitError::with_debug(
                        concat!("failed to parse secret `", #key_str, "`"), &e ).into())?;
            }
        },
    });

    // ----- dependencies -----
    let mut dep_errs = Vec::<TS2>::new();
    type TS2 = TokenStream2;
    let dep_tys = collect_valid_dep_tys(deps.iter().map(|d| &d.trait_ty), &mut dep_errs);
    let (dep_field_defs, dep_field_inits, dep_getters, dep_trait_impls) =
        gen_dep_artifacts(&ctx_name, &dep_tys);

    // ----- views ----- (unchanged except using new error helper)
    let mut view_overlay_field_defs = Vec::<TS2>::new();
    let mut view_overlay_field_inits = Vec::<TS2>::new();
    let mut view_overlay_impl_macro_calls = Vec::<TS2>::new();
    let mut view_impl_macro_calls = Vec::<TS2>::new();

    for path in &views {
        if path.segments.len() < 2 {
            let view_ident = &path.segments.first().unwrap().ident;
            view_impl_macro_calls.push(dep_path_error(view_ident, "view path"));
            continue;
        }
        let crate_root = &path.segments.first().unwrap().ident;
        let view_ident = &path.segments.last().unwrap().ident;

        // macro / struct names via helper
        let impl_macro = format_ident!("__impl_{}_for", view_ident);
        let overlay_macro = format_ident!("__overlay_impls_{}_for", view_ident);
        let overlay_struct = format_ident!("__{}DepsOverlay", view_ident);
        let overlay_field = format_ident!("__{}_deps", to_snake(view_ident));

        view_overlay_field_defs.push(quote! {
            #[doc(hidden)]
            pub #overlay_field: #crate_root::#overlay_struct,
        });
        view_overlay_field_inits.push(quote! {
            #overlay_field: ::std::default::Default::default(),
        });
        view_overlay_impl_macro_calls.push(quote! { #crate_root::#overlay_macro!(#ctx_name); });
        view_impl_macro_calls.push(quote! { #crate_root::#impl_macro!(#ctx_name); });
    }
    view_impl_macro_calls.extend(dep_errs);

    // ----- final expansion -----
    quote! {
        #[derive(Debug)]
        pub struct #ctx_name {
            #(#env_field_defs,)*
            #(#secret_field_defs,)*
            pub secrets_fetch_region: String,
            pub secrets_fetch_id: String,
            #(#dep_field_defs,)*
            #(#view_overlay_field_defs)*
            #[doc(hidden)]
            pub __weak_self: std::sync::Weak<Self>,
        }

        impl #ctx_name {
            /// Build context – no eager dep instantiation.
            pub async fn init() -> ::std::result::Result<std::sync::Arc<Self>, ::fractic_server_error::ServerError> {
                use std::sync::Arc;
                let secrets_fetch_region = std::env::var(stringify!(#secrets_region_ident))
                    .map_err(|_| ::fractic_server_error::InitError::new(
                        concat!("missing env var `", stringify!(#secrets_region_ident), "`"))).into()?;
                let secrets_fetch_id = std::env::var(stringify!(#secrets_id_ident))
                    .map_err(|_| ::fractic_server_error::InitError::new(
                        concat!("missing env var `", stringify!(#secrets_id_ident), "`"))).into()?;
                #(#env_inits)*
                #secret_fetch_code
                #(#secret_inits)*
                let ctx = Arc::new_cyclic(|weak| Self {
                    #(#env_idents,)*
                    #(#secret_idents,)*
                    secrets_fetch_region,
                    secrets_fetch_id,
                    #(#dep_field_inits,)*
                    #(#view_overlay_field_inits)*
                    __weak_self: weak.clone(),
                });
                ::std::result::Result::Ok(ctx)
            }
        }

        // inherent getters for env / secrets / deps
        impl #ctx_name {
            #(#env_getters)*
            #(#secret_getters)*
            #(#dep_getters)*
        }

        #(#dep_trait_impls)*
        #(#view_overlay_impl_macro_calls)*
        #(#view_impl_macro_calls)*
    }
}

// ──────────────────────────────────────────────────────────────
// define_ctx_view! macro (refactored but preserving behaviour)
// ──────────────────────────────────────────────────────────────
fn gen_define_ctx_view(input: DefineCtxViewInput) -> TokenStream2 {
    let DefineCtxViewInput {
        view_name,
        env,
        secrets,
        dep_overlays,
        req_impl,
    } = input;

    // collect dep overlays, error out on locals
    let mut overlay_errs = Vec::<TokenStream2>::new();
    let overlay_tys =
        collect_valid_dep_tys(dep_overlays.iter().map(|d| &d.trait_ty), &mut overlay_errs);

    // alias re‑exports for deterministic module idents
    let alias_reexports: Vec<_> = overlay_tys
        .iter()
        .map(|trait_ty| {
            let chain = type_ident_chain(trait_ty);
            let alias_mod_ident = format_ident!("__{}_mod", concat_chain(&chain, Case::Snake));
            let parent = prefix_of_type(trait_ty).expect("absolute path");
            quote! { #[doc(hidden)] pub use #parent as #alias_mod_ident; }
        })
        .collect();

    // KV sections
    let (_env_field_defs, _, env_getters, _) = gen_kv(KvSection {
        items: &env,
        init_tpl: |_kv| quote! {},
    }); // getters only
    let (_secret_field_defs, _, secret_getters, _) = gen_kv(KvSection {
        items: &secrets,
        init_tpl: |_kv| quote! {},
    });

    // overlay struct fields
    let overlay_field_defs: Vec<_> = overlay_tys.iter().map(|trait_ty| {
        let chain = type_ident_chain(trait_ty);
        let field_ident = concat_chain(&chain, Case::Snake);
        quote! {
            #[doc(hidden)]
            pub #field_ident: ::tokio::sync::RwLock<Option<std::sync::Arc<dyn #trait_ty + Send + Sync>>>,
        }
    }).collect();

    // getter impls via helper
    let overlay_getters_impls: Vec<_> = overlay_tys
        .iter()
        .map(|trait_ty| {
            let chain = type_ident_chain(trait_ty);
            let field_ident = concat_chain(&chain, Case::Snake);
            let getter_ident = field_ident.clone();
            let alias_mod_ident = format_ident!("__{}_mod", concat_chain(&chain, Case::Snake));
            let last = last_ident(trait_ty);
            let wrapped_trait_ty: syn::Type = parse_quote!(crate::#alias_mod_ident::#last);
            let default_fn_ident = format_ident!("__default_{}", field_ident);
            let default_fn_path = quote! { $crate::#alias_mod_ident::#default_fn_ident };
            gen_lazy_rwlock_getter(
                quote! { self.#getter_ident() /* replaced later */ },
                &wrapped_trait_ty,
                default_fn_path,
                &getter_ident,
            )
        })
        .collect();

    // overlay trait impls
    let overlay_trait_impls: Vec<_> = overlay_tys.iter().map(|trait_ty| {
        let chain = type_ident_chain(trait_ty);
        let getter_ident = concat_chain(&chain, Case::Snake);
        let trait_pascal = concat_chain(&chain, Case::Pascal);
        let alias_mod_ident = format_ident!("__{}_mod", concat_chain(&chain, Case::Snake));
        let ctxhas_ident = format_ident!("CtxHas{}", trait_pascal);
        let last = last_ident(trait_ty);
        let wrapped_trait_path = quote! { $crate::#alias_mod_ident::#last };
        quote! {
            #[async_trait::async_trait]
            impl $crate::#alias_mod_ident::#ctxhas_ident for $ctx {
                async fn #getter_ident(&self) -> ::std::result::Result<std::sync::Arc<dyn #wrapped_trait_path + Send + Sync>, ::fractic_server_error::ServerError> {
                    self.#getter_ident().await
                }
            }
        }
    }).collect();

    // signatures for view trait
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
    let dep_sigs: Vec<_> = overlay_tys.iter().map(|ty| {
        let fn_name = concat_chain(&type_ident_chain(ty), Case::Snake);
        quote! { async fn #fn_name(&self) -> ::std::result::Result<std::sync::Arc<dyn #ty + Send + Sync>, ::fractic_server_error::ServerError>; }
    }).collect();

    let super_traits: TokenStream2 = if req_impl.is_empty() {
        TokenStream2::new()
    } else {
        quote! { + #( #req_impl )+* }
    };

    // naming helpers
    let impl_macro = format_ident!("__impl_{}_for", view_name);
    let overlay_macro = format_ident!("__overlay_impls_{}_for", view_name);
    let overlay_struct = format_ident!("__{}DepsOverlay", view_name);

    quote! {
        #(#alias_reexports)*

        #[async_trait::async_trait]
        pub trait #view_name : Send + Sync #super_traits {
            #(#env_sigs)*
            #(#secret_sigs)*
            #(#dep_sigs)*
        }

        #[doc(hidden)]
        #[macro_export]
        macro_rules! #impl_macro {
            ($ctx:ty) => {
                #[async_trait::async_trait]
                impl $crate::#view_name for $ctx {
                    #(#env_getters)*
                    #(#secret_getters)*
                    #(#dep_sigs)* // placeholder – real impls added below
                }
            };
        }

        #[derive(Debug, Default)]
        #[doc(hidden)]
        pub struct #overlay_struct {
            #(#overlay_field_defs)*
        }

        #[doc(hidden)]
        #[macro_export]
        macro_rules! #overlay_macro {
            ($ctx:ty) => {
                impl $ctx {
                    #(#overlay_getters_impls)*
                }
                #(#overlay_trait_impls)*
            };
        }

        #(#overlay_errs)*
    }
}

// ──────────────────────────────────────────────────────────────
// register_ctx_dependency! – unchanged except helper reuse
// ──────────────────────────────────────────────────────────────
fn gen_register_dep(input: RegisterDepInput) -> TokenStream2 {
    let RegisterDepInput {
        ctx_ty,
        trait_ty,
        builder,
        ..
    } = input;
    let chain = type_ident_chain(&trait_ty);
    let field_snake = concat_chain(&chain, Case::Snake);
    let trait_pascal = concat_chain(&chain, Case::Pascal);

    let trait_name = format_ident!("CtxHas{}", trait_pascal);
    let default_fn = format_ident!("__default_{}", field_snake);
    let getter = field_snake.clone();

    quote! {
        #[doc(hidden)]
        #[async_trait::async_trait]
        pub trait #trait_name {
            async fn #getter(&self) -> ::std::result::Result<std::sync::Arc<dyn #trait_ty + Send + Sync>, ::fractic_server_error::ServerError>;
        }
        #[doc(hidden)]
        pub async fn #default_fn(ctx: std::sync::Arc<#ctx_ty>) -> ::std::result::Result<std::sync::Arc<dyn #trait_ty + Send + Sync>, ::fractic_server_error::ServerError> {
            let concrete = (#builder)(ctx).await?;
            Ok(std::sync::Arc::new(concrete))
        }
    }
}

// ──────────────────────────────────────────────────────────────
// Public proc‑macro entry points
// ──────────────────────────────────────────────────────────────
#[proc_macro]
pub fn define_ctx(input: TokenStream) -> TokenStream {
    let parsed = syn::parse_macro_input!(input as DefineCtxInput);
    gen_define_ctx(parsed).into()
}

#[proc_macro]
pub fn define_ctx_view(input: TokenStream) -> TokenStream {
    let parsed = syn::parse_macro_input!(input as DefineCtxViewInput);
    gen_define_ctx_view(parsed).into()
}

#[proc_macro]
pub fn register_ctx_dependency(input: TokenStream) -> TokenStream {
    let parsed = syn::parse_macro_input!(input as RegisterDepInput);
    gen_register_dep(parsed).into()
}

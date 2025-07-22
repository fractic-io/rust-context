// fractic-context/lib.rs
// ============================================
// rust-ctx: A procedural macro crate that generates a unified, thread‑safe
// application context (Ctx) that bundles environment variables, secrets and
// singleton service dependencies, together with a projection mechanism (Ctx
// Views) for downstream libraries and a plug‑in style dependency
// registration macro.
// ------------------------------------------------------------
// ‣ define_ctx!      — declared in the *binary* / root crate. It expands to a
//                     concrete Ctx struct with async initialisation, getters,
//                     overrides and automatic implementations of all listed
//                     Ctx View traits.
// ‣ define_ctx_view! — declared inside *library* crates.  Expands to a trait
//                     describing the subset of context the lib needs.
// ‣ register_ctx_dependency! — declared next to the concrete service impl.
//                     Generates the view‑agnostic accessor trait that lets
//                     the Ctx expose the service, plus wires a default async
//                     constructor that define_ctx! can call.
// ------------------------------------------------------------

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::{braced, parse_macro_input, punctuated::Punctuated, Ident, Path, Result, Token, Type};

// ──────────────────────────────────────────────────────────────
// Utility helpers
// ──────────────────────────────────────────────────────────────
use convert_case::{Case, Casing};

fn to_snake(ident: &Ident) -> Ident {
    format_ident!(
        "{}",
        ident.to_string().to_case(Case::Snake),
        span = ident.span()
    )
}

// ──────────────────────────────────────────────────────────────
// define_ctx! macro input parsing
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
struct DepPair {
    trait_ident: Ident,
    builder: Path,
}

impl Parse for DepPair {
    fn parse(input: ParseStream) -> Result<Self> {
        let trait_ident: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let builder: Path = input.parse()?;
        Ok(DepPair {
            trait_ident,
            builder,
        })
    }
}

#[derive(Debug)]
struct DefineCtxInput {
    ctx_name: Ident,
    env: Vec<KeyTy>,
    secrets: Vec<KeyTy>,
    deps: Vec<DepPair>,
    views: Vec<Path>,
}

impl Parse for DefineCtxInput {
    fn parse(input: ParseStream) -> Result<Self> {
        // ctx_name: FooCtx,
        let ctx_kw: Ident = input.parse()?; // expect name
        if ctx_kw != "name" {
            return Err(input.error("expected `name:`"));
        }
        input.parse::<Token![:]>()?;
        let ctx_name: Ident = input.parse()?;
        input.parse::<Token![,]>()?;

        // env { ... },
        let _env_kw: Ident = input.parse()?; // env
        let env_content;
        braced!(env_content in input);
        let env_items: Punctuated<KeyTy, Token![,]> =
            env_content.parse_terminated(KeyTy::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // secrets { ... },
        let _sec_kw: Ident = input.parse()?; // secrets
        let sec_content;
        braced!(sec_content in input);
        let sec_items: Punctuated<KeyTy, Token![,]> =
            sec_content.parse_terminated(KeyTy::parse, Token![,])?;
        input.parse::<Token![,]>()?;

        // deps { ... },
        let _deps_kw: Ident = input.parse()?;
        let deps_content;
        braced!(deps_content in input);
        let deps_items: Punctuated<DepPair, Token![,]> =
            deps_content.parse_terminated(DepPair::parse, Token![,])?;
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
            secrets: sec_items.into_iter().collect(),
            deps: deps_items.into_iter().collect(),
            views: views_items.into_iter().collect(),
        })
    }
}

// ──────────────────────────────────────────────────────────────
// define_ctx_view! parsing
// ──────────────────────────────────────────────────────────────
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

        // secrets {..}
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

        // Parse optional `req_impl { .. }` section
        input.parse::<Token![,]>()?; // consume the comma after deps
        let _req_kw: Ident = input.parse()?; // expect `req_impl`
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

// ──────────────────────────────────────────────────────────────
// register_ctx_dependency! parsing
// ──────────────────────────────────────────────────────────────
#[derive(Debug)]
struct RegisterDepInput {
    trait_ident: Ident,
    builder: Path,
}
impl Parse for RegisterDepInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let trait_ident: Ident = input.parse()?;
        input.parse::<Token![,]>()?;
        let builder: Path = input.parse()?;
        Ok(RegisterDepInput {
            trait_ident,
            builder,
        })
    }
}

// ──────────────────────────────────────────────────────────────
// Macro generators
// ──────────────────────────────────────────────────────────────

fn gen_define_ctx(input: DefineCtxInput) -> TokenStream2 {
    let DefineCtxInput {
        ctx_name,
        env,
        secrets,
        deps,
        views,
    } = input;

    // ENV
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
                    .expect(concat!("Missing env var `", #var_name, "`"))
                    .parse()
                    .expect(concat!("Failed to parse env var `", #var_name, "`"));
            }
        })
        .collect();
    let env_getters: Vec<_> = env
        .iter()
        .map(|kv| {
            let name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { pub fn #name(&self) -> &#ty { &self.#name } }
        })
        .collect();

    // Helper lists for struct initialisation
    let env_idents: Vec<_> = env
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            quote! { #ident }
        })
        .collect();

    let secret_idents: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let ident = to_snake(&kv.key);
            quote! { #ident }
        })
        .collect();

    // SECRETS
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
    // Secret map fetch (single call to the backend)
    let secret_fetch: TokenStream2 = if !secrets.is_empty() {
        quote! {
            // Build the AWS Secrets Manager helper and fetch the subset in one request.
            let __secrets_util = ::fractic_aws_secrets::SecretsUtil::new(secrets_region.clone()).await;
            let __secret_map = __secrets_util
                .load_secrets(&secrets_id, &[
                    #(#secret_key_strs),*
                ])
                .await
                .expect("Failed to load secrets");
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
                    .expect(concat!("Missing secret key `", #key_name, "`"))
                    .parse()
                    .expect(concat!("Failed to parse secret `", #key_name, "`"));
            }
        })
        .collect();
    let secret_getters: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { pub fn #name(&self) -> &#ty { &self.#name } }
        })
        .collect();

    // DEPS
    let dep_field_defs: Vec<_> = deps
        .iter()
        .map(|dp| {
            let field = to_snake(&dp.trait_ident);
            let dep_trait = &dp.trait_ident;
            quote! {
                pub #field: std::sync::RwLock<std::sync::Arc<dyn #dep_trait + Send + Sync>>
            }
        })
        .collect();

    let dep_builder_inits: Vec<_> = deps
        .iter()
        .map(|dp| {
            let temp_ident = format_ident!("__{}", to_snake(&dp.trait_ident));
            let builder_path = &dp.builder;
            quote! {
                let #temp_ident = #builder_path().await;
            }
        })
        .collect();

    let dep_field_inits: Vec<_> = deps
        .iter()
        .map(|dp| {
            let field = to_snake(&dp.trait_ident);
            let temp_ident = format_ident!("__{}", field);
            quote! { #field: std::sync::RwLock::new(#temp_ident) }
        })
        .collect();

    let dep_getters: Vec<_> = deps
        .iter()
        .map(|dp| {
            let field = to_snake(&dp.trait_ident);
            let dep_trait = &dp.trait_ident;
            let getter = field.clone();
            let override_fn = format_ident!("override_{}", field);
            quote! {
                pub fn #getter(&self) -> std::sync::Arc<dyn #dep_trait + Send + Sync> {
                    self.#field.read().unwrap().clone()
                }
                pub fn #override_fn(&self, new_impl: std::sync::Arc<dyn #dep_trait + Send + Sync>) {
                    let mut lock = self.#field.write().unwrap();
                    *lock = new_impl;
                }
            }
        })
        .collect();

    // Automatically implement the `CtxHas*` accessor traits for the context.
    let dep_trait_impls: Vec<_> = deps
        .iter()
        .map(|dp| {
            let trait_name = format_ident!("CtxHas{}", dp.trait_ident);
            quote! { impl #trait_name for #ctx_name {} }
        })
        .collect();

    // Views impls
    let view_impls: Vec<_> = views
        .iter()
        .map(|p| {
            quote! { impl #p for #ctx_name {} }
        })
        .collect();

    quote! {
        #[derive(Debug)]
        pub struct #ctx_name {
            #(#env_field_defs,)*
            #(#secret_field_defs,)*
            pub secrets_region: String,
            pub secrets_id: String,
            #(#dep_field_defs,)*
        }

        impl #ctx_name {
            /// Build a fully-initialised, reference-counted Ctx.
            pub async fn init(secrets_fetch_region: &str, secrets_fetch_id: &str) -> std::sync::Arc<Self> {
                use std::sync::Arc;

                // Resolve the region and secret identifier from environment variables.
                let secrets_region = std::env::var(secrets_fetch_region)
                    .expect("Missing secrets region env var");
                let secrets_id = std::env::var(secrets_fetch_id)
                    .expect("Missing secrets id env var");

                #(#env_inits)*
                #secret_fetch
                #(#secret_inits)*
                #(#dep_builder_inits)*

                let ctx = Arc::new(Self {
                    #(#env_idents),*,
                    #(#secret_idents),*,
                    secrets_region,
                    secrets_id,
                    #(#dep_field_inits),*
                });

                ctx
            }
        }

        // Views / getters
        impl #ctx_name {
            #(#env_getters)*
            #(#secret_getters)*
            #(#dep_getters)*
        }

        #(#view_impls)*
        #(#dep_trait_impls)*
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

    let env_methods: Vec<_> = env
        .iter()
        .map(|kv| {
            let fn_name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { fn #fn_name(&self) -> &#ty; }
        })
        .collect();
    let secret_methods: Vec<_> = secrets
        .iter()
        .map(|kv| {
            let fn_name = to_snake(&kv.key);
            let ty = &kv.ty;
            quote! { fn #fn_name(&self) -> &#ty; }
        })
        .collect();
    let dep_methods: Vec<_> = deps
        .iter()
        .map(|id| {
            let field = to_snake(id);
            quote! { fn #field(&self) -> std::sync::Arc<dyn #id + Send + Sync>; }
        })
        .collect();

    // Supertrait list
    let supertraits: TokenStream2 = if !req_impl.is_empty() {
        quote! { : #( #req_impl )+* }
    } else {
        TokenStream2::new()
    };

    quote! {
        pub trait #view_name #supertraits {
            #(#env_methods)*
            #(#secret_methods)*
            #(#dep_methods)*
        }
    }
}

fn gen_register_dep(input: RegisterDepInput) -> TokenStream2 {
    let RegisterDepInput {
        trait_ident,
        builder,
    } = input;
    let field_snake = to_snake(&trait_ident);
    let trait_name = format_ident!("CtxHas{}", trait_ident);
    let getter = field_snake.clone();
    let default_fn = format_ident!("default_{}", field_snake);

    quote! {
        pub trait #trait_name {
            fn #getter(&self) -> std::sync::Arc<dyn #trait_ident + Send + Sync>;
        }

        pub async fn #default_fn() -> std::sync::Arc<dyn #trait_ident + Send + Sync> {
            #builder().await
        }
    }
}

// ──────────────────────────────────────────────────────────────
// Public macro entry points
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

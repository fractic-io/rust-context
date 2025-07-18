// EXPERIMENTAL
//
// Version 2.0 of the env config library.
//
// Eventually will be nicely organized and replace the other version, but need
// to try it out for a bit first.

use convert_case::{Case, Casing};
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::{parse_macro_input, punctuated::Punctuated, Ident, ItemTrait, Token, Type};

// Helper for parsing a single env variable definition like `VAR: Type`
struct EnvField {
    ident: Ident,
    _colon_token: Token![:],
    ty: Type,
}

impl Parse for EnvField {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident: Ident = input.parse()?;
        let _colon_token: Token![:] = input.parse()?;
        let ty: Type = input.parse()?;
        Ok(EnvField {
            ident,
            _colon_token,
            ty,
        })
    }
}

const SECRETS_REGION: &str = "SECRETS_REGION";
const SECRETS_ID: &str = "SECRETS_ID";

/// Application side ─────────────────────────────────────────────────────────
///
///     env_config! { DB_URL: Url, REDIS_ADDR: SocketAddr, FEATURE_FLAG: bool }
///
/// expands to:
///     pub struct Env { db_url: Url, redis_addr: SocketAddr, … }
///     static ENV: OnceCell<Env> = …;
///
///     impl Env { pub fn init() …; pub fn get() -> &'static Env … }
///
/// Plus a convenience macro to *implement* any view-trait for `Env`.
#[proc_macro]
pub fn env_config(input: TokenStream) -> TokenStream {
    let vars = parse_macro_input!(input with Punctuated::<EnvField, Token![,]>::parse_terminated);

    let mut fields = Vec::<(Ident, Type)>::new();
    for field in vars {
        fields.push((field.ident, field.ty));
    }

    let field_defs = fields.iter().map(|(i, t)| quote!(pub #i: #t,));
    let inits = fields.iter().map(|(i, t)| {
        quote! {
            #i: std::env::var(stringify!(#i))
                   .map_err(|_| format!("missing env {}", stringify!(#i)))?
                   .parse::<#t>()
                   .map_err(|e| format!("parsing {}: {e}", stringify!(#i)))?,
        }
    });

    quote! {
        #[derive(Debug)]
        pub struct Env { #(#field_defs)* }

        static ENV: once_cell::sync::OnceCell<Env> = once_cell::sync::OnceCell::new();

        impl Env {
            pub fn init() -> Result<(), String> {
                let cfg = Env { #(#inits)* };
                ENV.set(cfg).map_err(|_| "Env already initialised".into())
            }
            pub fn get() -> &'static Env {
                ENV.get().expect("call Env::init() first")
            }
        }

        /// `impl_env_view!(NeedsSomething for Env);`
        #[macro_export]
        macro_rules! impl_env_view {
            ($trait:path for $env:ty) => {
                impl $trait for $env {
                    envy_macros::delegate_env_view_methods!($trait, self);
                }
            };
        }
    }
    .into()
}

// Help parse the arguments for delegate_env_view_methods: a trait path and a self identifier
struct DelegateArgs {
    trait_path: syn::Path,
    _comma: Token![,],
    self_ident: Ident,
}

impl Parse for DelegateArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let trait_path: syn::Path = input.parse()?;
        let _comma: Token![,] = input.parse()?;
        let self_ident: Ident = input.parse()?;
        Ok(DelegateArgs {
            trait_path,
            _comma,
            self_ident,
        })
    }
}

/// Used *inside* the helper above.  Generates a body for every method in the
/// trait that looks like `&self.db_url`.
#[proc_macro]
pub fn delegate_env_view_methods(input: TokenStream) -> TokenStream {
    // input = `$trait, self`
    let DelegateArgs {
        trait_path,
        self_ident,
        ..
    } = parse_macro_input!(input as DelegateArgs);

    // Load the trait declaration so we can iterate over its methods.
    // (We rely on the trait being in scope – fine for normal Rust workflows.)
    let item: ItemTrait = syn::parse_quote!( trait Dummy for DummyType : #trait_path {} );
    let methods = item.items.iter().filter_map(|it| {
        if let syn::TraitItem::Fn(m) = it {
            Some(m.sig.clone())
        } else {
            None
        }
    });

    let impl_fns = methods.map(|sig| {
        let name = &sig.ident;
        quote! { fn #sig { &#self_ident.#name } }
    });

    quote! { #(#impl_fns)* }.into()
}

/// Library side ─────────────────────────────────────────────────────────────
///
///     env_view_config! {
///         pub trait NeedsMyUtilEnv {
///             DB_URL     : url::Url,
///             REDIS_ADDR : std::net::SocketAddr,
///         }
///     }
///
/// expands to a trait with nicely-named getters:
///
///     pub trait NeedsMyUtilEnv {
///         fn db_url(&self) -> &url::Url;
///         fn redis_addr(&self) -> &std::net::SocketAddr;
///     }
#[proc_macro]
pub fn env_view_config(input: TokenStream) -> TokenStream {
    // trait header + block of pairs
    let input = parse_macro_input!(input as syn::ItemTrait);
    let vis = &input.vis;
    let ident = &input.ident;

    // We reuse the methods already written by the author, if any, but we add
    // one for each associated const-style item.
    let mut methods = Vec::<proc_macro2::TokenStream>::new();
    for item in &input.items {
        if let syn::TraitItem::Const(c) = item {
            let var = &c.ident;
            let ty = &c.ty;
            let meth = format_ident!("{}", var.to_string().to_case(Case::Snake));
            methods.push(quote! { fn #meth(&self) -> &#ty; });
        }
    }

    quote! {
        #vis trait #ident { #(#methods)* }
    }
    .into()
}

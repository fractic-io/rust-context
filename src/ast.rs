use syn::parse::{Parse, ParseStream};
use syn::{braced, punctuated::Punctuated, Expr, Ident, Path, Result, Token, Type};

#[derive(Debug)]
pub struct KeyTy {
    pub key: Ident,
    pub ty: Type,
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
pub struct DepItem {
    pub trait_ty: Type, // e.g. crate::rsc::tts::repositories::TtsRepository
    pub blocking: bool,
}
impl Parse for DepItem {
    fn parse(input: ParseStream) -> Result<Self> {
        // Optional `blocking` keyword before the type.
        let mut blocking = false;
        let ahead = input.fork();
        let has_blocking = if ahead.peek(Ident) {
            let kw: Ident = ahead.parse()?;
            kw == "blocking"
        } else {
            false
        };
        if has_blocking {
            let _: Ident = input.parse()?; // consume the "blocking" keyword
            blocking = true;
        }
        let trait_ty: Type = input.parse()?;
        Ok(DepItem { trait_ty, blocking })
    }
}

#[derive(Debug)]
pub struct DepOverlayItem {
    pub trait_ty: Type,
    pub blocking: bool,
}
impl Parse for DepOverlayItem {
    fn parse(input: ParseStream) -> Result<Self> {
        // Optional `blocking` keyword before the type.
        let ahead = input.fork();
        let has_blocking = if ahead.peek(Ident) {
            let kw: Ident = ahead.parse()?;
            kw == "blocking"
        } else {
            false
        };
        if has_blocking {
            let _: Ident = input.parse()?; // consume the "blocking" keyword
            let trait_ty: Type = input.parse()?;
            Ok(DepOverlayItem {
                trait_ty,
                blocking: true,
            })
        } else {
            input.parse::<Type>().map(|trait_ty| DepOverlayItem {
                trait_ty,
                blocking: false,
            })
        }
    }
}

#[derive(Debug)]
pub struct DefineCtxInput {
    pub ctx_name: Ident,
    pub env: Vec<KeyTy>,
    pub secrets_region_ident: Ident,
    pub secrets_id_ident: Ident,
    pub secrets: Vec<KeyTy>,
    pub deps: Vec<DepItem>,
    pub views: Vec<Path>,
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
pub struct DefineCtxViewInput {
    pub view_name: Ident,
    pub env: Vec<KeyTy>,
    pub secrets: Vec<KeyTy>,
    pub dep_overlays: Vec<DepOverlayItem>,
    pub req_impl: Vec<Path>,
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
pub struct RegisterDepInput {
    pub ctx_ty: Type,  // e.g. `MyCtx` or `dyn SomeCtxView`
    pub type_ty: Type, // generic aware
    pub builder: Expr,
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

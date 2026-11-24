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

/// Names of the env vars holding the Secrets Manager region and secret id.
#[derive(Debug)]
pub struct SecretsFetch {
    pub region_ident: Ident,
    pub id_ident: Ident,
}

#[derive(Debug)]
pub struct DefineCtxInput {
    pub ctx_name: Ident,
    pub env: Vec<KeyTy>,
    /// `Some` exactly when `secrets` is non-empty. Without secrets the keys
    /// may be left out, and are ignored when given.
    pub secrets_fetch: Option<SecretsFetch>,
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

        // secrets_fetch_region: REGION_ENV_VAR,  (optional)
        // secrets_fetch_id: ID_ENV_VAR,          (optional)
        let secrets_region_ident = parse_optional_ident_entry(input, "secrets_fetch_region")?;
        let secrets_id_ident = parse_optional_ident_entry(input, "secrets_fetch_id")?;

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

        // The fetch keys only matter when there is something to fetch.
        let secrets_fetch = if sec_items.is_empty() {
            None
        } else {
            match (secrets_region_ident, secrets_id_ident) {
                (Some(region_ident), Some(id_ident)) => Some(SecretsFetch {
                    region_ident,
                    id_ident,
                }),
                (region, id) => {
                    let missing = [
                        region.is_none().then_some("`secrets_fetch_region:`"),
                        id.is_none().then_some("`secrets_fetch_id:`"),
                    ]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>()
                    .join(" and ");
                    return Err(syn::Error::new(
                        sec_kw.span(),
                        format!(
                            "`define_ctx!`: a non-empty `secrets` needs {missing} before it, \
                             naming the env vars that hold the Secrets Manager region and \
                             secret id"
                        ),
                    ));
                }
            }
        };

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
            secrets_fetch,
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

// Helpers.
// ----------------------------------------------------------------------------

/// Parses `<key>: IDENT,` if the next token is `key`, otherwise consumes
/// nothing.
fn parse_optional_ident_entry(input: ParseStream, key: &str) -> Result<Option<Ident>> {
    let ahead = input.fork();
    match ahead.parse::<Ident>() {
        Ok(kw) if kw == key => {}
        _ => return Ok(None),
    }
    let _: Ident = input.parse()?;
    input.parse::<Token![:]>()?;
    let value: Ident = input.parse()?;
    input.parse::<Token![,]>()?;
    Ok(Some(value))
}

// Tests.
// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(input: &str) -> Result<DefineCtxInput> {
        syn::parse_str(input)
    }

    #[test]
    fn fetch_keys_are_optional_without_secrets() {
        let input = parse("name: Ctx, env {}, secrets {}, deps {}, views {}").unwrap();
        assert!(input.secrets_fetch.is_none());
    }

    #[test]
    fn fetch_keys_are_accepted_and_ignored_without_secrets() {
        let input = parse(
            "name: Ctx, env {}, secrets_fetch_region: REGION, secrets_fetch_id: ID, \
             secrets {}, deps {}, views {}",
        )
        .unwrap();
        assert!(input.secrets_fetch.is_none());
    }

    #[test]
    fn fetch_keys_are_kept_with_secrets() {
        let input = parse(
            "name: Ctx, env {}, secrets_fetch_region: REGION, secrets_fetch_id: ID, \
             secrets { KEY: String }, deps {}, views {}",
        )
        .unwrap();
        let fetch = input.secrets_fetch.unwrap();
        assert_eq!(fetch.region_ident, "REGION");
        assert_eq!(fetch.id_ident, "ID");
    }

    #[test]
    fn missing_fetch_keys_with_secrets_are_named_in_the_error() {
        let err = parse("name: Ctx, env {}, secrets { KEY: String }, deps {}, views {}")
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("`secrets_fetch_region:` and `secrets_fetch_id:`"),
            "{err}"
        );

        let err = parse(
            "name: Ctx, env {}, secrets_fetch_region: REGION, secrets { KEY: String }, \
             deps {}, views {}",
        )
        .unwrap_err()
        .to_string();
        assert!(err.contains("needs `secrets_fetch_id:` before"), "{err}");
        assert!(!err.contains("secrets_fetch_region"), "{err}");
    }
}

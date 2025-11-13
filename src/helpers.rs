use convert_case::{Boundary, Case, Casing};
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{
    GenericArgument, Ident, Path, PathArguments, PathSegment, Type, TypeParamBound, TypePath,
    TypeTraitObject,
};

#[derive(Clone, Copy)]
pub enum DepKind {
    Trait,  // e.g. `dyn crate::FooRepository`
    Struct, // e.g. `crate::Config`
}
pub fn dep_kind(ty: &Type) -> DepKind {
    match ty {
        Type::TraitObject(_) => DepKind::Trait,
        _ => DepKind::Struct,
    }
}

/// Convert an identifier to `snake_case`, but keep digit sequences glued to the
/// letters that precede them. For example:
///   > `S3Util` → `s3_util`
///   > `Version10Beta` → `version10_beta`
pub fn to_snake(ident: &Ident) -> Ident {
    let snake = ident
        .to_string()
        // treat the input as Camel/Pascal-case
        .from_case(Case::Camel)
        // ⤵ strip the two “letter → digit” split points
        .without_boundaries(&Boundary::letter_digit())
        .to_case(Case::Snake);

    format_ident!("{}", snake, span = ident.span())
}

/// Get the prefix of a fully-qualified path. For example:
///   > `crate::rsc::tts::repositories::TtsRepository`
///      → `crate::rsc::tts::repositories`
pub fn path_prefix(path: &Path) -> TokenStream2 {
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

/// Return a vector containing the main identifier *plus* the last identifier of
/// every generic type argument (depth-1 only).
pub fn type_ident_chain(ty: &Type) -> Vec<Ident> {
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

/// Snake case concatenation. For example:
///   > `["DatabaseRepository", "MySql"]` → `database_repository_mysql`
pub fn chain_to_snake(idents: &[Ident]) -> Ident {
    let s = idents
        .iter()
        .map(|id| to_snake(id).to_string())
        .collect::<Vec<_>>()
        .join("_");
    format_ident!("{}", s)
}

/// Pascal case concatenation. For example:
///   > `["DatabaseRepository", "MySql"]` → `DatabaseRepositoryMysql`
pub fn chain_to_pascal(idents: &[Ident]) -> Ident {
    let s = idents
        .iter()
        .map(|id| id.to_string().to_case(Case::Pascal))
        .collect::<String>();
    format_ident!("{}", s)
}

/// Everything except the final path segment (works even if the last segment has
/// generics).
pub fn type_path_prefix(ty: &Type) -> TokenStream2 {
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
pub fn type_is_local(ty: &Type) -> bool {
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
pub fn last_ident(ty: &Type) -> PathSegment {
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
/// `Type::Path` *and* that starts at the crate root (≥ 2 segments).
pub fn is_absolute_dep_ty(ty: &Type) -> bool {
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

/// Collect a list of valid dependency types while also generating
/// `compile_error!`s for every bad entry. The returned vector is then safe to
/// feed into later stages that use `last_ident()`.
pub fn collect_valid_dep_tys<'a>(
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

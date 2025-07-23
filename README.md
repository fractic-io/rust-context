# fractic-context

Procedural macros for generating a typed, thread-safe **application context** that bundles:

* mandatory environment variables
* selected AWS Secrets Manager secrets (fetched once, cached)
* overridable singleton dependencies

Macros
------
* `define_ctx!` – emits a concrete `Ctx` with async `init`, getters and override helpers.
* `define_ctx_view!` – emits a trait describing the subset of context a library needs.
* `register_ctx_dependency!` – emits a `CtxHas*` accessor trait and a default async builder.

Example
-------
```rust
// ─── root crate ─────────────────────────────────────────────
use rust_context::define_ctx;

define_ctx! {
    name: Ctx,
    env { PORT: u16 },
    secrets_fetch_region: SECRETS_REGION,
    secrets_fetch_id: SECRETS_ID,
    secrets { DB_URL: String },
    deps { crate::Database },
    views { my_lib::DbCtxView }
}

// Initialise once at startup.
let ctx = Ctx::init().await;

// ─── library crate ──────────────────────────────────────────
use rust_context::define_ctx_view;

define_ctx_view! {
    name: DbCtxView,
    env { PORT: u16 },
    secrets { DB_URL: String },
    deps_overlay { crate::Database },
    req_impl { LoggingCtxView }
}

// ─── dependency registration ───────────────────────────────
use rust_context::register_ctx_dependency;

register_ctx_dependency!(
    Ctx, // in binary
    Database,
    |ctx: Arc<Ctx>| async move {
        DatabaseImpl::new(&*ctx).await
    }
);

register_ctx_dependency!(
    dyn DbCtxView, // in library
    Database,
    |ctx: Arc<dyn DbCtxView>| async move {
        DatabaseImpl::new(&*ctx).await
    }
);
```

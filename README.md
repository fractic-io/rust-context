# fractic-context

Procedural macros for generating a typed, thread-safe **application context** that bundles:

* mandatory environment variables
* selected AWS Secrets Manager secrets (fetched once, cached)
* overridable singleton dependencies

Macros
------
* `define_ctx!` – emits a concrete `Ctx` with async `init`, getters and override helpers.
* `define_ctx_view!` – emits a trait describing the subset of context a library needs.
* `register_ctx_trait_async!` – registers a singleton `dyn Trait` dependency built via an **async** builder.
* `register_ctx_trait!` – same as above but for a **sync** builder.
* `register_ctx_struct_async!` – registers a singleton concrete struct built via an **async** builder and returned as `Arc<T>`.
* `register_ctx_struct!` – same as above but for a **sync** builder.
* `register_ctx_factory!` – registers a factory that builds a **new** `Arc<dyn Trait>` instance on every call (builder signature is mirrored by the generated getter).

Example
-------
```rust
// ─── root crate ─────────────────────────────────────────────
use fractic_context::define_ctx;

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
use fractic_context::define_ctx_view;

define_ctx_view! {
    name: DbCtxView,
    env { PORT: u16 },
    secrets { DB_URL: String },
    deps_overlay { crate::Database },
    req_impl { LoggingCtxView }
}

// ─── dependency registration ───────────────────────────────
use fractic_context::{
    register_ctx_trait_async,
    register_ctx_struct,
    register_ctx_factory,
};

// ex. `dyn Trait` singleton, w/ async constructor.
register_ctx_trait_async!(
    Ctx,
    Database,
    |ctx: Arc<Ctx>| async move { DatabaseImpl::new(&*ctx).await }
);

// ex. concrete struct singleton, w/ sync constructor.
register_ctx_struct!(
    Ctx,
    MetricsRegistry,
    |ctx: Arc<Ctx>| {
        MetricsRegistry::new(ctx.port())
    }
);

// ex. factory – every call returns a fresh instance.
register_ctx_factory!(
    Ctx,
    dyn DbCtxView,
    |ctx: Arc<Ctx>, user_id: Uuid| async move {
        DbSession::new(&*ctx, user_id).await
    }
);
```

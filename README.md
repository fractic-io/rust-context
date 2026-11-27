# fractic-context

Procedural macros for generating a typed, thread-safe **application context** that bundles:

* mandatory environment variables
* selected AWS Secrets Manager secrets (fetched once, cached)
* overridable singleton dependencies

Macros
------
* `define_ctx!` – emits a concrete `Ctx` with async `init`, getters and override helpers.
* `define_ctx_view!` – emits a trait describing the subset of context a library needs.
* `register_ctx_singleton!` – registers a dependency accessed as `Arc<T>` or `Arc<dyn Trait>`.
* `register_ctx_factory!` – registers a factory that builds a new `Arc<dyn Trait>` instance on every call (builder signature is mirrored by the generated getter).

Example
-------
```rust
// ─── root crate ─────────────────────────────────────────────
use fractic_context::define_ctx;

define_ctx! {
    name: Ctx,
    env { PORT: u16 },
    // Env vars naming the Secrets Manager region and secret id. Needed only
    // when `secrets` is non-empty; see "Secrets" below.
    secrets_fetch_region: SECRETS_REGION,
    secrets_fetch_id: SECRETS_ID,
    secrets { DB_URL: String },
    deps {
        crate::Config,
        crate::ProcessorFactory,
        dyn crate::UserRepository,
    },
    views { db_lib::DbCtxView }
}

// Initialise once at startup.
let ctx = Ctx::init().await;

// ─── library crate ──────────────────────────────────────────
use fractic_context::define_ctx_view;

define_ctx_view! {
    name: DbCtxView,
    env { PORT: u16 },
    secrets { DB_URL: String },
    deps_overlay {
        dyn crate::Database
    },
    req_impl { log_lib::LoggingCtxView }
}

// ─── dependency registration ───────────────────────────────
use fractic_context::{
    register_ctx_factory,
    register_ctx_struct,
    register_ctx_trait_async,
};

// ex. concrete struct singleton (accessible as `Arc<Config>`).
register_ctx_singleton!(
    Ctx, // or dyn SomeCtxView
    Config,
    |ctx: Arc<Ctx>| async move {
        Config::new(&*ctx)
    }
);

// ex. trait singleton (accessible as `Arc<dyn DbSession>`).
register_ctx_singleton!(
    Ctx, // or dyn SomeCtxView
    dyn Database,
    |ctx: Arc<Ctx>| async move {
        DatabaseImpl::new(&*ctx).await
    }
);

// ex. factory (generates `Arc<dyn Processor>` objects).
register_ctx_factory!(
    Ctx, // or dyn SomeCtxView
    dyn Processor,
    |ctx: Arc<Ctx>, user_id: Uuid| { // or async move { ... }
        ProcessorImpl::new(&*ctx, user_id)
    }
); // -> ProcessorFactory
```

### Secrets

`init()` reads the env vars named by `secrets_fetch_region` and
`secrets_fetch_id` and fetches the `secrets` keys from that Secrets Manager
secret. Both keys are required when `secrets` is non-empty (omitting one is a
compile error). With `secrets {}` they can be left out: nothing is fetched,
neither env var is read, and the context has no `secrets_fetch_region` /
`secrets_fetch_id` fields, so a context of only `deps` initializes with no
environment at all:

```rust
define_ctx! {
    name: Ctx,
    env {},
    secrets {},
    deps { dyn crate::UserRepository },
    views {}
}
```

Keys given alongside an empty `secrets {}` are accepted and ignored.

### Optional secrets

Declare `XAI_API_KEY: Option<String>` in `secrets` to permit a missing key or JSON
`null`. A present value must deserialize to the declared type. Required keys,
malformed values, and Secrets Manager failures still fail initialization.
`Option<T>`, `std::option::Option<T>`, and `core::option::Option<T>` are supported;
type aliases are not inspected by the macro. Getters retain the declared type.

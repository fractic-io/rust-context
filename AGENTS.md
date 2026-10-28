# fractic-context

Procedural macros for the typed application context of every Fractic
binary: `define_ctx!` (env vars, Secrets Manager secrets, overridable
singleton dependencies, library views), `define_ctx_view!` (the subset a
library needs, with `deps_overlay` and `req_impl`),
`register_ctx_singleton!` / `register_ctx_singleton_alias!` /
`register_ctx_factory!` / `register_ctx_blocking!`. `README.md` has the
usage example; consumer side: `/efs/fractic/_/rust.md` §4.

Proc-macro crate: `src/lib.rs` (entry points) → `ast.rs` (parse the macro
input), `codegen/{define_ctx,define_ctx_view,register_ctx_singleton,
register_ctx_factory,register_ctx_blocking,shared}.rs` (emit Rust),
`helpers.rs`.

- Verify macro changes by building a consumer (`storyengine/api/v0`,
  `app/backend/api/v1`) through its `[patch]`. Generated code may only
  reference paths that resolve there (`fractic_aws_secrets`, `tokio`,
  `std`); keep new generated items behind `__`-prefixed names.
- A change to the macro grammar is breaking for every `cfg/context.rs` in
  the workspace: title it `Breaking: …` and update the README example.
- Commit / PR titles: imperative, trailing period.

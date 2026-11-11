# fractic-context

Procedural macros for the typed application context of every Fractic
binary: `define_ctx!` (env vars, Secrets Manager secrets, overridable
singleton dependencies, library views), `define_ctx_view!` (the subset a
library needs, with `deps_overlay` and `req_impl`),
`register_ctx_singleton!` / `register_ctx_singleton_alias!` /
`register_ctx_factory!` / `register_ctx_blocking!`. `README.md` has the
usage example.

Proc-macro crate: `src/lib.rs` (entry points) → `ast.rs` (parse the macro
input), `codegen/{define_ctx,define_ctx_view,register_ctx_singleton,
register_ctx_factory,register_ctx_blocking,shared}.rs` (emit Rust),
`helpers.rs`.

- Verify macro changes by building a consumer. Generated code may only
  reference paths that resolve in the consuming crate
  (`fractic_aws_secrets`, `tokio`, `std`); keep new generated items behind
  `__`-prefixed names.
- A change to the macro grammar is breaking for every consumer's
  `define_ctx!`: mark the PR `↯` and update the README example.

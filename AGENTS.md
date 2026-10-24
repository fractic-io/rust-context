# fractic-context

Procedural macros for the typed application context used by every Fractic
binary: `define_ctx!` (env vars, Secrets Manager secrets, overridable
singleton dependencies, library views), `define_ctx_view!` (the subset a
library needs, with `deps_overlay` and `req_impl`),
`register_ctx_singleton!` / `register_ctx_singleton_alias!` /
`register_ctx_factory!` / `register_ctx_blocking!`. Public, provided as-is
(`fractic-io/rust-context`, identity `fractic`). `README.md` has the usage
example.

## Read first

- `~/.agents/AGENTS.md` (workspace orientation; loaded automatically by Claude
  Code, read it if you are Codex or Grok) and `~/.agents/guides/rust.md`
  (§4 "Dependency injection" is how consumers use these macros).

## Layout

Proc-macro crate: `src/lib.rs` (entry points) → `ast.rs` (parse the macro
input), `codegen/{define_ctx,define_ctx_view,register_ctx_singleton,
register_ctx_factory,register_ctx_blocking,shared}.rs` (emit Rust),
`helpers.rs`. The same parse → codegen split as `fractic-crate-scaffolding`.

## Working here

- No flake here: build and test through a product devshell, e.g.
  `nix develop /efs/fractic/storyengine/util --command cargo test`. Macro
  changes are best verified by building a consumer (`storyengine/api/v0`,
  `app/backend/api/v1`) through its `[patch]`.
- Generated code must only reference paths that resolve in the consuming
  crate (`fractic_aws_secrets`, `tokio`, `std`); keep new generated items
  behind `__`-prefixed names.
- A change to the macro grammar is breaking for every `cfg/context.rs` in the
  workspace; title it `Breaking: …` and update the README example.
- Commit / PR titles: imperative, trailing period.

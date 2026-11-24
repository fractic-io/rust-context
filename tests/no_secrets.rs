use std::sync::Arc;

use fractic_context::{define_ctx, register_ctx_singleton};
use fractic_server_error::ServerError;

pub struct Greeter {
    pub greeting: &'static str,
}

define_ctx!(
    name: DepsOnlyContext,
    env {},
    secrets {},
    deps {
        crate::Greeter,
    },
    views {}
);

register_ctx_singleton!(
    DepsOnlyContext,
    Greeter,
    |_ctx: Arc<DepsOnlyContext>| async move { Ok::<_, ServerError>(Greeter { greeting: "hello" }) }
);

// Fetch keys given without secrets: accepted, never read.
define_ctx!(
    name: UnusedFetchKeysContext,
    env {},
    secrets_fetch_region: NO_SECRETS_TEST_REGION,
    secrets_fetch_id: NO_SECRETS_TEST_ID,
    secrets {},
    deps {},
    views {}
);

#[tokio::test]
async fn deps_only_context_inits_without_any_env_var() {
    let ctx = DepsOnlyContext::init().await.unwrap();
    assert_eq!(ctx.greeter().await.unwrap().greeting, "hello");
}

#[tokio::test]
async fn fetch_keys_without_secrets_need_no_env_var() {
    assert!(std::env::var_os("NO_SECRETS_TEST_REGION").is_none());
    assert!(std::env::var_os("NO_SECRETS_TEST_ID").is_none());
    UnusedFetchKeysContext::init().await.unwrap();
}

use fractic_context::define_ctx;

define_ctx!(
    name: OptionalContext,
    env {},
    secrets_fetch_region: REGION,
    secrets_fetch_id: ID,
    secrets {
        REQUIRED: String,
        OPTIONAL: Option<String>,
        QUALIFIED: std::option::Option<String>,
    },
    deps {},
    views {}
);

#[test]
fn optional_getters_and_redaction_survive_macro_expansion() {
    let ctx = OptionalContext::init_test(
        "required-secret".into(),
        None,
        Some("optional-secret".into()),
    );
    assert_eq!(ctx.required(), "required-secret");
    assert!(ctx.optional().is_none());
    assert_eq!(ctx.qualified().as_deref(), Some("optional-secret"));
    let debug = format!("{ctx:?}");
    assert!(!debug.contains("required-secret"));
    assert!(!debug.contains("optional-secret"));
}

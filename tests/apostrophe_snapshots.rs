use std::fmt::Write as _;

fn format_error(err: &anyhow::Error) -> String {
    let mut lines = vec!["error chain:".to_string()];
    for cause in err.chain() {
        lines.push(format!("  - {cause}"));
    }
    lines.join("\n")
}

#[test]
fn apostrophe_identifiers_snapshot() {
    let cases = [
        (
            "const_with_apostrophe",
            "type const Prop : Type\nconst foo' : Prop\n",
        ),
        (
            "axiom_with_apostrophe",
            "type const Prop : Type\nconst foo : Prop\naxiom bar' : foo\n",
        ),
        (
            "type_const_with_apostrophe",
            "type const Prop : Type\ntype const P' : Type\n",
        ),
        (
            "const_starting_with_apostrophe",
            "type const Prop : Type\nconst 'x : Prop\n",
        ),
    ];

    let mut report = String::new();

    for (name, input) in cases {
        writeln!(report, "{name}:").expect("write succeeds");
        match shari::process(input) {
            Ok(()) => {
                writeln!(report, "  ok").expect("write succeeds");
            }
            Err(err) => {
                writeln!(report, "  error").expect("write succeeds");
                for line in format_error(&err).lines() {
                    writeln!(report, "    {line}").expect("write succeeds");
                }
            }
        }
        writeln!(report).expect("write succeeds");
    }

    insta::assert_snapshot!("apostrophe_identifiers", report);
}

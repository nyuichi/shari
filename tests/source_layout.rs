use std::fs;

#[test]
fn declarations_keep_primary_fields_before_auxiliary_fields() {
    let cmd = read("src/cmd.rs");
    assert_struct_fields(
        &cmd,
        "CmdConst",
        &["id", "local_types", "local_classes", "ty"],
    );
    assert_struct_fields(
        &cmd,
        "CmdTypeInductive",
        &[
            "id",
            "this",
            "this_name",
            "local_types",
            "ind_id",
            "rec_id",
            "ctors",
        ],
    );
    assert_struct_fields(&cmd, "StructureAxiom", &["id", "field_name", "target"]);
    assert_struct_fields(&cmd, "ClassStructureAxiom", &["id", "field_name", "target"]);

    let proof = read("src/proof.rs");
    assert_struct_fields(
        &proof,
        "LocalStructureConst",
        &["field_id", "field_name", "id", "name", "ty"],
    );
    assert_struct_fields(
        &proof,
        "LocalStructureAxiom",
        &["id", "field_name", "target"],
    );

    let parse = read("src/parse.rs");
    assert_struct_fields(&parse, "LocalConst", &["id", "name"]);
    assert_struct_fields(&parse, "LocalBinding", &["id", "name"]);

    let tt = read("src/tt.rs");
    assert_struct_fields(
        &tt,
        "LocalEnv",
        &["local_types", "local_classes", "locals", "local_deltas"],
    );

    let main = read("src/main.shari");
    for name in [
        "axiom Prop.complete_lattice.join_eq_or",
        "axiom Prop.complete_lattice.meet_eq_and",
        "axiom Prop.complete_lattice.top_eq_true",
        "axiom Prop.complete_lattice.bot_eq_false",
    ] {
        assert!(
            !main.contains(name),
            "main prelude should not keep helper axiom `{name}`",
        );
    }
}

fn assert_struct_fields(text: &str, name: &str, expected: &[&str]) {
    let body = struct_body(text, name);
    let actual = body.lines().filter_map(field_name).collect::<Vec<_>>();
    assert_eq!(actual, expected, "{name} field order changed");
}

fn struct_body<'a>(text: &'a str, name: &str) -> &'a str {
    let marker = format!("struct {name} {{");
    let start = text
        .find(&marker)
        .unwrap_or_else(|| panic!("missing struct {name}"));
    let rest = &text[start + marker.len()..];
    let end = rest
        .find("\n}")
        .unwrap_or_else(|| panic!("missing closing brace for {name}"));
    &rest[..end]
}

fn field_name(line: &str) -> Option<&str> {
    let line = line.trim();
    if !line.starts_with("pub ") && !line.contains(':') {
        return None;
    }
    let line = line.strip_prefix("pub ").unwrap_or(line);
    let (name, _) = line.split_once(':')?;
    Some(name.trim())
}

fn read(path: &str) -> String {
    fs::read_to_string(path).unwrap_or_else(|err| panic!("failed to read {path}: {err}"))
}

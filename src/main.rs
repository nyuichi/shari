use anyhow::Context;
use clap::{Arg, ArgAction, Command, ValueHint, value_parser};
use std::{fs, path::PathBuf, sync::Arc};

fn build_cli() -> Command {
    Command::new("shari")
        .version(env!("CARGO_PKG_VERSION"))
        .disable_version_flag(true)
        .arg(
            Arg::new("version")
                .short('v')
                .long("version")
                .action(ArgAction::Version)
                .help("Show version information"),
        )
        .arg(
            Arg::new("file")
                .value_name("FILE")
                .value_hint(ValueHint::FilePath)
                .value_parser(value_parser!(PathBuf))
                .num_args(0..=1),
        )
}

fn main() -> anyhow::Result<()> {
    env_logger::init();

    let matches = build_cli().get_matches();

    let prelude = include_str!("main.shari");
    let prelude_file = Arc::new(shari::File::new("src/main.shari", prelude.to_owned()));
    shari::process(prelude_file)?;

    if let Some(path) = matches.get_one::<PathBuf>("file") {
        let user_input = fs::read_to_string(path)
            .with_context(|| format!("failed to read `{}`", path.display()))?;
        let file_name = path.display().to_string();
        let user_file = Arc::new(shari::File::new(file_name, user_input));
        shari::process(user_file)?;
    }

    Ok(())
}

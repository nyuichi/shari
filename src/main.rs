fn main() -> anyhow::Result<()> {
    env_logger::builder().format_timestamp(None).init();
    let input = include_str!("main.shari");
    shari::process(input)
}

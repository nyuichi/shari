fn main() -> anyhow::Result<()> {
    env_logger::init();
    let input = include_str!("main.shari");
    shari::process(input)
}

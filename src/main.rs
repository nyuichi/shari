fn main() -> anyhow::Result<()> {
    let input = include_str!("main.shari");
    shari::process(input)
}

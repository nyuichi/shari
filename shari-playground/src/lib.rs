use log::{LevelFilter, Log, Metadata, Record};
use shari::{process, File};
use wasm_bindgen::prelude::*;
use std::sync::Arc;

#[wasm_bindgen]
pub fn run_process(input: &str) -> String {
    let file = Arc::new(File::new("<playground>", input.to_owned()));
    match process(file) {
        Ok(()) => "Success".to_string(),
        Err(e) => format!("Error: {:#}", e),
    }
}

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_name = appendLog)]
    fn append_log(msg: &str);
}

struct TextAreaLogger;

impl Log for TextAreaLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            let msg = format!("[{}] {}", record.level(), record.args());
            append_log(&msg);
        }
    }

    fn flush(&self) {}
}

static LOGGER: TextAreaLogger = TextAreaLogger;

#[wasm_bindgen]
pub fn init_all() {
    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(LevelFilter::Info);
    std::panic::set_hook(Box::new(console_error_panic_hook::hook));
}

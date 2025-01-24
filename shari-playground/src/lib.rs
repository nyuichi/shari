use shari::process;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn run_process(input: &str) -> String {
    match process(input) {
        Ok(()) => "Success".to_string(),
        Err(e) => format!("Error: {:#}", e),
    }
}

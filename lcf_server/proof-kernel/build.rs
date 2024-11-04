use std::path::PathBuf;

fn main() {
    let bdwgc = pkg_config::probe_library("bdw-gc").unwrap();

    let bindings = bindgen::Builder::default()
        .header("src/gc_wrapper.h")
        .clang_args(
            bdwgc
                .include_paths
                .iter()
                .map(|path| format!("-I{}", path.to_string_lossy())),
        )
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate bindings");
    let out_path = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("gc_bindings.rs"))
        .expect("Couldn't write bindings!");
}

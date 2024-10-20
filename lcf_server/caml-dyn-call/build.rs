use std::{io::BufRead, path::PathBuf};

fn main() -> std::io::Result<()> {
    let hol_light_dir = std::env::var("HOLLIGHT_DIR").expect("HOLLIGHT_DIR not set");
    std::process::Command::new("make")
        .current_dir(&hol_light_dir)
        .status()?;
    println!("cargo:rerun-if-changed={}", hol_light_dir);

    let ocaml_files = [
        "src/eval.ml",
        &format!("{}/bignum.cmo", hol_light_dir),
        &format!("{}/hol_loader.cmo", hol_light_dir),
    ];
    let ocaml_packages = ["compiler-libs.toplevel", "zarith", "camlp-streams"];

    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let ocamlopt = std::env::var("OCAMLOPT").unwrap_or_else(|_| "ocamlopt".to_string());

    let ocaml_path = std::process::Command::new(ocamlopt)
        .arg("-where")
        .output()?
        .stdout;
    let ocaml_path = std::str::from_utf8(&ocaml_path).unwrap().trim();

    compile(out_dir, &ocaml_files, &ocaml_packages)?;
    link(ocaml_path)?;

    Ok(())
}

const CC_LIB_PREFIX: &str = "NATIVECCLIBS=";

fn compile(out_dir: PathBuf, ocaml_files: &[&str], ocaml_packages: &[&str]) -> std::io::Result<()> {
    let object_file = out_dir.join("caml").with_extension("o");

    // Compile OCaml files
    let mut args = vec![
        "ocamlc",
        "-o",
        object_file.to_str().unwrap(),
        "-cclib",
        "-L/usr/lib",
        "-linkall",
        "-output-complete-obj",
        "-linkpkg",
    ];
    for package in ocaml_packages.iter() {
        args.push("-package");
        args.push(package);
    }
    for file in ocaml_files.iter() {
        args.push(file);
    }
    let status = std::process::Command::new("ocamlfind")
        .args(args)
        .status()
        .expect("Failed to compile OCaml file");
    if !status.success() {
        panic!("Failed to compile OCaml file");
    }

    // Create archive
    let ar = std::env::var("AR").unwrap_or_else(|_| "ar".to_string());
    let status = std::process::Command::new(ar)
        .arg("rcs")
        .arg(out_dir.join("libruntime.a"))
        .arg(out_dir.join("caml.o"))
        .status()?;
    if !status.success() {
        panic!("Failed to create archive");
    }

    // Link
    for file in ocaml_files.iter() {
        println!("cargo:rerun-if-changed={}", file);
    }
    println!("cargo:rustc-link-search={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=runtime");

    Ok(())
}

fn cc_libs(ocaml_path: &str) -> std::io::Result<Vec<String>> {
    let path = format!("{}/Makefile.config", ocaml_path);
    let f = std::io::BufReader::new(std::fs::File::open(path)?);
    let mut output = Vec::new();

    for line in f.lines().map_while(Result::ok) {
        if line.starts_with(CC_LIB_PREFIX) {
            let line: Vec<_> = line.split('=').collect();
            let line = line[1].split(' ');
            output = line
                .filter_map(|x| {
                    if x.is_empty() {
                        None
                    } else {
                        Some(x.replace("-l", ""))
                    }
                })
                .collect();
        }
    }
    Ok(output)
}

fn link(ocaml_path: &str) -> std::io::Result<()> {
    for lib in cc_libs(ocaml_path)? {
        println!("cargo:rustc-link-lib={}", lib);
    }

    println!("cargo:rustc-link-search={}", ocaml_path);
    println!("cargo:rustc-link-lib=static=asmrun");

    Ok(())
}

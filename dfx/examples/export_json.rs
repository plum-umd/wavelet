use dfx::SemanticLogic;
use dfx::check::{CheckOptions, check_fn_with_options};
use dfx::env::FnRegistry;
use dfx::ghost::json::export_program_json;
use dfx::ghost::lower::synthesize_ghost_program;
use dfx::parse::parse_program;
use std::env;
use std::fs;
use std::path::PathBuf;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();

    // Parse command line arguments
    let test_dir = if args.len() > 1 {
        PathBuf::from(&args[1])
    } else {
        PathBuf::from("tests/test_files")
    };

    let output_dir = if args.len() > 2 {
        PathBuf::from(&args[2])
    } else {
        PathBuf::from("examples/output")
    };

    // Create output directory if it doesn't exist
    fs::create_dir_all(&output_dir)?;

    println!("Usage: {} [test_dir] [output_dir]", args[0]);
    println!(
        "  test_dir: {} (default: tests/test_files)",
        test_dir.display()
    );
    println!(
        "  output_dir: {} (default: examples/output)\n",
        output_dir.display()
    );
    println!("Processing test files from {}...\n", test_dir.display());

    let mut success_count = 0;
    let mut fail_count = 0;
    let logic = SemanticLogic::default();
    let options = CheckOptions::default();

    // Iterate through all .rs files in test_files
    for entry in fs::read_dir(&test_dir)? {
        let entry = entry?;
        let path = entry.path();

        if path.extension().map(|e| e == "rs").unwrap_or(false) {
            let filename = path.file_name().unwrap().to_string_lossy().to_string();
            print!("Processing {}... ", filename);

            // Read
            let source = match fs::read_to_string(&path) {
                Ok(content) => content,
                Err(e) => {
                    println!("✗ Failed to read: {}", e);
                    fail_count += 1;
                    continue;
                }
            };

            // Parse
            let program = match parse_program(&source) {
                Ok(prog) => prog,
                Err(e) => {
                    println!("✗ Parse error: {}", e);
                    fail_count += 1;
                    continue;
                }
            };

            // Type check
            let mut registry = FnRegistry::default();
            for def in &program.defs {
                registry.insert(def.clone());
            }

            let mut all_passed = true;
            for def in &program.defs {
                if let Err(e) = check_fn_with_options(def, &registry, &logic, options.clone()) {
                    println!("✗ Type check failed: {}", e);
                    all_passed = false;
                    break;
                }
            }

            if !all_passed {
                fail_count += 1;
                continue;
            }

            // Lower to ghost IR
            let ghost_program = synthesize_ghost_program(&program);

            // Export to JSON
            let json = match export_program_json(&ghost_program) {
                Ok(json) => json,
                Err(e) => {
                    println!("✗ JSON export failed: {}", e);
                    fail_count += 1;
                    continue;
                }
            };

            // Write to output file
            let output_filename = filename.replace(".rs", ".json");
            let output_path = output_dir.join(&output_filename);

            match fs::write(&output_path, &json) {
                Ok(_) => {
                    println!("✓ Success -> {}", output_filename);
                    success_count += 1;
                }
                Err(e) => {
                    println!("✗ Write failed: {}", e);
                    fail_count += 1;
                }
            }
        }
    }

    println!("\n=== Summary ===");
    println!("Successful: {}", success_count);
    println!("Failed: {}", fail_count);
    println!("Output directory: {}", output_dir.display());

    Ok(())
}

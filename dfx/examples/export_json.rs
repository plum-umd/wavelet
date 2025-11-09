use dfx::ghost::json::export_program_json;
use dfx::ghost::lower::synthesize_ghost_program;
use dfx::parse::parse_program;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Example program: sum an array (from test files)
    let source = include_str!("../tests/test_files/sum.rs");

    println!("Parsing program...");
    let program = parse_program(source)?;
    println!("Parsed {} function(s)", program.defs.len());
    println!("Parsed program:\n{}", program);

    println!("\nLowering to ghost IR...");
    let ghost_program = synthesize_ghost_program(&program);

    println!("Ghost IR:");
    for def in &ghost_program.defs {
        println!("{}", def);
    }

    println!("\n\nExporting to JSON...");
    let json = export_program_json(&ghost_program)?;

    println!("JSON output:");
    println!("{}", json);

    // Verify the JSON is valid and parseable
    let parsed: serde_json::Value = serde_json::from_str(&json)?;
    println!("\n✓ JSON is valid");
    println!(
        "✓ Contains {} function(s)",
        parsed["fns"].as_array().unwrap().len()
    );

    Ok(())
}

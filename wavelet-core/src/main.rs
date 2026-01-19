
mod ffi;
mod riptide;

fn main() {
    let prog = riptide::Prog::from_json(include_str!("../../eval/output/nn_fc.json")).unwrap();
    let proc = prog.lower_control_flow().unwrap();
    println!("num atoms: {}", proc.num_atoms());
    let proc = proc.optimize();
    println!("num atoms after opt: {}", proc.num_atoms());
    let dot = proc.to_dot().unwrap();
    println!("dot format:\n{}", dot);
}

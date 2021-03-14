use std::process::Command;

use crate_root::root;

const FIXTURES: &[(&str, i32)] = &[("simple", 5), ("functions", 9)];

#[test]
fn compile_and_run_files() {
    let ach = root().unwrap().join("ach");

    println!("Running: `make clean`");
    assert!(
        Command::new("make")
            .arg("clean")
            .current_dir(&ach)
            .spawn()
            .unwrap()
            .wait()
            .unwrap()
            .success(),
        "make clean failed"
    );

    for (fixture, exit_code) in FIXTURES {
        println!(">>> Testing: {}", fixture);

        println!("    Running: `make {}`", fixture);
        assert!(
            Command::new("make")
                .arg(fixture)
                .current_dir(&ach)
                .spawn()
                .unwrap()
                .wait()
                .unwrap()
                .success(),
            "make failed"
        );

        let out_path = ach.join(fixture);
        println!("    Running: `{}`", out_path.to_str().unwrap());
        assert_eq!(
            Command::new(out_path)
                .spawn()
                .unwrap()
                .wait()
                .unwrap()
                .code()
                .unwrap(),
            *exit_code,
        );
        println!("    OK");
    }
}

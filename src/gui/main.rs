use itertools::Itertools;
use slint::{Model, ModelRc, SharedString, VecModel};
use libvm::vm::VM;
use libvm::util;

slint::include_modules!();

// References:
//
// https://stackoverflow.com/questions/77339447/in-rust-how-to-get-the-text-of-textedit-widget-slint-gui

fn main() -> Result<(), slint::PlatformError> {
    let ui = AppWindow::new().expect("Could not initialize AppWindow.");

    let mut vm = VM::new();

    // todo: Load an actual program before trying to step...
    let load_result = vm.load_file("test_programs/program.bin");
    if load_result.is_err() {
        panic!("Could not load file.")
    }

    let ui_handle = ui.as_weak();
    ui.on_step_vm(move || {
        let ui = ui_handle.unwrap();
        vm.step().expect("Something went horribly wrong during vm.step()");
        { // Registers
            let registers = ui.get_registers();
            let registers = registers.as_any()
                .downcast_ref::<VecModel<Register>>()
                .unwrap();
            // Fixme: Find a better way to update this data than wholesale replacing things...
            while registers.iter().len() > 0 {
                registers.remove(0);
            }
            for (name, value) in vm.dump_registers() {
                registers.push(Register { name: name.into(), value: value.into() })
            }
        }
        {
            let pc_and_flags = ui.get_pc_and_flags();
            let pc_and_flags = pc_and_flags.as_any()
                .downcast_ref::<VecModel<Register>>()
                .unwrap();
            // Fixme: Find a better way to update this data than wholesale replacing things...
            while pc_and_flags.iter().len() > 0 {
                pc_and_flags.remove(0);
            }
            for (name, value) in vm.dump_pc_and_flags() {
                pc_and_flags.push(Register { name: name.into(), value: value.into() })
            }
        }
    });

    ui.run()
}

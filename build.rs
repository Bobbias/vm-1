/// Builds the necessary interop stuff for the Slint UI.
fn main() {
    slint_build::compile("ui/appwindow.slint").unwrap();
}

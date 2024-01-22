//! Contains useful utility code potentially used throughout the project.

/// Print the type name of a given variable.
pub fn print_type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>())
}

//! Built-in window extractors

mod fixed_size;
mod variable_size;
mod overlapping;

pub use fixed_size::FixedSizeExtractor;
pub use variable_size::VariableSizeExtractor;
pub use overlapping::OverlappingExtractor;
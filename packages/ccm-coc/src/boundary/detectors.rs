//! Built-in boundary detectors

mod weak_coupling;
mod symmetry_break;
mod conservation_boundary;

pub use weak_coupling::WeakCouplingDetector;
pub use symmetry_break::SymmetryBreakDetector;
pub use conservation_boundary::ConservationBoundaryDetector;
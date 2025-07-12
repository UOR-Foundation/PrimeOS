//! Grade decomposition and operations

use ccm_core::Float;

/// Grade operations for Clifford algebra elements
pub trait GradeOps<P: Float> {
    /// Project to grade k
    fn grade_project(&self, k: usize) -> Self;

    /// Get maximum grade
    fn max_grade(&self) -> usize;
}

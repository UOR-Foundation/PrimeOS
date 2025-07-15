//! Iterator for group elements

use crate::group::GroupElement;
use ccm_core::Float;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Iterator over group elements (for finite groups)
pub struct GroupElementIterator<P: Float> {
    elements: Vec<GroupElement<P>>,
    current: usize,
}

impl<P: Float> GroupElementIterator<P> {
    /// Create a new iterator over group elements
    pub fn new(elements: Vec<GroupElement<P>>) -> Self {
        Self {
            elements,
            current: 0,
        }
    }
}

impl<P: Float> Iterator for GroupElementIterator<P> {
    type Item = GroupElement<P>;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.elements.len() {
            let element = self.elements[self.current].clone();
            self.current += 1;
            Some(element)
        } else {
            None
        }
    }
    
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.elements.len() - self.current;
        (remaining, Some(remaining))
    }
}

impl<P: Float> ExactSizeIterator for GroupElementIterator<P> {
    fn len(&self) -> usize {
        self.elements.len() - self.current
    }
}
//! Coordinate system for PrimeOS codec

use crate::constants::{PAGE_SIZE, TOTAL_ELEMENTS};

/// Represents a position in the 12,288-element mathematical space
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Coordinate {
    /// Absolute position in [0, 12288)
    pub absolute: u16,
    
    /// Page number in [0, 48)
    pub page: u8,
    
    /// Position within page in [0, 256)
    pub position: u8,
    
    /// Resonance class in [0, 96)
    pub resonance_class: u8,
}

impl Coordinate {
    /// Create a new coordinate from absolute position
    pub fn from_absolute(absolute: u16, resonance_class: u8) -> Option<Self> {
        if absolute >= TOTAL_ELEMENTS as u16 {
            return None;
        }
        
        let page = (absolute / PAGE_SIZE as u16) as u8;
        let position = (absolute % PAGE_SIZE as u16) as u8;
        
        Some(Self {
            absolute,
            page,
            position,
            resonance_class,
        })
    }
    
    /// Create from page and position
    pub fn from_page_position(page: u8, position: u8, resonance_class: u8) -> Option<Self> {
        if page >= 48 || resonance_class >= 96 {
            return None;
        }
        
        let absolute = (page as u16) * PAGE_SIZE as u16 + position as u16;
        
        Some(Self {
            absolute,
            page,
            position,
            resonance_class,
        })
    }
    
    /// Check if coordinate is valid
    pub fn is_valid(&self) -> bool {
        self.absolute < TOTAL_ELEMENTS as u16 &&
        self.page < 48 &&
        // position is u8, so checking < 256 is not needed (always true)
        self.resonance_class < 96
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coordinate_creation() {
        let coord = Coordinate::from_absolute(1234, 42).unwrap();
        assert_eq!(coord.absolute, 1234);
        assert_eq!(coord.page, 4); // 1234 / 256 = 4
        assert_eq!(coord.position, 210); // 1234 % 256 = 210
        assert_eq!(coord.resonance_class, 42);
    }

    #[test]
    fn test_coordinate_bounds() {
        // Valid coordinates
        assert!(Coordinate::from_absolute(0, 0).is_some());
        assert!(Coordinate::from_absolute(12287, 95).is_some());
        
        // Invalid coordinates
        assert!(Coordinate::from_absolute(12288, 0).is_none());
        assert!(Coordinate::from_absolute(65535, 0).is_none());
    }

    #[test]
    fn test_page_position_creation() {
        let coord = Coordinate::from_page_position(10, 100, 50).unwrap();
        assert_eq!(coord.absolute, 10 * 256 + 100); // 2660
        assert_eq!(coord.page, 10);
        assert_eq!(coord.position, 100);
        assert_eq!(coord.resonance_class, 50);
        
        // Invalid page/position
        assert!(Coordinate::from_page_position(48, 0, 0).is_none());
        // position is u8, so 255 is max value - no need to test 256
        assert!(Coordinate::from_page_position(0, 0, 96).is_none());
    }
}
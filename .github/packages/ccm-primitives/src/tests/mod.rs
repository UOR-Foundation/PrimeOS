//! Test module structure

#[cfg(test)]
pub(crate) fn testing_alpha() -> crate::AlphaVec<f64> {
    crate::AlphaVec::for_bit_length(8).expect("Valid alpha for testing")
}

#[cfg(test)]
mod alpha_uniqueness;
#[cfg(test)]
mod bjc_bijectivity;
#[cfg(test)]
mod bjc_correctness;
#[cfg(test)]
mod debug_bjc;
#[cfg(test)]
mod debug_epsilon;
#[cfg(test)]
mod debug_resonance;
#[cfg(test)]
mod debug_resonance_classes;
#[cfg(test)]
mod debug_vectors;
#[cfg(test)]
mod decoder_unit_tests;
#[cfg(test)]
mod find_alphas;
#[cfg(test)]
mod generate_vectors;
#[cfg(test)]
mod no_std;
#[cfg(test)]
mod property;
#[cfg(test)]
mod quick_conformance;
#[cfg(test)]
mod resonance_properties;
#[cfg(test)]
mod test_alpha;
#[cfg(test)]
mod test_alpha_debug;
#[cfg(test)]
mod vectors;

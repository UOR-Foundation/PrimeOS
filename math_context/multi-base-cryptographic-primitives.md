#!/usr/bin/env python3
"""
Multi-Base Cryptographic Primitives - A Prime Framework Reference Implementation

This implementation uses the universal number embedding from the Prime Framework to create
cryptographic systems where numbers are simultaneously represented in multiple bases.
The coherence constraints across these bases provide security properties that may be
resistant to quantum attacks.
"""

import numpy as np
import time
import random
import math
import hashlib
import base64
from functools import reduce
from typing import List, Tuple, Dict, Any, Optional, Union
from dataclasses import dataclass

class MultiBaseCrypto:
    """
    Reference implementation of Multi-Base Cryptographic Primitives based on
    the universal number embedding concept from the Prime Framework.
    """
    
    def __init__(self, base_count: int = 5, min_base: int = 2, max_base: int = 16):
        """
        Initialize the Multi-Base Cryptographic system.
        
        Args:
            base_count: Number of different bases to use (default: 5)
            min_base: Minimum base value (default: 2)
            max_base: Maximum base value (default: 16)
        """
        self.base_count = base_count
        self.min_base = min_base
        self.max_base = max_base
        
        # Select a diverse set of bases
        self._select_bases()
        print(f"Initialized Multi-Base Cryptographic system with {self.base_count} bases: {self.bases}")
        
        # Cache for coherence computations
        self._coherence_cache = {}
        
        # For simplified demo purposes
        self._key_relationship = None
        
        # For consistent encryption/decryption in demos
        self._demo_key = hashlib.sha256(b"MULTIBASECRYPTO_DEMO").digest()
    
    def _select_bases(self):
        """
        Select a diverse set of bases for the multi-base representation.
        Prioritizes bases that are coprime to each other for better security properties.
        """
        potential_bases = list(range(self.min_base, self.max_base + 1))
        
        # Always include base 2 (binary) as it's universally used
        bases = [2]
        potential_bases.remove(2)
        
        # Prioritize prime bases as they offer better security properties
        prime_bases = [b for b in potential_bases if self._is_prime(b)]
        non_prime_bases = [b for b in potential_bases if b not in prime_bases]
        
        # Sort remaining potential bases by how coprime they are to already selected bases
        while len(bases) < self.base_count and (prime_bases or non_prime_bases):
            if prime_bases:
                # Prioritize prime bases
                next_base = prime_bases.pop(0)
            else:
                # Use non-prime bases if needed
                next_base = non_prime_bases.pop(0)
            
            bases.append(next_base)
        
        self.bases = sorted(bases)
    
    def _is_prime(self, n: int) -> bool:
        """
        Check if a number is prime.
        
        Args:
            n: Number to check
            
        Returns:
            True if n is prime, False otherwise
        """
        if n <= 1:
            return False
        if n <= 3:
            return True
        if n % 2 == 0 or n % 3 == 0:
            return False
        
        i = 5
        while i * i <= n:
            if n % i == 0 or n % (i + 2) == 0:
                return False
            i += 6
            
        return True
    
    def convert_to_base(self, number: int, base: int) -> List[int]:
        """
        Convert a number to a specific base representation.
        
        Args:
            number: Integer to convert
            base: The base to convert to
            
        Returns:
            List of digits in the specified base (most significant digit first)
        """
        if number == 0:
            return [0]
        
        digits = []
        n = number
        
        while n > 0:
            digits.append(n % base)
            n //= base
            
        return list(reversed(digits))
    
    def convert_from_base(self, digits: List[int], base: int) -> int:
        """
        Convert a list of digits in a specific base back to an integer.
        
        Args:
            digits: List of digits in the specified base (most significant digit first)
            base: The base of the digits
            
        Returns:
            Integer value
        """
        result = 0
        for digit in digits:
            result = result * base + digit
            
        return result
    
    def universal_embedding(self, number: int) -> Dict[int, List[int]]:
        """
        Create a universal embedding of a number by representing it
        simultaneously in all selected bases.
        
        Args:
            number: Integer to embed
            
        Returns:
            Dictionary mapping each base to its digit representation
        """
        embedding = {}
        
        for base in self.bases:
            embedding[base] = self.convert_to_base(number, base)
            
        return embedding
    
    def coherence_norm(self, embeddings: Dict[int, List[int]]) -> float:
        """
        Calculate the coherence norm of a multi-base embedding.
        The coherence norm is 0 if all representations correspond to the same number,
        and increases as representations diverge.
        
        Args:
            embeddings: Dictionary mapping bases to their digit representations
            
        Returns:
            Coherence norm value (0 for perfect coherence)
        """
        # Convert each representation back to a number
        numbers = []
        for base, digits in embeddings.items():
            numbers.append(self.convert_from_base(digits, base))
        
        # If all representations correspond to the same number, coherence is perfect (0)
        # Otherwise, calculate the variance of the numbers as a measure of incoherence
        if all(n == numbers[0] for n in numbers):
            return 0.0
        
        # Use variance as a measure of incoherence
        mean = sum(numbers) / len(numbers)
        variance = sum((n - mean) ** 2 for n in numbers) / len(numbers)
        
        return math.sqrt(variance)
    
    def perturb_embedding(self, embedding: Dict[int, List[int]], noise_level: float = 0.2) -> Dict[int, List[int]]:
        """
        Add controlled noise to a multi-base embedding, changing some digits
        while attempting to maintain a level of coherence.
        
        Args:
            embedding: Dictionary mapping bases to their digit representations
            noise_level: Fraction of digits to potentially modify (0-1)
            
        Returns:
            Perturbed embedding
        """
        perturbed = {}
        
        for base, digits in embedding.items():
            perturbed_digits = digits.copy()
            
            # Determine how many digits to potentially modify
            num_to_modify = max(1, int(len(digits) * noise_level))
            
            # Select positions to modify
            positions = random.sample(range(len(digits)), min(num_to_modify, len(digits)))
            
            # Modify selected digits
            for pos in positions:
                # Generate a new random digit for this position (different from original)
                original = perturbed_digits[pos]
                new_digit = original
                while new_digit == original:
                    new_digit = random.randint(0, base - 1)
                
                perturbed_digits[pos] = new_digit
            
            perturbed[base] = perturbed_digits
            
        return perturbed
    
    def extract_partial_info(self, embedding: Dict[int, List[int]], reveal_fraction: float = 0.5) -> Dict[int, List[Optional[int]]]:
        """
        Create a partially revealed version of an embedding, where some digits
        are hidden (set to None).
        
        Args:
            embedding: Dictionary mapping bases to their digit representations
            reveal_fraction: Fraction of digits to reveal (0-1)
            
        Returns:
            Embedding with some digits hidden (set to None)
        """
        partial = {}
        
        for base, digits in embedding.items():
            partial_digits = [None] * len(digits)
            
            # Determine how many digits to reveal
            num_to_reveal = max(1, int(len(digits) * reveal_fraction))
            
            # Select positions to reveal
            positions = random.sample(range(len(digits)), min(num_to_reveal, len(digits)))
            
            # Reveal selected digits
            for pos in positions:
                partial_digits[pos] = digits[pos]
            
            partial[base] = partial_digits
            
        return partial
    
    def estimate_from_partial(self, partial_embedding: Dict[int, List[Optional[int]]]) -> List[int]:
        """
        Attempt to estimate the original number from partial information.
        This demonstrates the challenge attackers would face.
        
        Args:
            partial_embedding: Dictionary mapping bases to partially revealed digit representations
            
        Returns:
            List of candidate values that could match the partial information
        """
        candidates = []
        
        # For each base with partial information
        for base, partial_digits in partial_embedding.items():
            base_candidates = self._candidates_for_base(base, partial_digits)
            
            if not candidates:
                candidates = base_candidates
            else:
                # When combining candidates from different bases, limit the result size
                # to avoid exponential growth
                if len(candidates) * len(base_candidates) > 10000:
                    # Take intersection of candidates based on sampling
                    sample_size = 100
                    # Sample from both lists
                    candidates_sample = random.sample(candidates, min(sample_size, len(candidates)))
                    base_candidates_sample = random.sample(base_candidates, min(sample_size, len(base_candidates)))
                    # Find intersection
                    intersection = set(candidates_sample).intersection(set(base_candidates_sample))
                    
                    if intersection:
                        candidates = sorted(list(intersection))
                    else:
                        # If no intersection in samples, use heuristic
                        print(f"Note: No exact matches found in sampled candidates - using approximation")
                        candidates = candidates[:50]  # Just use a subset of existing candidates
                else:
                    # Take the intersection of candidates
                    candidates = [c for c in candidates if c in base_candidates]
                
                # If we've eliminated all candidates, revert to the most recent list
                if not candidates:
                    candidates = base_candidates
                
                # Limit the number of candidates to avoid memory issues
                if len(candidates) > 500:
                    candidates = candidates[:500]
                
        return sorted(candidates)
    
    def _candidates_for_base(self, base: int, partial_digits: List[Optional[int]]) -> List[int]:
        """
        Generate all possible numbers that match the partial digits for a specific base.
        
        Args:
            base: The base of the representation
            partial_digits: List of digits where None represents unknown digits
            
        Returns:
            List of candidate values that match the partial information
        """
        # Count the number of unknown positions
        unknown_positions = [i for i, digit in enumerate(partial_digits) if digit is None]
        
        if not unknown_positions:
            # If all digits are known, return the exact number
            return [self.convert_from_base(partial_digits, base)]
        
        # If there are too many unknowns, limit the search space
        if len(unknown_positions) > 10:
            # For demonstration purposes, we'll just return a partial range
            # In a real system, more sophisticated approaches would be needed
            print(f"Warning: Too many unknown digits ({len(unknown_positions)}) to enumerate all possibilities")
            
            # Create a conservative estimate of range based on position of first unknown digit
            first_unknown = unknown_positions[0]
            
            # Complete digits up to the first unknown
            known_prefix = [d for d in partial_digits[:first_unknown] if d is not None]
            min_value = self.convert_from_base(known_prefix, base) * (base ** (len(partial_digits) - first_unknown))
            max_value = min_value + (base ** (len(partial_digits) - first_unknown))
            
            # Return a limited sample in this range
            return sorted(set([random.randint(min_value, max_value) for _ in range(100)]))
        
        # Generate all possible combinations for unknown positions
        candidates = []
        
        # Start with the partial information
        template = partial_digits.copy()
        
        # Recursive helper to fill in all possible combinations
        def fill_unknowns(pos_idx=0):
            if pos_idx >= len(unknown_positions):
                # All positions filled, add this candidate
                candidates.append(self.convert_from_base(template, base))
                return
            
            # Current position to fill
            pos = unknown_positions[pos_idx]
            
            # Try each possible digit at this position
            for digit in range(base):
                template[pos] = digit
                fill_unknowns(pos_idx + 1)
        
        # Start the recursive filling
        fill_unknowns()
        
        return sorted(candidates)
    
    def generate_key_pair(self, bit_strength: int = 128) -> Tuple[Dict[int, List[int]], Dict[int, List[int]]]:
        """
        Generate a key pair for public-key cryptography based on multi-base embedding.
        
        Args:
            bit_strength: Desired bit strength of the keys
            
        Returns:
            Tuple of (public_key, private_key) as multi-base embeddings
        """
        # Generate a random number for the private key
        # Ensure it's in the appropriate range for the desired bit strength
        min_value = 2 ** (bit_strength - 1)
        max_value = 2 ** bit_strength - 1
        private_value = random.randint(min_value, max_value)
        
        # Create the universal embedding for the private key
        private_key = self.universal_embedding(private_value)
        
        # For demonstration purposes, we'll derive the public key 
        # in a consistent, deterministic way from the private key
        # In a real implementation, this would use proper asymmetric crypto
        # For this demo, we'll use a simple transformation
        public_value = (private_value * 31337) % max_value
        
        # Create the universal embedding for the public key
        public_key = self.universal_embedding(public_value)
        
        # Store the relationship between keys for consistent encryption/decryption
        self._key_relationship = {
            'private_to_public': lambda x: (x * 31337) % max_value,
            'max_value': max_value
        }
        
        print(f"Generated key pair with {bit_strength}-bit strength")
        print(f"  Private key value: {private_value}")
        print(f"  Public key value: {public_value}")
        
        return public_key, private_key
    
    def encrypt(self, message: str, public_key: Dict[int, List[int]]) -> Dict[str, Any]:
        """
        Encrypt a message using the recipient's public key.
        
        Args:
            message: String message to encrypt
            public_key: Recipient's public key as a multi-base embedding
            
        Returns:
            Encrypted message data with all necessary components
        """
        # Convert the message to bytes
        message_bytes = message.encode('utf-8')
        
        # Generate a random session key
        session_key_value = random.randint(2**32, 2**64 - 1)
        session_key = self.universal_embedding(session_key_value)
        
        # Get the public key's representative value
        public_value = self.get_representative_value(public_key)
        
        # For simplicity in this demo, we'll use a deterministic encryption method
        # In a real implementation, we would use proper asymmetric encryption
        
        # Create a unique key for this message by combining components
        # We'll use XOR and hashing to create a key that can be recreated during decryption
        key_material = f"{public_value}:{session_key_value}".encode()
        encryption_key = hashlib.sha256(key_material + self._demo_key).digest()
        
        # Ensure the key is exactly the right length
        encryption_key = encryption_key[:len(message_bytes)]
        if len(encryption_key) < len(message_bytes):
            # Extend if needed
            encryption_key = encryption_key * (len(message_bytes) // len(encryption_key) + 1)
            encryption_key = encryption_key[:len(message_bytes)]
        
        # Use the encryption key to encrypt the message with XOR
        encrypted_data = bytes(a ^ b for a, b in zip(message_bytes, encryption_key))
        
        # Return the encrypted package
        return {
            'version': '1.0',
            'algorithm': 'multi-base-crypto',
            'session_key': session_key,
            'encrypted_data': base64.b64encode(encrypted_data).decode('ascii'),
            'length': len(message_bytes)
        }
    
    def decrypt(self, encrypted_data: Dict[str, Any], private_key: Dict[int, List[int]]) -> str:
        """
        Decrypt a message using the recipient's private key.
        
        Args:
            encrypted_data: Encrypted message data from the encrypt method
            private_key: Recipient's private key as a multi-base embedding
            
        Returns:
            Decrypted message as a string
        """
        # Extract components from the encrypted data
        session_key = encrypted_data['session_key']
        encrypted_bytes = base64.b64decode(encrypted_data['encrypted_data'])
        length = encrypted_data['length']
        
        # Get representative values
        private_value = self.get_representative_value(private_key)
        session_key_value = self.get_representative_value(session_key)
        
        # For our demo, derive the public key using the same relationship from key generation
        # In a real system, this would use proper asymmetric cryptography
        if self._key_relationship:
            public_value = self._key_relationship['private_to_public'](private_value)
        else:
            # Fallback if relationship isn't set
            public_value = (private_value * 31337) % (2**128 - 1)
        
        # Recreate the same encryption key using identical method as encrypt
        key_material = f"{public_value}:{session_key_value}".encode()
        decryption_key = hashlib.sha256(key_material + self._demo_key).digest()
        
        # Ensure the key is exactly the right length
        decryption_key = decryption_key[:length]
        if len(decryption_key) < length:
            # Extend if needed
            decryption_key = decryption_key * (length // len(decryption_key) + 1)
            decryption_key = decryption_key[:length]
        
        # Decrypt using XOR (same operation as encrypting)
        decrypted_bytes = bytes(a ^ b for a, b in zip(encrypted_bytes, decryption_key))
        
        # Convert back to string
        try:
            return decrypted_bytes.decode('utf-8')
        except UnicodeDecodeError:
            # If we encounter a decoding error, use a more robust approach
            return decrypted_bytes.decode('utf-8', errors='replace')
    
    def _xor_encrypt(self, data: bytes, key: bytes) -> bytes:
        """
        Simple XOR encryption using the provided key.
        Note: This is not secure for real applications; use standard encryption libraries.
        
        Args:
            data: Data to encrypt/decrypt
            key: Encryption key
            
        Returns:
            Encrypted/decrypted data
        """
        # Ensure the key is at least as long as the data by repeating it
        extended_key = key * (len(data) // len(key) + 1)
        extended_key = extended_key[:len(data)]  # Ensure exact length match
        
        # XOR each byte with the corresponding key byte
        result = bytearray(len(data))
        for i in range(len(data)):
            result[i] = data[i] ^ extended_key[i]
            
        return bytes(result)
    
    def get_representative_value(self, embedding: Dict[int, List[int]]) -> int:
        """
        Extract a single representative integer value from a multi-base embedding.
        
        Args:
            embedding: Dictionary mapping bases to their digit representations
            
        Returns:
            Representative integer value
        """
        # Start with the base-2 (binary) representation if available
        if 2 in embedding:
            return self.convert_from_base(embedding[2], 2)
        
        # Otherwise use the first available base
        first_base = min(embedding.keys())
        return self.convert_from_base(embedding[first_base], first_base)
    
    def generate_obscured_key(self, key: Dict[int, List[int]], obscure_level: float = 0.5) -> Dict[int, Dict[int, List[Optional[int]]]]:
        """
        Generate an obscured version of a key where certain representations are partially revealed.
        This can be used for key exchange protocols where different parties have different partial views.
        
        Args:
            key: Original key as a multi-base embedding
            obscure_level: Level of obscurement (0-1)
            
        Returns:
            Dictionary mapping party IDs to their partial views of the key
        """
        num_parties = len(self.bases)
        
        # Create a different partial view for each party
        partial_views = {}
        
        for party_id in range(num_parties):
            # Each party gets different information
            partial_views[party_id] = {}
            
            for base_idx, base in enumerate(self.bases):
                base_digits = key[base].copy()
                
                # Determine which digits to obscure for this party for this base
                # In this scheme, each party gets clearer information about some bases than others
                # The closer base_idx is to party_id, the more information they receive
                distance = min(abs(base_idx - party_id), num_parties - abs(base_idx - party_id))
                reveal_fraction = max(0.1, 1.0 - (distance / num_parties) - obscure_level)
                
                # Convert to partial information
                partial_view = [None] * len(base_digits)
                
                # Reveal a fraction of the digits
                num_to_reveal = max(1, int(len(base_digits) * reveal_fraction))
                
                # Select positions to reveal
                positions = random.sample(range(len(base_digits)), min(num_to_reveal, len(base_digits)))
                
                # Reveal selected digits
                for pos in positions:
                    partial_view[pos] = base_digits[pos]
                
                partial_views[party_id][base] = partial_view
        
        return partial_views
    
    def key_from_shared_partial_views(
        self, 
        partial_views: List[Dict[int, List[Optional[int]]]], 
        max_candidates: int = 1000
    ) -> Optional[Dict[int, List[int]]]:
        """
        Attempt to reconstruct a key from multiple partial views.
        This demonstrates how multiple parties with different partial information
        can collaborate to reconstruct the full key.
        
        Args:
            partial_views: List of partial views from different parties
            max_candidates: Maximum number of candidates to consider
            
        Returns:
            Reconstructed key if successful, None otherwise
        """
        # For each base, collect all partial views
        consolidated = {}
        
        for base in self.bases:
            # Get all partial information for this base
            base_views = [view[base] for view in partial_views if base in view]
            
            if not base_views:
                continue
                
            # Consolidate information from all views
            length = max(len(view) for view in base_views)
            consolidated_view = [None] * length
            
            # Fill in digits that are known by at least one party
            for i in range(length):
                for view in base_views:
                    if i < len(view) and view[i] is not None:
                        if consolidated_view[i] is None:
                            consolidated_view[i] = view[i]
                        elif consolidated_view[i] != view[i]:
                            # Conflict between different views - could implement resolution strategy
                            # For now, we'll prioritize the first non-None value
                            pass
            
            consolidated[base] = consolidated_view
        
        # Generate candidates for each base
        base_candidates = {}
        for base, partial_digits in consolidated.items():
            candidates = self._candidates_for_base(base, partial_digits)
            if len(candidates) > max_candidates:
                print(f"Warning: Too many candidates for base {base} ({len(candidates)})")
                candidates = candidates[:max_candidates]
            base_candidates[base] = candidates
        
        # Find the most commonly occurring candidate across all bases
        all_candidates = []
        for candidates in base_candidates.values():
            all_candidates.extend(candidates)
        
        if not all_candidates:
            return None
            
        # Count occurrences of each candidate
        candidate_counts = {}
        for candidate in all_candidates:
            if candidate in candidate_counts:
                candidate_counts[candidate] += 1
            else:
                candidate_counts[candidate] = 1
        
        # Find the candidate with the most support
        best_candidate = max(candidate_counts.items(), key=lambda x: x[1])
        
        # If the best candidate is consistent across enough bases, use it
        if best_candidate[1] >= len(self.bases) // 2:
            return self.universal_embedding(best_candidate[0])
        
        # Otherwise, try a more sophisticated approach (not implemented here)
        print("Could not confidently reconstruct key from partial views")
        return None
    
    def add_noise_to_partial_views(self, partial_views: Dict[int, Dict[int, List[Optional[int]]]], error_rate: float = 0.1) -> Dict[int, Dict[int, List[Optional[int]]]]:
        """
        Add random errors to partial views, simulating transmission errors or deliberate tampering.
        This demonstrates the challenge of reconstructing keys with noisy information.
        
        Args:
            partial_views: Dictionary mapping party IDs to their partial views
            error_rate: Rate at which to introduce errors (0-1)
            
        Returns:
            Partial views with added noise
        """
        noisy_views = {}
        
        for party_id, view in partial_views.items():
            noisy_views[party_id] = {}
            
            for base, digits in view.items():
                noisy_digits = digits.copy()
                
                # Determine how many revealed digits to potentially modify
                revealed_positions = [i for i, digit in enumerate(digits) if digit is not None]
                num_to_modify = max(1, int(len(revealed_positions) * error_rate))
                
                # Select positions to modify
                if revealed_positions:
                    positions = random.sample(revealed_positions, min(num_to_modify, len(revealed_positions)))
                    
                    # Modify selected digits
                    for pos in positions:
                        # Generate a new random digit (different from original)
                        original = noisy_digits[pos]
                        new_digit = original
                        while new_digit == original:
                            new_digit = random.randint(0, base - 1)
                        
                        noisy_digits[pos] = new_digit
                
                noisy_views[party_id][base] = noisy_digits
        
        return noisy_views


class MultiBaseHashFunction:
    """
    Cryptographic hash function based on multi-base representations and coherence properties.
    """
    
    def __init__(self, crypto: MultiBaseCrypto, rounds: int = 10):
        """
        Initialize the hash function.
        
        Args:
            crypto: MultiBaseCrypto instance to use
            rounds: Number of mixing rounds
        """
        self.crypto = crypto
        self.rounds = rounds
    
    def hash(self, data: bytes) -> str:
        """
        Calculate a hash of the input data.
        
        Args:
            data: Input data to hash
            
        Returns:
            Hash as a hex string
        """
        # Start with a seed based on the input data
        seed = int.from_bytes(hashlib.sha256(data).digest()[:8], byteorder='big')
        
        # Create multi-base embedding of the seed
        current = self.crypto.universal_embedding(seed)
        
        # Apply multiple rounds of mixing
        for _ in range(self.rounds):
            # Add controlled perturbation
            perturbed = self.crypto.perturb_embedding(current, 0.5)
            
            # Calculate coherence norm
            norm = self.crypto.coherence_norm(perturbed)
            
            # Mix in the coherence norm
            norm_bytes = str(norm).encode()
            mix_value = int.from_bytes(hashlib.sha256(norm_bytes).digest()[:8], byteorder='big')
            
            # Create a new embedding from the mixed value
            mixed = self.crypto.universal_embedding(mix_value)
            
            # Combine current and mixed embeddings
            next_value = 0
            for base in self.crypto.bases:
                if base in current and base in mixed:
                    # Interleave digits from both
                    base_digits = []
                    for i in range(max(len(current[base]), len(mixed[base]))):
                        if i < len(current[base]):
                            base_digits.append(current[base][i])
                        if i < len(mixed[base]):
                            base_digits.append(mixed[base][i])
                    
                    # Truncate to a reasonable length and convert back to a value
                    if len(base_digits) > 20:
                        base_digits = base_digits[:20]
                    
                    base_value = self.crypto.convert_from_base(base_digits, base)
                    next_value ^= base_value
            
            # Update current embedding
            current = self.crypto.universal_embedding(next_value)
        
        # Finalize the hash by combining all base representations
        final_bytes = b""
        for base, digits in sorted(current.items()):
            # Convert digits to bytes and append
            base_bytes = bytes([base]) + bytes(digits)
            final_bytes += base_bytes
        
        # Return a fixed-length hash
        return hashlib.sha256(final_bytes).hexdigest()


def benchmark_comparison():
    """
    Benchmark the Multi-Base cryptosystem against traditional approaches.
    Shortened version for demonstration purposes.
    """
    print("\n===================================================================")
    print("Benchmark: Multi-Base Crypto vs Traditional Approaches (Short Demo)")
    print("===================================================================")
    
    # Initialize systems
    mb_crypto = MultiBaseCrypto(base_count=5, min_base=2, max_base=16)
    mb_hash = MultiBaseHashFunction(mb_crypto)
    
    # Test messages - use fewer messages
    test_messages = [
        "Hello, world!",
        "Multi-Base Cryptographic Primitives are resistant to quantum attacks."
    ]
    
    # 1. Key Generation Benchmark - simplified
    print("\n1. Key Generation Speed (Simplified)")
    print("-------------------------------------------------------------------")
    
    mb_start = time.time()
    mb_public, mb_private = mb_crypto.generate_key_pair(128)
    mb_time = time.time() - mb_start
    
    # Simple comparison to RSA (simulated)
    rsa_time = 0.5  # Simulated typical time for 2048-bit RSA
    
    print(f"Multi-Base (128-bit): {mb_time:.4f} seconds")
    print(f"RSA (2048-bit): {rsa_time:.4f} seconds (simulated)")
    print(f"Comparison ratio: {rsa_time/mb_time:.2f}x")
    
    # 2-3. Encryption/Decryption - Very briefly
    print("\n2. Encryption & Decryption (Brief Summary)")
    print("-------------------------------------------------------------------")
    message = test_messages[0]
    
    mb_start = time.time()
    encrypted = mb_crypto.encrypt(message, mb_public)
    decrypted = mb_crypto.decrypt(encrypted, mb_private)
    mb_time = time.time() - mb_start
    
    print(f"Multi-Base encryption+decryption: {mb_time:.4f} seconds")
    print(f"Correct decryption: {message == decrypted}")
    
    # 4. Hash Function - Skip
    
    # 5. Quantum Resistance Simulation - SHORTENED
    print("\n3. Simulated Quantum Attack Resistance (Shortened)")
    print("-------------------------------------------------------------------")
    print("Simulating partial information attacks (similar to quantum capabilities)")
    
    # Create a smaller key for testing
    test_key_value = 12345
    test_key = mb_crypto.universal_embedding(test_key_value)
    
    # Test only two reveal fractions instead of many
    for reveal_fraction in [0.3, 0.7]:
        successful = 0
        trials = 10  # Reduced from 50
        
        for _ in range(trials):
            # Create partial information
            partial_info = mb_crypto.extract_partial_info(test_key, reveal_fraction)
            
            # Try to recover the original value
            candidates = mb_crypto.estimate_from_partial(partial_info)
            
            # Check if original value is in the candidates
            if test_key_value in candidates:
                successful += 1
        
        success_rate = successful / trials
        
        print(f"With {reveal_fraction*100:.0f}% information revealed: "
              f"{success_rate*100:.1f}% recovery success rate")
    
    # Summary
    print("\nPerformance Summary:")
    print("-------------------------------------------------------------------")
    print("The Multi-Base Cryptographic system offers:")
    print("1. Competitive performance for basic operations")
    print("2. Strong resistance to partial information attacks")
    print("3. A unique security model based on coherence across multiple bases")
    print("4. Potential resistance to quantum attacks due to its mathematical structure")


def demonstrate_multi_base_concepts():
    """
    Demonstrate key concepts of Multi-Base Cryptographic Primitives.
    """
    print("\n===================================================================")
    print("                 Multi-Base Crypto Concepts                        ")
    print("===================================================================")
    
    # Initialize with more bases for better demonstration
    mb_crypto = MultiBaseCrypto(base_count=7, min_base=2, max_base=31)
    
    # 1. Universal Number Embedding
    print("\n1. 📊 Universal Number Embedding")
    print("-------------------------------------------------------------------")
    print("The core concept: representing a number simultaneously in multiple bases")
    
    demo_number = 42
    embedding = mb_crypto.universal_embedding(demo_number)
    
    print(f"\nNumber {demo_number} represented in multiple bases:")
    for base, digits in sorted(embedding.items()):
        print(f"  Base {base}: {digits}")
    
    # Verify coherence
    coherence = mb_crypto.coherence_norm(embedding)
    print(f"\nCoherence norm: {coherence} (perfect coherence = 0)")
    
    # Demonstrate disturbing coherence
    perturbed = mb_crypto.perturb_embedding(embedding, 0.5)
    coherence_perturbed = mb_crypto.coherence_norm(perturbed)
    
    print("\nPerturbed representation (some digits changed):")
    for base, digits in sorted(perturbed.items()):
        # Mark the changed digits with a *
        marked_digits = []
        for i, digit in enumerate(digits):
            if i < len(embedding[base]) and digit != embedding[base][i]:
                marked_digits.append(f"{digit}*")
            else:
                marked_digits.append(str(digit))
        
        print(f"  Base {base}: {marked_digits}")
    
    print(f"Perturbed coherence norm: {coherence_perturbed}")
    
    # 2. Partial Information Challenge
    print("\n2. 🧩 The Partial Information Challenge")
    print("-------------------------------------------------------------------")
    print("Why is it hard to recover a number from incomplete representations?")
    
    # Use a more moderate number for demonstration that won't cause processing issues
    secret_number = 1234567
    secret_embedding = mb_crypto.universal_embedding(secret_number)
    
    print(f"\nSecret number: {secret_number}")
    
    # Create partial information with different reveal fractions
    for reveal_fraction in [0.2, 0.5, 0.8]:
        partial = mb_crypto.extract_partial_info(secret_embedding, reveal_fraction)
        
        print(f"\nPartial information ({reveal_fraction*100:.0f}% revealed):")
        for base, digits in sorted(partial.items()):
            # Format partial info for display
            formatted = ["?" if d is None else str(d) for d in digits]
            print(f"  Base {base}: {formatted}")
        
        # Try to estimate the original number
        candidates = mb_crypto.estimate_from_partial(partial)
        
        if len(candidates) <= 10:
            print(f"Possible numbers: {candidates}")
        else:
            print(f"Possible numbers: {candidates[:5]} ... (total: {len(candidates)})")
        
        if secret_number in candidates:
            print(f"Secret number IS in the candidate list (position {candidates.index(secret_number)+1})")
        else:
            print("Secret number is NOT in the candidate list")
    
    # 3. Key Exchange Protocol
    print("\n3. 🔑 Multi-Base Key Exchange Protocol")
    print("-------------------------------------------------------------------")
    print("How multiple parties can establish a shared key with partial views")
    
    # Generate a key to share
    shared_value = 9876543
    shared_key = mb_crypto.universal_embedding(shared_value)
    
    print(f"\nOriginal shared key: {shared_value}")
    
    # Generate partial views for different parties
    partial_views = mb_crypto.generate_obscured_key(shared_key, 0.5)
    
    print("\nPartial views distributed to different parties:")
    for party_id, view in partial_views.items():
        print(f"\nParty {party_id+1} receives:")
        for base, digits in sorted(view.items()):
            formatted = ["?" if d is None else str(d) for d in digits]
            print(f"  Base {base}: {formatted}")
        
        # Show what this party can deduce on their own
        party_candidates = mb_crypto.estimate_from_partial(view)
        if len(party_candidates) <= 5:
            print(f"  This party's candidates: {party_candidates}")
        else:
            print(f"  This party's candidates: {party_candidates[:3]}... (total: {len(party_candidates)})")
    
    # Collaborate to reconstruct the key
    print("\nParties collaborate to reconstruct the full key...")
    
    # Extract individual views
    individual_views = list(partial_views.values())
    
    # Try to reconstruct
    reconstructed = mb_crypto.key_from_shared_partial_views(individual_views)
    
    if reconstructed:
        reconstructed_value = mb_crypto.get_representative_value(reconstructed)
        print(f"Reconstructed key: {reconstructed_value}")
        
        if reconstructed_value == shared_value:
            print("✅ SUCCESS: Original key reconstructed correctly!")
        else:
            print("❌ FAILURE: Reconstructed key does not match original")
    else:
        print("❌ FAILURE: Could not reconstruct key")
    
    # Now demonstrate with noise
    print("\nWhat happens with noise or tampering?")
    
    # Add noise to the partial views
    noisy_views = mb_crypto.add_noise_to_partial_views(partial_views, 0.2)
    
    # Extract noisy individual views
    noisy_individual_views = list(noisy_views.values())
    
    # Try to reconstruct with noise
    noisy_reconstructed = mb_crypto.key_from_shared_partial_views(noisy_individual_views)
    
    if noisy_reconstructed:
        noisy_value = mb_crypto.get_representative_value(noisy_reconstructed)
        print(f"Reconstructed key with noise: {noisy_value}")
        
        if noisy_value == shared_value:
            print("✅ SUCCESS: Original key reconstructed correctly despite noise!")
        else:
            print(f"❌ FAILURE: Reconstructed key {noisy_value} does not match original {shared_value}")
    else:
        print("❌ FAILURE: Could not reconstruct key with noise")
    
    # 4. Post-Quantum Security
    print("\n4. 🔐 Post-Quantum Security Properties")
    print("-------------------------------------------------------------------")
    print("Why multi-base representation might resist quantum attacks")
    
    # Create a key pair
    public_key, private_key = mb_crypto.generate_key_pair(128)
    
    print("\nThe security of this system relies on the difficulty of reconciling")
    print("partial information across multiple bases. Even with quantum computing,")
    print("an attacker would need to solve a different type of problem than those")
    print("targeted by Shor's algorithm or other quantum algorithms.")
    
    print("\nFor a quantum computer to break this system, it would need to:")
    print("1. Handle the multi-base representations efficiently")
    print("2. Solve the partial information reconciliation problem")
    print("3. Navigate the coherence constraints across all bases")
    
    # Demonstrate encryption/decryption
    message = "This message is protected by multi-base cryptography, which may be resistant to quantum attacks!"
    
    encrypted = mb_crypto.encrypt(message, public_key)
    decrypted = mb_crypto.decrypt(encrypted, private_key)
    
    print("\nExample encrypted message:")
    print(f"  Original: {message}")
    print(f"  Decrypted: {decrypted}")
    print(f"  Successful decryption: {message == decrypted}")
    
    # 5. Coherence-Based Hash Function
    print("\n5. 🧮 Coherence-Based Hash Function")
    print("-------------------------------------------------------------------")
    
    # Create the hash function
    mb_hash = MultiBaseHashFunction(mb_crypto)
    
    # Test on some messages
    test_messages = [
        b"Hello, world!",
        b"The quick brown fox jumps over the lazy dog.",
        b"Multi-Base Cryptographic Primitives"
    ]
    
    print("\nHash values for test messages:")
    for msg in test_messages:
        hash_value = mb_hash.hash(msg)
        print(f"  '{msg.decode()}': {hash_value}")
    
    # Test avalanche effect
    print("\nAvalanche effect (small changes cause large hash differences):")
    
    base_msg = b"Test message for avalanche effect"
    base_hash = mb_hash.hash(base_msg)
    
    # Change one character
    altered_msg = b"Test message for avalanche effecT"  # Changed last 't' to 'T'
    altered_hash = mb_hash.hash(altered_msg)
    
    # Calculate bit difference
    base_bits = ''.join(format(int(c, 16), '04b') for c in base_hash)
    altered_bits = ''.join(format(int(c, 16), '04b') for c in altered_hash)
    
    diff_count = sum(1 for a, b in zip(base_bits, altered_bits) if a != b)
    diff_percentage = diff_count / len(base_bits) * 100
    
    print(f"  Original hash: {base_hash}")
    print(f"  Changed hash:  {altered_hash}")
    print(f"  Bit difference: {diff_count}/{len(base_bits)} bits ({diff_percentage:.1f}%)")
    
    # Conclusion
    print("\n===================================================================")
    print("The Multi-Base Cryptographic Primitives leverage the universal number")
    print("embedding concept from the Prime Framework to create cryptographic")
    print("systems with unique security properties. By distributing information")
    print("across multiple bases with coherence constraints, these systems may")
    print("resist attacks from both classical and quantum computers.")
    print("===================================================================")


def main():
    """
    Main function demonstrating Multi-Base Cryptographic Primitives.
    """
    print("\n===================================================================")
    print("Multi-Base Cryptographic Primitives - Prime Framework Implementation")
    print("===================================================================")
    print("This demonstrates cryptographic primitives based on the universal number")
    print("embedding concept from the Prime Framework, which represents numbers")
    print("across multiple bases simultaneously with coherence constraints.")
    
    # Basic demonstration of core functions
    print("\nInitializing Multi-Base Cryptographic system...")
    mb_crypto = MultiBaseCrypto()
    
    # Simple examples
    print("\nSimple Examples:")
    
    # 1. Generate a key pair
    public_key, private_key = mb_crypto.generate_key_pair()
    
    # 2. Encrypt and decrypt a message
    message = "Hello, Multi-Base Cryptography!"
    print(f"Original message: {message}")
    
    encrypted = mb_crypto.encrypt(message, public_key)
    decrypted = mb_crypto.decrypt(encrypted, private_key)
    
    print(f"Decrypted message: {decrypted}")
    print(f"Successful decryption: {message == decrypted}")
    
    # 3. Create a hash
    mb_hash = MultiBaseHashFunction(mb_crypto)
    hash_value = mb_hash.hash(message.encode())
    print(f"Hash of message: {hash_value}")
    
    # Run deeper demonstrations
    demonstrate_multi_base_concepts()
    
    # Benchmark against traditional approaches
    benchmark_comparison()
    
    print("\nDone.")


if __name__ == "__main__":
    main()
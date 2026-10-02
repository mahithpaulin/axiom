//! Fast, dependency-free hasher.
//!
//! `std`'s default `RandomState` uses SipHash-1-3, which is a deliberate
//! denial-of-service defence. That is the right trade-off for a network-facing
//! server hashing untrusted keys. It is the wrong trade-off for an inference
//! engine that hashes a few hundred million structural keys (term hash-consing,
//! clause fingerprints, transposition-table buckets) and gains nothing from
//! attack-resistance, because the keys are produced by the engine itself.
//!
//! `FxHasher` is the rustc-hash construction: a single multiply-rotate per word.
//! It is measurably faster than SipHash on this workload. The correctness
//! argument does not depend on it being collision-resistant against an attacker;
//! it only depends on the hash table also comparing keys, which it does.
//!
//! Rationale and measurements: docs/DESIGN_DECISIONS.md (DD-0008).

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

const SEED: u64 = 0x9E37_79B9_7F4A_7C15;
const ROTATE: u32 = 5;

#[derive(Default, Clone, Copy)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(ROTATE) ^ word).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut b = bytes;
        while b.len() >= 8 {
            self.add(u64::from_le_bytes([
                b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
            ]));
            b = &b[8..];
        }
        if b.len() >= 4 {
            self.add(u32::from_le_bytes([b[0], b[1], b[2], b[3]]) as u64);
            b = &b[4..];
        }
        for &x in b {
            self.add(x as u64);
        }
    }
    #[inline]
    fn write_u8(&mut self, n: u8) {
        self.add(n as u64)
    }
    #[inline]
    fn write_u16(&mut self, n: u16) {
        self.add(n as u64)
    }
    #[inline]
    fn write_u32(&mut self, n: u32) {
        self.add(n as u64)
    }
    #[inline]
    fn write_u64(&mut self, n: u64) {
        self.add(n)
    }
    #[inline]
    fn write_usize(&mut self, n: usize) {
        self.add(n as u64)
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

pub type FxBuildHasher = BuildHasherDefault<FxHasher>;
pub type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;
pub type FxHashSet<K> = HashSet<K, FxBuildHasher>;

/// Incremental mixing step, exposed for callers that build their own keys.
#[inline]
pub fn mix(h: u64, word: u64) -> u64 {
    (h ^ word).wrapping_mul(SEED)
}

/// Order-dependent combination, used when scanning node ids into a fingerprint.
#[inline]
pub fn fold(mut h: u64, ids: &[u32]) -> u64 {
    for &id in ids {
        h = (h.rotate_left(ROTATE) ^ id as u64).wrapping_mul(SEED);
    }
    h
}

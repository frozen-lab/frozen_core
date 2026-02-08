//! Implementation of branch preditor hints

#![deny(missing_docs)]

/// empty function used as a placeholder to influence branch prediction
#[cold]
#[inline]
const fn cold_fn() {}

/// Branch predictor hint, which marks given condition as *likely* to be
#[inline]
pub const fn likely(b: bool) -> bool {
    if !b {
        cold_fn();
    }
    b
}

/// Branch predictor hint, which marks given condition as *unlikely* to be
#[inline]
pub const fn unlikely(b: bool) -> bool {
    if b {
        cold_fn();
    }
    b
}

#[test]
fn sanity_checks() {
    assert!(likely(true));
    assert!(!likely(false));
    assert!(unlikely(true));
    assert!(!unlikely(false));
}

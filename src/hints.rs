//! Implementation of branch preditor hints

/// empty function used as a placeholder to influence branch prediction
#[cold]
#[inline]
const fn cold_fn() {}

/// Branch predictor hint, which marks given condition as *likely* to be
///
/// # Example
///
/// ```
/// use frozen_core::hints::likely;
/// assert!(likely(true));
/// assert!(!likely(false));
/// ```
#[inline]
pub const fn likely(b: bool) -> bool {
    if !b {
        cold_fn();
    }
    b
}

/// Branch predictor hint, which marks given condition as *unlikely* to be
///
/// # Example
///
/// ```
/// use frozen_core::hints::unlikely;
/// assert!(unlikely(true));
/// assert!(!unlikely(false));
/// ```
#[inline]
pub const fn unlikely(b: bool) -> bool {
    if b {
        cold_fn();
    }
    b
}

#[cfg(test)]
mod hints {
    use super::*;

    #[test]
    fn sanity_checks_for_likely() {
        assert!(likely(true));
        assert!(!likely(false));
    }

    #[test]
    fn sanity_checks_for_unlikely() {
        assert!(unlikely(true));
        assert!(!unlikely(false));
    }
}

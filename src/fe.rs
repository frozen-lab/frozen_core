//!
//! Custom errors implementation for Frozen Codebases
//!

/// Default `module_id` for testing
#[cfg(test)]
pub const MID: u8 = 0x00;

/// 32-bit error code used in [`FErr`]
pub type FECode = u32;

/// Custom result type w/ [`FErr`] as error type
pub type FRes<T> = Result<T, FErr>;

/// Utility trait to print the error if present
pub trait FECheckOk {
    /// Returns `true` when [`FRes`] is `Ok`, otherwise _prints_ the error
    fn check_ok(self) -> bool;
}

impl<T> FECheckOk for Result<T, FErr> {
    #[inline]
    fn check_ok(self) -> bool {
        const SEPERATOR: &'static str = "\n----------\n";
        match self {
            Err(e) => {
                eprintln!("{SEPERATOR}FErr {{ code: {}, msg: {} }}{SEPERATOR}", e.code, e.msg);
                false
            }
            Ok(_) => true,
        }
    }
}

/// Custom error object for frozen codebases
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FErr {
    /// 32-bit error code
    pub code: FECode,

    /// error message
    pub msg: std::borrow::Cow<'static, str>,
}

impl FErr {
    /// Create a new error with a static message
    #[inline]
    pub fn new(code: FECode, msg: &'static str) -> Self {
        Self {
            code,
            msg: std::borrow::Cow::Borrowed(msg),
        }
    }

    /// Create a new error with an owned message
    #[inline]
    pub fn with_msg(code: FECode, msg: String) -> Self {
        Self {
            code,
            msg: std::borrow::Cow::Owned(msg),
        }
    }

    /// Create a new error from any type implementing [`std::fmt::Display`]
    #[inline]
    pub fn with_err<E>(code: FECode, err: E) -> Self
    where
        E: std::fmt::Display,
    {
        Self {
            code,
            msg: std::borrow::Cow::Owned(err.to_string()),
        }
    }
}

/// Construct an [`FECode`] from raw values
///
/// ## Notes
///
/// - Moudle should be <= 16
/// - Domain should be >= 17 && <= 32
pub const fn new_err_code(module: u8, domain: u8, reason: u16) -> FECode {
    // sanity check
    debug_assert!(module <= 0x10, "Module should be 0-16");
    debug_assert!(domain >= 0x11 && domain <= 0x20, "Domain should be 17-32");

    ((module as u32) << 24) | ((domain as u32) << 16) | (reason as u32)
}

/// De-construct an [`FECode`] error code into raw values
pub const fn from_err_code(code: FECode) -> (u8, u8, u16) {
    let reason = code as u16;
    let domain = (code >> 16) as u8;
    let module = (code >> 24) as u8;

    (module, domain, reason)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn err_code_roundtrip() {
        let module: u8 = 0x0A;
        let domain: u8 = 0x15;
        let reason: u16 = 0xBEEF;

        let code = new_err_code(module, domain, reason);
        let (m, d, r) = from_err_code(code);

        assert_eq!(m, module);
        assert_eq!(d, domain);
        assert_eq!(r, reason);
        assert_eq!(code, 0x0A15BEEF);
    }
}

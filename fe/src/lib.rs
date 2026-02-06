//!
//! Custom errors implementation for Frozen Codebases
//!

pub type FECode = u32;
pub type FRes<T> = Result<T, FErr>;

pub trait FEAsOk {
    fn check_ok(self) -> bool;
}

impl<T> FEAsOk for Result<T, FErr> {
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FErr {
    pub code: FECode,
    pub msg: std::borrow::Cow<'static, str>,
}

impl FErr {
    #[inline]
    pub fn new(code: FECode, msg: &'static str) -> Self {
        Self {
            code,
            msg: std::borrow::Cow::Borrowed(msg),
        }
    }

    #[inline]
    pub fn with_msg(code: FECode, msg: String) -> Self {
        Self {
            code,
            msg: std::borrow::Cow::Owned(msg),
        }
    }

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

pub fn from_err_code(code: FECode) -> (u8, u8, u16) {
    let reason = code as u16;
    let domain = (code >> 16) as u8;
    let module = (code >> 24) as u8;

    (module, domain, reason)
}

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

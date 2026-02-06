use fe::{FErr, FRes};

/// Domain Id for [`ff`] is **17**
const ERRDOMAIN: u8 = 0x11;

#[inline]
pub(crate) fn new_error<R>(mid: u8, reason: FFErr, error: std::io::Error) -> FRes<R> {
    let code = fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    let err = FErr::with_err(code, error);
    Err(err)
}

/// Error codes for [`FF`]
#[repr(u16)]
pub enum FFErr {
    /// (256) internal fuck up
    Hcf = 0x100,

    /// (257) unknown error (fallback)
    Unk = 0x101,

    /// (258) no more space available
    Nsp = 0x102,

    /// (259) failed to obtain os lock
    Lck = 0x103,

    /// (260) unexpected eof
    Eof = 0x104,

    /// (261) syncing error
    Syn = 0x105,

    /// (262) mutext poisoned
    Mpn = 0x106,

    /// (263) thread poisoned
    Tpn = 0x107,

    /// (264) no write perm
    Wrt = 0x108,

    /// (265) no read perm
    Red = 0x109,

    /// (266) invalid path
    Inv = 0x10A,
}

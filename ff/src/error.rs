use fe::{FErr, FRes};

/// Domain Id for [`ff`] is **17**
const ERRDOMAIN: u8 = 0x11;

#[inline]
pub(crate) fn new_error<E, R>(mid: u8, reason: FFErr, error: E) -> FRes<R>
where
    E: std::fmt::Display,
{
    let code = fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    let err = FErr::with_err(code, error);
    Err(err)
}

#[inline]
pub(crate) fn raw_error<E>(mid: u8, reason: FFErr, error: E) -> FErr
where
    E: std::fmt::Display,
{
    let code = fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    FErr::with_err(code, error)
}

#[inline]
pub(crate) fn raw_err_with_msg<E>(mid: u8, error: E, reason: FFErr, msg: &'static str) -> FErr
where
    E: std::fmt::Display,
{
    let code = fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    FErr::with_msg(code, format!("{msg} due to error =>\n{error}"))
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

    /// (259) unexpected eof
    Eof = 0x103,

    /// (260) syncing error
    Syn = 0x104,

    /// (261) no write perm
    Wrt = 0x105,

    /// (262) no read perm
    Red = 0x106,

    /// (263) invalid path
    Inv = 0x107,

    /// (264) thread error or panic inside thread
    Txe = 0x108,

    /// (265) lock error (failed or poisoned)
    Lpn = 0x109,
}

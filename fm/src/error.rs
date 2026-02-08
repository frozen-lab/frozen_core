use fe::{FErr, FRes};

/// Domain Id for [`ff`] is **17**
const ERRDOMAIN: u8 = 0x11;

#[inline]
pub(crate) fn new_error<E, R>(mid: u8, reason: FMErr, error: E) -> FRes<R>
where
    E: std::fmt::Display,
{
    let code = fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    let err = FErr::with_err(code, error);
    Err(err)
}

#[inline]
pub(crate) fn raw_error<E>(mid: u8, reason: FMErr, error: E) -> FErr
where
    E: std::fmt::Display,
{
    let code = fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    FErr::with_err(code, error)
}

#[inline]
pub(crate) fn raw_err_with_msg<E>(mid: u8, error: E, reason: FMErr, msg: &'static str) -> FErr
where
    E: std::fmt::Display,
{
    let code = fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    FErr::with_msg(code, format!("{msg} due to error =>\n{error}"))
}

/// Error codes for [`FM`]
#[repr(u16)]
pub enum FMErr {
    /// (512) internal fuck up
    Hcf = 0x200,

    /// (513) unknown error (fallback)
    Unk = 0x201,

    /// (514) no more memory available
    Nmm = 0x202,

    /// (515) syncing error
    Syn = 0x203,

    /// (516) thread error or panic inside thread
    Txe = 0x204,

    /// (517) lock error (failed or poisoned)
    Lpn = 0x205,
}

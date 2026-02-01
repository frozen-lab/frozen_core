use std::borrow::Cow;

type ErrorCode = u32;

pub type FrozenResult<T> = Result<T, FrozenError>;

pub struct FrozenError {
    pub code: ErrorCode,
    pub msg: Cow<'static, str>,
}

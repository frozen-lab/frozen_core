//! Custom implementation of MemMap

#![deny(missing_docs)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(unused)]

#[cfg(target_os = "linux")]
mod linux;

mod error;
pub use error::FMErr;

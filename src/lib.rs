#![deny(missing_docs)]
#![allow(unsafe_op_in_unsafe_fn)]
#![doc = include_str!("../README.md")]

pub mod fe;
pub mod hints;

#[cfg(any(test, feature = "ff"))]
pub mod ff;

#[cfg(any(test, feature = "fm"))]
pub mod fm;

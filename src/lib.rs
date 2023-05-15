#![no_std]
#![cfg_attr(any(kernel, feature = "nightly"), feature(const_trait_impl))]
#![warn(clippy::cargo)]

pub mod vmem;

#[doc(inline)]
pub use crate::vmem::*;

extern crate alloc;
#![no_std]

pub mod vmem;

#[doc(inline)]
pub use vmem::*;

extern crate alloc;
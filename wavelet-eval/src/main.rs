#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![allow(unused_braces)]
#![allow(dead_code)]

pub use wavelet_embedding::cap;

mod dconv;
mod dither;
mod dmm;
mod dmv;
mod fft;
mod nn_conv;
mod nn_fc;
mod nn_norm;
mod nn_pool;
mod nn_relu;
mod nn_vadd;
mod sort;

fn main() {
    println!("Hello, world!");
}

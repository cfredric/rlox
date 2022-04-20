#![feature(test)]

extern crate test;

use rlox::{run_file, Opt};
use test::Bencher;

#[bench]
fn fibonacci(b: &mut Bencher) {
    let prog: String = "
      fun fib(n) {
        if (n <= 1) return n;
        return fib(n - 2) + fib(n - 1);
      }

      fib(10);
    "
    .into();

    b.iter(|| run_file(&Opt::default(), prog.clone()).unwrap());
}

#[bench]
fn factorial(b: &mut Bencher) {
    let prog: String = "
      fun fact(n) {
        if (n <= 1) return 1;
        return n * fact(n - 1);
      }

      fact(15);
    "
    .into();

    b.iter(|| run_file(&Opt::default(), prog.clone()).unwrap());
}

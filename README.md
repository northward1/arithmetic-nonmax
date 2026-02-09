# Arithmetic Nonmax

[![Crates.io](https://img.shields.io/crates/v/arithmetic-nonmax.svg)](https://crates.io/crates/arithmetic-nonmax)
[![Docs.rs](https://docs.rs/arithmetic-nonmax/badge.svg)](https://docs.rs/arithmetic-nonmax)
[![License](https://img.shields.io/crates/l/arithmetic-nonmax.svg)](LICENSE)

The `arithmetic-nonmax` crate provides `NonMax*` types for integer types that are guaranteed to never be their maximum value (`MAX`). Using `NonMax*` types enables memory layout optimization.

Additionally, arithmetic operations can be written intuitively as shown below. For example, in shortest path algorithms, using the `Option<NonMax*>` type allows you to leverage the type system while optimizing the memory layout. See [Benchmarks](#benchmarks) for more details.

```rust
use arithmetic_nonmax::{NonMaxU32, non_max};

let a: NonMaxU32 = NonMaxU32::new(5).unwrap();

let b = non_max!(10); // Conveniently create values with the non_max! macro
let c = b - a; // Arithmetic operations between NonMax types
assert_eq!(a, c);

let d = a * 5; // Arithmetic operations with primitive integers
assert!(a < d);
assert_eq!(d.to_string(), "25"); // Can be converted to string
```

Memory layout optimization can be verified as follows:

```rust
use arithmetic_nonmax::*;

// Check byte size for u32
assert_eq!(std::mem::size_of::<NonMaxU32>(), 4);
assert_eq!(std::mem::size_of::<Option<NonMaxU32>>(), 4);
assert_eq!(std::mem::size_of::<u32>(), 4);
assert_eq!(std::mem::size_of::<Option<u32>>(), 8);

// Check byte size for Option<NonMax*>
assert_eq!(std::mem::size_of::<Option<NonMaxU8>>(), 1);
assert_eq!(std::mem::size_of::<Option<NonMaxU16>>(), 2);
assert_eq!(std::mem::size_of::<Option<NonMaxU32>>(), 4);
assert_eq!(std::mem::size_of::<Option<NonMaxU64>>(), 8);
assert_eq!(std::mem::size_of::<Option<NonMaxU128>>(), 16);
assert_eq!(std::mem::size_of::<Option<NonMaxI8>>(), 1);
assert_eq!(std::mem::size_of::<Option<NonMaxI16>>(), 2);
assert_eq!(std::mem::size_of::<Option<NonMaxI32>>(), 4);
assert_eq!(std::mem::size_of::<Option<NonMaxI64>>(), 8);
assert_eq!(std::mem::size_of::<Option<NonMaxI128>>(), 16);
```

## Benchmarks

Benchmarks are available in `benches/comparison.rs`. They compare execution time and memory usage between using and not using `NonMax` types.

| Algorithm | With `NonMax` | Without `NonMax` |
|---|---|---|
| Dijkstra ($V=5.0 \times 10^5, E = 5.0 \times 10^6$) | 450ms / 18.8MB | 505ms / 20.8MB |
| Floyd-Warshall ($V=5.0 \times 10^2, E = 5.0 \times 10^3$) | 103ms / 1.00MB | 112ms / 2.00MB |

## Examples

You can find programs that solve [Aizu Online Judge](https://onlinejudge.u-aizu.ac.jp/home) problems using this library in the `examples/` directory.
Note that you need to bundle the library into a single file when submitting to an online judge.

* [GRL_1_A: Single Source Shortest Path](examples/dijkstra.rs): Uses `Option<NonMax<u32>>` for distances, representing unreachable nodes as `None`.
* [GRL_1_C: All Pairs Shortest Path](examples/floyd_warshall.rs): Uses `Option<NonMax<i32>>` for distances, representing unreachable nodes as `None`.
* [DSL_1_A: Disjoint Set](examples/union_find.rs): Manages parent indices in a Union-Find data structure using `Option<NonMaxUsize>`.

## Similar Libraries

* [`nonmax`](https://github.com/LPGhatguy/nonmax)
* [`nonany`](https://github.com/rick-de-water/nonany)

## License

[CC0 1.0 Universal](LICENSE)
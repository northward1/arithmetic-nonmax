# Arithmetic Nonmax

[![Crates.io](https://img.shields.io/crates/v/arithmetic-nonmax.svg)](https://crates.io/crates/arithmetic-nonmax)
[![Docs.rs](https://docs.rs/arithmetic-nonmax/badge.svg)](https://docs.rs/arithmetic-nonmax)
[![License](https://img.shields.io/crates/l/arithmetic-nonmax.svg)](LICENSE)

The `arithmetic-nonmax` crate provides `NonMax*` types for integer types that are guaranteed to never be their maximum value (`MAX`). Using `NonMax*` types enables memory layout optimization.

Additionally, arithmetic operations can be written intuitively as shown below. For example, in shortest path algorithms, using the `Option<NonMax*>` type allows you to leverage the type system while optimizing the memory layout. See [Benchmarks](#benchmarks) for more details.

```rust
use arithmetic_nonmax::NonMaxU32;

let a: NonMaxU32 = NonMaxU32::new(5).unwrap();

let b = NonMaxU32::ZERO;
let c = a + b; // Arithmetic operations between NonMaxU32 types
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

## Similar Libraries

* [`nonmax`](https://github.com/LPGhatguy/nonmax)
* [`nonany`](https://github.com/rick-de-water/nonany)

## License

[CC0 1.0 Universal](LICENSE)

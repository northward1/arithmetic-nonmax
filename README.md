# Arithmetic Nonmax

[![Crates.io](https://img.shields.io/crates/v/arithmetic-nonmax.svg)](https://crates.io/crates/arithmetic-nonmax)
[![Docs.rs](https://docs.rs/arithmetic-nonmax/badge.svg)](https://docs.rs/arithmetic-nonmax)
[![License](https://img.shields.io/crates/l/arithmetic-nonmax.svg)](LICENSE)

The `arithmetic-nonmax` crate provides `NonMax*` types for integer types guaranteed never to take their maximum value (`MAX`). This enables Rust's "niche optimization," allowing `Option<NonMax*>` to occupy the same memory space as the underlying integer type.

Additionally, arithmetic operations can be written intuitively. For example, in shortest path algorithms, using the `Option<NonMax*>` type allows you to leverage the type system while optimizing the memory layout. See [Benchmarks](#benchmarks) for more details.

```rust
use arithmetic_nonmax::{NonMaxU32, non_max};

let a: NonMaxU32 = NonMaxU32::new(5).unwrap();

let b = non_max!(10); // Concise value creation via macro
let c = b - a; // Arithmetic between NonMaxU32 types
assert_eq!(a, c);

let d = a * 5; // Arithmetic with integer types
assert!(a < d);
assert_eq!(d.to_string(), "25"); // Conversion to string

let array = [non_max!(3), non_max!(4), non_max!(5)];
let e = array[non_max!(2)]; // Access by index
assert_eq!(a, e);
```

## Benchmarks

The following results were measured using `iai` and `divan`. `NonMax` achieves memory savings equivalent to the sentinel method while providing more efficient operations and reduced instruction counts compared to standard `Option`.

### Instruction Count Benchmarks (`benches/iai_comparison.rs`)

We measured the number of instructions for operations on each type using `iai`.

#### i32
| Operation (i32) | `Option<NonMaxI32>` | `Option<i32>` | `Raw (Sentinel)` |
| :--- | :---: | :---: | :---: |
| New (`new`) | 24 | 25 | 23 |
| Get (`get`) | 24 | 29 | 23 |
| Add (`add`) | 32 | 41 | 25 |
| Compare (`cmp`) | 30 | 32 | 26 |

#### usize
| Operation (usize) | `Option<NonMaxUsize>` | `Option<usize>` | `Raw (Sentinel)` |
| :--- | :---: | :---: | :---: |
| New (`new`) | 24 | 25 | 23 |
| Get (`get`) | 24 | 29 | 23 |
| Add (`add`) | 30 | 41 | 25 |
| Compare (`cmp`) | 30 | 32 | 26 |

*Measured on an x86_64 environment. Comparisons (`cmp`) include the cost of infinity-aware logic. For a full report, see `bench_result_iai.txt`.*

### Performance & Memory Benchmarks (`benches/comparison.rs`)

We measured performance in practical algorithms and large-scale data operations using `divan`.

#### Algorithms
| Algorithm (u32) | Metric | `Option<NonMaxU32>` | `Option<u32>` | `Sentinel (MAX)` |
| :--- | :--- | :---: | :---: | :---: |
| Floyd-Warshall<br>($V=400$) | Execution Time | 52 ms | 55 ms | 45 ms |
| | Memory Usage | 640 KB | 1.3 MB | 640 KB |
| Dijkstra<br>($V=500,000$) | Execution Time | 340 ms | 380 ms | 340 ms |
| | Memory Usage | 19 MB | 21 MB | 19 MB |

#### Large-scale Data Operations ($N=1,000,000$)
| Operation (u32) | `Option<NonMaxU32>` | `Option<u32>` | `Sentinel (MAX)` |
| :--- | :---: | :---: | :---: |
| Sort (`sort`) | 70 ms | 31 ms | 17 ms |
| Sum (`sum`) | 0.51 ms | 0.58 ms | 0.24 ms |
| Update (`update`) | 1.9 ms | 1.9 ms | 1.9 ms |

*Measured on an x86_64 environment (median). For a full report, see `bench_result.txt`.*

## Bundling for Competitive Programming

When submitting to online judges, you can bundle the library into a single file using the following command:

```bash
(echo "pub mod arithmetic_nonmax {"; sed -e 's/#!\[no_std\]//' -e '/#\[cfg(test)\]/,$d' -e 's/\$crate/crate::arithmetic_nonmax/g' -e 's|//.*||' -e '/^[[:space:]]*$/d' src/lib.rs; echo "}") > bundled.rs
```

## Examples

This repository includes example solutions for [Aizu Online Judge](https://onlinejudge.u-aizu.ac.jp/home) problems using this library. Note that you need to bundle the library into a single file when submitting to an online judge.

* [GRL_1_A: Single Source Shortest Path](examples/dijkstra.rs): Uses `Option<NonMax<u32>>` for distances, representing unreachable nodes as `None`.
* [GRL_1_C: All Pairs Shortest Path](examples/floyd_warshall.rs): Uses `Option<NonMax<i32>>` for distances, representing unreachable nodes as `None`.
* [DSL_1_A: Disjoint Set](examples/union_find.rs): Manages parent indices in a Union-Find data structure using `Option<NonMaxUsize>`.
* [DPL_1_A: Coin Changing Problem](examples/coin_change.rs): Solves the coin change problem using DP with `Option<NonMax<u32>>`.

## Similar Libraries

* [`nonmax`](https://github.com/LPGhatguy/nonmax)
* [`nonany`](https://github.com/rick-de-water/nonany)

## License

[CC0 1.0 Universal](LICENSE)

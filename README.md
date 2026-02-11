# Arithmetic Nonmax

[![Crates.io](https://img.shields.io/crates/v/arithmetic-nonmax.svg)](https://crates.io/crates/arithmetic-nonmax)
[![Docs.rs](https://docs.rs/arithmetic-nonmax/badge.svg)](https://docs.rs/arithmetic-nonmax)
[![License](https://img.shields.io/crates/l/arithmetic-nonmax.svg)](LICENSE)

The `arithmetic-nonmax` crate provides `NonMax*` types for integer types that are guaranteed to never be their maximum value (`MAX`). Using these types enables Rust's "niche optimization," where `Option<NonMax*>` has the same size as the underlying integer type.

Additionally, arithmetic operations can be written intuitively. For example, in shortest path algorithms, using the `Option<NonMax*>` type allows you to leverage the type system while optimizing the memory layout. See [Benchmarks](#benchmarks) for more details.

```rust
use arithmetic_nonmax::{NonMax, NonMaxU32, non_max};

let a: NonMaxU32 = NonMaxU32::new(5).unwrap();

let b = non_max!(10); // Conveniently create values with the non_max! macro
let c = b - a; // Arithmetic operations between NonMax types
assert_eq!(a, c);

let d = a * 5; // Arithmetic operations with primitive integers
assert!(a < d);
assert_eq!(d.to_string(), "25"); // Can be converted to string

let array = [non_max!(1), non_max!(4), non_max!(5)];
let e = array[non_max!(2)]; // Support indexing
let f = array.iter().sum::<NonMax<_>>();
assert_eq!(f / 2, e);
```

## Benchmarks

The following values are based on measurements using `iai` and `divan`. `NonMax` achieves the same memory savings as the sentinel method (the fastest) while allowing for more efficient operations (reduced instruction counts) than the standard `Option`.

### Instruction-based Benchmarks (`benches/iai_comparison.rs`)

We measured the number of instructions for operations on each type using `iai`. Here, we extract results for `i32` (default integer type) and `usize` (indexing type), which are commonly used (other integer types show similar trends).

#### i32 (Default integer type)
| Operation (i32) | `NonMax` | `Option<i32>` | `Raw (Sentinel)` |
| :--- | :---: | :---: | :---: |
| New (`new`) | 24 | 25 | 23 |
| Get (`get`) | 24 | 29 | 23 |
| Add (`add`) | 32 | 41 | 25 |
| Compare (`cmp`) | 30 | 32 | 26 |

#### usize (Index type)
| Operation (usize) | `NonMax` | `Option<usize>` | `Raw (Sentinel)` |
| :--- | :---: | :---: | :---: |
| New (`new`) | 24 | 25 | 23 |
| Get (`get`) | 24 | 29 | 23 |
| Add (`add`) | 30 | 41 | 25 |
| Compare (`cmp`) | 30 | 32 | 26 |

Note: Values are measured with `iai` (x86_64 environment). Comparisons (`cmp`) measure the cost of infinity-aware comparisons (`curr.is_none() || Some(next) < curr` vs `next < curr`). For a full report, see `bench_result_iai.txt`.

### Execution Time and Memory Usage Benchmarks (`benches/comparison.rs`)

We measured performance in practical algorithms and large-scale data operations using `divan`. Reducing the memory size by half (8 bytes → 4 bytes) improves cache efficiency, delivering faster execution speeds than the standard `Option` for large data.

#### Algorithms
| Algorithm (u32) | Metric | `NonMax` | `Option<u32>` | `Sentinel (MAX)` |
| :--- | :--- | :---: | :---: | :---: |
| **Floyd-Warshall**<br>(V=400) | Execution Time | 51 ms | 56 ms | 45 ms |
| | Memory Usage | **640 KB** | 1.3 MB | 640 KB |
| **Dijkstra**<br>(V=100,000) | Execution Time | 44 ms | 45 ms | 43 ms |
| | Memory Usage | **2.5 MB** | 2.9 MB | 2.5 MB |

#### Large-scale Data Operations (N=1,000,000)
| Operation (u32) | `NonMax` | `Option<u32>` | `Sentinel (MAX)` |
| :--- | :---: | :---: | :---: |
| Sort (`sort`) | 74 ms | 41 ms | 18 ms |
| Sum (`sum`) | 0.54 ms | 0.64 ms | 0.15 ms |
| Update (`update`) | 1.9 ms | 2.0 ms | 1.9 ms |

Note: Values are measured with `divan` (x86_64 environment, median). For a full report, see `bench_result.txt`.

## Bundling for Competitive Programming

When submitting to online judges, you can bundle the library into a single file using the following command:

```bash
(echo "pub mod arithmetic_nonmax {"; sed -e 's/#!\[no_std\]//' -e '/#\[cfg(test)\]/,$d' -e 's/\$crate/crate::arithmetic_nonmax/g' -e 's|//.*||' -e '/^[[:space:]]*$/d' src/lib.rs; echo "}") > bundled.rs
```

## Examples

You can find programs that solve [Aizu Online Judge](https://onlinejudge.u-aizu.ac.jp/home) problems using this library in the `examples/` directory.
Note that you need to bundle the library into a single file when submitting to an online judge.

* [GRL_1_A: Single Source Shortest Path](examples/dijkstra.rs): Uses `Option<NonMax<u32>>` for distances, representing unreachable nodes as `None`.
* [GRL_1_C: All Pairs Shortest Path](examples/floyd_warshall.rs): Uses `Option<NonMax<i32>>` for distances, representing unreachable nodes as `None`.
* [DSL_1_A: Disjoint Set](examples/union_find.rs): Manages parent indices in a Union-Find data structure using `Option<NonMaxUsize>`.
* [DPL_1_A: Coin Changing Problem](examples/coin_change.rs): Solves the coin change problem using DP with `Option<NonMax<u32>>`.

## Similar Libraries

* [`nonmax`](https://github.com/LPGhatguy/nonmax)
* [`nonany`](https://github.com/rick-de-water/nonany)

## License

[CC0 1.0 Universal](LICENSE)

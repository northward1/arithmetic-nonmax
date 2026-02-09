# Arithmetic Nonmax

[![Crates.io](https://img.shields.io/crates/v/arithmetic-nonmax.svg)](https://crates.io/crates/arithmetic-nonmax)
[![Docs.rs](https://docs.rs/arithmetic-nonmax/badge.svg)](https://docs.rs/arithmetic-nonmax)
[![License](https://img.shields.io/crates/l/arithmetic-nonmax.svg)](LICENSE)

`arithmetic-nonmax`クレートは、整数型がその最大値を取らないことが保証されているとき、`NonMax*`型を利用できるようにします。`NonMax*`型を利用することで、メモリレイアウトの最適化を受けることができるようになります。

また、四則演算を以下のように直感的に記述できます。例えば、最短経路問題では、`Option<NonMax*>`型を使うことで、型システムを活用しながら、メモリレイアウトの最適化も行えます。それについては、[ベンチマーク](#ベンチマーク)を参考にしてください。

```rust
use arithmetic_nonmax::NonMaxU32;

let a: NonMaxU32 = NonMaxU32::new(5).unwrap();

let b = NonMaxU32::ZERO;
let c = a + b; // NonMaxU32同士で四則演算ができる 
assert_eq!(a, c);

let d = a * 5; // 整数型とも四則演算ができる
assert!(a < d);
assert_eq!(d.to_string(), "25"); // 文字列に変換できる
```

メモリレイアウトが最適化されていることは、以下のように確認できます。

```rust
use arithmetic_nonmax::*;

// u32の場合のバイト数を確認する
assert_eq!(std::mem::size_of::<NonMaxU32>(), 4);
assert_eq!(std::mem::size_of::<Option<NonMaxU32>>(), 4);
assert_eq!(std::mem::size_of::<u32>(), 4);
assert_eq!(std::mem::size_of::<Option<u32>>(), 8);

// Option<NonMax*>のバイト数を確認する
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

## ベンチマーク

`benches/comparison.rs`にベンチマークがあります。`NonMax`型を利用した場合としない場合で実行時間やメモリの使用量を比較しています。

||`NonMax`を利用した場合|`NonMax`を利用しない場合|
|---|---|---|
|Dijkstra法 ($V=5.0 \times 10^5, E = 5.0 \times 10^6$)|450ms 18.8MB|505ms 20.8MB|
|Floyd-Warshall法 ($V=5.0 \times 10^2, E = 5.0 \times 10^3$)|103ms 1.00MB|112ms 2.00MB|

## 関連ライブラリ

* [`nonmax`](https://github.com/LPGhatguy/nonmax)
* [`nonany`](https://github.com/rick-de-water/nonany)

## ライセンス

[CC0ライセンス](LICENSE)

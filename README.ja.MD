# Arithmetic Nonmax

[![Crates.io](https://img.shields.io/crates/v/arithmetic-nonmax.svg)](https://crates.io/crates/arithmetic-nonmax)
[![Docs.rs](https://docs.rs/arithmetic-nonmax/badge.svg)](https://docs.rs/arithmetic-nonmax)
[![License](https://img.shields.io/crates/l/arithmetic-nonmax.svg)](LICENSE)

`arithmetic-nonmax`クレートは、整数型がその最大値を取らないことが保証されているとき、`NonMax*`型を利用できるようにします。`NonMax*`型を利用することで、メモリレイアウトの最適化を受けることができるようになります。

また、四則演算を以下のように直感的に記述できます。例えば、最短経路問題では、`Option<NonMax*>`型を使うことで、型システムを活用しながら、メモリレイアウトの最適化も行えます。それについては、[ベンチマーク](#ベンチマーク)を参考にしてください。

```rust
use arithmetic_nonmax::{NonMaxU32, non_max};

let a: NonMaxU32 = NonMaxU32::new(5).unwrap();

let b = non_max!(10); // non_max!マクロで簡潔に値を生成できる
let c = b - a; // NonMaxU32同士で四則演算ができる 
assert_eq!(a, c);

let d = a * 5; // 整数型とも四則演算ができる
assert!(a < d);
assert_eq!(d.to_string(), "25"); // 文字列に変換できる

let array = [non_max!(3), non_max!(4), non_max!(5)];
let e = array[non_max!(2)]; // 添え字によるアクセスができる
assert_eq!(a, e);
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

||`NonMax`を利用した場合|`NonMax`を利用しない場合|番兵を利用した場合|
|---|---|---|---|
|Dijkstra法 ($V=5.0 \times 10^5, E = 5.0 \times 10^6$)|447ms/18.8MB|487ms/20.8MB|456ms/18.8MB|
|Floyd-Warshall法 ($V=5.0 \times 10^2, E = 5.0 \times 10^3$)|100ms/1.00MB|126ms/2.00MB|83ms/1.00MB|

Dijkstra法において、`NonMax`を利用した場合が番兵を利用した場合よりも高速になっています。これは、`NonMaxU32`で`None`が`0`であることを利用した特殊な最適化が機能している結果です。

## 競技プログラミング用のバンドル

オンラインジャッジに提出する際、以下のコマンドを使用してライブラリを1つのファイルにまとめることができます。

```bash
(echo "pub mod arithmetic_nonmax {"; sed -e 's/#!\[no_std\]//' -e '/#\[cfg(test)\]/,$d' -e 's/\$crate/crate::arithmetic_nonmax/g' -e 's|//.*||' -e '/^[[:space:]]*$/d' src/lib.rs; echo "}") > bundled.rs
```

## 使用例

このライブラリを使用して[Aizu Online Judge](https://onlinejudge.u-aizu.ac.jp/home)の問題にACできるプログラムを置いています。
ただし、ライブラリを適切に1ファイルにバンドルする必要があります。

* [GRL_1_A: Single Source Shortest Path](examples/dijkstra.rs): Dijkstra法で距離を`Option<NonMax<u32>>`で表し、到達不可能であることを`None`で表す。
* [GRL_1_C: All Pairs Shortest Path](examples/floyd_warshall.rs): Floyd-Warshall法で距離を`Option<NonMax<i32>>`で表し、到達不可能であることを`None`で表す。
* [DSL_1_A: Disjoint Set](examples/union_find.rs): Union-Findで親の添え字を`Option<NonMaxUsize>`で管理する。
* [DPL_1_A: Coin Changing Problem](examples/coin_change.rs): コイン問題を`Option<NonMax<u32>>`を用いたDPで解く。

## 関連ライブラリ

* [`nonmax`](https://github.com/LPGhatguy/nonmax)
* [`nonany`](https://github.com/rick-de-water/nonany)

## ライセンス

[CC0ライセンス](LICENSE)

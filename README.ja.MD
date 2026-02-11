# Arithmetic Nonmax

[![Crates.io](https://img.shields.io/crates/v/arithmetic-nonmax.svg)](https://crates.io/crates/arithmetic-nonmax)
[![Docs.rs](https://docs.rs/arithmetic-nonmax/badge.svg)](https://docs.rs/arithmetic-nonmax)
[![License](https://img.shields.io/crates/l/arithmetic-nonmax.svg)](LICENSE)

`arithmetic-nonmax`クレートは、整数型がその最大値を取らないことが保証されているとき、`NonMax*`型を利用できるようにします。これを利用することで、Rustのニッチ最適化（Niche Optimization）が働き、`Option<NonMax*>`のサイズが元の整数型と同じになるなど、メモリレイアウトの最適化を受けることができます。

また、四則演算を以下のように直感的に記述できます。例えば、最短経路問題では、`Option<NonMax*>`型を使うことで、型システムを活用しながら、メモリレイアウトの最適化も行えます。それについては、[ベンチマーク](#ベンチマーク)を参考にしてください。

## ベンチマーク

以下の数値は`iai`および`divan`を用いた計測結果です。`NonMax`は最速である番兵方式と同等のメモリ節約を実現しつつ、標準の`Option`よりも効率的な操作や命令数の削減が可能です。

### 命令数ベースのベンチマーク(`benches/iai_comparison.rs`)

`iai`を用いて、各型の操作における命令数（Instructions）を計測しました。

#### i32
| 操作 (i32) | `NonMax` | `Option<i32>` | `Raw (Sentinel)` |
| :--- | :---: | :---: | :---: |
| 生成 (`new`) | 24 | 25 | 23 |
| 取得 (`get`) | 24 | 29 | 23 |
| 加算 (`add`) | 32 | 41 | 25 |
| 比較 (`cmp`) | 30 | 32 | 26 |

#### usize
| 操作 (usize) | `NonMax` | `Option<usize>` | `Raw (Sentinel)` |
| :--- | :---: | :---: | :---: |
| 生成 (`new`) | 24 | 25 | 23 |
| 取得 (`get`) | 24 | 29 | 23 |
| 加算 (`add`) | 30 | 41 | 25 |
| 比較 (`cmp`) | 30 | 32 | 26 |

数値は`iai`による計測結果（x86_64環境）。比較 (`cmp`) は無限大（None/MAX）を考慮した比較のコストを計測しています。
詳細なレポートは`bench_result_iai.txt`を参照してください。

### 実行時間・メモリ使用量ベースのベンチマーク(`benches/comparison.rs`)

`divan`を用いて、実用的なアルゴリズムや大規模なデータの操作におけるパフォーマンスを計測しました。

#### アルゴリズム
| アルゴリズム (u32) | 指標 | `NonMax` | `Option<u32>` | `Sentinel (MAX)` |
| :--- | :--- | :---: | :---: | :---: |
| Floyd-Warshall<br>($V=400$) | 実行時間 | 51 ms | 56 ms | 45 ms |
| | メモリ使用量 | 640 KB | 1.3 MB | 640 KB |
| Dijkstra<br>($V=100,000$) | 実行時間 | 44 ms | 45 ms | 43 ms |
| | メモリ使用量 | 2.5 MB | 2.9 MB | 2.5 MB |

#### 大規模なデータの操作 ($N=1,000,000$)
| 操作 (u32) | `NonMax` | `Option<u32>` | `Sentinel (MAX)` |
| :--- | :---: | :---: | :---: |
| ソート (`sort`) | 74 ms | 41 ms | 18 ms |
| 合計 (`sum`) | 0.54 ms | 0.64 ms | 0.15 ms |
| 更新 (`update`) | 1.9 ms | 2.0 ms | 1.9 ms |

数値は`divan`による計測結果（x86_64環境、中央値）。
詳細なレポートは`bench_result.txt`を参照してください。

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

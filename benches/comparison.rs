use arithmetic_nonmax::*;
use divan::{AllocProfiler, Bencher, black_box};
use paste::paste;
use rand::{Rng, SeedableRng};
use std::collections::BinaryHeap;

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

fn main() {
    divan::main();
}

const SIZES: &[usize] = &[1000, 10000, 100000, 1000000];

// --- Helper for generating random test data ---
fn gen_random_vec<T, F>(n: usize, mut f: F) -> Vec<T>
where
    F: FnMut(&mut rand::rngs::StdRng) -> T,
{
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    (0..n).map(|_| f(&mut rng)).collect()
}

macro_rules! bench_suite {
    ($t:ident, $prim:ident) => {
        paste! {
            #[divan::bench_group(name = stringify!($prim))]
            mod [<mod_ $prim>] {
                use super::*;

                // --- Summation ---
                #[divan::bench(args = SIZES)]
                fn sum_nonmax(bencher: Bencher, n: usize) {
                    bencher
                        .with_inputs(|| gen_random_vec(n, |r| [<$t>]::new(r.random_range(0..10))))
                        .bench_values(|data| {
                            let res: [<$t>] = data.iter().flatten().sum();
                            black_box(res);
                        });
                }

                #[divan::bench(args = SIZES)]
                fn sum_primitive(bencher: Bencher, n: usize) {
                    bencher
                        .with_inputs(|| gen_random_vec(n, |r| Some(r.random_range(0..10) as $prim)))
                        .bench_values(|data| {
                            let res: $prim = data.iter().flatten().sum();
                            black_box(res);
                        });
                }

                #[divan::bench(args = SIZES)]
                fn sum_sentinel(bencher: Bencher, n: usize) {
                    bencher
                        .with_inputs(|| gen_random_vec(n, |r| r.random_range(0..10) as $prim))
                        .bench_values(|data| {
                            let res: $prim = data.iter().filter(|&&x| x != $prim::MAX).sum();
                            black_box(res);
                        });
                }

                // --- Array Update ---
                #[divan::bench(args = SIZES)]
                fn update_nonmax(bencher: Bencher, n: usize) {
                    bencher
                        .with_inputs(|| vec![[<$t>]::new(0); n])
                        .bench_values(|mut data| {
                            for i in 1..n {
                                if let Some(prev) = data[i-1] {
                                    data[i] = Some(prev + 1);
                                }
                            }
                            black_box(data);
                        });
                }

                #[divan::bench(args = SIZES)]
                fn update_primitive(bencher: Bencher, n: usize) {
                    bencher
                        .with_inputs(|| vec![Some(0 as $prim); n])
                        .bench_values(|mut data| {
                            for i in 1..n {
                                if let Some(prev) = data[i-1] {
                                    data[i] = Some(prev.wrapping_add(1));
                                }
                            }
                            black_box(data);
                        });
                }

                #[divan::bench(args = SIZES)]
                fn update_sentinel(bencher: Bencher, n: usize) {
                    bencher
                        .with_inputs(|| vec![0 as $prim; n])
                        .bench_values(|mut data| {
                            for i in 1..n {
                                let prev = data[i-1];
                                if prev != $prim::MAX {
                                    data[i] = prev.wrapping_add(1);
                                }
                            }
                            black_box(data);
                        });
                }

                // --- Sorting ---
                #[divan::bench(args = SIZES)]
                fn sort_nonmax(bencher: Bencher, n: usize) {
                    bencher
                        .with_inputs(|| gen_random_vec(n, |r| [<$t>]::new(r.random_range(0..$prim::MAX - 1))))
                        .bench_values(|mut data| {
                            data.sort();
                            black_box(data);
                        });
                }

                #[divan::bench(args = SIZES)]
                fn sort_primitive(bencher: Bencher, n: usize) {
                    bencher
                        .with_inputs(|| gen_random_vec(n, |r| Some(r.random_range(0..$prim::MAX - 1))))
                        .bench_values(|mut data| {
                            data.sort();
                            black_box(data);
                        });
                }

                #[divan::bench(args = SIZES)]
                fn sort_sentinel(bencher: Bencher, n: usize) {
                    bencher
                        .with_inputs(|| gen_random_vec(n, |r| r.random_range(0..$prim::MAX - 1)))
                        .bench_values(|mut data| {
                            data.sort();
                            black_box(data);
                        });
                }
            }
        }
    };
}

bench_suite!(NonMaxU32, u32);
bench_suite!(NonMaxU64, u64);
bench_suite!(NonMaxU128, u128);

// --- Integrated Application: Floyd-Warshall ---

#[divan::bench_group(name = "floyd_warshall")]
mod floyd_warshall {
    use super::*;

    const FW_SIZES: &[usize] = &[10, 100, 400];

    struct Graph {
        v: usize,
        edges: Vec<(usize, usize, u32)>,
    }

    fn gen_graph(v: usize) -> Graph {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let mut edges = vec![];
        for s in 0..v {
            for _ in 0..10 {
                let t = rng.random_range(0..v);
                let d = rng.random_range(1..100);
                edges.push((s, t, d));
            }
        }
        Graph { v, edges }
    }

    #[divan::bench(args = FW_SIZES)]
    fn nonmax(bencher: Bencher, n: usize) {
        bencher.with_inputs(|| gen_graph(n)).bench_values(|graph| {
            let v = graph.v;
            let mut dist = vec![None; v * v];

            for i in 0..v {
                dist[i * v + i] = NonMaxU32::new(0);
            }
            for &(s, t, d) in &graph.edges {
                let idx = s * v + t;
                let d_nm = NonMaxU32::new(d);
                if dist[idx].is_none() || d_nm < dist[idx] {
                    dist[idx] = d_nm;
                }
            }

            for k in 0..v {
                for i in 0..v {
                    if let Some(dik) = dist[i * v + k] {
                        for j in 0..v {
                            if let Some(dkj) = dist[k * v + j] {
                                // NonMax + NonMax -> NonMax
                                let new_dist = dik + dkj;
                                let ij = i * v + j;
                                if dist[ij].is_none() || Some(new_dist) < dist[ij] {
                                    dist[ij] = Some(new_dist);
                                }
                            }
                        }
                    }
                }
            }
            black_box(dist)
        });
    }

    #[divan::bench(args = FW_SIZES)]
    fn primitive(bencher: Bencher, n: usize) {
        bencher.with_inputs(|| gen_graph(n)).bench_values(|graph| {
            let v = graph.v;
            let mut dist = vec![None; v * v];

            for i in 0..v {
                dist[i * v + i] = Some(0u32);
            }
            for &(s, t, d) in &graph.edges {
                let idx = s * v + t;
                if dist[idx].is_none() || Some(d) < dist[idx] {
                    dist[idx] = Some(d);
                }
            }

            for k in 0..v {
                for i in 0..v {
                    if let Some(dik) = dist[i * v + k] {
                        for j in 0..v {
                            if let Some(dkj) = dist[k * v + j] {
                                let new_dist = dik + dkj;
                                let ij = i * v + j;
                                if dist[ij].is_none() || Some(new_dist) < dist[ij] {
                                    dist[ij] = Some(new_dist);
                                }
                            }
                        }
                    }
                }
            }
            black_box(dist)
        });
    }

    #[divan::bench(args = FW_SIZES)]
    fn sentinel(bencher: Bencher, n: usize) {
        bencher.with_inputs(|| gen_graph(n)).bench_values(|graph| {
            let v = graph.v;
            let mut dist = vec![u32::MAX; v * v];

            for i in 0..v {
                dist[i * v + i] = 0;
            }
            for &(s, t, d) in &graph.edges {
                let idx = s * v + t;
                if d < dist[idx] {
                    dist[idx] = d;
                }
            }

            for k in 0..v {
                for i in 0..v {
                    let dik = dist[i * v + k];
                    if dik == u32::MAX {
                        continue;
                    }
                    for j in 0..v {
                        let dkj = dist[k * v + j];
                        if dkj == u32::MAX {
                            continue;
                        }
                        let new_dist = dik + dkj;
                        let ij = i * v + j;
                        if new_dist < dist[ij] {
                            dist[ij] = new_dist;
                        }
                    }
                }
            }
            black_box(dist)
        });
    }
}

// --- Integrated Application: Dijkstra ---

#[divan::bench_group(name = "dijkstra")]
mod dijkstra {
    use super::*;

    const GRAPH_SIZES: &[usize] = &[1000, 10000, 100000];

    #[derive(Copy, Clone, Eq, PartialEq)]
    struct State<T> {
        cost: T,
        position: usize,
    }

    impl<T: Ord> Ord for State<T> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            other.cost.cmp(&self.cost)
        }
    }

    impl<T: Ord> PartialOrd for State<T> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }

    struct Graph {
        adj: Vec<Vec<(usize, u32)>>,
    }

    fn gen_graph(v: usize) -> Graph {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let mut adj = vec![vec![]; v];
        for slot in &mut adj {
            for _ in 0..10 {
                let t = rng.random_range(0..v);
                let d = rng.random_range(1..100);
                slot.push((t, d));
            }
        }
        Graph { adj }
    }

    #[divan::bench(args = GRAPH_SIZES)]
    fn nonmax(bencher: Bencher, n: usize) {
        bencher.with_inputs(|| gen_graph(n)).bench_values(|graph| {
            let mut dists = vec![None; n];
            let mut pq = BinaryHeap::new();

            let start = NonMaxU32::new(0).unwrap();
            dists[0] = Some(start);
            pq.push(State {
                cost: start,
                position: 0,
            });

            while let Some(State { cost, position }) = pq.pop() {
                if Some(cost) > dists[position] {
                    continue;
                }
                for &(next, edge_cost) in &graph.adj[position] {
                    let next_val = Some(cost + edge_cost);
                    if dists[next].is_none() || next_val < dists[next] {
                        dists[next] = next_val;
                        if let Some(nv) = next_val {
                            pq.push(State {
                                cost: nv,
                                position: next,
                            });
                        }
                    }
                }
            }
            black_box(dists)
        });
    }

    #[divan::bench(args = GRAPH_SIZES)]
    fn primitive(bencher: Bencher, n: usize) {
        bencher.with_inputs(|| gen_graph(n)).bench_values(|graph| {
            let mut dists = vec![None; n];
            let mut pq = BinaryHeap::new();

            dists[0] = Some(0u32);
            pq.push(State {
                cost: 0u32,
                position: 0,
            });

            while let Some(State { cost, position }) = pq.pop() {
                if Some(cost) > dists[position] {
                    continue;
                }
                for &(next, edge_cost) in &graph.adj[position] {
                    let next_dist = cost + edge_cost;
                    if dists[next].is_none() || Some(next_dist) < dists[next] {
                        dists[next] = Some(next_dist);
                        pq.push(State {
                            cost: next_dist,
                            position: next,
                        });
                    }
                }
            }
            black_box(dists)
        });
    }

    #[divan::bench(args = GRAPH_SIZES)]
    fn sentinel(bencher: Bencher, n: usize) {
        bencher.with_inputs(|| gen_graph(n)).bench_values(|graph| {
            let mut dists = vec![u32::MAX; n];
            let mut pq = BinaryHeap::new();

            dists[0] = 0;
            pq.push(State {
                cost: 0u32,
                position: 0,
            });

            while let Some(State { cost, position }) = pq.pop() {
                if cost > dists[position] {
                    continue;
                }
                for &(next, edge_cost) in &graph.adj[position] {
                    let next_dist = cost + edge_cost;
                    if next_dist < dists[next] {
                        dists[next] = next_dist;
                        pq.push(State {
                            cost: next_dist,
                            position: next,
                        });
                    }
                }
            }
            black_box(dists)
        });
    }
}

// --- Struct Padding and Cache Density ---

#[derive(Clone, Copy)]
struct PaddingPrimitive {
    _a: Option<u32>, // 24 bytes total (8 * 3) due to tag alignment
    _b: Option<u32>,
    _c: Option<u32>,
}

#[derive(Clone, Copy)]
struct PaddingNonMax {
    _a: Option<NonMaxU32>, // 12 bytes total (4 * 3) due to niche optimization
    _b: Option<NonMaxU32>,
    _c: Option<NonMaxU32>,
}

#[divan::bench]
fn struct_scan_primitive(bencher: Bencher) {
    let n = 100_000;
    bencher
        .with_inputs(|| {
            vec![
                PaddingPrimitive {
                    _a: Some(1),
                    _b: Some(2),
                    _c: Some(3)
                };
                n
            ]
        })
        .bench_values(|data| {
            divan::black_box(
                data.iter()
                    .map(|x| x._a.unwrap_or(0) + x._b.unwrap_or(0) + x._c.unwrap_or(0))
                    .sum::<u32>(),
            )
        });
}

#[divan::bench]
fn struct_scan_nonmax(bencher: Bencher) {
    let n = 100_000;
    bencher
        .with_inputs(|| {
            vec![
                PaddingNonMax {
                    _a: NonMaxU32::new(1),
                    _b: NonMaxU32::new(2),
                    _c: NonMaxU32::new(3)
                };
                n
            ]
        })
        .bench_values(|data| {
            divan::black_box(
                data.iter()
                    .map(|x| {
                        x._a.unwrap_or(NonMaxU32::ZERO)
                            + x._b.unwrap_or(NonMaxU32::ZERO)
                            + x._c.unwrap_or(NonMaxU32::ZERO)
                    })
                    .sum::<NonMaxU32>(),
            )
        });
}

// --- Indexing ---

#[divan::bench]
fn indexing_nonmax(bencher: Bencher) {
    let data = vec![0u32; 1000];
    let idx = NonMaxUsize::new(500).unwrap();
    bencher.bench_local(move || divan::black_box(data[idx]));
}

#[divan::bench]
fn indexing_primitive(bencher: Bencher) {
    let data = vec![0u32; 1000];
    let idx = 500usize;
    bencher.bench_local(move || divan::black_box(data[idx]));
}

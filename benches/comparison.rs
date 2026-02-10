use arithmetic_nonmax::NonMaxU32;
use divan::{AllocProfiler, black_box};
use rand::{Rng, SeedableRng};
use std::collections::{BinaryHeap, HashMap};
use std::sync::{OnceLock, Mutex};

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

fn main() {
    divan::main();
}

struct PreparedGraph {
    v: usize,
    // Dijkstra 用: 隣接リスト
    adj: Vec<Vec<(usize, u32)>>,
    // Floyd-Warshall 用: エッジリスト
    edges: Vec<(usize, usize, u32)>,
}

fn get_graph(v: usize, is_dijkstra: bool) -> &'static PreparedGraph {
    static CACHE: OnceLock<Mutex<HashMap<(usize, bool), &'static PreparedGraph>>> = OnceLock::new();
    let mutex = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut guard = mutex.lock().unwrap();
    
    if let Some(&graph) = guard.get(&(v, is_dijkstra)) {
        return graph;
    }

    let mut adj = vec![];
    let mut edges = vec![];
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);

    if is_dijkstra {
        adj = vec![vec![]; v];
        for i in 0..v {
            for _ in 0..10 {
                let t = rng.random_range(0..v);
                let d = rng.random_range(1..1001);
                adj[i].push((t, d));
            }
        }
    } else {
        for s in 0..v {
            for _ in 0..10 {
                let t = rng.random_range(0..v);
                let d = rng.random_range(1..1001);
                edges.push((s, t, d));
            }
        }
    }

    let graph = Box::leak(Box::new(PreparedGraph { v, adj, edges }));
    guard.insert((v, is_dijkstra), graph);
    graph
}

// --- Floyd-Warshall (1次元配列版) ---

const FW_SIZES: &[usize] = &[1, 10, 100, 200, 400];

#[divan::bench(args = FW_SIZES)]
fn floyd_warshall_primitive(n: usize) {
    let graph = get_graph(n, false);
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
    black_box(dist);
}

#[divan::bench(args = FW_SIZES)]
fn floyd_warshall_nonmax(n: usize) {
    let graph = get_graph(n, false);
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
                        let new_dist = dik + dkj.get();
                        let ij = i * v + j;
                        if dist[ij].is_none() || Some(new_dist) < dist[ij] {
                            dist[ij] = Some(new_dist);
                        }
                    }
                }
            }
        }
    }
    black_box(dist);
}

#[divan::bench(args = FW_SIZES)]
fn floyd_warshall_manual_inf(n: usize) {
    let graph = get_graph(n, false);
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
    black_box(dist);
}

// --- Dijkstra (隣接リスト事前構築版) ---

const DIJKSTRA_SIZES: &[usize] = &[1, 10, 100, 1000, 10000, 100000, 200000, 400000];

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

#[divan::bench(args = DIJKSTRA_SIZES)]
fn dijkstra_primitive(n: usize) {
    let graph = get_graph(n, true);
    let v = graph.v;
    if v == 0 { return; }
    let mut dists = vec![None; v];
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
    black_box(dists);
}

#[divan::bench(args = DIJKSTRA_SIZES)]
fn dijkstra_nonmax(n: usize) {
    let graph = get_graph(n, true);
    let v = graph.v;
    if v == 0 { return; }
    let mut dists = vec![None; v];
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
    black_box(dists);
}

#[divan::bench(args = DIJKSTRA_SIZES)]
fn dijkstra_manual_inf(n: usize) {
    let graph = get_graph(n, true);
    let v = graph.v;
    if v == 0 { return; }
    let mut dists = vec![u32::MAX; v];
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
    black_box(dists);
}

// --- Array Scan and Sum ---

const SIZES: &[usize] = &[1, 10, 100, 1000, 10000, 100000, 1000000];

macro_rules! sum_bench_type {
    ($t:ty, $name:ident, $nonmax_t:ident) => {
        mod $name {
            use super::SIZES;
            use arithmetic_nonmax::$nonmax_t;

            #[divan::bench(args = SIZES)]
            fn sum_nonmax(bencher: divan::Bencher, n: usize) {
                let data = vec![$nonmax_t::new(1 as $t); n];
                bencher.bench_local(move || {
                    divan::black_box(data.iter().flatten().map(|x| x.get()).sum::<$t>())
                });
            }

            #[divan::bench(args = SIZES)]
            fn sum_primitive(bencher: divan::Bencher, n: usize) {
                let data = vec![Some(1 as $t); n];
                bencher.bench_local(move || {
                    divan::black_box(data.iter().flatten().sum::<$t>())
                });
            }

            #[divan::bench(args = SIZES)]
            fn sum_raw(bencher: divan::Bencher, n: usize) {
                let data = vec![1 as $t; n];
                bencher.bench_local(move || {
                    divan::black_box(data.iter().sum::<$t>())
                });
            }
        }
    };
}

sum_bench_type!(u8, sum_u8, NonMaxU8);
sum_bench_type!(u32, sum_u32, NonMaxU32);
sum_bench_type!(u64, sum_u64, NonMaxU64);
sum_bench_type!(u128, sum_u128, NonMaxU128);
sum_bench_type!(usize, sum_usize, NonMaxUsize);
sum_bench_type!(i32, sum_i32, NonMaxI32);

// --- Micro Operations ---

macro_rules! micro_bench_type {
    ($t:ty, $name:ident, $nonmax_t:ident) => {
        mod $name {
            use arithmetic_nonmax::$nonmax_t;

            #[divan::bench]
            fn new_nonmax() -> Option<$nonmax_t> {
                $nonmax_t::new(divan::black_box(123 as $t))
            }

            #[divan::bench]
            fn new_primitive() -> Option<$t> {
                divan::black_box(Some(123 as $t))
            }

            #[divan::bench]
            fn new_raw() -> $t {
                divan::black_box(123 as $t)
            }

            #[divan::bench]
            fn get_nonmax() -> $t {
                let val = divan::black_box($nonmax_t::new(123 as $t).unwrap());
                val.get()
            }

            #[divan::bench]
            fn get_raw() -> $t {
                divan::black_box(123 as $t)
            }

            #[divan::bench]
            fn add_nonmax() -> Option<$nonmax_t> {
                let a = divan::black_box($nonmax_t::new(100 as $t).unwrap());
                let b = divan::black_box($nonmax_t::new(50 as $t).unwrap());
                a.checked_add(b)
            }

            #[divan::bench]
            fn add_primitive() -> Option<$t> {
                let a = divan::black_box(Some(100 as $t));
                let b = divan::black_box(Some(50 as $t));
                a.and_then(|x| x.checked_add(b.unwrap()))
            }

            #[divan::bench]
            fn add_raw() -> $t {
                let a = divan::black_box(100 as $t);
                let b = divan::black_box(50 as $t);
                a.wrapping_add(b)
            }
        }
    };
}

micro_bench_type!(u8, u8_bench, NonMaxU8);
micro_bench_type!(u16, u16_bench, NonMaxU16);
micro_bench_type!(u32, u32_bench, NonMaxU32);
micro_bench_type!(u64, u64_bench, NonMaxU64);
micro_bench_type!(u128, u128_bench, NonMaxU128);
micro_bench_type!(usize, usize_bench, NonMaxUsize);
micro_bench_type!(i8, i8_bench, NonMaxI8);
micro_bench_type!(i16, i16_bench, NonMaxI16);
micro_bench_type!(i32, i32_bench, NonMaxI32);
micro_bench_type!(i64, i64_bench, NonMaxI64);
micro_bench_type!(i128, i128_bench, NonMaxI128);
micro_bench_type!(isize, isize_bench, NonMaxIsize);

// --- Struct Padding and Cache Density ---

#[derive(Clone, Copy)]
struct PaddingPrimitive {
    _a: Option<u32>,
    _b: Option<u32>,
    _c: Option<u32>,
}

#[derive(Clone, Copy)]
struct PaddingNonMax {
    _a: Option<NonMaxU32>,
    _b: Option<NonMaxU32>,
    _c: Option<NonMaxU32>,
}

#[divan::bench]
fn struct_scan_primitive(bencher: divan::Bencher) {
    let n = 100_000;
    let data = vec![PaddingPrimitive { _a: Some(1), _b: Some(2), _c: Some(3) }; n];
    bencher.bench_local(move || {
        divan::black_box(data.iter().fold(0u32, |acc, x| {
            acc + x._a.unwrap_or(0) + x._b.unwrap_or(0) + x._c.unwrap_or(0)
        }))
    });
}

#[divan::bench]
fn struct_scan_nonmax(bencher: divan::Bencher) {
    let n = 100_000;
    let data = vec![PaddingNonMax { _a: NonMaxU32::new(1), _b: NonMaxU32::new(2), _c: NonMaxU32::new(3) }; n];
    bencher.bench_local(move || {
        divan::black_box(data.iter().fold(0u32, |acc, x| {
            acc + x._a.map(|v| v.get()).unwrap_or(0) + x._b.map(|v| v.get()).unwrap_or(0) + x._c.map(|v| v.get()).unwrap_or(0)
        }))
    });
}

// --- Indexing ---

#[divan::bench]
fn indexing_nonmax(bencher: divan::Bencher) {
    let data = vec![0u32; 1000];
    let idx = arithmetic_nonmax::NonMaxUsize::new(500).unwrap();
    bencher.bench_local(move || {
        divan::black_box(data[idx])
    });
}

#[divan::bench]
fn indexing_primitive(bencher: divan::Bencher) {
    let data = vec![0u32; 1000];
    let idx = 500usize;
    bencher.bench_local(move || {
        divan::black_box(data[idx])
    });
}

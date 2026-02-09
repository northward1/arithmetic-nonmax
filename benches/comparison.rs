use arithmetic_nonmax::NonMaxU32;
use divan::{AllocProfiler, black_box};
use rand::{Rng, SeedableRng};
use std::collections::BinaryHeap;
use std::sync::OnceLock;

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

fn main() {
    // Pre-initialize graphs so their construction isn't counted in benchmarks
    let _ = get_small_graph();
    let _ = get_large_graph();
    divan::main();
}

struct PreparedGraph {
    v: usize,
    // Dijkstra 用: 隣接リスト
    adj: Vec<Vec<(usize, u32)>>,
    // Floyd-Warshall 用: エッジリスト
    edges: Vec<(usize, usize, u32)>,
}

fn get_small_graph() -> &'static PreparedGraph {
    static GRAPH: OnceLock<PreparedGraph> = OnceLock::new();
    GRAPH.get_or_init(|| {
        let v = 500;
        let mut edges = Vec::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        for s in 0..v {
            for _ in 0..10 {
                let t = rng.random_range(0..v);
                let d = rng.random_range(1..1001);
                edges.push((s, t, d));
            }
        }
        PreparedGraph {
            v,
            adj: vec![],
            edges,
        }
    })
}

fn get_large_graph() -> &'static PreparedGraph {
    static GRAPH: OnceLock<PreparedGraph> = OnceLock::new();
    GRAPH.get_or_init(|| {
        let v = 500_000;
        let mut adj = vec![vec![]; v];
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        for row in &mut adj {
            for _ in 0..10 {
                let t = rng.random_range(0..v);
                let d = rng.random_range(1..1001);
                row.push((t, d));
            }
        }
        PreparedGraph {
            v,
            adj,
            edges: vec![],
        }
    })
}

// --- Floyd-Warshall (1次元配列版) ---

#[divan::bench]
fn floyd_warshall_primitive() {
    let graph = get_small_graph();
    let v = graph.v;
    // 1次元配列で管理 [i * v + j]
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

#[divan::bench]
fn floyd_warshall_nonmax() {
    let graph = get_small_graph();
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

#[divan::bench]
fn floyd_warshall_manual_inf() {
    let graph = get_small_graph();
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

#[divan::bench]
fn dijkstra_primitive() {
    let graph = get_large_graph();
    let v = graph.v;
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

#[divan::bench]
fn dijkstra_nonmax() {
    let graph = get_large_graph();
    let v = graph.v;
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

#[divan::bench]
fn dijkstra_manual_inf() {
    let graph = get_large_graph();
    let v = graph.v;
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
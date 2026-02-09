// AOJ GRL_1_A: Single Source Shortest Path
// URL: https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_A
#![allow(non_snake_case, unused_must_use, unused_imports)]
use arithmetic_nonmax::NonMax;
use std::collections::BinaryHeap;
use std::io::{self, prelude::*};

#[derive(Copy, Clone, Eq, PartialEq)]
struct State {
    cost: NonMax<u32>,
    position: usize,
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other
            .cost
            .cmp(&self.cost)
            .then_with(|| self.position.cmp(&other.position))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn main() {
    let (stdin, stdout) = (io::read_to_string(io::stdin()).unwrap(), io::stdout());
    let (mut stdin, mut buffer) = (stdin.split_whitespace(), io::BufWriter::new(stdout.lock()));

    macro_rules! input {
        ($t: ty) => {
            stdin.next().unwrap().parse::<$t>().unwrap()
        };
    }

    let V = match stdin.next() {
        Some(v) => v.parse::<usize>().unwrap(),
        None => return,
    };
    let E = input!(usize);
    let r = input!(usize);

    let mut adj = vec![vec![]; V];
    for _ in 0..E {
        let s = input!(usize);
        let t = input!(usize);
        let d = input!(u32);
        adj[s].push((t, d));
    }

    let mut dists: Vec<Option<NonMax<u32>>> = vec![None; V];
    let mut pq = BinaryHeap::new();

    let start_dist = NonMax::new(0).unwrap();
    dists[r] = Some(start_dist);
    pq.push(State {
        cost: start_dist,
        position: r,
    });

    while let Some(State { cost, position }) = pq.pop() {
        if let Some(d) = dists[position]
            && cost > d
        {
            continue;
        }

        for &(next_node, edge_cost) in &adj[position] {
            let next_dist = cost + edge_cost;

            if dists[next_node].is_none() || Some(next_dist) < dists[next_node] {
                dists[next_node] = Some(next_dist);
                pq.push(State {
                    cost: next_dist,
                    position: next_node,
                });
            }
        }
    }

    for d in dists {
        match d {
            Some(v) => writeln!(buffer, "{}", v),
            None => writeln!(buffer, "INF"),
        };
    }
}

// AOJ GRL_1_C: All Pairs Shortest Path
// URL: https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_C
#![allow(non_snake_case, unused_must_use, unused_imports)]
use arithmetic_nonmax::NonMax;
use std::io::{self, prelude::*};

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

    let mut dist = vec![vec![None; V]; V];
    for (i, row) in dist.iter_mut().enumerate() {
        row[i] = Some(NonMax::new(0).unwrap());
    }

    for _ in 0..E {
        let s = input!(usize);
        let t = input!(usize);
        let d = input!(i32);
        dist[s][t] = Some(NonMax::new(d).unwrap());
    }

    // Floyd-Warshall
    for k in 0..V {
        for i in 0..V {
            if dist[i][k].is_none() {
                continue;
            }
            for j in 0..V {
                if dist[k][j].is_none() {
                    continue;
                }
                let new_dist = dist[i][k].unwrap() + i32::from(dist[k][j].unwrap());
                if dist[i][j].is_none() || Some(new_dist) < dist[i][j] {
                    dist[i][j] = Some(new_dist);
                }
            }
        }
    }

    // Negative cycle check
    for (i, row) in dist.iter().enumerate() {
        if let Some(d) = row[i]
            && i32::from(d) < 0
        {
            writeln!(buffer, "NEGATIVE CYCLE");
            return;
        }
    }

    for row in &dist {
        for (j, item) in row.iter().enumerate() {
            match item {
                Some(d) => write!(buffer, "{}", d),
                None => write!(buffer, "INF"),
            };
            if j < V - 1 {
                write!(buffer, " ");
            }
        }
        writeln!(buffer);
    }
}

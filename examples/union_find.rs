// AOJ DSL_1_A: Disjoint Set
// URL: https://onlinejudge.u-aizu.ac.jp/courses/library/3/DSL/1/DSL_1_A
#![allow(non_snake_case, unused_must_use, unused_imports)]
use arithmetic_nonmax::NonMaxUsize;
use std::io::{self, prelude::*};

struct UnionFind {
    // parent[i] == None means i is a root
    // Using Option<NonMaxUsize> saves 50% memory compared to Option<usize>
    parent: Vec<Option<NonMaxUsize>>,
    size: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: vec![None; n],
            size: vec![1; n],
        }
    }

    // By taking NonMaxUsize as argument, we can use it directly for indexing
    fn find(&mut self, i: NonMaxUsize) -> NonMaxUsize {
        match self.parent[i] {
            None => i,
            Some(p) => {
                // p is NonMaxUsize, so it can be passed directly to find and used as index
                let root = self.find(p);
                // Path compression
                self.parent[i] = Some(root);
                root
            }
        }
    }

    fn unite(&mut self, i: NonMaxUsize, j: NonMaxUsize) {
        let mut root_i = self.find(i);
        let mut root_j = self.find(j);
        if root_i != root_j {
            // Union by size
            // root_i and root_j can be used as indices for self.size directly
            if self.size[root_i] < self.size[root_j] {
                std::mem::swap(&mut root_i, &mut root_j);
            }
            self.parent[root_j] = Some(root_i);
            self.size[root_i] += self.size[root_j];
        }
    }

    fn same(&mut self, i: NonMaxUsize, j: NonMaxUsize) -> bool {
        self.find(i) == self.find(j)
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

    let n = match stdin.next() {
        Some(v) => v.parse::<usize>().unwrap(),
        None => return,
    };
    let q = input!(usize);

    let mut uf = UnionFind::new(n);

    for _ in 0..q {
        let com = input!(u8);
        // Convert input usize to NonMaxUsize immediately
        let x = NonMaxUsize::new(input!(usize)).expect("input exceeds usize::MAX - 1");
        let y = NonMaxUsize::new(input!(usize)).expect("input exceeds usize::MAX - 1");

        if com == 0 {
            uf.unite(x, y);
        } else if uf.same(x, y) {
            writeln!(buffer, "1");
        } else {
            writeln!(buffer, "0");
        }
    }
}
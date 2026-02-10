// AOJ DPL_1_A: Coin Changing Problem
// URL: https://onlinejudge.u-aizu.ac.jp/courses/library/7/DPL/1/DPL_1_A
#![allow(non_snake_case, unused_must_use, unused_imports)]
use arithmetic_nonmax::NonMaxU32;
use std::io::{self, prelude::*};

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
    let m = input!(usize);

    let mut coins = vec![0; m];
    for coin in &mut coins {
        *coin = input!(usize);
    }

    // dp[i] = minimum number of coins to pay amount i
    // Option<NonMaxU32> is memory-efficient (same size as u32)
    // None represent "infinity" (cannot pay this amount yet)
    let mut dp: Vec<Option<NonMaxU32>> = vec![None; n + 1];
    dp[0] = Some(NonMaxU32::ZERO);

    // Iterate through amounts from 1 to n
    for i in 1..=n {
        for &coin in &coins {
            if i >= coin {
                // If amount (i - coin) is payable
                if let Some(prev_count) = dp[i - coin] {
                    let new_count = prev_count + 1u32;
                    // Update if current dp[i] is None or new_count is smaller
                    if dp[i].is_none() || Some(new_count) < dp[i] {
                        dp[i] = Some(new_count);
                    }
                }
            }
        }
    }

    if let Some(ans) = dp[n] {
        writeln!(buffer, "{}", ans);
    }
}

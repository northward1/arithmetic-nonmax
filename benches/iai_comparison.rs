use arithmetic_nonmax::NonMaxU32;
use iai::{black_box, main};

const ITERS: u32 = 1000;

fn bench_new_nonmax() {
    for i in 0..ITERS {
        let _ = black_box(NonMaxU32::new(black_box(i)));
    }
}

fn bench_new_primitive() {
    for i in 0..ITERS {
        let _ = black_box(Some(black_box(i)));
    }
}

fn bench_new_raw() {
    for i in 0..ITERS {
        let _ = black_box(i);
    }
}

fn bench_add_nonmax() {
    let a = NonMaxU32::new(100).unwrap();
    let b = NonMaxU32::new(50).unwrap();
    for _ in 0..ITERS {
        let _ = black_box(black_box(a).checked_add(black_box(b)));
    }
}

fn bench_add_primitive() {
    let a = Some(100u32);
    let b = Some(50u32);
    for _ in 0..ITERS {
        let _ = black_box(black_box(a).and_then(|x| x.checked_add(black_box(b).unwrap())));
    }
}

fn bench_add_raw() {
    let a = 100u32;

    let b = 50u32;

    for _ in 0..ITERS {
        let _ = black_box(black_box(a).wrapping_add(black_box(b)));
    }
}

// --- Logic Steps (Dijkstra / FW) ---

fn bench_dijkstra_step_nonmax() {
    let mut dists: [Option<NonMaxU32>; 1] = black_box([None; 1]);
    let cost = black_box(NonMaxU32::new(100).unwrap());
    let edge_cost = black_box(50u32);
    for i in 0..ITERS {
        let next_dist = cost.get() + edge_cost + (black_box(i) & 1);
        if dists[0].is_none() || Some(NonMaxU32::new(next_dist).unwrap()) < dists[0] {
            dists[0] = NonMaxU32::new(next_dist);
        }
        black_box(&dists);
    }
}

fn bench_dijkstra_step_primitive() {
    let mut dists: [Option<u32>; 1] = black_box([None; 1]);
    let cost = black_box(Some(100u32));
    let edge_cost = black_box(50u32);
    for i in 0..ITERS {
        let next_dist = cost.unwrap() + edge_cost + (black_box(i) & 1);
        if dists[0].is_none() || Some(next_dist) < dists[0] {
            dists[0] = Some(next_dist);
        }
        black_box(&dists);
    }
}

fn bench_fw_step_nonmax() {
    let mut dist: [Option<NonMaxU32>; 3] =
        black_box([None, NonMaxU32::new(100), NonMaxU32::new(50)]);
    for i in 0..ITERS {
        if let (Some(dik), Some(dkj)) = (dist[1], dist[2]) {
            let new_dist = dik + dkj.get() + (black_box(i) & 1);
            if dist[0].is_none() || Some(new_dist) < dist[0] {
                dist[0] = Some(new_dist);
            }
        }
        black_box(&dist);
    }
}

fn bench_fw_step_primitive() {
    let mut dist: [Option<u32>; 3] = black_box([None, Some(100u32), Some(50u32)]); // [ij, ik, kj]

    for i in 0..ITERS {
        if let (Some(dik), Some(dkj)) = (dist[1], dist[2]) {
            let new_dist = dik + dkj + (black_box(i) & 1);

            if dist[0].is_none() || Some(new_dist) < dist[0] {
                dist[0] = Some(new_dist);
            }
        }

        black_box(&dist);
    }
}

fn bench_dijkstra_step_nonmax_unchecked() {
    let mut dists: [Option<NonMaxU32>; 1] = black_box([None; 1]);
    let cost = black_box(NonMaxU32::new(100).unwrap());
    let edge_cost = black_box(50u32);
    for i in 0..ITERS {
        let next_dist = cost.get() + edge_cost + (black_box(i) & 1);
        if dists[0].is_none() || unsafe { Some(NonMaxU32::new_unchecked(next_dist)) } < dists[0] {
            dists[0] = unsafe { Some(NonMaxU32::new_unchecked(next_dist)) };
        }
        black_box(&dists);
    }
}

fn bench_fw_step_nonmax_unchecked() {
    let mut dist: [Option<NonMaxU32>; 3] =
        black_box([None, NonMaxU32::new(100), NonMaxU32::new(50)]);
    for i in 0..ITERS {
        if let (Some(dik), Some(dkj)) = (dist[1], dist[2]) {
            let new_dist = dik.get() + dkj.get() + (black_box(i) & 1);
            if dist[0].is_none() || unsafe { Some(NonMaxU32::new_unchecked(new_dist)) } < dist[0] {
                dist[0] = unsafe { Some(NonMaxU32::new_unchecked(new_dist)) };
            }
        }
        black_box(&dist);
    }
}

main!(
    bench_new_nonmax,
    bench_new_primitive,
    bench_new_raw,
    bench_add_nonmax,
    bench_add_primitive,
    bench_add_raw,
    bench_dijkstra_step_nonmax,
    bench_dijkstra_step_primitive,
    bench_dijkstra_step_nonmax_unchecked,
    bench_fw_step_nonmax,
    bench_fw_step_primitive,
    bench_fw_step_nonmax_unchecked
);

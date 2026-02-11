use arithmetic_nonmax::*;
use iai::{black_box, main};
use paste::paste;

macro_rules! bench_ops {
    ($($t:ident, $prim:ident),*) => {
        paste! {
            $(
                // --- NonMax ---
                fn [<bench_new_nonmax_ $t:lower>]() {
                    let _ = black_box($t::new(black_box(10)));
                }

                fn [<bench_get_nonmax_ $t:lower>]() {
                    let val = black_box($t::new(10).unwrap());
                    let _ = black_box(val.get());
                }

                fn [<bench_add_nonmax_ $t:lower>]() {
                    let a = black_box($t::new(10).unwrap());
                    let b = black_box($t::new(5).unwrap());
                    let _ = black_box(a.checked_add(b));
                }

                fn [<bench_cmp_nonmax_ $t:lower>]() {
                    let curr = black_box($t::new(20));
                    let next = black_box($t::new(10).unwrap());
                    let _ = black_box(curr.is_none() || Some(next) < curr);
                }

                // --- Option<Primitive> ---
                fn [<bench_new_primitive_ $t:lower>]() {
                    let _ = black_box(Some(black_box(10 as $prim)));
                }

                fn [<bench_get_primitive_ $t:lower>]() {
                    let val = black_box(Some(10 as $prim));
                    let _ = black_box(val.unwrap());
                }

                fn [<bench_add_primitive_ $t:lower>]() {
                    let a = black_box(Some(10 as $prim));
                    let b = black_box(Some(5 as $prim));
                    let _ = black_box(a.and_then(|x| x.checked_add(b.unwrap())));
                }

                fn [<bench_cmp_primitive_ $t:lower>]() {
                    let curr = black_box(Some(20 as $prim));
                    let next = black_box(10 as $prim);
                    let _ = black_box(curr.is_none() || Some(next) < curr);
                }

                // --- Raw Primitive (Sentinel baseline) ---
                fn [<bench_new_raw_ $t:lower>]() {
                    let _ = black_box(black_box(10 as $prim));
                }

                fn [<bench_get_raw_ $t:lower>]() {
                    let val = black_box(10 as $prim);
                    let _ = black_box(val);
                }

                fn [<bench_add_raw_ $t:lower>]() {
                    let a = black_box(10 as $prim);
                    let b = black_box(5 as $prim);
                    let _ = black_box(a.wrapping_add(b));
                }

                fn [<bench_cmp_raw_ $t:lower>]() {
                    let curr = black_box($prim::MAX);
                    let next = black_box(10 as $prim);
                    let _ = black_box(next < curr);
                }
            )*
        }
    };
}

// Target types for iai
bench_ops!(
    NonMaxU32,
    u32,
    NonMaxI32,
    i32,
    NonMaxUsize,
    usize,
    NonMaxIsize,
    isize
);

main!(
    // u32
    bench_new_nonmax_nonmaxu32,
    bench_new_primitive_nonmaxu32,
    bench_new_raw_nonmaxu32,
    bench_get_nonmax_nonmaxu32,
    bench_get_primitive_nonmaxu32,
    bench_get_raw_nonmaxu32,
    bench_add_nonmax_nonmaxu32,
    bench_add_primitive_nonmaxu32,
    bench_add_raw_nonmaxu32,
    bench_cmp_nonmax_nonmaxu32,
    bench_cmp_primitive_nonmaxu32,
    bench_cmp_raw_nonmaxu32,
    // i32
    bench_new_nonmax_nonmaxi32,
    bench_new_primitive_nonmaxi32,
    bench_new_raw_nonmaxi32,
    bench_get_nonmax_nonmaxi32,
    bench_get_primitive_nonmaxi32,
    bench_get_raw_nonmaxi32,
    bench_add_nonmax_nonmaxi32,
    bench_add_primitive_nonmaxi32,
    bench_add_raw_nonmaxi32,
    bench_cmp_nonmax_nonmaxi32,
    bench_cmp_primitive_nonmaxi32,
    bench_cmp_raw_nonmaxi32,
    // usize
    bench_new_nonmax_nonmaxusize,
    bench_new_primitive_nonmaxusize,
    bench_new_raw_nonmaxusize,
    bench_get_nonmax_nonmaxusize,
    bench_get_primitive_nonmaxusize,
    bench_get_raw_nonmaxusize,
    bench_add_nonmax_nonmaxusize,
    bench_add_primitive_nonmaxusize,
    bench_add_raw_nonmaxusize,
    bench_cmp_nonmax_nonmaxusize,
    bench_cmp_primitive_nonmaxusize,
    bench_cmp_raw_nonmaxusize,
    // isize
    bench_new_nonmax_nonmaxisize,
    bench_new_primitive_nonmaxisize,
    bench_new_raw_nonmaxisize,
    bench_get_nonmax_nonmaxisize,
    bench_get_primitive_nonmaxisize,
    bench_get_raw_nonmaxisize,
    bench_add_nonmax_nonmaxisize,
    bench_add_primitive_nonmaxisize,
    bench_add_raw_nonmaxisize,
    bench_cmp_nonmax_nonmaxisize,
    bench_cmp_primitive_nonmaxisize,
    bench_cmp_raw_nonmaxisize
);

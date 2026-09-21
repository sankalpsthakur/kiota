//! Synthetic expression-substitution timings, not a Lean proof or Arena score.
use kiota::{expr, level};
use rustc_hash::FxHashMap;
use std::hint::black_box;
use std::time::Instant;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn tree(start: u32, leaves: u32) -> expr::Expr {
    if leaves == 1 {
        return expr::const_(1000 + start, vec![level::param(start % 16)]);
    }
    let half = leaves / 2;
    expr::app(tree(start, half), tree(start + half, leaves - half))
}

fn main() {
    let term = tree(0, 4096);
    let bindings: FxHashMap<u32, _> = (0..16)
        .map(|n| (n, level::mk_const(u64::from(n % 4))))
        .collect();
    for (workload, iterations) in [("cold", 100u32), ("warm", 20_000u32)] {
        expr::clear_subst_memos();
        black_box(expr::instantiate_level_params(&term, &bindings));
        let started = Instant::now();
        for _ in 0..iterations {
            if workload == "cold" {
                expr::clear_subst_memos();
            }
            black_box(expr::instantiate_level_params(black_box(&term), black_box(&bindings)));
        }
        let elapsed = started.elapsed();
        println!(
            "{{\"scope\":\"synthetic-universe-substitution\",\"workload\":\"{}\",\"leaves\":4096,\"bindings\":16,\"iterations\":{},\"elapsed_ns\":{}}}",
            workload, iterations, elapsed.as_nanos()
        );
    }
}

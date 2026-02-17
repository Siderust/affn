// Microbenchmarks for Rotation3 operations.
//
// Run with:
//   cargo bench -p affn --bench rotation

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use std::time::Duration;

use affn::Rotation3;
use qtty::Radians;

fn bench_rotation_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("rotation3");
    group
        .sample_size(5_000)
        .measurement_time(Duration::from_secs(3))
        .warm_up_time(Duration::from_millis(500));

    // Prepare test data
    let angle_a = Radians::new(0.409_092_804); // ~23.4° obliquity
    let angle_b = Radians::new(0.001_234_567); // small precession angle
    let angle_c = Radians::new(-0.000_012_345); // small nutation angle
    let angle_d = Radians::new(1.234_567_890); // arbitrary angle

    let rot_a = Rotation3::rx(angle_a);
    let rot_b = Rotation3::rz(angle_b);
    let rot_c = Rotation3::rx(angle_c);
    let rot_d = Rotation3::rz(angle_d);

    let v = [0.123_456_789, 0.987_654_321, 0.456_789_012];

    // ── Single operations ──

    group.bench_function("apply_array", |b| {
        b.iter(|| black_box(rot_a).apply_array(black_box(v)))
    });

    group.bench_function("compose (Mul)", |b| {
        b.iter(|| black_box(rot_a) * black_box(rot_b))
    });

    group.bench_function("transpose", |b| b.iter(|| black_box(rot_a).transpose()));

    // ── Axis constructors ──

    group.bench_function("rx (from angle)", |b| {
        b.iter(|| Rotation3::rx(black_box(angle_a)))
    });

    group.bench_function("rz (from angle)", |b| {
        b.iter(|| Rotation3::rz(black_box(angle_b)))
    });

    // ── Euler constructors ──

    group.bench_function("from_euler_zxz", |b| {
        b.iter(|| {
            Rotation3::from_euler_zxz(black_box(angle_a), black_box(angle_b), black_box(angle_c))
        })
    });

    // ── Composition chains (the real hot path in astronomy) ──

    // 3-rotation chain: Rz * Ry * Rz (Meeus precession)
    group.bench_function("chain_3rot (Rz*Ry*Rz)", |b| {
        b.iter(|| {
            let z = Rotation3::rz(black_box(angle_a));
            let y = Rotation3::ry(black_box(-angle_b));
            let z2 = Rotation3::rz(black_box(angle_c));
            z2 * y * z
        })
    });

    // 4-rotation chain: Rx * Rz * Rx * Rz (Fukushima-Williams precession)
    group.bench_function("chain_4rot (Rx*Rz*Rx*Rz, FW)", |b| {
        b.iter(|| {
            let r1 = Rotation3::rx(black_box(angle_a));
            let r2 = Rotation3::rz(black_box(angle_b));
            let r3 = Rotation3::rx(black_box(-angle_c));
            let r4 = Rotation3::rz(black_box(-angle_d));
            r1 * r2 * r3 * r4
        })
    });

    // 4-rotation chain + apply (full precession + nutation pipeline)
    group.bench_function("chain_4rot + apply", |b| {
        b.iter(|| {
            let r1 = Rotation3::rx(black_box(angle_a));
            let r2 = Rotation3::rz(black_box(angle_b));
            let r3 = Rotation3::rx(black_box(-angle_c));
            let r4 = Rotation3::rz(black_box(-angle_d));
            let composed = r1 * r2 * r3 * r4;
            composed.apply_array(black_box(v))
        })
    });

    // Pre-composed rotation + apply (amortized)
    let precomposed = rot_a * rot_b * rot_c * rot_d;
    group.bench_function("precomposed apply_array", |b| {
        b.iter(|| black_box(precomposed).apply_array(black_box(v)))
    });

    // ── Nutation: 3-rotation chain (Rx * Rz * Rx) ──

    group.bench_function("chain_3rot (nutation Rx*Rz*Rx)", |b| {
        b.iter(|| {
            let r_eps = Rotation3::rx(black_box(-angle_a));
            let r_dpsi = Rotation3::rz(black_box(angle_c));
            let r_eps_true = Rotation3::rx(black_box(angle_a + angle_c));
            r_eps_true * r_dpsi * r_eps
        })
    });

    // ── Combined precession + nutation (7 rotations total in current code) ──

    group.bench_function("full_prec_nut_chain (7 rot)", |b| {
        b.iter(|| {
            // FW precession: 4 rotations
            let fw = Rotation3::rx(black_box(angle_a))
                * Rotation3::rz(black_box(angle_b))
                * Rotation3::rx(black_box(-angle_c))
                * Rotation3::rz(black_box(-angle_d));
            // Nutation: 3 rotations
            let nut = Rotation3::rx(black_box(angle_a + angle_c))
                * Rotation3::rz(black_box(angle_c))
                * Rotation3::rx(black_box(-angle_a));
            // Compose and apply
            let total = nut * fw;
            total.apply_array(black_box(v))
        })
    });

    // ── Fused constructors ──

    group.bench_function("fused_rx_rz", |b| {
        b.iter(|| Rotation3::fused_rx_rz(black_box(angle_a), black_box(angle_b)))
    });

    group.bench_function("fused_rz_rx", |b| {
        b.iter(|| Rotation3::fused_rz_rx(black_box(angle_a), black_box(angle_b)))
    });

    group.bench_function("fused_rx_rz_rx (nutation)", |b| {
        b.iter(|| {
            Rotation3::fused_rx_rz_rx(
                black_box(angle_a + angle_c),
                black_box(angle_c),
                black_box(-angle_a),
            )
        })
    });

    group.bench_function("fused_rz_ry_rz (Meeus prec)", |b| {
        b.iter(|| {
            Rotation3::fused_rz_ry_rz(black_box(angle_a), black_box(-angle_b), black_box(angle_c))
        })
    });

    group.bench_function("fused_rx_rz_rx_rz (FW prec)", |b| {
        b.iter(|| {
            Rotation3::fused_rx_rz_rx_rz(
                black_box(angle_a),
                black_box(angle_b),
                black_box(-angle_c),
                black_box(-angle_d),
            )
        })
    });

    // Fused FW + apply (the complete optimized path for a single vector)
    group.bench_function("fused_rx_rz_rx_rz + apply", |b| {
        b.iter(|| {
            let rot = Rotation3::fused_rx_rz_rx_rz(
                black_box(angle_a),
                black_box(angle_b),
                black_box(-angle_c),
                black_box(-angle_d),
            );
            rot.apply_array(black_box(v))
        })
    });

    // Full pipeline: fused FW precession-nutation + apply
    group.bench_function("fused_full_pn + apply", |b| {
        b.iter(|| {
            // FW precession-nutation: single fused constructor with nutation folded into angles
            let rot = Rotation3::fused_rx_rz_rx_rz(
                black_box(angle_a + angle_c), // epsa + deps
                black_box(angle_b + angle_c), // psib + dpsi
                black_box(-angle_c),          // -phib
                black_box(-angle_d),          // -gamb
            );
            rot.apply_array(black_box(v))
        })
    });

    group.finish();
}

criterion_group!(benches, bench_rotation_ops);
criterion_main!(benches);

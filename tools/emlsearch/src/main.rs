// Bottom-up EML search. Mirrors lib/eml/complex.ts float semantics (lower cut,
// signed zeros, quarter-turn trig reduction, ulp cancellation snap) and the
// golf.ts pool rules (reject exp overflow/underflow of a finite input, and an
// infinity that ln 0 did not produce).
//
// Value dedup is heuristic: a key is ~11 significant digits per component, and
// each key admits SLOTS representatives. One slot is not enough: the K 17 word
// 1111EE1E1E1EE11EE is -1 + 4.4e-114, float64 cannot tell it from -1, and if it
// holds the only slot every word built on -1 inherits the error (the strict K 31
// -1/2 and K 37 1/3 records are then missed). Hits are CANDIDATES only; verify
// them with verify.py (100 and 700 digits) and the repo's acceptsConstantProgram.
//
// usage: emlsearch <max_leaves> <strict:0|1> <targets.tsv> [store_leaves]
//        emlsearch eval <word>            trace a word gate by gate
// env:   SLOTS (default 1, use 3), CAND_CAP (per target per level, default 64),
//        KEY_SHIFT (dropped mantissa bits, default 16), PROBE=<word> (report
//        whether each subtree's key is in the pool, and its representative).
// The last level is streamed (checked against targets, not stored).
// K 41 (max_leaves 21, store 20, SLOTS=3) takes ~5 min on 16 cores and ~35 GB.
// MITM=1 (with store_leaves = max_leaves): after building the pool, invert the last
// gate. For each stored a and target t, ln_lower(b) = exp(a) - t gives b; b is looked
// up among all stored values, so words up to 2*K(pool)+1 are reached. MITM_KMAX caps
// the length kept, MITM_TOL the float tolerance (default 1e-11). A K 35 pool takes
// about 90 s; that run found -i*pi without ln 0 at K 47.
use std::f64::consts::{LN_2, PI};
use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::sync::Mutex;

#[derive(Clone, Copy)]
struct C { re: f64, im: f64 }

fn js_round(x: f64) -> f64 { (x + 0.5).floor() }
fn is_neg_zero(x: f64) -> bool { x == 0.0 && x.is_sign_negative() }

fn reduced_trig(im: f64) -> C {
    if !im.is_finite() { return C { re: f64::NAN, im: f64::NAN }; }
    let quarter = PI / 2.0;
    let steps = js_round(im / quarter);
    let delta = im - steps * quarter;
    let sine = if delta == 0.0 { 0.0 } else { delta.sin() };
    let cosine = if delta == 0.0 { 1.0 } else { delta.cos() };
    let axis = (steps.rem_euclid(4.0) as i32) & 3;
    match axis { 0 => C { re: cosine, im: sine }, 1 => C { re: -sine, im: cosine }, 2 => C { re: -cosine, im: -sine }, _ => C { re: sine, im: -cosine } }
}
fn cis(im: f64, mag: f64) -> C {
    let t = reduced_trig(im);
    if mag == f64::INFINITY {
        let f = |p: f64| if p == 0.0 { 0.0 } else if p > 0.0 { f64::INFINITY } else { f64::NEG_INFINITY };
        return C { re: f(t.re), im: f(t.im) };
    }
    C { re: mag * t.re, im: mag * t.im }
}
fn signed_zero(p: f64) -> f64 { if p < 0.0 || is_neg_zero(p) { -0.0 } else { 0.0 } }
fn underflow_cis(im: f64) -> C { let t = reduced_trig(im); C { re: signed_zero(t.re), im: signed_zero(t.im) } }
fn cexp(z: C) -> C {
    if z.re == f64::NEG_INFINITY && z.im.is_finite() { return underflow_cis(z.im); }
    if z.re == f64::INFINITY && z.im.is_finite() { return cis(z.im, f64::INFINITY); }
    if !z.re.is_finite() || !z.im.is_finite() { return C { re: f64::NAN, im: f64::NAN }; }
    let m = z.re.exp();
    if m == 0.0 { return underflow_cis(z.im); }
    if m == f64::INFINITY { return cis(z.im, f64::INFINITY); }
    cis(z.im, m)
}
fn log_mag(re: f64, im: f64) -> f64 {
    let (ax, ay) = (re.abs(), im.abs());
    let large = f64::MAX / 4.0;
    if ax > large || ay > large { return (ax / 2.0).hypot(ay / 2.0).ln() + LN_2; }
    ax.hypot(ay).ln()
}
fn clog(z: C) -> C {
    if z.re == 0.0 && z.im == 0.0 {
        if is_neg_zero(z.re) { return C { re: f64::NEG_INFINITY, im: -PI }; }
        return C { re: f64::NEG_INFINITY, im: if is_neg_zero(z.im) { -0.0 } else { 0.0 } };
    }
    let arg = if z.re < 0.0 && z.im == 0.0 { -PI } else { z.im.atan2(z.re) };
    let re = log_mag(z.re, z.im);
    if re.is_nan() || arg.is_nan() { return C { re: f64::NAN, im: f64::NAN }; }
    C { re, im: arg }
}
fn unit_ulp(s: f64) -> f64 { let ax = s.abs(); if !(ax > 0.0) || !ax.is_finite() { 0.0 } else { 2f64.powi(ax.log2().floor() as i32 - 52) } }
fn cancelled(diff: f64, l: f64, r: f64) -> f64 {
    if diff == 0.0 || !diff.is_finite() { return diff; }
    let scale = l.abs().max(r.abs());
    if scale > 0.0 && diff.abs() <= 2.0 * unit_ulp(scale) { 0.0 } else { diff }
}
fn eml(x: C, y: C) -> C {
    let a = cexp(x);
    let b = clog(y);
    let re = cancelled(a.re - b.re, a.re, b.re);
    let im = cancelled(a.im - b.im, a.im, b.im);
    if re.is_nan() || im.is_nan() { C { re: f64::NAN, im: f64::NAN } } else { C { re, im } }
}
fn exp_underflows(a: C) -> bool {
    if !a.re.is_finite() || !a.im.is_finite() { return false; }
    if a.re == 0.0 && a.im == 0.0 { return false; }
    let m = a.re.exp();
    m == 0.0 || m < 2f64.powi(-1022)
}
static SHIFT: AtomicU32 = AtomicU32::new(16);
fn part_key(x: f64) -> u64 {
    let sh = SHIFT.load(Ordering::Relaxed);
    if sh == 0 {
        // Use reserved quiet-NaN tags for special values so bit 63 (the sign bit) is preserved on finite nonzeros.
        if x == 0.0 { return if x.is_sign_negative() { 0x7ff8_0000_0000_0001 } else { 0x7ff8_0000_0000_0002 }; }
        if x == f64::INFINITY { return 0x7ff8_0000_0000_0003; }
        if x == f64::NEG_INFINITY { return 0x7ff8_0000_0000_0004; }
        return x.to_bits();
    }
    if x == 0.0 { return if x.is_sign_negative() { 1 } else { 2 }; }
    if x == f64::INFINITY { return 3; }
    if x == f64::NEG_INFINITY { return 4; }
    let b = x.to_bits();
    let rounded = b.wrapping_add(1u64 << (sh - 1)) >> sh;
    rounded | (1u64 << 63)
}
fn key(v: C) -> u128 { ((part_key(v.re) as u128) << 64) | part_key(v.im) as u128 }

struct Pool { re: Vec<f64>, im: Vec<f64>, l: Vec<u32>, r: Vec<u32>, ln0: Vec<bool>, level: Vec<usize> }

fn word(p: &Pool, id: u32, out: &mut String) {
    // iterative post-order
    let mut st: Vec<(u32, bool)> = vec![(id, false)];
    while let Some((n, seen)) = st.pop() {
        if p.l[n as usize] == u32::MAX { out.push('1'); continue; }
        if !seen { st.push((n, true)); st.push((p.r[n as usize], false)); st.push((p.l[n as usize], false)); } else { out.push('E'); }
    }
}

struct Target { id: String, re: f64, im: f64 }

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args[1] == "eval" {
        let mut st: Vec<(C, String)> = Vec::new();
        for ch in args[2].chars() {
            if ch == '1' { st.push((C { re: 1.0, im: 0.0 }, "1".into())); continue; }
            let (y, wy) = st.pop().unwrap(); let (x, wx) = st.pop().unwrap();
            let v = eml(x, y);
            let w = format!("{}{}E", wx, wy);
            println!("{:>40} = {:e} {:e}  under={} ovf={} ln0={}", w, v.re, v.im, exp_underflows(x), x.re.is_finite() && x.re.exp().is_infinite(), y.re == 0.0 && y.im == 0.0);
            st.push((v, w));
        }
        return;
    }
    let max_leaves: usize = args[1].parse().unwrap();
    let strict = args[2] == "1";
    let mut targets: Vec<Target> = Vec::new();
    for line in std::io::BufReader::new(std::fs::File::open(&args[3]).unwrap()).lines() {
        let line = line.unwrap();
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() < 3 { continue; }
        targets.push(Target { id: f[0].to_string(), re: f[1].parse().unwrap(), im: f[2].parse().unwrap() });
    }
    targets.sort_by(|a, b| a.re.partial_cmp(&b.re).unwrap());
    let max_target_re = targets.iter().map(|t| t.re.abs()).fold(1e4_f64, f64::max) + 1.0;
    let store_leaves: usize = args.get(4).map(|s| s.parse().unwrap()).unwrap_or_else(|| max_leaves.saturating_sub(1));
    if let Ok(v) = std::env::var("KEY_SHIFT") {
        let sh: u32 = v.parse().unwrap();
        assert!(sh <= 52, "KEY_SHIFT must be in 0..=52");
        SHIFT.store(sh, Ordering::Relaxed);
    }
    let per_target_cap: usize = std::env::var("CAND_CAP").map(|v| v.parse().unwrap()).unwrap_or(64);
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8);
    const SHARDS: usize = 4096;
    let seen: Vec<Mutex<std::collections::HashMap<u128, u8>>> = (0..SHARDS).map(|_| Mutex::new(std::collections::HashMap::new())).collect();
    let slots: u8 = std::env::var("SLOTS").map(|v| v.parse().unwrap()).unwrap_or(1);
    let mut pool = Pool { re: vec![1.0], im: vec![0.0], l: vec![u32::MAX], r: vec![u32::MAX], ln0: vec![false], level: vec![0, 0, 1] };
    seen[(key(C { re: 1.0, im: 0.0 }) % SHARDS as u128) as usize].lock().unwrap().insert(key(C { re: 1.0, im: 0.0 }), 1);
    let cands: Mutex<Vec<(usize, usize, u32, u32, bool)>> = Mutex::new(Vec::new());
    let tcount: Vec<AtomicUsize> = (0..targets.len()).map(|_| AtomicUsize::new(0)).collect();
    let mut probes: Vec<(usize, C, String)> = Vec::new();
    if let Ok(pw) = std::env::var("PROBE") {
        let mut st: Vec<(C, String, usize)> = Vec::new();
        for ch in pw.chars() {
            if ch == '1' { st.push((C { re: 1.0, im: 0.0 }, "1".into(), 1)); continue; }
            let (y, wy, ny) = st.pop().unwrap(); let (x, wx, nx) = st.pop().unwrap();
            let v = eml(x, y); let w = format!("{}{}E", wx, wy);
            probes.push((nx + ny, v, w.clone())); st.push((v, w, nx + ny));
        }
    }
    let mut cum_finite = 1usize;
    println!("LEVEL n=1 K=1 new=1 finite_new=1 cum_finite=1");
    let started = std::time::Instant::now();
    for n in 2..=max_leaves {
        let store = n <= store_leaves;
        // all (i, j) with i + j = n, over left index ranges
        let mut tasks: Vec<(usize, usize, usize)> = Vec::new(); // (left node, j level, ...)
        for i in 1..n {
            let j = n - i;
            for a in pool.level[i]..pool.level[i + 1] { tasks.push((a, j, 0)); }
        }
        let next = AtomicUsize::new(0);
        let chunk = 64usize;
        let results: Vec<Vec<(f64, f64, u32, u32, bool)>> = std::thread::scope(|s| {
            let mut hs = Vec::new();
            for _ in 0..threads {
                let (pool, tasks, next, seen, targets, cands, tcount, slots) = (&pool, &tasks, &next, &seen, &targets, &cands, &tcount, slots);
                hs.push(s.spawn(move || {
                    let mut local: Vec<(f64, f64, u32, u32, bool)> = Vec::new();
                    let mut local_full: std::collections::HashMap<u128, u8> = std::collections::HashMap::new();
                    loop {
                        let st = next.fetch_add(chunk, Ordering::Relaxed);
                        if st >= tasks.len() { break; }
                        for t in &tasks[st..(st + chunk).min(tasks.len())] {
                            let a = t.0;
                            let av = C { re: pool.re[a], im: pool.im[a] };
                            if exp_underflows(av) { continue; }
                            if av.re.is_finite() && av.re.exp() == f64::INFINITY { continue; }
                            for b in pool.level[t.1]..pool.level[t.1 + 1] {
                                let bv = C { re: pool.re[b], im: pool.im[b] };
                                let fl = pool.ln0[a] || pool.ln0[b] || (bv.re == 0.0 && bv.im == 0.0);
                                if strict && fl { continue; }
                                let v = eml(av, bv);
                                if v.re.is_nan() || v.im.is_nan() { continue; }
                                let fin = v.re.is_finite() && v.im.is_finite();
                                if !fin && !fl { continue; }
                                if fin && v.re.abs() <= max_target_re {
                                    // binary search targets by re
                                    let tol = 1e-9 * v.re.abs().max(v.im.abs()).max(1.0);
                                    let lo = targets.partition_point(|x| x.re < v.re - tol);
                                    let mut k = lo;
                                    while k < targets.len() && targets[k].re <= v.re + tol {
                                        if (targets[k].im - v.im).abs() <= tol && tcount[k].fetch_add(1, Ordering::Relaxed) < per_target_cap {
                                            cands.lock().unwrap().push((k, n, a as u32, b as u32, fl));
                                        }
                                        k += 1;
                                    }
                                }
                                if !store { continue; }
                                let kk = key(v);
                                if local_full.get(&kk).copied().unwrap_or(0) >= slots { continue; }
                                let (admit, global_c) = {
                                    let mut g = seen[(kk % SHARDS as u128) as usize].lock().unwrap();
                                    let c = g.entry(kk).or_insert(0);
                                    if *c < slots { *c += 1; (true, *c) } else { (false, *c) }
                                };
                                if global_c >= slots && local_full.len() < 1_048_576 {
                                    local_full.insert(kk, global_c);
                                }
                                if admit { local.push((v.re, v.im, a as u32, b as u32, fl)); }
                            }
                        }
                    }
                    local
                }));
            }
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        // reset per-level cap so each level reports its own candidates
        for c in &tcount { c.store(0, Ordering::Relaxed); }
        let mut new = 0usize;
        let mut finite_new = 0usize;
        for r in results { for (re, im, l, rr, fl) in r {
            new += 1; if re.is_finite() && im.is_finite() { finite_new += 1; }
            pool.re.push(re); pool.im.push(im); pool.l.push(l); pool.r.push(rr); pool.ln0.push(fl);
        } }
        cum_finite += finite_new;
        for (pn, pv, pw) in &probes { if *pn == n {
            let kk = key(*pv);
            let present = seen[(kk % SHARDS as u128) as usize].lock().unwrap().contains_key(&kk);
            // find representative with same key
            let mut rep = String::from("-");
            for id in 0..pool.re.len() { if key(C { re: pool.re[id], im: pool.im[id] }) == kk { rep.clear(); word(&pool, id as u32, &mut rep); break; } }
            println!("PROBE n={} {} present={} rep={} val={:e},{:e}", n, pw, present, rep, pv.re, pv.im);
        } }
        pool.level.push(pool.re.len());
        println!("LEVEL n={} K={} new={} finite_new={} cum_finite={} stored={} t={:.1}s", n, 2 * n - 1, new, finite_new, cum_finite, store, started.elapsed().as_secs_f64());
        std::io::stdout().flush().unwrap();
        let mut cs = cands.lock().unwrap();
        for &(k, nn, a, b, fl) in cs.iter() {
            let mut w = String::new();
            word(&pool, a, &mut w); word(&pool, b, &mut w); w.push('E');
            println!("CAND\t{}\t{}\t{}\t{}", targets[k].id, 2 * nn - 1, if fl { 1 } else { 0 }, w);
        }
        cs.clear();
        std::io::stdout().flush().unwrap();
    }
    // MITM=1: invert the last gate. eml(a, b) = t  <=>  ln_lower(b) = exp(a) - t, so for
    // each stored a the needed b is exp(exp(a) - t), valid when Im(exp(a) - t) is in
    // [-pi, pi). b is looked up among all stored values by a coarse key (and the
    // adjacent buckets); every hit is re-evaluated and must land within 1e-9 of t.
    if matches!(std::env::var("MITM").as_deref(), Ok("1")) {
        let coarse = |x: f64| -> i64 {
            if x.abs() <= 1e-12 { return 0; }
            if !x.is_finite() { return if x > 0.0 { i64::MAX - 1 } else { i64::MIN + 1 }; }
            let b = x.abs().to_bits() as i64 >> 22; // ~30 mantissa bits, about 9 digits
            if x < 0.0 { -b } else { b }
        };
        let n = pool.re.len();
        let mut table: Vec<(i64, i64, u32)> = (0..n).filter(|&i| pool.re[i].is_finite() && pool.im[i].is_finite())
            .map(|i| (coarse(pool.re[i]), coarse(pool.im[i]), i as u32)).collect();
        table.sort_unstable();
        let leaves_of = |id: usize| -> usize { pool.level.partition_point(|&s| s <= id) - 1 };
        println!("MITM table {} values, t={:.1}s", table.len(), started.elapsed().as_secs_f64());
        let hits: Mutex<Vec<(usize, usize, u32, u32, bool)>> = Mutex::new(Vec::new());
        let next = AtomicUsize::new(0);
        let kmax: usize = std::env::var("MITM_KMAX").map(|v| v.parse().unwrap()).unwrap_or(99);
        let tolerance: f64 = std::env::var("MITM_TOL").map(|v| v.parse().unwrap()).unwrap_or(1e-11);
        std::thread::scope(|sc| {
            for _ in 0..threads {
                let (pool, table, targets, hits, next, kmax, tolerance) = (&pool, &table, &targets, &hits, &next, kmax, tolerance);
                sc.spawn(move || loop {
                    let st = next.fetch_add(1024, Ordering::Relaxed);
                    if st >= n { break; }
                    for a in st..(st + 1024).min(n) {
                        let av = C { re: pool.re[a], im: pool.im[a] };
                        if av.re == f64::INFINITY || av.re.is_nan() || !av.im.is_finite() || exp_underflows(av) || (av.re.is_finite() && av.re.exp() == f64::INFINITY) { continue; }
                        if strict && (pool.ln0[a] || !av.re.is_finite()) { continue; }
                        let ea = cexp(av);
                        let ka = 2 * leaves_of(a) - 1;
                        for (ti, t) in targets.iter().enumerate() {
                            let w = C { re: ea.re - t.re, im: ea.im - t.im };
                            if !(w.im >= -PI - 1e-12 && w.im < PI + 1e-12) || !w.re.is_finite() || w.re > 709.0 || w.re < -700.0 { continue; }
                            let bv = cexp(w);
                            let snap = |x: f64, s: f64| if x.abs() <= 1e-13 * s { 0.0 } else { x };
                            let scale = bv.re.abs().max(bv.im.abs());
                            let tries = [bv, C { re: snap(bv.re, scale), im: snap(bv.im, scale) }];
                            for (ti2, bq) in tries.iter().enumerate() {
                                if ti2 == 1 && bq.re == bv.re && bq.im == bv.im { continue; }
                                let (kr, ki) = (coarse(bq.re), coarse(bq.im));
                                for dr in [-1i64, 0, 1] { for di in [-1i64, 0, 1] {
                                    let (qr, qi) = (kr.saturating_add(if kr == 0 { 0 } else { dr }), ki.saturating_add(if ki == 0 { 0 } else { di }));
                                    if (kr == 0 && dr != 0) || (ki == 0 && di != 0) { continue; }
                                    let lo = table.partition_point(|e| (e.0, e.1) < (qr, qi));
                                    let mut j = lo;
                                    while j < table.len() && table[j].0 == qr && table[j].1 == qi {
                                        let b = table[j].2 as usize; j += 1;
                                        if strict && pool.ln0[b] { continue; }
                                        let v = eml(av, C { re: pool.re[b], im: pool.im[b] });
                                        let tol = tolerance * t.re.abs().max(t.im.abs()).max(1.0);
                                        if (v.re - t.re).abs() > tol || (v.im - t.im).abs() > tol { continue; }
                                        let k = ka + 2 * leaves_of(b) - 1 + 1;
                                        // No "best so far" filter: an impostor found early must not
                                        // hide a genuine longer word. Keep everything up to MITM_KMAX.
                                        if k <= kmax {
                                            hits.lock().unwrap().push((ti, k, a as u32, b as u32, pool.ln0[a] || pool.ln0[b] || (pool.re[b] == 0.0 && pool.im[b] == 0.0)));
                                        }
                                    }
                                } }
                            }
                        }
                    }
                });
            }
        });
        let mut hs = hits.into_inner().unwrap();
        hs.sort_by_key(|h| (h.0, h.1));
        let mut per: std::collections::HashMap<(usize, usize), usize> = std::collections::HashMap::new();
        for &(ti, k, a, b, fl) in hs.iter() {
            let c = per.entry((ti, k)).or_insert(0); *c += 1; if *c > 300 { continue; }
            let mut w = String::new(); word(&pool, a, &mut w); word(&pool, b, &mut w); w.push('E');
            println!("CAND\t{}\t{}\t{}\t{}", targets[ti].id, k, if fl { 1 } else { 0 }, w);
        }
        println!("MITM done t={:.1}s", started.elapsed().as_secs_f64());
    }
}

#![allow(dead_code)]
use std::collections::BTreeMap;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::process;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

const A_WITNESS: [u64; 6] = [221, 289, 299, 323, 391, 437];
const M_WITNESS: u64 = 437;
const X_START: u128 = 581_200_167;
const WITNESS_OFFSETS: [u64; 8] = [12, 15, 32, 35, 49, 86, 128, 219];

fn v_p_u64(mut n: u64, p: u64) -> u32 {
    let mut c = 0;
    while n > 0 && n % p == 0 {
        n /= p;
        c += 1;
    }
    c
}

fn v_p_u128(mut n: u128, p: u64) -> u32 {
    let p128 = p as u128;
    let mut c = 0;
    while n > 0 && n % p128 == 0 {
        n /= p128;
        c += 1;
    }
    c
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn primes_up_to(limit: u64) -> Vec<u64> {
    let mut is_prime = vec![true; (limit + 1) as usize];
    is_prime[0] = false;
    if limit >= 1 {
        is_prime[1] = false;
    }
    let mut p = 2u64;
    while p * p <= limit {
        if is_prime[p as usize] {
            let mut m = p * p;
            while m <= limit {
                is_prime[m as usize] = false;
                m += p;
            }
        }
        p += 1;
    }
    (2..=limit).filter(|&i| is_prime[i as usize]).collect()
}

fn verify_witness_generic(
    a_set: &[u64],
    m_wit: u64,
    x_start: u128,
    offsets: &[u64],
    forbid_picks: usize,
) -> Result<(), String> {
    if a_set.is_empty() || a_set[0] < 2 || *a_set.last().unwrap() != m_wit {
        return Err("Witness A bounds invalid".to_string());
    }
    for i in 0..(a_set.len() - 1) {
        if a_set[i] >= a_set[i + 1] {
            return Err("Witness A not strictly increasing".to_string());
        }
    }
    for i in 0..offsets.len() {
        let b = offsets[i];
        if b < 1 || b > m_wit {
            return Err(format!("Witness offset {} out of range 1..={}", b, m_wit));
        }
        if i + 1 < offsets.len() && offsets[i] >= offsets[i + 1] {
            return Err("Witness offsets not strictly increasing".to_string());
        }
    }
    let all_primes = primes_up_to(m_wit);
    let mut active_primes = Vec::new();
    let mut demands = Vec::new();
    for &p in &all_primes {
        let d: u32 = a_set.iter().map(|&a| v_p_u64(a, p)).sum();
        if d > 0 {
            active_primes.push(p);
            demands.push(d);
        }
    }
    for (idx, &p) in active_primes.iter().enumerate() {
        let got: u32 = offsets
            .iter()
            .map(|&b| v_p_u128(x_start + b as u128, p))
            .sum();
        if got < demands[idx] {
            return Err(format!(
                "Witness fails prime {} demand: got {}, need {}",
                p, got, demands[idx]
            ));
        }
    }
    let mut profile_counts: BTreeMap<Vec<u32>, usize> = BTreeMap::new();
    for j in 1..=m_wit {
        let prof: Vec<u32> = active_primes
            .iter()
            .map(|&p| v_p_u128(x_start + j as u128, p))
            .collect();
        if prof.iter().any(|&v| v > 0) {
            *profile_counts.entry(prof).or_insert(0) += 1;
        }
    }
    let profiles: Vec<(Vec<u32>, usize)> = profile_counts
        .into_iter()
        .map(|(p, c)| (p, c.min(forbid_picks)))
        .collect();
    let k = active_primes.len();
    let n = profiles.len();
    let mut suffix_max = vec![vec![0u32; k]; n + 1];
    for i in (0..n).rev() {
        for p_idx in 0..k {
            suffix_max[i][p_idx] = suffix_max[i + 1][p_idx].max(profiles[i].0[p_idx]);
        }
    }
    fn can_cover(
        idx: usize,
        rem_picks: usize,
        rem_demands: &mut [u32],
        profiles: &[(Vec<u32>, usize)],
        suffix_max: &[Vec<u32>],
    ) -> bool {
        if rem_demands.iter().all(|&d| d == 0) {
            return true;
        }
        if rem_picks == 0 || idx >= profiles.len() {
            return false;
        }
        for (p_idx, &d) in rem_demands.iter().enumerate() {
            if d > (rem_picks as u32) * suffix_max[idx][p_idx] {
                return false;
            }
        }
        let (ref prof, max_c) = profiles[idx];
        let limit = max_c.min(rem_picks);
        for take in (0..=limit).rev() {
            let mut next_demands = rem_demands.to_vec();
            if take > 0 {
                for p_idx in 0..next_demands.len() {
                    next_demands[p_idx] =
                        next_demands[p_idx].saturating_sub(prof[p_idx] * (take as u32));
                }
            }
            if can_cover(
                idx + 1,
                rem_picks - take,
                &mut next_demands,
                profiles,
                suffix_max,
            ) {
                return true;
            }
        }
        false
    }
    let mut rem = demands.clone();
    if can_cover(0, forbid_picks, &mut rem, &profiles, &suffix_max) {
        return Err(format!(
            "Found a <= {} element cover for {:?} at x={}!",
            forbid_picks, a_set, x_start
        ));
    }
    Ok(())
}

fn verify_part1_lower_bound() -> Result<(), String> {
    const X4: u128 = 631_559;
    verify_witness_generic(&[77, 91, 143], 143, X4, &[2, 7, 20, 61], 3)?;
    verify_witness_generic(&[49, 77, 91, 143], 143, X4, &[2, 7, 20, 51, 61], 4)?;
    verify_witness_generic(
        &[289, 299, 323, 391, 437],
        M_WITNESS,
        X_START,
        &[10, 12, 15, 32, 35, 219],
        5,
    )?;
    verify_witness_generic(&A_WITNESS, M_WITNESS, X_START, &WITNESS_OFFSETS, 7)?;
    Ok(())
}

fn is_gcd_connected(set: &[u64; 6]) -> bool {
    let mut visited = [false; 6];
    let mut stack = vec![0usize];
    visited[0] = true;
    let mut count = 1;
    while let Some(u) = stack.pop() {
        for v in 0..6 {
            if !visited[v] && gcd_u64(set[u], set[v]) > 1 {
                visited[v] = true;
                count += 1;
                stack.push(v);
            }
        }
    }
    count == 6
}

/// Sound universal upper bound on `sup_{x >= 0} tau(D_slice, (x, x + m])` via
/// Coprime Prime-Set Subadditivity (`p_j^{d_j} <= m` packed into coprime products `<= m`).
fn coprime_suffix_ub(items: &[(u64, u32, usize)], m: u64) -> usize {
    let mut big_sum = 0usize;
    let mut small_q = Vec::new();
    for &(p, d, wp) in items {
        let mut q = 1u64;
        let mut fits = true;
        for _ in 0..d {
            if let Some(nq) = q.checked_mul(p) {
                if nq <= m {
                    q = nq;
                } else {
                    fits = false;
                    break;
                }
            } else {
                fits = false;
                break;
            }
        }
        if fits {
            small_q.push(q);
        } else {
            big_sum += wp;
        }
    }
    small_q.sort_unstable_by(|a, b| b.cmp(a));
    let mut bins: Vec<u64> = Vec::new();
    for q in small_q {
        let mut placed = false;
        for b in &mut bins {
            if let Some(prod) = b.checked_mul(q) {
                if prod <= m {
                    *b = prod;
                    placed = true;
                    break;
                }
            }
        }
        if !placed {
            bins.push(q);
        }
    }
    big_sum + bins.len()
}

/// For a given 6-set `set` with max element `m`, check if there exists any `x`
/// such that `tau(set, (x, x+m]) > 8`.
/// Uses prime-power CRT branch-and-bound over primes dividing `prod(set)`.
fn check_set_universal_tau_le_8(set: &[u64; 6], m: u64, primes: &[u64]) -> bool {
    let mut active_primes = Vec::new();
    let mut demands = Vec::new();
    for &p in primes {
        if p > m {
            break;
        }
        let d: u32 = set.iter().map(|&a| v_p_u64(a, p)).sum();
        if d > 0 {
            active_primes.push(p);
            demands.push(d);
        }
    }

    // For each active prime p, compute modulus q = p^k <= m < p^{k+1}.
    // For a residue r in 0..q, the base valuation of (r + j) is v_p(r + j) for j in 1..=m,
    // and at most one j where (r + j) % q == 0 can have arbitrarily high valuation (capped at demand).
    // If we can cover all demands with <= 8 elements even when we only use base valuations
    // (or when we branch on residues), we prove tau <= 8.
    // Specifically, we branch on residues r_p mod q_p for each active prime.
    // To keep branching tiny, we sort active primes by q_p ascending and prune as soon as
    // the partial residue assignment already admits a <= 8 cover.
    struct PrimeInfo {
        p: u64,
        demand: u32,
        worst_picks: usize,
        branches: Vec<Vec<u32>>,
    }

    let mut pinfos: Vec<PrimeInfo> = active_primes
        .iter()
        .zip(demands.iter())
        .map(|(&p, &d)| {
            let mut q = p;
            let mut e_m = 1u32;
            while q.saturating_mul(p) <= m {
                q *= p;
                e_m += 1;
            }
            let cap_v = e_m.min(d);
            let mut worst = 0usize;
            let mut seen = std::collections::BTreeSet::new();
            let mut vals = Vec::new();
            for r in 0..q {
                vals.clear();
                let mut row = vec![0u32; m as usize];
                let first_j = if r == 0 { p } else { p - (r % p) };
                let mut j = first_j;
                while j <= m {
                    let sum = r + j;
                    let v = if sum % q == 0 {
                        cap_v
                    } else {
                        v_p_u64(sum, p).min(d)
                    };
                    if v > 0 {
                        row[(j - 1) as usize] = v;
                        vals.push(v);
                    }
                    j += p;
                }
                vals.sort_unstable_by(|a, b| b.cmp(a));
                let mut acc = 0u32;
                let mut picks = 0usize;
                for &v in &vals {
                    acc += v;
                    picks += 1;
                    if acc >= d {
                        break;
                    }
                }
                if picks > worst {
                    worst = picks;
                }
                seen.insert(row);
            }
            let mut raw: Vec<Vec<u32>> = seen.into_iter().collect();
            raw.sort_by(|a, b| {
                let sa: u32 = a.iter().sum();
                let sb: u32 = b.iter().sum();
                sa.cmp(&sb).then_with(|| a.cmp(b))
            });
            let mut branches: Vec<Vec<u32>> = Vec::with_capacity(raw.len());
            'cand: for b in raw {
                for a in &branches {
                    if a.iter().zip(b.iter()).all(|(&va, &vb)| va <= vb) {
                        continue 'cand;
                    }
                }
                branches.push(b);
            }
            PrimeInfo {
                p,
                demand: d,
                worst_picks: worst,
                branches,
            }
        })
        .collect();
    pinfos.sort_by(|a, b| {
        b.worst_picks
            .cmp(&a.worst_picks)
            .then_with(|| a.branches.len().cmp(&b.branches.len()))
    });
    let total_wp: usize = pinfos.iter().map(|i| i.worst_picks).sum();
    if total_wp <= 8 {
        return true;
    }

    // Fast pairwise subadditive check (`tau(S_1 u S_2) <= tau(S_1) + tau(S_2)`):
    if pinfos.len() >= 2 {
        let mut pair_sum = 0usize;
        let mut idx = 0usize;
        while idx + 1 < pinfos.len() {
            let a = &pinfos[idx];
            let b = &pinfos[idx + 1];
            let wp_ab = a.worst_picks + b.worst_picks;
            if a.branches.len() * b.branches.len() <= 2_500 {
                let mut worst_ab = 0usize;
                let sub_infos = [
                    PrimeInfo {
                        p: a.p,
                        demand: a.demand,
                        worst_picks: a.worst_picks,
                        branches: Vec::new(),
                    },
                    PrimeInfo {
                        p: b.p,
                        demand: b.demand,
                        worst_picks: b.worst_picks,
                        branches: Vec::new(),
                    },
                ];
                let mut jv = vec![vec![0u32; 2]; m as usize];
                for ba in &a.branches {
                    for bb in &b.branches {
                        for j in 0..(m as usize) {
                            jv[j][0] = ba[j];
                            jv[j][1] = bb[j];
                        }
                        let g = greedy_prefix_picks(&jv, &sub_infos, 2);
                        if g > worst_ab {
                            worst_ab = g;
                            if worst_ab >= wp_ab {
                                break;
                            }
                        }
                    }
                    if worst_ab >= wp_ab {
                        break;
                    }
                }
                pair_sum += worst_ab.min(wp_ab);
            } else {
                pair_sum += wp_ab;
            }
            idx += 2;
        }
        if idx < pinfos.len() {
            pair_sum += pinfos[idx].worst_picks;
        }
        if pair_sum <= 8 {
            return true;
        }
    }
    let mut suffix_wp = vec![0usize; pinfos.len() + 1];
    for i in (0..pinfos.len()).rev() {
        let items: Vec<(u64, u32, usize)> = pinfos[i..]
            .iter()
            .map(|x| (x.p, x.demand, x.worst_picks))
            .collect();
        let pd_slice: Vec<(u64, u32)> = pinfos[i..].iter().map(|x| (x.p, x.demand)).collect();
        let h_ub = hybrid_coprime_ub(&pd_slice, m);
        suffix_wp[i] = coprime_suffix_ub(&items, m)
            .min(h_ub)
            .min(suffix_wp[i + 1] + pinfos[i].worst_picks);
    }
    if suffix_wp[0] <= 8 {
        return true;
    }

    fn greedy_prefix_picks(j_vals: &[Vec<u32>], pinfos: &[PrimeInfo], t: usize) -> usize {
        let mut rem: Vec<u32> = pinfos[..t].iter().map(|i| i.demand).collect();
        let mut used = vec![false; j_vals.len()];
        let mut picked = 0usize;
        while rem.iter().any(|&d| d > 0) {
            let mut best_j = None;
            let mut best_gain = 0u32;
            for (j, v) in j_vals.iter().enumerate() {
                if used[j] {
                    continue;
                }
                let gain: u32 = (0..t).map(|pi| v[pi].min(rem[pi])).sum();
                if gain > best_gain {
                    best_gain = gain;
                    best_j = Some(j);
                }
            }
            if let Some(j) = best_j {
                used[j] = true;
                picked += 1;
                for pi in 0..t {
                    rem[pi] = rem[pi].saturating_sub(j_vals[j][pi]);
                }
            } else {
                break;
            }
        }
        picked
    }

    fn search_residues(
        p_idx: usize,
        pinfos: &[PrimeInfo],
        suffix_wp: &[usize],
        m: u64,
        j_vals: &mut [Vec<u32>],
    ) -> bool {
        if p_idx > 0 {
            let rem_ub = suffix_wp[p_idx];
            if rem_ub <= 8 {
                let allow = 8 - rem_ub;
                let g = greedy_prefix_picks(j_vals, pinfos, p_idx);
                if g <= allow {
                    return false;
                }
                if allow > 0 && g <= allow + 2 && has_cover_le_k(j_vals, &pinfos[..p_idx], allow) {
                    return false;
                }
            }
        }
        if p_idx == pinfos.len() {
            return !has_cover_le_k(j_vals, pinfos, 8);
        }
        let info = &pinfos[p_idx];
        for br in &info.branches {
            for j in 0..(m as usize) {
                j_vals[j].push(br[j]);
            }
            let bad = search_residues(p_idx + 1, pinfos, suffix_wp, m, j_vals);
            for j in 0..(m as usize) {
                j_vals[j].pop();
            }
            if bad {
                return true;
            }
        }
        false
    }

    fn has_cover_le_k(j_vals: &[Vec<u32>], pinfos: &[PrimeInfo], budget: usize) -> bool {
        let k = pinfos.len();
        let mut profs: BTreeMap<Vec<u32>, usize> = BTreeMap::new();
        for v in j_vals {
            let sub = &v[..k];
            if sub.iter().any(|&x| x > 0) {
                *profs.entry(sub.to_vec()).or_insert(0) += 1;
            }
        }
        let list: Vec<(Vec<u32>, usize)> =
            profs.into_iter().map(|(v, c)| (v, c.min(budget))).collect();
        let n = list.len();
        let mut suffix_max = vec![vec![0u32; k]; n + 1];
        for i in (0..n).rev() {
            for pi in 0..k {
                suffix_max[i][pi] = suffix_max[i + 1][pi].max(list[i].0[pi]);
            }
        }
        let mut rem: Vec<u32> = pinfos.iter().map(|i| i.demand).collect();
        fn bt(
            idx: usize,
            picks: usize,
            rem: &mut [u32],
            list: &[(Vec<u32>, usize)],
            suffix_max: &[Vec<u32>],
        ) -> bool {
            if rem.iter().all(|&d| d == 0) {
                return true;
            }
            if picks == 0 || idx >= list.len() {
                return false;
            }
            for (pi, &d) in rem.iter().enumerate() {
                if d > (picks as u32) * suffix_max[idx][pi] {
                    return false;
                }
            }
            let (ref prof, max_c) = list[idx];
            for take in (0..=max_c.min(picks)).rev() {
                let mut next = rem.to_vec();
                if take > 0 {
                    for pi in 0..next.len() {
                        next[pi] = next[pi].saturating_sub(prof[pi] * (take as u32));
                    }
                }
                if bt(idx + 1, picks - take, &mut next, list, suffix_max) {
                    return true;
                }
            }
            false
        }
        bt(0, budget, &mut rem, &list, &suffix_max)
    }

    let mut j_vals = vec![Vec::with_capacity(pinfos.len()); m as usize];
    !search_residues(0, &pinfos, &suffix_wp, m, &mut j_vals)
}

fn verify_part2_small_m(max_m: u64) -> Result<usize, String> {
    let primes = Arc::new(primes_up_to(max_m));
    let mut tasks = Vec::new();
    for m in 7..=max_m {
        tasks.push(m);
    }

    let next_idx = Arc::new(AtomicUsize::new(0));
    let checked_sets = Arc::new(AtomicUsize::new(0));
    let failures = Arc::new(AtomicUsize::new(0));
    let tasks = Arc::new(tasks);

    let num_threads = thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1);

    let mut handles = Vec::new();
    for _ in 0..num_threads {
        let next_idx = Arc::clone(&next_idx);
        let checked_sets = Arc::clone(&checked_sets);
        let failures = Arc::clone(&failures);
        let tasks = Arc::clone(&tasks);
        let primes = Arc::clone(&primes);

        handles.push(thread::spawn(move || {
            loop {
                let idx = next_idx.fetch_add(1, Ordering::Relaxed);
                if idx >= tasks.len() {
                    break;
                }
                let m = tasks[idx];
                let mut local_checked = 0usize;
                for a1 in 2..m {
                    for a2 in (a1 + 1)..m {
                        for a3 in (a2 + 1)..m {
                            for a4 in (a3 + 1)..m {
                                for a5 in (a4 + 1)..m {
                                    let set = [a1, a2, a3, a4, a5, m];
                                    if !is_gcd_connected(&set) {
                                        continue;
                                    }
                                    local_checked += 1;
                                    if !check_set_universal_tau_le_8(&set, m, &primes) {
                                        failures.fetch_add(1, Ordering::Relaxed);
                                    }
                                }
                            }
                        }
                    }
                }
                checked_sets.fetch_add(local_checked, Ordering::Relaxed);
            }
        }));
    }

    for h in handles {
        h.join().map_err(|_| "Worker thread panicked".to_string())?;
    }

    let fail_count = failures.load(Ordering::Relaxed);
    if fail_count > 0 {
        return Err(format!("Found {} 6-sets with tau > 8", fail_count));
    }
    Ok(checked_sets.load(Ordering::Relaxed))
}

fn isqrt_u64(n: u64) -> u64 {
    if n < 2 {
        return n;
    }
    let mut x = (n as f64).sqrt() as u64;
    while x.saturating_mul(x) > n {
        x -= 1;
    }
    while (x + 1).saturating_mul(x + 1) <= n {
        x += 1;
    }
    x
}

fn min_subinterval_len(m: u64, k: usize) -> u64 {
    let del = (6 - k) as u64;
    if m <= del {
        return 0;
    }
    let rem = m - del;
    let bins = (7 - k) as u64;
    (rem + bins - 1) / bins
}

/// Theorem (Sequential Slot-Threshold Packing):
/// If the prime-factor multiset `factors` can be partitioned into 8 products `h_1..h_8` with
/// `h_k <= floor(M / k)` for `k = 1..=8`, then every interval `I` of `M` consecutive integers
/// contains `b_k in I \ {b_1..b_{k-1}}` divisible by `h_k` (`floor(M / h_k) >= k`), proving
/// `tau(A, I) <= 8` for ALL `x >= 0` in nanoseconds without CRT branching!
#[inline]
fn gcd_prod_prefix_u64(prefix: &[u64], y: u64) -> u64 {
    let mut rem = y;
    let mut g_acc = 1u64;
    for &x in prefix {
        if rem <= 1 {
            break;
        }
        let g = gcd_u64(x, rem);
        if g > 1 {
            g_acc *= g;
            rem /= g;
        }
    }
    g_acc
}

/// Universal Cumulative-GCD Slot Theorem:
/// Given `h_0..h_{l-1} in [1, m]`, if `gcd(prod_{i < j} h_i, h_j) <= floor(m / (j + 1))`
/// for all `j in 0..l`, then every interval `I` of length `m` contains `<= l` distinct
/// elements whose product is divisible by `prod_{j=0}^{l-1} h_j`.
#[inline]
fn fits_cum_gcd_slots(k: usize, prod: u64, bins: &[u64; 8], l: usize, m: u64) -> bool {
    if prod > m {
        return false;
    }
    let mut tmp = *bins;
    tmp[k] = prod;
    for j in k..l {
        let bj = tmp[j];
        if bj <= 1 {
            continue;
        }
        if bj > m {
            return false;
        }
        if j > 0 && gcd_prod_prefix_u64(&tmp[..j], bj) > m / ((j + 1) as u64) {
            return false;
        }
    }
    true
}

/// Minimum slots `l in 1..=budget` needed to pack a single prime-group's prime factors
/// using the Universal Cumulative-GCD Slot Theorem on `0..l`.
fn min_slots_for_group(factors_desc: &[u64], m: u64, budget: usize) -> usize {
    if factors_desc.is_empty() {
        return 0;
    }
    let max_l = budget.min(8);
    // Build prime-power chunks `p^e <= m` sorted descending:
    let mut chunks = Vec::with_capacity(factors_desc.len());
    let mut i = 0usize;
    while i < factors_desc.len() {
        let p = factors_desc[i];
        let mut end = i + 1;
        while end < factors_desc.len() && factors_desc[end] == p {
            end += 1;
        }
        let mut rem = end - i;
        while rem > 0 {
            let mut cur = p;
            rem -= 1;
            while rem > 0 {
                if let Some(nxt) = cur.checked_mul(p) {
                    if nxt <= m {
                        cur = nxt;
                        rem -= 1;
                        continue;
                    }
                }
                break;
            }
            chunks.push(cur);
        }
        i = end;
    }
    chunks.sort_unstable_by(|a, b| b.cmp(a));

    for l in 1..=max_l {
        // Try chunked FFD:
        let mut bins = [1u64; 8];
        let mut ok_ch = true;
        for &ch in &chunks {
            let mut placed = false;
            for k in (0..l).rev() {
                if let Some(prod) = bins[k].checked_mul(ch) {
                    if fits_cum_gcd_slots(k, prod, &bins, l, m) {
                        bins[k] = prod;
                        placed = true;
                        break;
                    }
                }
            }
            if !placed {
                ok_ch = false;
                break;
            }
        }
        if ok_ch {
            return l;
        }
        // Try unchunked raw primes (both tightest-slot-first `rev` and largest-slot-first `0..l` so
        // `361, 323, 247, 76, 289, 17, 169` at `M = 494` and K_{2,3} sets pack in one linear pass!):
        for forward in [true, false] {
            bins = [1u64; 8];
            let mut ok_raw = true;
            for &p in factors_desc {
                let mut placed = false;
                if forward {
                    for k in 0..l {
                        if let Some(prod) = bins[k].checked_mul(p) {
                            if fits_cum_gcd_slots(k, prod, &bins, l, m) {
                                bins[k] = prod;
                                placed = true;
                                break;
                            }
                        }
                    }
                } else {
                    for k in (0..l).rev() {
                        if let Some(prod) = bins[k].checked_mul(p) {
                            if fits_cum_gcd_slots(k, prod, &bins, l, m) {
                                bins[k] = prod;
                                placed = true;
                                break;
                            }
                        }
                    }
                }
                if !placed {
                    ok_raw = false;
                    break;
                }
            }
            if ok_raw {
                return l;
            }
        }
        // Bounded exact backtracking (`<= 128` nodes) for small groups (`<= 16` prime factors, e.g. K_{2,3}):
        if factors_desc.len() <= 16 {
            fn bt_grp(
                idx: usize,
                l: usize,
                m: u64,
                fac: &[u64],
                bins: &mut [u64; 8],
                nodes: &mut usize,
            ) -> bool {
                if idx == fac.len() {
                    return true;
                }
                *nodes += 1;
                if *nodes > 128 {
                    return false;
                }
                let p = fac[idx];
                for k in 0..l {
                    if k > 0 && bins[k] == 1 && bins[k - 1] == 1 {
                        break;
                    }
                    if let Some(prod) = bins[k].checked_mul(p) {
                        if fits_cum_gcd_slots(k, prod, bins, l, m) {
                            let old = bins[k];
                            bins[k] = prod;
                            if bt_grp(idx + 1, l, m, fac, bins, nodes) {
                                return true;
                            }
                            bins[k] = old;
                        }
                    }
                }
                false
            }
            let mut bt_bins = [1u64; 8];
            let mut nodes = 0usize;
            if bt_grp(0, l, m, factors_desc, &mut bt_bins, &mut nodes) {
                return l;
            }
        }
    }
    99
}

/// Theorem (Hybrid Coprime-Group Slot Packing):
/// Partition active primes `(p_i, d_i)` into disjoint coprime groups `G_1 sqcup ... sqcup G_t`.
/// Each group `G_r` gets its OWN fresh slot capacities `[M, M/2, ..., M/l_r]` because coprime
/// groups never need distinctness across groups (`gcd(G_r, G_s) = 1 => tau <= sum_r l_r`)!
fn hybrid_coprime_ub(active_pd: &[(u64, u32)], m: u64) -> usize {
    let k = active_pd.len();
    if k == 0 {
        return 0;
    }
    if k == 1 {
        let fac = vec![active_pd[0].0; active_pd[0].1 as usize];
        return min_slots_for_group(&fac, m, 8);
    }

    // Separate primes whose full prime power `p^d <= m` ("light" primes: cost <= 1 alone, can merge!)
    // from "heavy" primes (`p^d > m`: need >= 2 picks alone, benefit from absorbing light/partner primes!).
    // With `k <= 10` active primes in any 6-set, greedy group-merging + pairwise partner search is tiny!
    let mut single_cost = vec![0usize; k];
    let mut fac_per_p: Vec<Vec<u64>> = Vec::with_capacity(k);
    for (idx, &(p, d)) in active_pd.iter().enumerate() {
        let v = vec![p; d as usize];
        single_cost[idx] = min_slots_for_group(&v, m, 8);
        fac_per_p.push(v);
    }
    let base_sum: usize = single_cost.iter().sum();
    if base_sum <= 8 {
        return base_sum;
    }

    // Greedy agglomerative merging: repeatedly merge any two current groups `(a, b)` whose combined
    // `min_slots_for_group` is strictly `< cost[a] + cost[b]` (or `<=` when products are small)!
    let mut groups: Vec<(Vec<u64>, usize)> = fac_per_p
        .into_iter()
        .zip(single_cost.into_iter())
        .collect();
    // Sort heaviest cost (and largest prime) first:
    groups.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| b.0[0].cmp(&a.0[0])));

    loop {
        let cur_total: usize = groups.iter().map(|g| g.1).sum();
        if cur_total <= 8 {
            return cur_total;
        }
        let mut best_merge: Option<(usize, usize, Vec<u64>, usize, usize)> = None;
        for i in 0..groups.len() {
            for j in (i + 1)..groups.len() {
                let sum_ij = groups[i].1 + groups[j].1;
                let mut merged = Vec::with_capacity(groups[i].0.len() + groups[j].0.len());
                merged.extend_from_slice(&groups[i].0);
                merged.extend_from_slice(&groups[j].0);
                merged.sort_unstable_by(|a, b| b.cmp(a));
                let c = min_slots_for_group(&merged, m, sum_ij);
                if c < sum_ij {
                    let saving = sum_ij - c;
                    if best_merge.as_ref().is_none_or(|bm| saving > bm.4) {
                        best_merge = Some((i, j, merged, c, saving));
                    }
                }
            }
        }
        if let Some((i, j, merged, c, _)) = best_merge {
            groups.remove(j);
            groups[i] = (merged, c);
            continue;
        }
        // Also check 3-way merges `(i, j, r)` (e.g. `{17^2, 23^3, 29^3}` on K_{2,3} where
        // `17*29 <= M` and `17*23 <= M` with `gcd = 17 <= M/2` reduces `1 + 3 + 3 = 7` -> `6`!):
        let mut best_triple: Option<(usize, usize, usize, Vec<u64>, usize)> = None;
        if groups.len() >= 3 && groups.len() <= 12 {
            'trip: for i in 0..groups.len() {
                for j in (i + 1)..groups.len() {
                    for r in (j + 1)..groups.len() {
                        let sum_ijr = groups[i].1 + groups[j].1 + groups[r].1;
                        let mut merged =
                            Vec::with_capacity(groups[i].0.len() + groups[j].0.len() + groups[r].0.len());
                        merged.extend_from_slice(&groups[i].0);
                        merged.extend_from_slice(&groups[j].0);
                        merged.extend_from_slice(&groups[r].0);
                        merged.sort_unstable_by(|a, b| b.cmp(a));
                        let c = min_slots_for_group(&merged, m, sum_ijr - 1);
                        if c < sum_ijr {
                            best_triple = Some((i, j, r, merged, c));
                            break 'trip;
                        }
                    }
                }
            }
        }
        if let Some((i, j, r, merged, c)) = best_triple {
            groups.remove(r);
            groups.remove(j);
            groups[i] = (merged, c);
        } else {
            break;
        }
    }
    groups.iter().map(|g| g.1).sum::<usize>()
}

#[inline]
fn can_hybrid_coprime_pack_le_8(active_pd: &[(u64, u32)], m: u64) -> bool {
    hybrid_coprime_ub(active_pd, m) <= 8
}

/// Pack `factors_desc` (sorted descending) into `caps` (sorted descending, length `2..=4`,
/// e.g. `[m/7, m/8]`, `[m/6, m/7, m/8]`, or `[m/5, m/6, m/7, m/8]`).
/// Soundness: When `d in {3, 4, 5}` elements of `A` share a prime `P_1`, the first `s_d` multiples
/// of `P_1` in `I` cover all `d` of them in `|B_1| <= g(d)` picks (`4, 5, 6`). If the remaining
/// `6 - d` smooth elements factor into `8 - g(d)` products bounded by `[m/(g(d)+1), ..., m/8]`,
/// sequential untouched multiples in `I \ B_1` cover all of `A` in `<= 8` picks!
fn can_pack_into_tail_caps(factors_desc: &[u64], caps: &[u64]) -> bool {
    if factors_desc.is_empty() {
        return true;
    }
    let k_len = caps.len();
    if k_len == 0 || factors_desc[0] > caps[0] {
        return false;
    }
    // Pass 1: Tightest-slot-first FFD (`k_len - 1` down to `0`)
    let mut bins = [1u64; 4];
    let mut ok1 = true;
    for &p in factors_desc {
        let mut placed = false;
        for k in (0..k_len).rev() {
            if let Some(prod) = bins[k].checked_mul(p) {
                if prod <= caps[k] {
                    bins[k] = prod;
                    placed = true;
                    break;
                }
            }
        }
        if !placed {
            ok1 = false;
            break;
        }
    }
    if ok1 {
        return true;
    }
    // Pass 2: Largest-slack-ratio first (`max caps[k] / bins[k]`)
    bins = [1u64; 4];
    let mut ok2 = true;
    for &p in factors_desc {
        let mut best_k = None;
        let mut best_slack = 0u64;
        for k in 0..k_len {
            if let Some(prod) = bins[k].checked_mul(p) {
                if prod <= caps[k] {
                    let slack = caps[k] / bins[k];
                    if best_k.is_none() || slack > best_slack {
                        best_slack = slack;
                        best_k = Some(k);
                    }
                }
            }
        }
        if let Some(k) = best_k {
            bins[k] *= p;
        } else {
            ok2 = false;
            break;
        }
    }
    if ok2 {
        return true;
    }
    if factors_desc.len() > 72 {
        return false;
    }
    fn bt_tail(
        idx: usize,
        prev_k: usize,
        fac: &[u64],
        bins: &mut [u64; 4],
        caps: &[u64],
        nodes: &mut usize,
    ) -> bool {
        if idx == fac.len() {
            return true;
        }
        *nodes += 1;
        if *nodes > 16_384 {
            return false;
        }
        let p = fac[idx];
        let start_k = if idx > 0 && fac[idx] == fac[idx - 1] {
            prev_k
        } else {
            0
        };
        for k in start_k..caps.len() {
            if k > start_k && bins[k] == bins[k - 1] && caps[k] == caps[k - 1] {
                continue;
            }
            if let Some(prod) = bins[k].checked_mul(p) {
                if prod <= caps[k] {
                    let old = bins[k];
                    bins[k] = prod;
                    if bt_tail(idx + 1, k, fac, bins, caps, nodes) {
                        return true;
                    }
                    bins[k] = old;
                }
            }
        }
        false
    }
    let mut bt_bins = [1u64; 4];
    let mut nodes = 0usize;
    bt_tail(0, 0, factors_desc, &mut bt_bins, caps, &mut nodes)
}

fn can_pack_factors_8_slots(factors_desc: &[u64], m: u64, allow_bt: bool) -> bool {
    if factors_desc.is_empty() {
        return true;
    }
    let caps: [u64; 8] = [
        m,
        m / 2,
        m / 3,
        m / 4,
        m / 5,
        m / 6,
        m / 7,
        m / 8,
    ];
    if factors_desc[0] > caps[0] {
        return false;
    }

    // Heuristic 0: Group runs of identical primes `p >= 5` into maximal prime-power chunks `p^e <= m`
    // (`19^2 = 361`, `13^2 = 169`, `11^2 = 121` > `31`) so large prime squares claim `caps[0..4]`
    // before smaller singleton primes `31, 31, 31`!
    if factors_desc.len() <= 96 {
        let mut chunks = [0u64; 96];
        let mut clen = 0usize;
        let mut idx = 0usize;
        while idx < factors_desc.len() {
            let p = factors_desc[idx];
            let mut end = idx + 1;
            while end < factors_desc.len() && factors_desc[end] == p {
                end += 1;
            }
            if p >= 5 && end - idx >= 2 {
                let mut rem = end - idx;
                while rem > 0 {
                    let mut cur = p;
                    rem -= 1;
                    while rem > 0 {
                        if let Some(nxt) = cur.checked_mul(p) {
                            if nxt <= m {
                                cur = nxt;
                                rem -= 1;
                                continue;
                            }
                        }
                        break;
                    }
                    chunks[clen] = cur;
                    clen += 1;
                }
            } else {
                for _ in idx..end {
                    chunks[clen] = p;
                    clen += 1;
                }
            }
            idx = end;
        }
        chunks[..clen].sort_unstable_by(|a, b| b.cmp(a));
        let mut cbins = [1u64; 8];
        let mut cok = true;
        for &ch in &chunks[..clen] {
            let mut placed = false;
            for k in (0..8).rev() {
                if let Some(prod) = cbins[k].checked_mul(ch) {
                    if prod <= caps[k] {
                        cbins[k] = prod;
                        placed = true;
                        break;
                    }
                }
            }
            if !placed {
                cok = false;
                break;
            }
        }
        if cok {
            return true;
        }
    }

    // Heuristic 1: Tightest-capacity bin first (`7` down to `0`)
    let mut bins = [1u64; 8];
    let mut ok1 = true;
    for &p in factors_desc {
        let mut placed = false;
        for k in (0..8).rev() {
            if let Some(prod) = bins[k].checked_mul(p) {
                if prod <= caps[k] {
                    bins[k] = prod;
                    placed = true;
                    break;
                }
            }
        }
        if !placed {
            ok1 = false;
            break;
        }
    }
    if ok1 {
        return true;
    }

    // Heuristic 2: Largest-remaining-ratio bin first (`max (caps[k] / bins[k])` — balances powers of 2/3 evenly!)
    bins = [1u64; 8];
    let mut ok2 = true;
    for &p in factors_desc {
        let mut best_k = None;
        let mut best_slack = 0u64;
        for k in 0..8 {
            if let Some(prod) = bins[k].checked_mul(p) {
                if prod <= caps[k] {
                    let slack = caps[k] / bins[k];
                    if best_k.is_none() || slack > best_slack {
                        best_slack = slack;
                        best_k = Some(k);
                    }
                }
            }
        }
        if let Some(k) = best_k {
            bins[k] *= p;
        } else {
            ok2 = false;
            break;
        }
    }
    if ok2 {
        return true;
    }

    // Heuristic 3: Best-Fit (minimum `caps[k] / (bins[k] * p)` >= 1 — packs `7 * 7 = 49 <= 70` together!)
    bins = [1u64; 8];
    let mut ok3 = true;
    for &p in factors_desc {
        let mut best_k = None;
        let mut best_rem_ratio = u64::MAX;
        let mut best_rem_diff = u64::MAX;
        for k in 0..8 {
            if let Some(prod) = bins[k].checked_mul(p) {
                if prod <= caps[k] {
                    let ratio = caps[k] / prod;
                    let diff = caps[k] - prod;
                    if ratio < best_rem_ratio || (ratio == best_rem_ratio && diff < best_rem_diff) {
                        best_rem_ratio = ratio;
                        best_rem_diff = diff;
                        best_k = Some(k);
                    }
                }
            }
        }
        if let Some(k) = best_k {
            bins[k] *= p;
        } else {
            ok3 = false;
            break;
        }
    }
    if ok3 {
        return true;
    }

    if !allow_bt || factors_desc.len() > 64 {
        return false;
    }

    // Heuristic 4: Universal Cumulative-GCD 8-slot greedy pass (forward & reverse):
    // Certifies sets like `[247, 289, 323, 361, 442, 494]` at `M = 494` in one linear pass!
    for forward in [true, false] {
        let mut gbins = [1u64; 8];
        let mut gok = true;
        for &p in factors_desc {
            let mut placed = false;
            if forward {
                for k in 0..8 {
                    if let Some(prod) = gbins[k].checked_mul(p) {
                        if fits_cum_gcd_slots(k, prod, &gbins, 8, m) {
                            gbins[k] = prod;
                            placed = true;
                            break;
                        }
                    }
                }
            } else {
                for k in (0..8).rev() {
                    if let Some(prod) = gbins[k].checked_mul(p) {
                        if fits_cum_gcd_slots(k, prod, &gbins, 8, m) {
                            gbins[k] = prod;
                            placed = true;
                            break;
                        }
                    }
                }
            }
            if !placed {
                gok = false;
                break;
            }
        }
        if gok {
            return true;
        }
    }

    // Bounded exact backtracking (<= 256 nodes) trying largest-slack bins first:
    fn bt_pack(
        idx: usize,
        factors: &[u64],
        bins: &mut [u64; 8],
        caps: &[u64; 8],
        nodes: &mut usize,
    ) -> bool {
        if idx == factors.len() {
            return true;
        }
        *nodes += 1;
        if *nodes > 256 {
            return false;
        }
        let p = factors[idx];
        for k in 0..8 {
            if let Some(prod) = bins[k].checked_mul(p) {
                if prod <= caps[k] {
                    if k > 0 && bins[k] == bins[k - 1] && caps[k] == caps[k - 1] {
                        continue;
                    }
                    let old = bins[k];
                    bins[k] = prod;
                    if bt_pack(idx + 1, factors, bins, caps, nodes) {
                        return true;
                    }
                    bins[k] = old;
                }
            }
        }
        false
    }
    let mut bt_bins = [1u64; 8];
    let mut nodes = 0usize;
    bt_pack(0, factors_desc, &mut bt_bins, &caps, &mut nodes)
}

fn precompute_prime_branches_for_m(p: u64, m: u64) -> (Vec<Vec<u8>>, [u8; 72]) {
    let mut q = p;
    let mut e_m = 1u8;
    while q.saturating_mul(p) <= m {
        q *= p;
        e_m += 1;
    }
    let mut seen = std::collections::BTreeSet::new();
    let mut max_possible = 0u32;
    let mut wp_arr = [0u8; 72];
    let mut sorted_vals_per_r: Vec<Vec<u8>> = Vec::with_capacity(q as usize);
    for r in 0..q {
        let mut row = vec![0u8; m as usize];
        let mut nz = Vec::new();
        let first_j = if r == 0 { p } else { p - (r % p) };
        let mut j = first_j;
        while j <= m {
            let sum = r + j;
            let v = if sum % q == 0 {
                e_m
            } else {
                v_p_u64(sum, p) as u8
            };
            if v > 0 {
                row[(j - 1) as usize] = v;
                nz.push(v);
            }
            j += p;
        }
        nz.sort_unstable_by(|a, b| b.cmp(a));
        let s: u32 = nz.iter().map(|&x| x as u32).sum();
        if s > max_possible {
            max_possible = s;
        }
        sorted_vals_per_r.push(nz);
        seen.insert(row);
    }
    for d in 1..72usize {
        let mut worst = 0usize;
        for nz in &sorted_vals_per_r {
            let mut acc = 0usize;
            let mut picks = 0usize;
            for &v in nz {
                acc += (v as usize).min(d);
                picks += 1;
                if acc >= d {
                    break;
                }
            }
            if acc < d {
                picks = m as usize + 1;
            }
            if picks > worst {
                worst = picks;
            }
        }
        wp_arr[d] = worst.min(255) as u8;
    }
    let mut raw: Vec<Vec<u8>> = seen.into_iter().collect();
    raw.sort_by(|a, b| {
        let sa: u32 = a.iter().map(|&x| x as u32).sum();
        let sb: u32 = b.iter().map(|&x| x as u32).sum();
        sa.cmp(&sb).then_with(|| a.cmp(b))
    });
    let mut branches: Vec<Vec<u8>> = Vec::with_capacity(raw.len());
    'cand: for b in raw {
        for a in &branches {
            if a.iter().zip(b.iter()).all(|(&va, &vb)| va <= vb) {
                continue 'cand;
            }
        }
        branches.push(b);
    }
    (branches, wp_arr)
}

fn check_crt_with_precomputed(
    cur_d: &[u32],
    primes: &[u64],
    m: u64,
    m_branches: &[Vec<Vec<u8>>],
    m_wp: &[[u8; 72]],
    pair_cache: &mut std::collections::HashMap<(u16, u8, u16, u8), u8>,
) -> bool {
    let mut active: Vec<(usize, usize, u32, usize)> = Vec::with_capacity(8);
    for (pi, &d) in cur_d.iter().enumerate() {
        if d > 0 {
            let wp = m_wp[pi][(d as usize).min(71)] as usize;
            let nb = m_branches[pi].len();
            active.push((nb, wp, d, pi));
        }
    }
    let sum_wp: usize = active.iter().map(|x| x.1).sum();
    if sum_wp <= 8 {
        return true;
    }
    // Pairwise subadditive check (`tau(S1 u S2) <= tau(S1) + tau(S2)`), memoized per M:
    active.sort_by_key(|x| x.3);
    let m_usize = m as usize;
    let greedy_pair = |ba: &[u8], da: u32, bb: &[u8], db: u32| -> usize {
        let mut ra = da;
        let mut rb = db;
        let mut used = vec![false; m_usize];
        let mut picks = 0usize;
        while ra > 0 || rb > 0 {
            let mut best_j = None;
            let mut best_g = 0u32;
            for j in 0..m_usize {
                if used[j] {
                    continue;
                }
                let g = (ba[j] as u32).min(ra) + (bb[j] as u32).min(rb);
                if g > best_g {
                    best_g = g;
                    best_j = Some(j);
                }
            }
            if let Some(j) = best_j {
                used[j] = true;
                picks += 1;
                ra = ra.saturating_sub(ba[j] as u32);
                rb = rb.saturating_sub(bb[j] as u32);
            } else {
                return 99;
            }
        }
        picks
    };
    {
        let mut pair_sum = 0usize;
        let mut i = 0usize;
        while i + 1 < active.len() {
            let (_, wpa, da, pa) = active[i];
            let (_, wpb, db, pb) = active[i + 1];
            let key = (pa as u16, da.min(255) as u8, pb as u16, db.min(255) as u8);
            let ub = if let Some(&c) = pair_cache.get(&key) {
                c as usize
            } else if m_branches[pa].len() * m_branches[pb].len() <= 2_500 {
                let cap_ab = wpa + wpb;
                let mut worst = 0usize;
                for ba in &m_branches[pa] {
                    for bb in &m_branches[pb] {
                        let g = greedy_pair(ba, da, bb, db);
                        if g > worst {
                            worst = g;
                            if worst >= cap_ab {
                                break;
                            }
                        }
                    }
                    if worst >= cap_ab {
                        break;
                    }
                }
                let ans = worst.min(cap_ab).min(255) as u8;
                pair_cache.insert(key, ans);
                ans as usize
            } else {
                wpa + wpb
            };
            pair_sum += ub;
            i += 2;
        }
        if i < active.len() {
            pair_sum += active[i].1;
        }
        if pair_sum <= 8 {
            return true;
        }
    }

    // Sort by `worst_picks` descending (largest demand primes like `P_1` and `2` first so
    // all remaining `wp == 1` small primes pack together in `coprime_suffix_ub`!):
    active.sort_by(|a, b| {
        b.1.cmp(&a.1)
            .then_with(|| a.0.cmp(&b.0))
    });
    let k = active.len();
    let mut suffix_wp = vec![0usize; k + 1];
    for i in (0..k).rev() {
        let items: Vec<(u64, u32, usize)> = active[i..]
            .iter()
            .map(|x| (primes[x.3], x.2, x.1))
            .collect();
        suffix_wp[i] = coprime_suffix_ub(&items, m).min(suffix_wp[i + 1] + active[i].1);
    }
    if suffix_wp[0] <= 8 {
        return true;
    }

    fn dfs_pre<'a>(
        depth: usize,
        active: &[(usize, usize, u32, usize)],
        suffix_wp: &[usize],
        m_usize: usize,
        m_branches: &'a [Vec<Vec<u8>>],
        chosen: &mut Vec<&'a [u8]>,
    ) -> bool {
        if depth > 0 {
            let rem_wp = suffix_wp[depth];
            if rem_wp <= 8 {
                let mut rem: Vec<u32> = active[..depth].iter().map(|x| x.2).collect();
                let mut used = vec![false; m_usize];
                let mut picks = 0usize;
                while rem.iter().any(|&d| d > 0) {
                    let mut best_j = None;
                    let mut best_g = 0u32;
                    for j in 0..m_usize {
                        if used[j] {
                            continue;
                        }
                        let g: u32 = (0..depth).map(|t| (chosen[t][j] as u32).min(rem[t])).sum();
                        if g > best_g {
                            best_g = g;
                            best_j = Some(j);
                        }
                    }
                    if let Some(j) = best_j {
                        used[j] = true;
                        picks += 1;
                        for t in 0..depth {
                            rem[t] = rem[t].saturating_sub(chosen[t][j] as u32);
                        }
                    } else {
                        picks = 99;
                        break;
                    }
                }
                if picks + rem_wp <= 8 {
                    return false;
                }
            }
            if depth == active.len() {
                // Exact 8-pick profile cover check at leaf:
                let mut profs: BTreeMap<Vec<u32>, usize> = BTreeMap::new();
                for j in 0..m_usize {
                    let mut v = Vec::with_capacity(depth);
                    let mut nz = false;
                    for t in 0..depth {
                        let c = (chosen[t][j] as u32).min(active[t].2);
                        if c > 0 {
                            nz = true;
                        }
                        v.push(c);
                    }
                    if nz {
                        *profs.entry(v).or_insert(0) += 1;
                    }
                }
                let list: Vec<(Vec<u32>, usize)> =
                    profs.into_iter().map(|(v, c)| (v, c.min(8))).collect();
                let n = list.len();
                let mut smax = vec![vec![0u32; depth]; n + 1];
                for i in (0..n).rev() {
                    for pi in 0..depth {
                        smax[i][pi] = smax[i + 1][pi].max(list[i].0[pi]);
                    }
                }
                fn bt_leaf(
                    idx: usize,
                    picks: usize,
                    rem: &[u32],
                    list: &[(Vec<u32>, usize)],
                    smax: &[Vec<u32>],
                ) -> bool {
                    if rem.iter().all(|&d| d == 0) {
                        return true;
                    }
                    if picks == 0 || idx >= list.len() {
                        return false;
                    }
                    for (pi, &d) in rem.iter().enumerate() {
                        if d > (picks as u32) * smax[idx][pi] {
                            return false;
                        }
                    }
                    let (ref prof, mc) = list[idx];
                    for take in (0..=mc.min(picks)).rev() {
                        let mut nxt = rem.to_vec();
                        if take > 0 {
                            for pi in 0..nxt.len() {
                                nxt[pi] = nxt[pi].saturating_sub(prof[pi] * (take as u32));
                            }
                        }
                        if bt_leaf(idx + 1, picks - take, &nxt, list, smax) {
                            return true;
                        }
                    }
                    false
                }
                let init_rem: Vec<u32> = active.iter().map(|x| x.2).collect();
                return !bt_leaf(0, 8, &init_rem, &list, &smax);
            }
        }
        let pi = active[depth].3;
        for br in &m_branches[pi] {
            chosen.push(br.as_slice());
            let bad = dfs_pre(depth + 1, active, suffix_wp, m_usize, m_branches, chosen);
            chosen.pop();
            if bad {
                return true;
            }
        }
        false
    }

    let mut chosen = Vec::with_capacity(k);
    !dfs_pre(0, &active, &suffix_wp, m_usize, m_branches, &mut chosen)
}

/// Exact pattern-first decomposed certifier for `M >= 64`:
/// Partition all 6-sets surviving `passes_large_prime_d3_filter` (`D_P >= 3` for every `P > floor(sqrt(M))`)
/// into their exact large-prime multiplicity cases (`[]`, `[3]`, `[4]`, `[5]`, `[6]`, `[3, 3]`), choosing
/// large-prime multiples (`<= floor(M / P) < sqrt(M)` candidates) FIRST and remaining slots ONLY from
/// `sqrt(M)`-smooth integers (`primes <= sqrt(M)`).
fn certify_single_m_ge64_decomposed(m: u64, all_primes: &[u64]) -> Result<(u64, u64, u64), String> {
    let a5_min = min_subinterval_len(m, 5) + 1;
    let a4_min = min_subinterval_len(m, 4) + 1;
    let a3_min = min_subinterval_len(m, 3) + 1;
    let a2_min = min_subinterval_len(m, 2) + 1;
    let a1_min = ((m / 8).max(min_subinterval_len(m, 1)) + 1).max(2);
    let a_mins = [a1_min, a2_min, a3_min, a4_min, a5_min];
    if a5_min >= m {
        return Ok((0, 0, 0));
    }

    let sqrt_m = isqrt_u64(m);
    let max_lp = m / 3;

    // Small primes `<= sqrt_m` and admissible large primes `sqrt_m < P <= M / 3`:
    let mut small_primes = Vec::new();
    let mut large_primes = Vec::new();
    for &p in all_primes {
        if p <= sqrt_m {
            small_primes.push(p);
        } else if p <= max_lp {
            large_primes.push(p);
        } else {
            break;
        }
    }

    // Factor `m`: check if `m` has any prime factor `> max_lp` (if so, 0 surviving sets!).
    let mut rem_m = m;
    for &p in &small_primes {
        while rem_m % p == 0 {
            rem_m /= p;
        }
    }
    let m_large_prime: Option<u64> = if rem_m == 1 {
        None
    } else if rem_m <= max_lp {
        // Since rem_m > sqrt_m and all primes <= sqrt_m are divided out, rem_m <= m implies rem_m is prime!
        Some(rem_m)
    } else {
        return Ok((0, 0, 0));
    };

    // Build `sqrt_m`-smooth candidates in `[a1_min .. m)`:
    let mut is_smooth = vec![false; (m + 1) as usize];
    is_smooth[1] = true;
    for v in 1..=(m as usize) {
        if is_smooth[v] {
            for &p in &small_primes {
                let prod = v * (p as usize);
                if prod <= m as usize {
                    is_smooth[prod] = true;
                } else {
                    break;
                }
            }
        }
    }
    let mut smooth_cands: Vec<u64> = Vec::new();
    for v in a1_min..m {
        if is_smooth[v as usize] {
            smooth_cands.push(v);
        }
    }

    let n_sp = small_primes.len();
    let n_sc = smooth_cands.len();
    let mut sc_vp = vec![0u8; n_sc * n_sp];
    for (ci, &v) in smooth_cands.iter().enumerate() {
        for (pi, &p) in small_primes.iter().enumerate() {
            if p > v {
                break;
            }
            if v % p == 0 {
                sc_vp[ci * n_sp + pi] = v_p_u64(v, p) as u8;
            }
        }
    }

    // Prefix top-`r` valuation sums (`r in 1..=5`) ONLY over `smooth_cands` (`n_sp` small primes!):
    let sc_stride = n_sc + 1;
    let mut sc_top_sums = vec![0u8; n_sp * sc_stride * 6];
    for pi in 0..n_sp {
        let mut top5 = [0u8; 5];
        for ci in 0..n_sc {
            let vp = sc_vp[ci * n_sp + pi];
            if vp > 0 {
                for pos in 0..5 {
                    if vp > top5[pos] {
                        for sh in (pos + 1..5).rev() {
                            top5[sh] = top5[sh - 1];
                        }
                        top5[pos] = vp;
                        break;
                    }
                }
            }
            let base = (pi * sc_stride + (ci + 1)) * 6;
            let mut acc = 0u8;
            for s in 1..=5 {
                acc += top5[s - 1];
                sc_top_sums[base + s] = acc;
            }
        }
    }

    let mut m_sp_vp = vec![0u32; n_sp];
    let mut sp_wp_table = vec![[0u8; 72]; n_sp];
    for (pi, &p) in small_primes.iter().enumerate() {
        m_sp_vp[pi] = v_p_u64(m, p);
        let mut fac = Vec::with_capacity(72);
        for d in 1..72usize {
            fac.push(p);
            let w = min_slots_for_group(&fac, m, 8);
            sp_wp_table[pi][d] = w.min(99) as u8;
            if w > 8 {
                for rest in (d + 1)..72 {
                    sp_wp_table[pi][rest] = 99;
                }
                break;
            }
        }
    }

    // Exact `u128` Heuristic-1 failure thresholds `t_mp[pi]` and prefix top-`r` tail products
    // `sc_top_tail_prod[(pi * sc_stride + len) * 6 + r]`:
    let caps8: [u64; 8] = [m, m / 2, m / 3, m / 4, m / 5, m / 6, m / 7, m / 8];
    let mut t_mp = vec![0u128; n_sp];
    for (pi, &p) in small_primes.iter().enumerate() {
        let mut prod = p as u128;
        for &ck in &caps8 {
            let lb_div = (ck / p) + 1;
            let lb = if p <= ck { lb_div.max(p) } else { lb_div };
            prod = prod.saturating_mul(lb as u128);
        }
        t_mp[pi] = prod;
    }

    let mut sc_tail_val = vec![1u64; n_sc * n_sp];
    for ci in 0..n_sc {
        let mut running = 1u64;
        for pi in (0..n_sp).rev() {
            let vp = sc_vp[ci * n_sp + pi];
            for _ in 0..vp {
                running = running.saturating_mul(small_primes[pi]);
            }
            sc_tail_val[ci * n_sp + pi] = running;
        }
    }

    let mut sc_top_tail_prod = vec![1u128; n_sp * sc_stride * 6];
    for pi in 0..n_sp {
        let mut top5 = [1u64; 5];
        for ci in 0..n_sc {
            let tv = sc_tail_val[ci * n_sp + pi];
            if tv > 1 {
                for pos in 0..5 {
                    if tv > top5[pos] {
                        for sh in (pos + 1..5).rev() {
                            top5[sh] = top5[sh - 1];
                        }
                        top5[pos] = tv;
                        break;
                    }
                }
            }
            let base = (pi * sc_stride + (ci + 1)) * 6;
            let mut acc = 1u128;
            for s in 1..=5 {
                acc = acc.saturating_mul(top5[s - 1] as u128);
                sc_top_tail_prod[base + s] = acc;
            }
        }
    }

    struct EvalCtx<'a> {
        m: u64,
        a_mins: [u64; 5],
        all_primes: &'a [u64],
        small_primes: &'a [u64],
        smooth_cands: &'a [u64],
        sc_vp: &'a [u8],
        sc_top_sums: &'a [u8],
        sp_wp_table: &'a [[u8; 72]],
        t_mp: &'a [u128],
        sc_top_tail_prod: &'a [u128],
        factors_buf: Vec<u64>,
        crt_cache: std::collections::HashSet<(Vec<u8>, u64, u8, u64, u8)>,
        leaves_crt: u64,
        pruned: u64,
        failed: bool,
    }

    impl<'a> EvalCtx<'a> {
        #[inline]
        fn check_full_6set(
            &mut self,
            fixed_lp: &[u64],
            chosen_sc: &[u64],
            sp_d: &[u32],
            lp1: (u64, u8),
            lp2: (u64, u8),
        ) {
            let mut a = [0u64; 6];
            let mut idx = 0usize;
            for &x in fixed_lp {
                a[idx] = x;
                idx += 1;
            }
            for &x in chosen_sc {
                a[idx] = x;
                idx += 1;
            }
            debug_assert_eq!(idx, 6);
            a.sort_unstable();
            // Interval-splitting check:
            for k in 0..5 {
                if a[k] < self.a_mins[k] {
                    self.pruned += 1;
                    return;
                }
            }
            // Divisor-closure maximality check (`k * a[i] <= m` must be in `a`):
            for i in 0..5 {
                if a[i] * 2 <= self.m {
                    let mut mult = a[i] * 2;
                    while mult <= self.m {
                        if !a[(i + 1)..6].contains(&mult) {
                            self.pruned += 1;
                            return;
                        }
                        mult += a[i];
                    }
                }
            }
            // Universal D_P >= 3 Elimination for all primes P >= 11 (`pi >= 4`), plus D_7 != 1 (`pi == 3`):
            if self.small_primes.len() > 3 && sp_d[3] == 1 {
                self.pruned += 1;
                return;
            }
            for pi in 4..self.small_primes.len() {
                if sp_d[pi] == 1 || sp_d[pi] == 2 {
                    self.pruned += 1;
                    return;
                }
            }
            if !is_gcd_connected(&a) {
                self.pruned += 1;
                return;
            }
            // Build sorted descending prime factors:
            self.factors_buf.clear();
            let (mut hi_lp, mut lo_lp) = (lp1, lp2);
            if lo_lp.0 > hi_lp.0 {
                std::mem::swap(&mut hi_lp, &mut lo_lp);
            }
            for _ in 0..hi_lp.1 {
                self.factors_buf.push(hi_lp.0);
            }
            for _ in 0..lo_lp.1 {
                self.factors_buf.push(lo_lp.0);
            }
            for pi in (0..self.small_primes.len()).rev() {
                for _ in 0..sp_d[pi] {
                    self.factors_buf.push(self.small_primes[pi]);
                }
            }
            if can_pack_factors_8_slots(&self.factors_buf, self.m, true) {
                self.pruned += 1;
                return;
            }
            let mut active_pd: Vec<(u64, u32)> = Vec::with_capacity(10);
            for (pi, &d) in sp_d.iter().enumerate() {
                if d > 0 {
                    active_pd.push((self.small_primes[pi], d));
                }
            }
            if lo_lp.1 > 0 {
                active_pd.push((lo_lp.0, lo_lp.1 as u32));
            }
            if hi_lp.1 > 0 {
                active_pd.push((hi_lp.0, hi_lp.1 as u32));
            }
            if can_hybrid_coprime_pack_le_8(&active_pd, self.m) {
                self.pruned += 1;
                return;
            }
            let key = (
                sp_d.iter().map(|&d| d.min(255) as u8).collect::<Vec<u8>>(),
                hi_lp.0,
                hi_lp.1,
                lo_lp.0,
                lo_lp.1,
            );
            if self.crt_cache.contains(&key) {
                self.pruned += 1;
                return;
            }
            self.leaves_crt += 1;
            if !check_set_universal_tau_le_8(&a, self.m, self.all_primes) {
                self.failed = true;
            } else {
                self.crt_cache.insert(key);
            }
        }

        /// Choose `rem_sc` smooth elements from `smooth_cands[0..upper_ci]` in descending order.
        fn dfs_smooth(
            &mut self,
            rem_sc: usize,
            upper_ci: usize,
            fixed_lp: &[u64],
            chosen_sc: &mut Vec<u64>,
            sp_d: &mut [u32],
            lp1: (u64, u8),
            lp2: (u64, u8),
        ) {
            if self.failed {
                return;
            }
            if rem_sc == 0 {
                self.check_full_6set(fixed_lp, chosen_sc, sp_d, lp1, lp2);
                return;
            }
            if upper_ci < rem_sc {
                return;
            }

            // O(n_sp) (`25ns`) Exact `u128` Heuristic-1 Tail-Product Threshold Pruning (`rem_sc in 1..=5`):
            // When `lp2.1 == 0`, any large prime `lp1 <= M/3` (`d <= 5` with `d * lp1 <= M`) always fits
            // in Heuristic 1; a small prime `p_i` can only fail if `P_{>= p_i}(A) >= t_mp[i]`!
            if lp2.1 == 0 {
                let n_sp = self.small_primes.len();
                let sc_stride = self.smooth_cands.len() + 1;
                let mut cur_tail = 1u128;
                for _ in 0..lp1.1 {
                    cur_tail = cur_tail.saturating_mul(lp1.0 as u128);
                }
                let mut can_any_fail = false;
                for pi in (0..n_sp).rev() {
                    let p128 = self.small_primes[pi] as u128;
                    for _ in 0..sp_d[pi] {
                        cur_tail = cur_tail.saturating_mul(p128);
                    }
                    let max_tail = cur_tail.saturating_mul(
                        self.sc_top_tail_prod[(pi * sc_stride + upper_ci) * 6 + rem_sc],
                    );
                    if max_tail >= self.t_mp[pi] {
                        can_any_fail = true;
                        break;
                    }
                }
                if !can_any_fail {
                    self.pruned += 1;
                    return;
                }
            }

            // Universal D_P >= 3 (`P >= 11`, `pi >= 4`) + D_7 != 1 (`pi == 3`) Deficit Pruning:
            // Any prime `p >= 11` currently at multiplicity `1` or `2` MUST reach `>= 3` within the
            // remaining `rem_sc` smooth picks from `0..upper_ci`, forcing their `>= 11`-tail product
            // to be divisible by `prod_{1 <= sp_d[pi] <= 2} p_i^{3 - sp_d[pi]}`!
            let n_sp = self.small_primes.len();
            let sc_stride = self.smooth_cands.len() + 1;
            if n_sp > 3 && sp_d[3] == 1 {
                if self.sc_top_sums[(3 * sc_stride + upper_ci) * 6 + rem_sc] == 0 {
                    self.pruned += 1;
                    return;
                }
            }
            let mut req_prod_11 = 1u128;
            for pi in 4..n_sp {
                let d0 = sp_d[pi];
                if d0 == 1 || d0 == 2 {
                    let need = 3 - d0;
                    if (self.sc_top_sums[(pi * sc_stride + upper_ci) * 6 + rem_sc] as u32) < need {
                        self.pruned += 1;
                        return;
                    }
                    let p128 = self.small_primes[pi] as u128;
                    for _ in 0..need {
                        req_prod_11 = req_prod_11.saturating_mul(p128);
                    }
                }
            }
            if req_prod_11 > 1 {
                let max_11_tail = self.sc_top_tail_prod[(4 * sc_stride + upper_ci) * 6 + rem_sc];
                if req_prod_11 > max_11_tail {
                    self.pruned += 1;
                    return;
                }
            }

            // Exact rank-quota pruning + lower bound on the next descending smooth element:
            // In any valid 6-set `A`, at least `6 - k` elements must be `>= a_mins[k]` (`k in 0..5`).
            // Since `chosen_sc` is picked in strictly descending order, if `already_ge + rem_sc < 6 - k`
            // no valid completion exists; if `already_ge == 5 - k`, even the NEXT smooth element must be `>= a_mins[k]`
            // when `already_ge < 6 - k` and `already_ge + 1` is needed! Specifically, since all future smooth
            // picks are `< val`, at least `(6 - k) - already_ge` remaining smooth picks must be `>= a_mins[k]`,
            // so whenever `already_ge < 6 - k` the largest remaining smooth pick `val` MUST be `>= a_mins[k]`!!
            let mut min_needed = self.a_mins[rem_sc - 1];
            for k in 0..5 {
                let req_ge = 6 - k;
                let mut already_ge = 0usize;
                for &x in fixed_lp {
                    if x >= self.a_mins[k] {
                        already_ge += 1;
                    }
                }
                for &x in chosen_sc.iter() {
                    if x >= self.a_mins[k] {
                        already_ge += 1;
                    }
                }
                if already_ge + rem_sc < req_ge {
                    self.pruned += 1;
                    return;
                }
                if already_ge < req_ge {
                    // At least `(req_ge - already_ge) >= 1` remaining smooth elements must be `>= a_mins[k]`.
                    // Because we pick smooth elements in strictly descending order, the FIRST (`largest`)
                    // remaining smooth element MUST be `>= a_mins[k]` (plus `(req_ge - already_ge - 1)` elements above `a_mins[k]`!).
                    let extra_above = req_ge - already_ge - 1;
                    let base_min = self.a_mins[k] + (extra_above as u64);
                    if base_min > min_needed {
                        min_needed = base_min;
                    }
                }
            }
            let start_ci = self.smooth_cands[..upper_ci].partition_point(|&v| v < min_needed);
            let lo_ci = start_ci.max(rem_sc - 1);
            if lo_ci >= upper_ci {
                return;
            }

            for ci in (lo_ci..upper_ci).rev() {
                let val = self.smooth_cands[ci];
                if rem_sc == 1 {
                    if req_prod_11 > (val as u128)
                        || (req_prod_11 > 1 && (val as u128) % req_prod_11 != 0)
                    {
                        self.pruned += 1;
                        continue;
                    }
                    if n_sp > 3 && sp_d[3] == 1 && val % 7 != 0 {
                        self.pruned += 1;
                        continue;
                    }
                }
                // Top-down divisor-closure check on smooth `val`: every `k * val <= m` (`k >= 2`)
                // must already appear in `fixed_lp` (if `k` has a large prime) or `chosen_sc` (since `k * val > val`)!
                if val * 2 <= self.m {
                    let mut mult = val * 2;
                    let mut miss = false;
                    while mult <= self.m {
                        if mult != self.m
                            && !fixed_lp.contains(&mult)
                            && !chosen_sc.contains(&mult)
                        {
                            miss = true;
                            break;
                        }
                        mult += val;
                    }
                    if miss {
                        self.pruned += 1;
                        continue;
                    }
                }

                let off = ci * n_sp;
                let mut bad_p = false;
                if n_sp > 3 && sp_d[3] + (self.sc_vp[off + 3] as u32) == 1 {
                    if self.sc_top_sums[(3 * sc_stride + ci) * 6 + (rem_sc - 1)] == 0 {
                        bad_p = true;
                    }
                }
                if !bad_p {
                    for pi in 4..n_sp {
                        let nd = sp_d[pi] + (self.sc_vp[off + pi] as u32);
                        if nd == 1 || nd == 2 {
                            if (self.sc_top_sums[(pi * sc_stride + ci) * 6 + (rem_sc - 1)] as u32)
                                < 3 - nd
                            {
                                bad_p = true;
                                break;
                            }
                        }
                    }
                }
                if bad_p {
                    self.pruned += 1;
                    continue;
                }

                chosen_sc.push(val);
                for pi in 0..n_sp {
                    sp_d[pi] += self.sc_vp[off + pi] as u32;
                }
                self.dfs_smooth(rem_sc - 1, ci, fixed_lp, chosen_sc, sp_d, lp1, lp2);
                for pi in 0..n_sp {
                    sp_d[pi] -= self.sc_vp[off + pi] as u32;
                }
                chosen_sc.pop();
                if self.failed {
                    return;
                }
            }
        }
    }

    // Helper: list all admissible multiples `< m` in `[a1_min .. m)` of a large prime `p`:
    let multiples_of_lp = |p: u64| -> Vec<u64> {
        let mut out = Vec::new();
        let first_s = (a1_min + p - 1) / p;
        let max_s = (m - 1) / p;
        for s in first_s..=max_s {
            if is_smooth[s as usize] {
                out.push(s * p);
            }
        }
        out
    };

    // Helper: enumerate combinations of `choose_k` elements from `mults` (filtered by divisor closure
    // for multiples `k * x <= m` that are ALSO multiples of the same large prime `p`!):
    fn choose_lp_subsets(
        mults: &[u64],
        choose_k: usize,
        m: u64,
        include_m: bool,
        out: &mut Vec<Vec<u64>>,
    ) {
        fn rec(
            idx: usize,
            rem: usize,
            mults: &[u64],
            m: u64,
            include_m: bool,
            cur: &mut Vec<u64>,
            out: &mut Vec<Vec<u64>>,
        ) {
            if rem == 0 {
                // Check divisor closure within multiples of `p`: for any `x in cur`, `2*x <= m` is ALSO a multiple of `p`!
                for &x in cur.iter() {
                    let mut mult = x * 2;
                    while mult <= m {
                        if !(mult == m && include_m) && !cur.contains(&mult) {
                            return;
                        }
                        mult += x;
                    }
                }
                out.push(cur.clone());
                return;
            }
            if idx + rem > mults.len() {
                return;
            }
            for i in idx..=(mults.len() - rem) {
                cur.push(mults[i]);
                rec(i + 1, rem - 1, mults, m, include_m, cur, out);
                cur.pop();
            }
        }
        let mut cur = Vec::with_capacity(choose_k);
        rec(0, choose_k, mults, m, include_m, &mut cur, out);
    }

    let mut ctx = EvalCtx {
        m,
        a_mins,
        all_primes,
        small_primes: &small_primes,
        smooth_cands: &smooth_cands,
        sc_vp: &sc_vp,
        sc_top_sums: &sc_top_sums,
        sp_wp_table: &sp_wp_table,
        t_mp: &t_mp,
        sc_top_tail_prod: &sc_top_tail_prod,
        factors_buf: Vec::with_capacity(48),
        crt_cache: std::collections::HashSet::new(),
        leaves_crt: 0,
        pruned: 0,
        failed: false,
    };

    let mut chosen_sc = Vec::with_capacity(5);
    let mut sp_d = vec![0u32; n_sp];

    // Pre-filter helper for `d in {3, 4, 5}` multiples of a large prime `P_1`:
    // Since any `d` multiples of `P_1` in `(0, M]` are covered in `<= g(d)` (`4, 5, 6`) picks on `I`,
    // any smooth complement whose prime factors pack into `tail_caps = [M/(g(d)+1) .. M/8]` is
    // universally certified `<= 8` independent of `P_1` and of which `d` multiples of `P_1` are chosen!
    let collect_unpacked_smooth = |rem_sc: usize,
                                   include_m_smooth: bool,
                                   tail_caps: &[u64]|
     -> Vec<(Vec<u64>, Vec<u32>)> {
        let mut t_mp_tail = vec![0u128; n_sp];
        for (pi, &p) in small_primes.iter().enumerate() {
            let mut prod = p as u128;
            for &ck in tail_caps {
                let lb_div = (ck / p) + 1;
                let lb = if p <= ck { lb_div.max(p) } else { lb_div };
                prod = prod.saturating_mul(lb as u128);
            }
            t_mp_tail[pi] = prod;
        }

        #[allow(clippy::too_many_arguments)]
        fn dfs_unpacked(
            rem: usize,
            upper_ci: usize,
            m: u64,
            small_primes: &[u64],
            smooth_cands: &[u64],
            sc_vp: &[u8],
            sc_top_tail_prod: &[u128],
            t_mp_tail: &[u128],
            tail_caps: &[u64],
            cur_sc: &mut Vec<u64>,
            cur_d: &mut [u32],
            fac_buf: &mut Vec<u64>,
            out: &mut Vec<(Vec<u64>, Vec<u32>)>,
        ) {
            let n_sp = small_primes.len();
            if rem == 0 {
                fac_buf.clear();
                for pi in (0..n_sp).rev() {
                    for _ in 0..cur_d[pi] {
                        fac_buf.push(small_primes[pi]);
                    }
                }
                if !can_pack_into_tail_caps(fac_buf, tail_caps) {
                    out.push((cur_sc.clone(), cur_d.to_vec()));
                }
                return;
            }
            if upper_ci < rem {
                return;
            }
            let sc_stride = smooth_cands.len() + 1;
            let mut cur_tail = 1u128;
            let mut can_fail = false;
            for pi in (0..n_sp).rev() {
                let p128 = small_primes[pi] as u128;
                for _ in 0..cur_d[pi] {
                    cur_tail = cur_tail.saturating_mul(p128);
                }
                let max_tail = cur_tail
                    .saturating_mul(sc_top_tail_prod[(pi * sc_stride + upper_ci) * 6 + rem]);
                if max_tail >= t_mp_tail[pi] {
                    can_fail = true;
                    break;
                }
            }
            if !can_fail {
                return;
            }
            for ci in ((rem - 1)..upper_ci).rev() {
                let val = smooth_cands[ci];
                if val * 2 <= m {
                    let mut mult = val * 2;
                    let mut miss = false;
                    while mult <= m {
                        if mult != m && !cur_sc.contains(&mult) {
                            miss = true;
                            break;
                        }
                        mult += val;
                    }
                    if miss {
                        continue;
                    }
                }
                cur_sc.push(val);
                let off = ci * n_sp;
                for pi in 0..n_sp {
                    cur_d[pi] += sc_vp[off + pi] as u32;
                }
                dfs_unpacked(
                    rem - 1,
                    ci,
                    m,
                    small_primes,
                    smooth_cands,
                    sc_vp,
                    sc_top_tail_prod,
                    t_mp_tail,
                    tail_caps,
                    cur_sc,
                    cur_d,
                    fac_buf,
                    out,
                );
                for pi in 0..n_sp {
                    cur_d[pi] -= sc_vp[off + pi] as u32;
                }
                cur_sc.pop();
            }
        }

        let mut out = Vec::new();
        let mut cur_sc = Vec::with_capacity(rem_sc + 1);
        let mut cur_d = if include_m_smooth {
            m_sp_vp.clone()
        } else {
            vec![0u32; n_sp]
        };
        let mut fac_buf = Vec::with_capacity(32);
        dfs_unpacked(
            rem_sc,
            n_sc,
            m,
            &small_primes,
            &smooth_cands,
            &sc_vp,
            &sc_top_tail_prod,
            &t_mp_tail,
            tail_caps,
            &mut cur_sc,
            &mut cur_d,
            &mut fac_buf,
            &mut out,
        );
        out
    };

    if let Some(p1) = m_large_prime {
        // Case A: `a_6 = M` is divisible by large prime `p1`!
        let mults1 = multiples_of_lp(p1);
        if mults1.len() < 2 {
            return Ok((0, 1, 0));
        }
        // Subcase A1: only large prime is `p1`, picking `t in 2..=4` additional multiples of `p1`
        // (`d = t + 1 in 3..=5` multiples of `p1` total, since `t == 5` reduces by Common-Factor Induction!):
        let max_s_p1 = (m - 1) / p1;
        for t in 2..=4usize.min(mults1.len()) {
            let rem_sc = 5 - t;
            if n_sc < rem_sc {
                continue;
            }
            let tail_caps_slice: &[u64] = match t + 1 {
                5 => &[m / 7, m / 8],
                4 => &[m / 6, m / 7, m / 8],
                _ => &[m / 5, m / 6, m / 7, m / 8],
            };
            let raw_unpacked = collect_unpacked_smooth(rem_sc, false, tail_caps_slice);
            if raw_unpacked.is_empty() {
                ctx.pruned += 1;
                continue;
            }
            let mut lp_max_add = vec![0u32; n_sp];
            for (pi, &q) in small_primes.iter().enumerate().skip(3) {
                let mut qk = q;
                let mut acc = 0u32;
                while qk <= max_s_p1 {
                    acc += ((max_s_p1 / qk) as usize).min(t) as u32;
                    qk = qk.saturating_mul(q);
                }
                lp_max_add[pi] = acc;
            }
            let max_s_pow = (max_s_p1 as u128).saturating_pow(t as u32);
            let unpacked: Vec<(Vec<u64>, Vec<u32>)> = raw_unpacked
                .into_iter()
                .filter(|(_, sc_d)| {
                    if n_sp > 3 && m_sp_vp[3] + sc_d[3] == 1 && lp_max_add[3] == 0 {
                        return false;
                    }
                    let mut req_lp = 1u128;
                    for pi in 4..n_sp {
                        let base_d = m_sp_vp[pi] + sc_d[pi];
                        if base_d == 1 || base_d == 2 {
                            let need = 3 - base_d;
                            if lp_max_add[pi] < need {
                                return false;
                            }
                            let q128 = small_primes[pi] as u128;
                            for _ in 0..need {
                                req_lp = req_lp.saturating_mul(q128);
                            }
                        }
                    }
                    req_lp <= max_s_pow
                })
                .collect();
            if unpacked.is_empty() {
                ctx.pruned += 1;
                continue;
            }
            let mut subsets1 = Vec::new();
            choose_lp_subsets(&mults1, t, m, true, &mut subsets1);
            for mut sub1 in subsets1 {
                sub1.push(m);
                let mut lp_sp_d = m_sp_vp.clone();
                for &v in &sub1[..t] {
                    let s = v / p1;
                    for (pi, &sp) in small_primes.iter().enumerate() {
                        if sp > s {
                            break;
                        }
                        if s % sp == 0 {
                            lp_sp_d[pi] += v_p_u64(s, sp);
                        }
                    }
                }
                for (sc_tup, sc_d) in &unpacked {
                    for pi in 0..n_sp {
                        sp_d[pi] = lp_sp_d[pi] + sc_d[pi];
                    }
                    ctx.check_full_6set(&sub1, sc_tup, &sp_d, (p1, (t + 1) as u8), (0, 0));
                    if ctx.failed {
                        return Err(format!("Counterexample found at M={}", m));
                    }
                }
            }
        }
        // Subcase A2: pattern `[3, 3]` (`2` additional multiples of `p1`, plus `3` multiples of `p2 != p1`):
        let mut subsets1_2 = Vec::new();
        choose_lp_subsets(&mults1, 2, m, true, &mut subsets1_2);
        if !subsets1_2.is_empty() {
            for &p2 in &large_primes {
                if p2 == p1 {
                    continue;
                }
                let mults2 = multiples_of_lp(p2);
                if mults2.len() < 3 {
                    continue;
                }
                let mut subsets2_3 = Vec::new();
                choose_lp_subsets(&mults2, 3, m, false, &mut subsets2_3);
                for sub1 in &subsets1_2 {
                    for sub2 in &subsets2_3 {
                        let mut fixed = Vec::with_capacity(6);
                        fixed.extend_from_slice(sub1);
                        fixed.extend_from_slice(sub2);
                        fixed.push(m);
                        sp_d.copy_from_slice(&m_sp_vp);
                        for &v in sub1 {
                            let s = v / p1;
                            for (pi, &sp) in small_primes.iter().enumerate() {
                                if sp > s {
                                    break;
                                }
                                if s % sp == 0 {
                                    sp_d[pi] += v_p_u64(s, sp);
                                }
                            }
                        }
                        for &v in sub2 {
                            let s = v / p2;
                            for (pi, &sp) in small_primes.iter().enumerate() {
                                if sp > s {
                                    break;
                                }
                                if s % sp == 0 {
                                    sp_d[pi] += v_p_u64(s, sp);
                                }
                            }
                        }
                        ctx.check_full_6set(&fixed, &[], &sp_d, (p1, 3), (p2, 3));
                        if ctx.failed {
                            return Err(format!("Counterexample found at M={}", m));
                        }
                    }
                }
            }
        }
    } else {
        // Case B: `a_6 = M` is `sqrt_m`-smooth!
        // Subcase B1: pattern `[]` (all 6 elements are `sqrt_m`-smooth), solved via exact
        // Bucket-by-Largest-Prime `(L(x), x)` descending decomposition on `q >= 11` + `bucket7`:
        if n_sc >= 5 {
            let mut bucket7: Vec<usize> = Vec::new();
            let mut buckets_ge11: Vec<Vec<usize>> = vec![Vec::new(); n_sp];
            for ci in 0..n_sc {
                let off = ci * n_sp;
                let mut hi_pi = None;
                for pi in (4..n_sp).rev() {
                    if sc_vp[off + pi] > 0 {
                        hi_pi = Some(pi);
                        break;
                    }
                }
                if let Some(pi) = hi_pi {
                    buckets_ge11[pi].push(ci);
                } else {
                    bucket7.push(ci);
                }
            }

            // Precompute prefix top-`r` (`r in 1..=5`) sums of `v_{p_pi}` inside each `buckets_ge11[pi]`:
            let mut b_pi_top_sums: Vec<Vec<u8>> = vec![Vec::new(); n_sp];
            for pi in 4..n_sp {
                let b_len = buckets_ge11[pi].len();
                let mut arr = vec![0u8; (b_len + 1) * 6];
                let mut top5 = [0u8; 5];
                for (bi, &ci) in buckets_ge11[pi].iter().enumerate() {
                    let vp = sc_vp[ci * n_sp + pi];
                    for pos in 0..5 {
                        if vp > top5[pos] {
                            for sh in (pos + 1..5).rev() {
                                top5[sh] = top5[sh - 1];
                            }
                            top5[pos] = vp;
                            break;
                        }
                    }
                    let base = (bi + 1) * 6;
                    let mut acc = 0u8;
                    for s in 1..=5 {
                        acc += top5[s - 1];
                        arr[base + s] = acc;
                    }
                }
                b_pi_top_sums[pi] = arr;
            }

            // Precompute prefix top-`r` tail products on `bucket7` (`pi in 0..n_sp.min(4)`):
            let n_b7 = bucket7.len();
            let b7_stride = n_b7 + 1;
            let n_lo = n_sp.min(4);
            let mut b7_top_tail_prod = vec![1u128; n_lo * b7_stride * 6];
            for pi in 0..n_lo {
                let mut top5 = [1u64; 5];
                for (bi, &ci) in bucket7.iter().enumerate() {
                    let tv = sc_tail_val[ci * n_sp + pi];
                    if tv > 1 {
                        for pos in 0..5 {
                            if tv > top5[pos] {
                                for sh in (pos + 1..5).rev() {
                                    top5[sh] = top5[sh - 1];
                                }
                                top5[pos] = tv;
                                break;
                            }
                        }
                    }
                    let base = (pi * b7_stride + (bi + 1)) * 6;
                    let mut acc = 1u128;
                    for s in 1..=5 {
                        acc = acc.saturating_mul(top5[s - 1] as u128);
                        b7_top_tail_prod[base + s] = acc;
                    }
                }
            }

            #[allow(clippy::too_many_arguments)]
            fn dfs_b7<'b>(
                ctx: &mut EvalCtx<'b>,
                rem: usize,
                upper_bi: usize,
                bucket7: &[usize],
                b7_top_tail_prod: &[u128],
                chosen_sc: &mut Vec<u64>,
                sp_d: &mut [u32],
            ) {
                if ctx.failed {
                    return;
                }
                if rem == 0 {
                    ctx.check_full_6set(&[ctx.m], chosen_sc, sp_d, (0, 0), (0, 0));
                    return;
                }
                if upper_bi < rem {
                    return;
                }
                let n_sp = ctx.small_primes.len();
                let n_lo = n_sp.min(4);
                let b7_stride = bucket7.len() + 1;

                // Exact `u128` Heuristic-1 Tail-Product Pruning on `bucket7`:
                // Primes `pi >= 4` (`q >= 11`) have ZERO remaining copies in `bucket7`, so their
                // final `sp_d[pi]` is already exact!
                let mut cur_tail = 1u128;
                let mut can_any_fail = false;
                for pi in (n_lo..n_sp).rev() {
                    let p128 = ctx.small_primes[pi] as u128;
                    for _ in 0..sp_d[pi] {
                        cur_tail = cur_tail.saturating_mul(p128);
                    }
                    if cur_tail >= ctx.t_mp[pi] {
                        can_any_fail = true;
                        break;
                    }
                }
                if !can_any_fail {
                    for pi in (0..n_lo).rev() {
                        let p128 = ctx.small_primes[pi] as u128;
                        for _ in 0..sp_d[pi] {
                            cur_tail = cur_tail.saturating_mul(p128);
                        }
                        let max_tail = cur_tail.saturating_mul(
                            b7_top_tail_prod[(pi * b7_stride + upper_bi) * 6 + rem],
                        );
                        if max_tail >= ctx.t_mp[pi] {
                            can_any_fail = true;
                            break;
                        }
                    }
                }
                if !can_any_fail {
                    ctx.pruned += 1;
                    return;
                }

                // Rank-quota + `min_needed` (exact on `bucket7` since no future buckets remain!):
                let mut min_needed = ctx.a_mins[rem - 1];
                for k in 0..5 {
                    let req_ge = 6 - k;
                    let mut already_ge = 1usize; // `ctx.m >= a_mins[k]`
                    for &x in chosen_sc.iter() {
                        if x >= ctx.a_mins[k] {
                            already_ge += 1;
                        }
                    }
                    if already_ge + rem < req_ge {
                        ctx.pruned += 1;
                        return;
                    }
                    if already_ge < req_ge {
                        let extra_above = req_ge - already_ge - 1;
                        let base_min = ctx.a_mins[k] + (extra_above as u64);
                        if base_min > min_needed {
                            min_needed = base_min;
                        }
                    }
                }
                let start_bi =
                    bucket7[..upper_bi].partition_point(|&ci| ctx.smooth_cands[ci] < min_needed);
                let lo_bi = start_bi.max(rem - 1);
                if lo_bi >= upper_bi {
                    return;
                }

                for bi in (lo_bi..upper_bi).rev() {
                    let ci = bucket7[bi];
                    let val = ctx.smooth_cands[ci];
                    if rem == 1 && n_sp > 3 && sp_d[3] == 1 && val % 7 != 0 {
                        ctx.pruned += 1;
                        continue;
                    }
                    if val * 2 <= ctx.m {
                        let mut mult = val * 2;
                        let mut miss = false;
                        while mult <= ctx.m {
                            if mult != ctx.m && !chosen_sc.contains(&mult) {
                                miss = true;
                                break;
                            }
                            mult += val;
                        }
                        if miss {
                            ctx.pruned += 1;
                            continue;
                        }
                    }
                    let off = ci * n_sp;
                    chosen_sc.push(val);
                    for pi in 0..n_lo {
                        sp_d[pi] += ctx.sc_vp[off + pi] as u32;
                    }
                    dfs_b7(
                        ctx,
                        rem - 1,
                        bi,
                        bucket7,
                        b7_top_tail_prod,
                        chosen_sc,
                        sp_d,
                    );
                    for pi in 0..n_lo {
                        sp_d[pi] -= ctx.sc_vp[off + pi] as u32;
                    }
                    chosen_sc.pop();
                    if ctx.failed {
                        return;
                    }
                }
            }

            #[allow(clippy::too_many_arguments)]
            fn dfs_bucket_b1<'b>(
                ctx: &mut EvalCtx<'b>,
                pi: usize,
                upper_bi: usize,
                rem: usize,
                buckets_ge11: &[Vec<usize>],
                b_pi_top_sums: &[Vec<u8>],
                bucket7: &[usize],
                b7_top_tail_prod: &[u128],
                chosen_sc: &mut Vec<u64>,
                sp_d: &mut [u32],
            ) {
                if ctx.failed {
                    return;
                }
                if rem == 0 {
                    for j in 4..=pi {
                        if sp_d[j] == 1 || sp_d[j] == 2 {
                            ctx.pruned += 1;
                            return;
                        }
                    }
                    ctx.check_full_6set(&[ctx.m], chosen_sc, sp_d, (0, 0), (0, 0));
                    return;
                }
                // Rank-quota check:
                for k in 0..5 {
                    let req_ge = 6 - k;
                    let mut already_ge = 1usize;
                    for &x in chosen_sc.iter() {
                        if x >= ctx.a_mins[k] {
                            already_ge += 1;
                        }
                    }
                    if already_ge + rem < req_ge {
                        ctx.pruned += 1;
                        return;
                    }
                }
                // Exact `u128` Heuristic-1 Tail-Product check (`j > pi` exact, `j <= pi` bounded by `(m-1)^rem`):
                let n_sp_all = ctx.small_primes.len();
                let max_rem_prod = ((ctx.m - 1) as u128).saturating_pow(rem as u32);
                let mut cur_tail = 1u128;
                let mut can_any_fail = false;
                for j in ((pi + 1)..n_sp_all).rev() {
                    let p128 = ctx.small_primes[j] as u128;
                    for _ in 0..sp_d[j] {
                        cur_tail = cur_tail.saturating_mul(p128);
                    }
                    if cur_tail >= ctx.t_mp[j] {
                        can_any_fail = true;
                        break;
                    }
                }
                if !can_any_fail {
                    for j in (0..=pi).rev() {
                        let p128 = ctx.small_primes[j] as u128;
                        for _ in 0..sp_d[j] {
                            cur_tail = cur_tail.saturating_mul(p128);
                        }
                        if cur_tail.saturating_mul(max_rem_prod) >= ctx.t_mp[j] {
                            can_any_fail = true;
                            break;
                        }
                    }
                }
                if !can_any_fail {
                    ctx.pruned += 1;
                    return;
                }

                // Deficit product check across `j in 4..=pi`:
                let mut req_prod = 1u128;
                for j in 4..=pi {
                    let dj = sp_d[j];
                    if dj == 1 || dj == 2 {
                        let p128 = ctx.small_primes[j] as u128;
                        for _ in 0..(3 - dj) {
                            req_prod = req_prod.saturating_mul(p128);
                        }
                    }
                }
                if req_prod > max_rem_prod {
                    ctx.pruned += 1;
                    return;
                }

                // Branch 1: pick one more element from `buckets_ge11[pi][0..upper_bi]`
                let n_sp = ctx.small_primes.len();
                let max_add_pi = b_pi_top_sums[pi][upper_bi * 6 + rem] as u32;
                if upper_bi >= 1 && (sp_d[pi] >= 3 || sp_d[pi] + max_add_pi >= 3) {
                    for bi in (0..upper_bi).rev() {
                        let ci = buckets_ge11[pi][bi];
                        let off = ci * n_sp;
                        let vp_pi = ctx.sc_vp[off + pi] as u32;
                        let nd_pi = sp_d[pi] + vp_pi;
                        if nd_pi < 3 {
                            let rem_add = b_pi_top_sums[pi][bi * 6 + (rem - 1)] as u32;
                            if nd_pi + rem_add < 3 {
                                ctx.pruned += 1;
                                continue;
                            }
                        }
                        let val = ctx.smooth_cands[ci];
                        if val * 2 <= ctx.m {
                            let mut mult = val * 2;
                            let mut miss = false;
                            while mult <= ctx.m {
                                if mult != ctx.m && !chosen_sc.contains(&mult) {
                                    miss = true;
                                    break;
                                }
                                mult += val;
                            }
                            if miss {
                                ctx.pruned += 1;
                                continue;
                            }
                        }
                        chosen_sc.push(val);
                        for j in 0..=pi {
                            sp_d[j] += ctx.sc_vp[off + j] as u32;
                        }
                        dfs_bucket_b1(
                            ctx,
                            pi,
                            bi,
                            rem - 1,
                            buckets_ge11,
                            b_pi_top_sums,
                            bucket7,
                            b7_top_tail_prod,
                            chosen_sc,
                            sp_d,
                        );
                        for j in 0..=pi {
                            sp_d[j] -= ctx.sc_vp[off + j] as u32;
                        }
                        chosen_sc.pop();
                        if ctx.failed {
                            return;
                        }
                    }
                }

                // Branch 2: finalize bucket `pi` (`sp_d[pi]` must be `0` or `>= 3`) and move down:
                if sp_d[pi] == 0 || sp_d[pi] >= 3 {
                    if pi == 4 {
                        dfs_b7(
                            ctx,
                            rem,
                            bucket7.len(),
                            bucket7,
                            b7_top_tail_prod,
                            chosen_sc,
                            sp_d,
                        );
                    } else {
                        dfs_bucket_b1(
                            ctx,
                            pi - 1,
                            buckets_ge11[pi - 1].len(),
                            rem,
                            buckets_ge11,
                            b_pi_top_sums,
                            bucket7,
                            b7_top_tail_prod,
                            chosen_sc,
                            sp_d,
                        );
                    }
                }
            }

            sp_d.copy_from_slice(&m_sp_vp);
            if n_sp <= 4 {
                dfs_b7(
                    &mut ctx,
                    5,
                    bucket7.len(),
                    &bucket7,
                    &b7_top_tail_prod,
                    &mut chosen_sc,
                    &mut sp_d,
                );
            } else {
                dfs_bucket_b1(
                    &mut ctx,
                    n_sp - 1,
                    buckets_ge11[n_sp - 1].len(),
                    5,
                    &buckets_ge11,
                    &b_pi_top_sums,
                    &bucket7,
                    &b7_top_tail_prod,
                    &mut chosen_sc,
                    &mut sp_d,
                );
            }
            if ctx.failed {
                return Err(format!("Counterexample found at M={}", m));
            }
        }
        // Subcase B2: patterns `[3], [4], [5]` (one large prime `p1`, `t in 3..=5` multiples of `p1`):
        for t in [5usize, 4, 3] {
            let rem_sc = 5 - t;
            if n_sc < rem_sc || large_primes.is_empty() {
                continue;
            }
            let tail_caps_slice: &[u64] = match t {
                5 => &[m / 7, m / 8],
                4 => &[m / 6, m / 7, m / 8],
                _ => &[m / 5, m / 6, m / 7, m / 8],
            };
            let unpacked = collect_unpacked_smooth(rem_sc, true, tail_caps_slice);
            if unpacked.is_empty() {
                ctx.pruned += 1;
                continue;
            }
            for &p1 in &large_primes {
                let max_s_p1 = (m - 1) / p1;
                if (max_s_p1 as usize) < t {
                    break;
                }
                let mut lp_max_add = vec![0u32; n_sp];
                for (pi, &q) in small_primes.iter().enumerate().skip(3) {
                    if q > max_s_p1 {
                        break;
                    }
                    let mut qk = q;
                    let mut acc = 0u32;
                    while qk <= max_s_p1 {
                        acc += ((max_s_p1 / qk) as usize).min(t) as u32;
                        qk = qk.saturating_mul(q);
                    }
                    lp_max_add[pi] = acc;
                }
                let mut ff_prod = 1u128;
                for j in 0..(t as u64) {
                    ff_prod = ff_prod.saturating_mul((max_s_p1 - j) as u128);
                }
                let surv_indices: Vec<usize> = (0..unpacked.len())
                    .filter(|&idx| {
                        let sc_d = &unpacked[idx].1;
                        if n_sp > 3 && sc_d[3] == 1 && lp_max_add[3] == 0 {
                            return false;
                        }
                        let mut req_lp = 1u128;
                        for pi in 4..n_sp {
                            let d0 = sc_d[pi];
                            if d0 == 1 || d0 == 2 {
                                let need = 3 - d0;
                                if lp_max_add[pi] < need {
                                    return false;
                                }
                                let q128 = small_primes[pi] as u128;
                                for _ in 0..need {
                                    req_lp = req_lp.saturating_mul(q128);
                                }
                            }
                        }
                        req_lp <= ff_prod
                    })
                    .collect();
                if surv_indices.is_empty() {
                    ctx.pruned += 1;
                    continue;
                }
                let mults1 = multiples_of_lp(p1);
                if mults1.len() < t {
                    continue;
                }
                let mut subsets1 = Vec::new();
                choose_lp_subsets(&mults1, t, m, false, &mut subsets1);
                for mut sub1 in subsets1 {
                    sub1.push(m);
                    let mut lp_sp_d = m_sp_vp.clone();
                    for &v in &sub1[..t] {
                        let s = v / p1;
                        for (pi, &sp) in small_primes.iter().enumerate() {
                            if sp > s {
                                break;
                            }
                            if s % sp == 0 {
                                lp_sp_d[pi] += v_p_u64(s, sp);
                            }
                        }
                    }
                    for &idx in &surv_indices {
                        let (ref sc_tup, ref sc_d) = unpacked[idx];
                        // Note: `sc_d` in Case B included `m_sp_vp` once (`include_m_smooth = true`),
                        // so subtract `m_sp_vp` before adding `lp_sp_d` (which also starts at `m_sp_vp`)!
                        for pi in 0..n_sp {
                            sp_d[pi] = lp_sp_d[pi] + sc_d[pi] - m_sp_vp[pi];
                        }
                        ctx.check_full_6set(&sub1, sc_tup, &sp_d, (p1, t as u8), (0, 0));
                        if ctx.failed {
                            return Err(format!("Counterexample found at M={}", m));
                        }
                    }
                }
            }
        }
    }

    Ok((ctx.leaves_crt, ctx.pruned, 8))
}

fn certify_single_m_fast(m: u64, all_primes: &[u64]) -> Result<(u64, u64, u64), String> {
    if m < 7 {
        return Ok((0, 0, 0));
    }
    if m >= 64 {
        return certify_single_m_ge64_decomposed(m, all_primes);
    }
    let a5_min = min_subinterval_len(m, 5) + 1;
    let a4_min = min_subinterval_len(m, 4) + 1;
    let a3_min = min_subinterval_len(m, 3) + 1;
    let a2_min = min_subinterval_len(m, 2) + 1;
    let a1_min = (m / 8).max(min_subinterval_len(m, 1)) + 1;
    let a_mins = [a1_min.max(2), a2_min, a3_min, a4_min, a5_min];
    if a_mins[4] >= m {
        return Ok((0, 0, 0));
    }

    let sqrt_m = isqrt_u64(m);
    let min_lp_mult: usize = if m >= 64 {
        3
    } else if m >= 49 {
        2
    } else {
        0
    };
    let max_lp = if m >= 64 { m / 3 } else { m / 2 };

    let mut is_adm = vec![true; (m + 1) as usize];
    is_adm[0] = false;
    is_adm[1] = false;
    let mut active_primes = Vec::new();
    for &p in all_primes {
        if p > m {
            break;
        }
        let forbid = if p > m / 2 {
            true
        } else if min_lp_mult >= 3 && p > sqrt_m && p > max_lp {
            true
        } else {
            false
        };
        if forbid {
            let mut mult = p;
            while mult <= m {
                is_adm[mult as usize] = false;
                mult += p;
            }
        } else {
            active_primes.push(p);
        }
    }
    if !is_adm[m as usize] {
        return Ok((0, 0, 0));
    }

    let mut cands = Vec::new();
    for v in a_mins[0]..=m {
        if is_adm[v as usize] {
            cands.push(v);
        }
    }
    if cands.len() < 6 || *cands.last().unwrap() != m {
        return Ok((0, 0, 0));
    }

    let nc = cands.len();
    let np = active_primes.len();
    let mut cand_vp = vec![0u8; nc * np];
    let mut cand_lp: Vec<Option<u16>> = vec![None; nc];
    for (ci, &v) in cands.iter().enumerate() {
        for (pi, &p) in active_primes.iter().enumerate() {
            if p > v {
                break;
            }
            if v % p == 0 {
                cand_vp[ci * np + pi] = v_p_u64(v, p) as u8;
                if p > sqrt_m {
                    cand_lp[ci] = Some(pi as u16);
                }
            }
        }
    }

    let stride = nc + 1;
    let mut lp_avail = vec![0u16; np * stride];
    let mut top_sums = vec![0u8; np * stride * 6];
    for pi in 0..np {
        let is_lp = active_primes[pi] > sqrt_m;
        let mut avail = 0u16;
        let mut top5 = [0u8; 5];
        for ci in 0..nc {
            let vp = cand_vp[ci * np + pi];
            if vp > 0 {
                avail += 1;
                for pos in 0..5 {
                    if vp > top5[pos] {
                        for sh in (pos + 1..5).rev() {
                            top5[sh] = top5[sh - 1];
                        }
                        top5[pos] = vp;
                        break;
                    }
                }
            }
            let base = (pi * stride + (ci + 1)) * 6;
            let mut acc = 0u8;
            for s in 1..=5 {
                acc += top5[s - 1];
                top_sums[base + s] = acc;
            }
            if is_lp {
                lp_avail[pi * stride + (ci + 1)] = avail;
            }
        }
    }

    let m_ci = nc - 1;
    let mut cur_d = vec![0u32; np];
    for pi in 0..np {
        cur_d[pi] = cand_vp[m_ci * np + pi] as u32;
    }
    let mut lp_touch: Vec<u16> = Vec::with_capacity(6);
    if let Some(lp) = cand_lp[m_ci] {
        if min_lp_mult >= 2
            && (cur_d[lp as usize] as usize) + (lp_avail[(lp as usize) * stride + m_ci] as usize)
                < min_lp_mult
        {
            return Ok((0, 1, 0));
        }
        lp_touch.push(lp);
    }

    // Root envelope check (rem_slots = 5) via 8-slot packing:
    {
        let mut root_factors = Vec::new();
        for pi in (0..np).rev() {
            let d = cur_d[pi] + (top_sums[(pi * stride + m_ci) * 6 + 5] as u32);
            for _ in 0..d {
                root_factors.push(active_primes[pi]);
            }
        }
        if can_pack_factors_8_slots(&root_factors, m, false) {
            return Ok((0, 1, 8));
        }
    }

    let mut m_branches: Vec<Option<Vec<Vec<u8>>>> = vec![None; np];
    let mut m_wp: Vec<[u8; 72]> = vec![[0u8; 72]; np];
    // Lazily populated per prime `pi` on first CRT leaf at this `M`!

    struct State<'a> {
        m: u64,
        min_lp_mult: usize,
        a_mins: [u64; 5],
        primes: &'a [u64],
        cands: &'a [u64],
        cand_vp: &'a [u8],
        cand_lp: &'a [Option<u16>],
        top_sums: &'a [u8],
        lp_avail: &'a [u16],
        m_branches: &'a mut [Option<Vec<Vec<u8>>>],
        m_wp: &'a mut [[u8; 72]],
        real_branches_ready: Vec<Vec<Vec<u8>>>,
        pair_cache: std::collections::HashMap<(u16, u8, u16, u8), u8>,
        cur_a: [u64; 6],
        cur_d: Vec<u32>,
        lp_touch: Vec<u16>,
        factors_buf: Vec<u64>,
        crt_cache: std::collections::HashSet<Vec<u8>>,
        leaves_crt: u64,
        pruned: u64,
        failed: bool,
    }

    impl<'a> State<'a> {
        fn ensure_crt_tables(&mut self) {
            if !self.real_branches_ready.is_empty() {
                return;
            }
            let np = self.primes.len();
            self.real_branches_ready.reserve(np);
            for pi in 0..np {
                let (br, wp) = precompute_prime_branches_for_m(self.primes[pi], self.m);
                self.real_branches_ready.push(br);
                self.m_wp[pi] = wp;
            }
        }

        fn lp_ok(&self, rem_slots: usize, prefix_len: usize) -> bool {
            if self.min_lp_mult < 2 {
                return true;
            }
            let stride = self.cands.len() + 1;
            let mut deficit = 0usize;
            let mut seen = [u16::MAX; 6];
            let mut slen = 0usize;
            for &lp in &self.lp_touch {
                if seen[..slen].contains(&lp) {
                    continue;
                }
                seen[slen] = lp;
                slen += 1;
                let d = self.cur_d[lp as usize] as usize;
                if d < self.min_lp_mult {
                    let need = self.min_lp_mult - d;
                    let av = self.lp_avail[(lp as usize) * stride + prefix_len] as usize;
                    if av < need {
                        return false;
                    }
                    deficit += need;
                    if deficit > rem_slots {
                        return false;
                    }
                }
            }
            true
        }

        fn envelope_packs(&mut self, rem_slots: usize, prefix_len: usize) -> bool {
            let stride = self.cands.len() + 1;
            let np = self.primes.len();
            self.factors_buf.clear();
            for pi in (0..np).rev() {
                let d = self.cur_d[pi]
                    + (self.top_sums[(pi * stride + prefix_len) * 6 + rem_slots] as u32);
                for _ in 0..d {
                    self.factors_buf.push(self.primes[pi]);
                }
            }
            can_pack_factors_8_slots(&self.factors_buf, self.m, false)
        }

        fn dfs(&mut self, slot_idx: usize, upper_ci: usize) {
            if self.failed || upper_ci <= slot_idx {
                return;
            }
            let min_v = self.a_mins[slot_idx];
            let start_ci = self.cands[..upper_ci].partition_point(|&v| v < min_v);
            let lo_ci = start_ci.max(slot_idx);
            if lo_ci >= upper_ci {
                return;
            }
            let np = self.primes.len();

            for ci in (lo_ci..upper_ci).rev() {
                let val = self.cands[ci];
                if val * 2 <= self.m {
                    let mut mult = val * 2;
                    let mut miss = false;
                    while mult <= self.m {
                        if !self.cur_a[(slot_idx + 1)..6].contains(&mult) {
                            miss = true;
                            break;
                        }
                        mult += val;
                    }
                    if miss {
                        self.pruned += 1;
                        continue;
                    }
                }
                self.cur_a[slot_idx] = val;
                let off = ci * np;
                for pi in 0..np {
                    self.cur_d[pi] += self.cand_vp[off + pi] as u32;
                }
                let pushed = if let Some(lp) = self.cand_lp[ci] {
                    self.lp_touch.push(lp);
                    true
                } else {
                    false
                };

                if self.lp_ok(slot_idx, ci) {
                    if slot_idx == 0 {
                        if is_gcd_connected(&self.cur_a) {
                            self.factors_buf.clear();
                            for pi in (0..np).rev() {
                                for _ in 0..self.cur_d[pi] {
                                    self.factors_buf.push(self.primes[pi]);
                                }
                            }
                            if can_pack_factors_8_slots(&self.factors_buf, self.m, true) {
                                self.pruned += 1;
                            } else {
                                let key: Vec<u8> =
                                    self.cur_d.iter().map(|&d| d.min(255) as u8).collect();
                                if self.crt_cache.contains(&key) {
                                    self.pruned += 1;
                                } else {
                                    self.leaves_crt += 1;
                                    self.ensure_crt_tables();
                                                            let ok = check_crt_with_precomputed(
                                        &self.cur_d,
                                        self.primes,
                                        self.m,
                                        &self.real_branches_ready,
                                        self.m_wp,
                                        &mut self.pair_cache,
                                    ) || check_set_universal_tau_le_8(
                                        &self.cur_a,
                                        self.m,
                                        self.primes,
                                    );
                                    if !ok {
                                        self.failed = true;
                                    } else {
                                        self.crt_cache.insert(key);
                                    }
                                }
                            }
                        } else {
                            self.pruned += 1;
                        }
                    } else if slot_idx <= 2 && self.envelope_packs(slot_idx, ci) {
                        self.pruned += 1;
                    } else {
                        self.dfs(slot_idx - 1, ci);
                    }
                } else {
                    self.pruned += 1;
                }

                if pushed {
                    self.lp_touch.pop();
                }
                for pi in 0..np {
                    self.cur_d[pi] -= self.cand_vp[off + pi] as u32;
                }
                if self.failed {
                    return;
                }
            }
        }
    }

    let _ = &mut m_branches;
    let mut cur_a = [0u64; 6];
    cur_a[5] = m;
    let mut st = State {
        m,
        min_lp_mult,
        a_mins,
        primes: &active_primes,
        cands: &cands,
        cand_vp: &cand_vp,
        cand_lp: &cand_lp,
        top_sums: &top_sums,
        lp_avail: &lp_avail,
        m_branches: &mut m_branches,
        m_wp: &mut m_wp,
        real_branches_ready: Vec::new(),
        pair_cache: std::collections::HashMap::new(),
        cur_a,
        cur_d,
        lp_touch,
        factors_buf: Vec::with_capacity(32),
        crt_cache: std::collections::HashSet::new(),
        leaves_crt: 0,
        pruned: 0,
        failed: false,
    };
    st.dfs(4, m_ci);
    if st.failed {
        return Err(format!("Counterexample to g(6) <= 8 found at M={}", m));
    }
    Ok((st.leaves_crt, st.pruned, 8))
}

fn prove_range_multicore(
    m_start: u64,
    m_end: u64,
    threads: usize,
    cert_out: Option<&str>,
) -> Result<(u64, u64), String> {
    use std::io::Write;
    let all_primes = Arc::new(primes_up_to(m_end));
    let mut already_done = std::collections::BTreeMap::new();
    if let Some(path) = cert_out {
        if let Ok(existing) = std::fs::read_to_string(path) {
            for line in existing.lines() {
                if !line.ends_with("status=OK") {
                    continue;
                }
                let mut m_v = None;
                let mut l_v = 0u64;
                let mut p_v = 0u64;
                let mut t_v = 8u64;
                for part in line.split('\t') {
                    if let Some(s) = part.strip_prefix("M=") {
                        m_v = s.parse::<u64>().ok();
                    } else if let Some(s) = part.strip_prefix("leaves=") {
                        l_v = s.parse::<u64>().unwrap_or(0);
                    } else if let Some(s) = part.strip_prefix("pruned=") {
                        p_v = s.parse::<u64>().unwrap_or(0);
                    } else if let Some(s) = part.strip_prefix("max_tau=") {
                        t_v = s.parse::<u64>().unwrap_or(8);
                    }
                }
                if let Some(m) = m_v {
                    if t_v <= 8 {
                        already_done.insert(m, (m, l_v, p_v, t_v));
                    }
                }
            }
        }
    }

    let mut todo: Vec<u64> = (m_start..=m_end)
        .filter(|m| !already_done.contains_key(m))
        .collect();
    // Sort descending so largest M values start immediately without tail stragglers:
    todo.sort_unstable_by(|a, b| b.cmp(a));
    let total_range = m_end.saturating_sub(m_start) + 1;
    let init_done = (m_start..=m_end)
        .filter(|m| already_done.contains_key(m))
        .count();
    let todo = Arc::new(todo);

    let append_file = if let Some(path) = cert_out {
        let f = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .map_err(|e| format!("Open {} failed: {}", path, e))?;
        Some(Arc::new(std::sync::Mutex::new(f)))
    } else {
        None
    };

    let next_idx = Arc::new(AtomicUsize::new(0));
    let done_cnt = Arc::new(AtomicUsize::new(init_done));
    let err_slot: Arc<std::sync::Mutex<Option<String>>> = Arc::new(std::sync::Mutex::new(None));
    let recs: Arc<std::sync::Mutex<Vec<(u64, u64, u64, u64)>>> =
        Arc::new(std::sync::Mutex::new(already_done.into_values().collect()));

    let n_threads = threads.max(1);
    let mut handles = Vec::with_capacity(n_threads);
    for _ in 0..n_threads {
        let primes_c = Arc::clone(&all_primes);
        let todo_c = Arc::clone(&todo);
        let next_c = Arc::clone(&next_idx);
        let done_c = Arc::clone(&done_cnt);
        let err_c = Arc::clone(&err_slot);
        let recs_c = Arc::clone(&recs);
        let app_c = append_file.clone();
        handles.push(thread::spawn(move || {
            let mut local = Vec::new();
            loop {
                if err_c.lock().unwrap().is_some() {
                    break;
                }
                let idx = next_c.fetch_add(1, Ordering::Relaxed);
                if idx >= todo_c.len() {
                    break;
                }
                let m = todo_c[idx];
                match certify_single_m_fast(m, &primes_c) {
                    Ok((leaves, pruned, max_tau)) => {
                        if let Some(ref f_mtx) = app_c {
                            if let Ok(mut f) = f_mtx.lock() {
                                let _ = writeln!(
                                    f,
                                    "M={}\tleaves={}\tpruned={}\tmax_tau={}\tstatus=OK",
                                    m, leaves, pruned, max_tau
                                );
                                let _ = f.flush();
                            }
                        }
                        local.push((m, leaves, pruned, max_tau));
                        let d = done_c.fetch_add(1, Ordering::Relaxed) + 1;
                        if d % 25 == 0 || d as u64 == total_range {
                            eprintln!(
                                "[prove-g6] certified {}/{} (latest M={}, crt_leaves={}, pruned={})",
                                d, total_range, m, leaves, pruned
                            );
                        }
                    }
                    Err(e) => {
                        *err_c.lock().unwrap() = Some(e);
                        break;
                    }
                }
            }
            recs_c.lock().unwrap().extend(local);
        }));
    }
    for h in handles {
        h.join().map_err(|_| "Worker thread panicked".to_string())?;
    }
    if let Some(e) = err_slot.lock().unwrap().clone() {
        return Err(e);
    }
    let mut list = recs.lock().unwrap().clone();
    list.sort_unstable_by_key(|r| r.0);
    list.dedup_by_key(|r| r.0);
    let total_crt_leaves: u64 = list.iter().map(|r| r.1).sum();
    let total_pruned: u64 = list.iter().map(|r| r.2).sum();
    if let Some(path) = cert_out {
        let mut buf = String::with_capacity(list.len() * 48);
        for (m, leaves, pruned, max_tau) in &list {
            buf.push_str(&format!(
                "M={}\tleaves={}\tpruned={}\tmax_tau={}\tstatus=OK\n",
                m, leaves, pruned, max_tau
            ));
        }
        std::fs::write(path, buf).map_err(|e| format!("Write {} failed: {}", path, e))?;
    }
    Ok((total_crt_leaves, total_pruned))
}

fn verify_part3_cert(path: &str) -> Result<(u64, usize, u64, u64), String> {
    let file = File::open(path).map_err(|e| format!("Failed to open {}: {}", path, e))?;
    let reader = BufReader::new(file);
    let mut expected_m = 7u64;
    let mut count = 0usize;
    let mut max_m = 0u64;
    let mut total_leaves = 0u64;
    let mut total_pruned = 0u64;

    for (line_no, line_res) in reader.lines().enumerate() {
        let line = line_res.map_err(|e| format!("Read error at line {}: {}", line_no + 1, e))?;
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let mut m_val = None;
        let mut leaves_val = None;
        let mut pruned_val = None;
        let mut max_tau = None;
        let mut status = None;
        for part in trimmed.split('\t') {
            if let Some(v) = part.strip_prefix("M=") {
                m_val = v.parse::<u64>().ok();
            } else if let Some(v) = part.strip_prefix("leaves=") {
                leaves_val = v.parse::<u64>().ok();
            } else if let Some(v) = part.strip_prefix("pruned=") {
                pruned_val = v.parse::<u64>().ok();
            } else if let Some(v) = part.strip_prefix("max_tau=") {
                max_tau = v.parse::<u64>().ok();
            } else if let Some(v) = part.strip_prefix("status=") {
                status = Some(v.to_string());
            }
        }
        let m = m_val.ok_or_else(|| format!("Missing M= on line {}", line_no + 1))?;
        let lv = leaves_val.ok_or_else(|| format!("Missing leaves= on line {}", line_no + 1))?;
        let pr = pruned_val.ok_or_else(|| format!("Missing pruned= on line {}", line_no + 1))?;
        let tau = max_tau.ok_or_else(|| format!("Missing max_tau= on line {}", line_no + 1))?;
        let st = status.ok_or_else(|| format!("Missing status= on line {}", line_no + 1))?;

        if m != expected_m {
            return Err(format!(
                "Non-contiguous M on line {}: expected {}, got {}",
                line_no + 1,
                expected_m,
                m
            ));
        }
        if st != "OK" {
            return Err(format!("Bad status on M={}: {}", m, st));
        }
        if tau > 8 {
            return Err(format!("max_tau > 8 on M={}: {}", m, tau));
        }
        if m >= 81 && lv != 0 {
            return Err(format!("Expected leaves=0 on M={}, got {}", m, lv));
        }
        expected_m += 1;
        max_m = m;
        count += 1;
        total_leaves += lv;
        total_pruned += pr;
    }

    if count == 0 {
        return Err("Certificate file contained no records".to_string());
    }
    if max_m < 3_481 {
        return Err(format!("Truncated certificate: max_m={} < 3481", max_m));
    }
    Ok((max_m, count, total_leaves, total_pruned))
}

fn verify_part1b_g8_lower_bound() -> Result<u128, String> {
    // Asymmetric K_{2,4}: {41, 43, 47, 53} x {59, 61}, M = 53 * 61 = 3,233.
    const A8: [u64; 8] = [2419, 2501, 2537, 2623, 2773, 2867, 3127, 3233];
    const PS: [u64; 6] = [41, 43, 47, 53, 59, 61];
    const M8: u64 = 3233;
    const CENTER: u64 = 1617;

    // Solve CRT for `y = x_g8 + CENTER` modulo `p^2` (`p in PS`):
    // - For `p in {41, 43, 47, 53}`: `y === p (mod p^2)` (`v_p(y) = 1`);
    // - For `p in {59, 61}`: `y === ((p - 1) / 2) * p (mod p^2)` (`1711` and `1830`, both `> 1616`,
    //   and `p^2 - y_mod = 1770, 1891 > 1616`, so ZERO multiples of `59^2` or `61^2` lie in `I`!).
    let mut m_acc = 1u128;
    let mut r_acc = 0u128;
    for &p in &PS {
        let p2 = (p * p) as u128;
        let target = if p >= 59 {
            (((p - 1) / 2) * p) as u128
        } else {
            p as u128
        };
        while r_acc % p2 != target {
            r_acc += m_acc;
        }
        m_acc *= p2;
    }
    let x_g8 = r_acc - (CENTER as u128);

    for j in 1..=M8 {
        let val = x_g8 + (j as u128);
        if j == CENTER {
            for &p in &PS {
                if v_p_u128(val, p) != 1 {
                    return Err(format!("Expected v_{}(center)=1", p));
                }
            }
        } else {
            let distinct_p = PS.iter().filter(|&&p| val % (p as u128) == 0).count();
            if distinct_p > 1 {
                return Err("Non-center element divisible by >= 2 primes in PS".to_string());
            }
            if v_p_u128(val, 59) > 1 || v_p_u128(val, 61) > 1 {
                return Err("59^2 or 61^2 landed in I".to_string());
            }
        }
    }

    // Also verify explicit 9-element cover for A7 and 11-element cover for A8 (and no <=8 / <=10 covers):
    let mut offsets11: Vec<u64> = vec![
        CENTER,
        CENTER - 41,
        CENTER - 43,
        CENTER - 47,
        CENTER - 53,
        CENTER - 118,
        CENTER - 59,
        CENTER + 59,
        CENTER - 122,
        CENTER - 61,
        CENTER + 61,
    ];
    offsets11.sort_unstable();
    let mut offsets9: Vec<u64> = vec![
        CENTER,
        CENTER - 43,
        CENTER - 47,
        CENTER - 53,
        CENTER - 118,
        CENTER - 59,
        CENTER - 122,
        CENTER - 61,
        CENTER + 61,
    ];
    offsets9.sort_unstable();
    verify_witness_generic(&A8[1..], M8, x_g8, &offsets9, 8)?;
    verify_witness_generic(&A8, M8, x_g8, &offsets11, 10)?;
    Ok(x_g8)
}

fn verify_part4_analytic_bridge() -> Result<usize, String> {
    // 0. Verify closed-form thresholds for n=3 (M>=184), n=4 (M>=9702), and Case 3b T_6(360030, q):
    let m3 = 184u128;
    for &(p, div) in &[(2u128, 1u128), (3, 6)] {
        let mut tv = p;
        for k in 1..=4u128 {
            tv *= ((m3 / k) / p) + 1;
        }
        if tv <= m3.pow(3) / div {
            return Err(format!("n=3 threshold failed at p={}", p));
        }
    }
    let m4 = 9_702u128;
    for &(p, div) in &[(2u128, 1u128), (3, 1), (5, 24)] {
        let mut tv = p;
        for k in 1..=5u128 {
            tv *= ((m4 / k) / p) + 1;
        }
        if tv <= m4.pow(4) / div {
            return Err(format!("n=4 threshold failed at p={}", p));
        }
    }
    let m_c3b = 360_065u128;
    for q in [2u128, 3, 5, 7, 11, 13, 17, 19, 23] {
        let mut t6 = q;
        for k in 3..=8u128 {
            t6 *= (((m_c3b / k) / q) + 1).max(q);
        }
        if t6 <= m_c3b.pow(4) {
            return Err(format!("Case 3b T_6(360065, {}) <= M^4", q));
        }
    }

    // 1. Verify closed-form Heuristic-1 `T(56125, p)` thresholds for `{2,3,5,7}`-smooth sets (`M >= 56,125`):
    let m_sm7 = 56_125u64;
    let caps8 = [
        m_sm7,
        m_sm7 / 2,
        m_sm7 / 3,
        m_sm7 / 4,
        m_sm7 / 5,
        m_sm7 / 6,
        m_sm7 / 7,
        m_sm7 / 8,
    ];
    let m6 = (m_sm7 as u128).pow(6);
    for &p in &[2u64, 3, 5, 7] {
        let mut t_val = p as u128;
        for &ck in &caps8 {
            t_val = t_val.saturating_mul(((ck / p) + 1) as u128);
        }
        let target = if p <= 5 { m6 } else { m6 / 720 };
        if t_val <= target {
            return Err(format!("Analytic threshold T(56125, {}) failed", p));
        }
    }

    // 2. Verify all `{2,3,5,7}`-smooth `M in [3482, 56125]` (`354` values) via exact `t_mp` tail pruning:
    let mut sm7 = vec![1u64];
    let (mut i2, mut i3, mut i5, mut i7) = (0usize, 0, 0, 0);
    while *sm7.last().unwrap() <= 576_240 {
        let (n2, n3, n5, n7) = (sm7[i2] * 2, sm7[i3] * 3, sm7[i5] * 5, sm7[i7] * 7);
        let nx = n2.min(n3).min(n5).min(n7);
        sm7.push(nx);
        if nx == n2 {
            i2 += 1;
        }
        if nx == n3 {
            i3 += 1;
        }
        if nx == n5 {
            i5 += 1;
        }
        if nx == n7 {
            i7 += 1;
        }
    }

    let primes4 = [2u64, 3, 5, 7];
    let mut sm_checked = 0usize;
    for &m in sm7.iter().filter(|&&x| x >= 3_482 && x <= 56_125) {
        sm_checked += 1;
        let lo = m / 8 + 1;
        let win: Vec<u64> = sm7.iter().copied().filter(|&x| x >= lo && x < m).collect();
        if win.len() < 5 {
            continue;
        }
        let c8 = [m, m / 2, m / 3, m / 4, m / 5, m / 6, m / 7, m / 8];
        let mut t_mp4 = [0u128; 4];
        for (pi, &p) in primes4.iter().enumerate() {
            let mut pr = p as u128;
            for &ck in &c8 {
                pr = pr.saturating_mul(((ck / p) + 1).max(p) as u128);
            }
            t_mp4[pi] = pr;
        }
        let strip = |mut v: u64, pi: usize| -> u64 {
            for &q in &primes4[..pi] {
                while v % q == 0 {
                    v /= q;
                }
            }
            v
        };
        let win_tails: Vec<[u64; 4]> = win
            .iter()
            .map(|&x| [x, strip(x, 1), strip(x, 2), strip(x, 3)])
            .collect();
        let m_tails = [m, strip(m, 1), strip(m, 2), strip(m, 3)];
        let w_len = win.len();
        let w_stride = w_len + 1;
        let mut top_prod = vec![1u128; 4 * w_stride * 6];
        for pi in 0..4 {
            let mut top5 = [1u64; 5];
            for (idx, wt) in win_tails.iter().enumerate() {
                let tv = wt[pi];
                if tv > 1 {
                    for pos in 0..5 {
                        if tv > top5[pos] {
                            for sh in (pos + 1..5).rev() {
                                top5[sh] = top5[sh - 1];
                            }
                            top5[pos] = tv;
                            break;
                        }
                    }
                }
                let base = (pi * w_stride + (idx + 1)) * 6;
                let mut acc = 1u128;
                for s in 1..=5 {
                    acc = acc.saturating_mul(top5[s - 1] as u128);
                    top_prod[base + s] = acc;
                }
            }
        }

        #[allow(clippy::too_many_arguments)]
        fn check_sm7_win(
            rem: usize,
            upper: usize,
            m: u64,
            win: &[u64],
            win_tails: &[[u64; 4]],
            top_prod: &[u128],
            t_mp4: &[u128; 4],
            cur_tails: [u128; 4],
            chosen: &mut Vec<u64>,
            fac: &mut Vec<u64>,
        ) -> Result<(), String> {
            if rem == 0 {
                let mut a = [chosen[4], chosen[3], chosen[2], chosen[1], chosen[0], m];
                a.sort_unstable();
                if !is_gcd_connected(&a) {
                    return Ok(());
                }
                fac.clear();
                for &q in &[7u64, 5, 3, 2] {
                    let d: u32 = a.iter().map(|&x| v_p_u64(x, q)).sum();
                    if q == 7 && d == 1 {
                        return Ok(());
                    }
                    for _ in 0..d {
                        fac.push(q);
                    }
                }
                if can_pack_factors_8_slots(fac, m, true) {
                    return Ok(());
                }
                let mut active_pd = Vec::new();
                for &q in &[2u64, 3, 5, 7] {
                    let d: u32 = a.iter().map(|&x| v_p_u64(x, q)).sum();
                    if d > 0 {
                        active_pd.push((q, d));
                    }
                }
                if can_hybrid_coprime_pack_le_8(&active_pd, m) {
                    return Ok(());
                }
                if !check_set_universal_tau_le_8(&a, m, &[2, 3, 5, 7]) {
                    return Err(format!("Counterexample on {{2,3,5,7}}-smooth {:?}", a));
                }
                return Ok(());
            }
            if upper < rem {
                return Ok(());
            }
            let w_stride = win.len() + 1;
            let mut any_fail = false;
            for pi in 0..4 {
                let max_t = cur_tails[pi]
                    .saturating_mul(top_prod[(pi * w_stride + upper) * 6 + rem]);
                if max_t >= t_mp4[pi] {
                    any_fail = true;
                    break;
                }
            }
            if !any_fail {
                return Ok(());
            }
            for idx in ((rem - 1)..upper).rev() {
                let val = win[idx];
                if val * 2 <= m {
                    let mut mult = val * 2;
                    let mut miss = false;
                    while mult <= m {
                        if mult != m && !chosen.contains(&mult) {
                            miss = true;
                            break;
                        }
                        mult += val;
                    }
                    if miss {
                        continue;
                    }
                }
                chosen.push(val);
                let wt = win_tails[idx];
                let nxt_tails = [
                    cur_tails[0].saturating_mul(wt[0] as u128),
                    cur_tails[1].saturating_mul(wt[1] as u128),
                    cur_tails[2].saturating_mul(wt[2] as u128),
                    cur_tails[3].saturating_mul(wt[3] as u128),
                ];
                check_sm7_win(
                    rem - 1,
                    idx,
                    m,
                    win,
                    win_tails,
                    top_prod,
                    t_mp4,
                    nxt_tails,
                    chosen,
                    fac,
                )?;
                chosen.pop();
            }
            Ok(())
        }
        let mut ch = Vec::with_capacity(5);
        let mut fb = Vec::with_capacity(64);
        check_sm7_win(
            5,
            w_len,
            m,
            &win,
            &win_tails,
            &top_prod,
            &t_mp4,
            [
                m_tails[0] as u128,
                m_tails[1] as u128,
                m_tails[2] as u128,
                m_tails[3] as u128,
            ],
            &mut ch,
            &mut fb,
        )?;
    }

    // 3. Verify `|S_{11}| = 1`, `d = 5` (`[M/7, M/8]`) at `M = 3,482`, and monotonic `{2,3,5,7}`-smooth
    //    `d = 4` (`[M/6, M/7, M/8]` up to `16,464`) + `d = 3` (`[M/5..M/8]` up to `576,240`) bridges:
    if ((3_482u64 / 49) + 1) * ((3_482u64 / 56) + 1) <= 3_482 {
        return Err("d=5 analytic inequality failed at 3482".to_string());
    }
    let win_d4: Vec<u64> = sm7
        .iter()
        .copied()
        .filter(|&x| x >= 435 && x <= 16_464)
        .collect();
    let mut fac_buf = Vec::with_capacity(32);
    for a_idx in 0..win_d4.len() {
        let x1 = win_d4[a_idx];
        let m_max = (8 * x1 - 1).min(16_464);
        for &x2 in &win_d4[(a_idx + 1)..] {
            if x2 > m_max {
                break;
            }
            let m_min = 3_482u64.max(x2);
            if m_min > m_max {
                continue;
            }
            fac_buf.clear();
            for &p in &[7u64, 5, 3, 2] {
                for _ in 0..(v_p_u64(x1, p) + v_p_u64(x2, p)) {
                    fac_buf.push(p);
                }
            }
            if !can_pack_into_tail_caps(&fac_buf, &[m_min / 6, m_min / 7, m_min / 8]) {
                return Err(format!("d=4 monotonic bridge failed at ({}, {})", x1, x2));
            }
        }
    }

    let win_d3: Vec<u64> = sm7
        .iter()
        .copied()
        .filter(|&x| x >= 435 && x <= 576_240)
        .collect();
    let vp_d3: Vec<[u8; 4]> = win_d3
        .iter()
        .map(|&x| {
            [
                v_p_u64(x, 2) as u8,
                v_p_u64(x, 3) as u8,
                v_p_u64(x, 5) as u8,
                v_p_u64(x, 7) as u8,
            ]
        })
        .collect();
    let tails_d3: Vec<[u64; 4]> = win_d3
        .iter()
        .map(|&x| {
            let mut t3 = x;
            while t3 % 2 == 0 {
                t3 /= 2;
            }
            let mut t5 = t3;
            while t5 % 3 == 0 {
                t5 /= 3;
            }
            let mut t7 = t5;
            while t7 % 5 == 0 {
                t7 /= 5;
            }
            [x, t3, t5, t7]
        })
        .collect();

    for a_idx in 0..win_d3.len() {
        let x1 = win_d3[a_idx];
        let m_bound1 = (8 * x1 - 1).min(576_240);
        if m_bound1 < 3_482 {
            continue;
        }
        for b_idx in (a_idx + 1)..win_d3.len() {
            let x2 = win_d3[b_idx];
            if x2 > m_bound1 {
                break;
            }
            for c_idx in (b_idx + 1)..win_d3.len() {
                let x3 = win_d3[c_idx];
                if x3 > m_bound1 {
                    break;
                }
                // Divisor-closure upper cap on `M`: since `x_i >= M/8 + 1`, any multiplier `k >= 2`
                // with `k * x_i <= M` has `k <= 7` (`{2,3,5,7}`-smooth!), so `k * x_i` cannot be
                // divisible by `P_1 >= 11` and MUST belong to `{x1, x2, x3}`!
                let mut m_max = m_bound1;
                for &xi in &[x1, x2, x3] {
                    for k in 2..=7u64 {
                        let mult = k * xi;
                        if mult != x2 && mult != x3 && mult - 1 < m_max {
                            m_max = mult - 1;
                            break;
                        }
                    }
                }
                let m_min = 3_482u64.max(x3);
                if m_min > m_max {
                    continue;
                }
                let c4 = [m_min / 5, m_min / 6, m_min / 7, m_min / 8];
                let mut screen_fail = false;
                for (ti, &p) in [2u64, 3, 5, 7].iter().enumerate() {
                    let prod_t = (tails_d3[a_idx][ti] as u128)
                        * (tails_d3[b_idx][ti] as u128)
                        * (tails_d3[c_idx][ti] as u128);
                    let mut thr = p as u128;
                    for &ck in &c4 {
                        thr *= ((ck / p) + 1).max(p) as u128;
                    }
                    if prod_t >= thr {
                        screen_fail = true;
                        break;
                    }
                }
                if !screen_fail {
                    continue;
                }
                fac_buf.clear();
                for (ti, &p) in [2u64, 3, 5, 7].iter().enumerate().rev() {
                    let cnt = vp_d3[a_idx][ti] + vp_d3[b_idx][ti] + vp_d3[c_idx][ti];
                    for _ in 0..cnt {
                        fac_buf.push(p);
                    }
                }
                if !can_pack_into_tail_caps(&fac_buf, &c4) {
                    return Err(format!(
                        "d=3 monotonic bridge failed at ({}, {}, {}) for m_min={}",
                        x1, x2, x3, m_min
                    ));
                }
            }
        }
    }

    Ok(sm_checked)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut cert_path: Option<String> = None;
    let mut timeout_secs: Option<u64> = None;
    let mut prove_cfg: Option<(u64, u64, usize, Option<String>)> = None;
    let mut i = 1;
    while i < args.len() {
        if args[i] == "--cert" {
            if i + 1 >= args.len() {
                eprintln!("ERROR: --cert requires a path argument");
                process::exit(1);
            }
            cert_path = Some(args[i + 1].clone());
            i += 2;
        } else if args[i] == "--timeout-secs" {
            if i + 1 >= args.len() {
                eprintln!("ERROR: --timeout-secs requires seconds");
                process::exit(1);
            }
            timeout_secs = Some(args[i + 1].parse::<u64>().expect("timeout_secs"));
            i += 2;
        } else if args[i] == "--prove" {
            if i + 3 >= args.len() {
                eprintln!("ERROR: --prove <m_start> <m_end> <threads> [cert_out]");
                process::exit(1);
            }
            let ms = args[i + 1].parse::<u64>().expect("m_start");
            let me = args[i + 2].parse::<u64>().expect("m_end");
            let th = args[i + 3].parse::<usize>().expect("threads");
            if i + 4 < args.len() && !args[i + 4].starts_with("--") {
                let out = Some(args[i + 4].clone());
                prove_cfg = Some((ms, me, th, out));
                i += 5;
            } else {
                prove_cfg = Some((ms, me, th, None));
                i += 4;
            }
        } else {
            eprintln!("ERROR: Unknown argument: {}", args[i]);
            process::exit(1);
        }
    }

    if let Some(secs) = timeout_secs {
        thread::spawn(move || {
            thread::sleep(std::time::Duration::from_secs(secs));
            eprintln!("TIMEOUT: exceeded --timeout-secs {}", secs);
            process::exit(124);
        });
    }

    if let Some((ms, me, th, ref out)) = prove_cfg {
        let t0 = std::time::Instant::now();
        match prove_range_multicore(ms, me, th, out.as_deref()) {
            Ok((crt_leaves, pruned)) => {
                println!(
                    "PROVED M={}..={} on {} threads in {:.3}s (crt_leaves={}, slot_pruned={})",
                    ms,
                    me,
                    th,
                    t0.elapsed().as_secs_f64(),
                    crt_leaves,
                    pruned
                );
            }
            Err(e) => {
                eprintln!("PROVE FAILED: {}", e);
                process::exit(1);
            }
        }
    }

    if let Err(e) = verify_part1_lower_bound() {
        eprintln!("PART 1 FAILED: {}", e);
        process::exit(1);
    }
    println!("Part 1a: g(3)>=4, g(4)>=5, g(5)>=6, g(6)>=8 witnesses VERIFIED");

    match verify_part1b_g8_lower_bound() {
        Ok(x_g8) => {
            println!(
                "Part 1b: g(7)>=9, g(8)>=11 witnesses at M=3233, X_START={} VERIFIED",
                x_g8
            );
        }
        Err(e) => {
            eprintln!("PART 1b FAILED: {}", e);
            process::exit(1);
        }
    }

    if let Some(path) = cert_path {
        match verify_part3_cert(&path) {
            Ok((max_m, count, total_leaves, total_pruned)) => {
                println!(
                    "Part 3: Certificate {} ({} records, M=7..={}, leaves={}, pruned={}) VERIFIED",
                    path, count, max_m, total_leaves, total_pruned
                );
                println!(
                    "accept (rust-standalone) rows={} max_m={} leaves={} pruned={}",
                    count, max_m, total_leaves, total_pruned
                );
            }
            Err(e) => {
                eprintln!("PART 3 FAILED: {}", e);
                process::exit(1);
            }
        }
    }

    if prove_cfg.is_none() {
        match verify_part2_small_m(30) {
            Ok(checked) => {
                println!(
                    "Part 2: Small-M brute-force (M=7..=30, {} GCD-connected 6-sets) VERIFIED",
                    checked
                );
            }
            Err(e) => {
                eprintln!("PART 2 FAILED: {}", e);
                process::exit(1);
            }
        }
    }

    if prove_cfg.is_none() {
        match verify_part4_analytic_bridge() {
            Ok(sm_cnt) => {
                println!(
                    "Part 4: Analytic bridge above M=3481 ({} {{2,3,5,7}}-smooth M + monotonic d=3,4,5 bridges) VERIFIED",
                    sm_cnt
                );
            }
            Err(e) => {
                eprintln!("PART 4 FAILED: {}", e);
                process::exit(1);
            }
        }
    }

    println!("VERIFIED OK");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_part1_g6_lower_bound() {
        verify_part1_lower_bound().expect("Part 1 witness should verify");
    }

    #[test]
    fn test_part2_small_m_up_to_25() {
        let checked = verify_part2_small_m(25).expect("Part 2 M<=25 should verify");
        assert!(checked > 0);
    }
}

"""
Numerical investigation of the near-equal-modulus families and the open residual class
(PLAN.md Steps B3, B4, D8, D9):

1. Family 1 (Order 3, D = 1, k_inf = 2):
     f_N(x) = x (x - N)^2 - 1 = x^3 - 2 N x^2 + N^2 x - 1
   Two nearly equal real roots (~ N +/- N^{-1/2}) and one small root (~ N^{-2}).
   Covered by Theorem 3' (Smyth gap at j = 2 + two-logarithm Baker).

2. Family 2 (Order 4, D = 1, k_inf = 3 — Open Class):
     h_N(x) = x (x - N)^3 - 1 = x^4 - 3 N x^3 + 3 N^2 x^2 - N^3 x - 1
   Three roots clustered near modulus N (one real ~ N + N^{-1/3}, complex pair of modulus
   ~ N - 0.5 N^{-1/3}, gap ~ 1.5 N^{-4/3}) and one small root (~ N^{-3}).

3. Family 3 (Order 3, D > 1, D_{k=1} = 1, large prime q | D — Open Class, Step B4):
     g_{N,c}(x) = (x - N)(x^2 + x + N^2) - c = x^3 - (N - 1) x^2 + N (N - 1) x - (N^3 + c)
   for c in {-2, +2} and N chosen so that q = |N^3 + c| is prime.
   - Slope normalization scalar S = 1 (all Newton slopes are already integers: 0, 0, 1 at q).
   - gcd(b_0, b_1) = gcd(N^3 + c, N(N - 1)) = 1 => D_{k=1} = 1 (no k_q = 1 prime).
   - Unique prime dividing b_0 (and D) is q = |N^3 + c| = Theta(N^3) = 2^{Theta(||u||)}, with k_q = 2.
   - All three Archimedean moduli lie within O(N^{-3}) of N:
       |mu_1| = N + c / (2 N^2) + O(N^{-3})          (real),
       |mu_2| = |mu_3| = N + c / (4 N^2) + O(N^{-3}) (complex conjugate pair),
       delta_inf = |log(|mu_1| / |mu_2|)| = |c| / (4 N^3) + O(N^{-4}).
     In particular, for c = -2, the complex conjugate pair has strictly larger modulus than
     the real root by delta_inf ~ 1 / (2 N^3).
"""

import itertools
import math
import os
import sys
from typing import Dict, List, Tuple

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import mpmath as mp

from src.deterministic_zero_test import (
    compute_m0_without_factoring,
    e2_cached_collision_reject,
    e2_large_prime_rejection_filter,
    e2_odd_order_trace_certificate,
    order3_global_local_dichotomy,
    order4_global_local_dichotomy,
    unit_root_modulus,
)
from src.skolem_algorithm import LinearRecurrenceSequence, v_p


def is_prime(n: int) -> bool:
    n = abs(n)
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    r = math.isqrt(n)
    for d in range(3, r + 1, 2):
        if n % d == 0:
            return False
    return True


def poly_root_moduli_and_gaps(b_desc: List[int]) -> Tuple[List[float], List[float]]:
    """
    Given [b_{d-1}, ..., b_0] for x^d + b_{d-1} x^{d-1} + ... + b_0,
    compute sorted root moduli |mu_1| >= ... >= |mu_d| and consecutive log-gaps
    delta_j = log(|mu_j| / |mu_{j+1}|) using 100-digit mpmath precision.
    """
    mp.mp.dps = 100
    roots = mp.polyroots([mp.mpf(1)] + [mp.mpf(c) for c in b_desc], maxsteps=500, extraprec=100)
    mods = sorted([float(abs(r)) for r in roots], reverse=True)
    gaps = [math.log(mods[i] / mods[i + 1]) for i in range(len(mods) - 1)]
    return mods, gaps


def basis_sequences(coeffs: List[int], max_k: int) -> List[List[int]]:
    """
    Compute the d basis sequences e^{(j)}_k (0 <= j < d, 0 <= k <= max_k) where
    e^{(j)}_i = delta_{i,j} for 0 <= i < d, so that u_k = sum_j u_j * e^{(j)}_k.
    """
    d = len(coeffs)
    basis: List[List[int]] = []
    for j in range(d):
        init = [1 if i == j else 0 for i in range(d)]
        state = list(init)
        seq = list(init)
        for _ in range(d, max_k + 1):
            nxt = sum(coeffs[i] * state[i] for i in range(d))
            seq.append(nxt)
            state = state[1:] + [nxt]
        basis.append(seq)
    return basis


def search_planted_and_extra_zeros(
    coeffs: List[int],
    max_plant: int = 30,
    max_scan: int = 300,
) -> Dict[str, object]:
    """
    For Order 3 (or Order 4 with u_0 = u_1 = 0):
    For every 1 <= k1 < k2 <= max_plant, compute the primitive integer initial vector
    u = (0, u_1, u_2) (or (0, 0, u_2, u_3)) that vanishes at k = 0 and k = k1,
    scan up to max_scan for any extra zero k2 > k1, and also record the maximum ratio
    k_max / ||u|| over all primitive initial vectors with u_0 = 0, u_{k1} = 0.
    """
    d = len(coeffs)
    basis = basis_sequences(coeffs, max_scan)
    coeff_bits = sum(abs(c).bit_length() + 1 for c in coeffs)
    extra_zeros_found: List[Tuple[int, List[int], List[int]]] = []
    max_ratio = 0.0
    max_ratio_info = None

    for k1 in range(1, max_plant + 1):
        # Set u_0 = ... = u_{d-3} = 0, and choose (u_{d-2}, u_{d-1}) orthogonal to
        # (basis[d-2][k1], basis[d-1][k1])
        a = basis[d - 2][k1]
        b = basis[d - 1][k1]
        if a == 0 and b == 0:
            continue
        g = math.gcd(abs(a), abs(b))
        u_d2 = -b // g
        u_d1 = a // g
        init = [0] * (d - 2) + [u_d2, u_d1]
        zs = [k for k in range(max_scan + 1) if sum(init[j] * basis[j][k] for j in range(d)) == 0]
        total_bits = coeff_bits + sum(abs(x).bit_length() + 1 for x in init)
        k_max = zs[-1]
        ratio = k_max / total_bits
        if ratio > max_ratio:
            max_ratio = ratio
            max_ratio_info = (k_max, total_bits, init, zs)
        if any(z > k1 for z in zs):
            extra_zeros_found.append((k1, init, zs))

    return {
        "max_ratio_k_over_bits": max_ratio,
        "max_ratio_info": max_ratio_info,
        "extra_zeros_count": len(extra_zeros_found),
        "extra_zeros_examples": extra_zeros_found[:3],
    }


def scan_zeros_exact(coeffs: List[int], initial: List[int], max_k: int) -> List[int]:
    """Scan u_0, ..., u_{max_k} in O(max_k) integer operations and return all indices with u_k == 0."""
    d = len(coeffs)
    state = list(initial)
    zeros = [k for k in range(d) if state[k] == 0]
    for k in range(d, max_k + 1):
        nxt = sum(coeffs[i] * state[i] for i in range(d))
        if nxt == 0:
            zeros.append(k)
        state = state[1:] + [nxt]
    return zeros


def search_family_zeros(
    coeffs: List[int],
    box: int = 4,
    max_k: int = 300,
) -> Dict[str, object]:
    """
    Search over non-trivial initial tuples in [-box, box]^d (plus targeted initial states
    engineered to vanish at a prescribed index k_target <= 12) and record the largest zero index.
    """
    d = len(coeffs)
    max_zero = -1
    best_init = None
    best_zeros: List[int] = []
    tested = 0

    for init in itertools.product(range(-box, box + 1), repeat=d):
        if all(x == 0 for x in init):
            continue
        if math.gcd(*init) != 1:
            continue
        tested += 1
        zs = scan_zeros_exact(coeffs, list(init), max_k=max_k)
        if zs and zs[-1] > max_zero:
            max_zero = zs[-1]
            best_init = list(init)
            best_zeros = zs

    bit_size = sum(abs(c).bit_length() + 1 for c in coeffs) + d * (box.bit_length() + 1)
    return {
        "tested_initial_states": tested,
        "bit_size": bit_size,
        "max_zero_index": max_zero,
        "best_initial": best_init,
        "best_zeros": best_zeros,
    }


def verify_order3_open_class_family() -> List[Dict[str, object]]:
    """
    Step B4: Construct and verify explicit Order-3 instances in the open residual class:
        g_{N,c}(x) = (x - N)(x^2 + x + N^2) - c = x^3 - (N - 1) x^2 + N (N - 1) x - (N^3 + c)
    with c = -2 (complex pair dominant over real root) and c = +2 (real root dominant over complex pair),
    for N such that q = |N^3 + c| is prime.
    """
    records: List[Dict[str, object]] = []
    for c in (-2, 2):
        found = 0
        for N in range(3, 120, 2):
            q = abs(N ** 3 + c)
            if not is_prime(q):
                continue
            b2 = -(N - 1)
            b1 = N * (N - 1)
            b0 = -(N ** 3 + c)
            coeffs = [-b0, -b1, -b2]
            lrs = LinearRecurrenceSequence(coeffs=coeffs, initial=[0, 1, N])
            info = order3_global_local_dichotomy(b2, b1, b0)
            q_k1 = unit_root_modulus(lrs)
            mods, gaps = poly_root_moduli_and_gaps([b2, b1, b0])
            asymp_gap = abs(c) / (4.0 * (N ** 3))

            assert info["S"] == 1, f"Expected S=1, got {info['S']}"
            assert q_k1 == 1, f"Expected D_{{k=1}}=1, got {q_k1}"
            assert info["branch"] == "NON_ARCHIMEDEAN_NEWTON_BRANCH"
            assert info["D"] % q == 0, f"Expected q={q} | D={info['D']}"

            m0_info = compute_m0_without_factoring(b2, b1, b0, q=q, K=4)
            assert m0_info is not None and m0_info["exact"] is True
            z_info = search_family_zeros(coeffs, box=3, max_k=250) if found < 4 else None
            records.append({
                "c": c,
                "N": N,
                "q": q,
                "b": (b2, b1, b0),
                "S": info["S"],
                "D": info["D"],
                "D_k_eq_1": q_k1,
                "m0": m0_info["m0"],
                "moduli": mods,
                "gaps": gaps,
                "max_consecutive_gap": max(gaps),
                "asymptotic_gap_c_over_4N3": asymp_gap,
                "zero_search": z_info,
            })
            found += 1
            if found >= 6:
                break
    return records


def verify_norm_identity_on_k_q_eq_2() -> Dict[str, object]:
    """
    Step D9: Verify the exact subfield norm identity for k_q = 2:
      In F = Q(mu_3), the three conjugates of Z_k = c_1 mu_1^k + c_2 mu_2^k are
      x + y, y + z, z + x where (x, y, z) = (c_1 mu_1^k, c_2 mu_2^k, c_3 mu_3^k).
      Since (x + y)(y + z)(z + x) = (x + y + z)(x y + y z + z x) - x y z,
      whenever u_k = x + y + z = 0 we have N_{F/Q}(Z_k) = -x y z = -c_1 c_2 c_3 (-b_0)^k.
    """
    mp.mp.dps = 80
    # Use g_{3, -2}(x) = x^3 - 2 x^2 + 6 x - 25 (or g_{5, -2}(x) = x^3 - 4 x^2 + 20 x - 123)
    N, c = 3, -2
    b2, b1, b0 = -(N - 1), N * (N - 1), -(N ** 3 + c)  # q = 25 = 5^2; for N=5, c=-2: q = 123 = 3*41; N=3, c=2: q = 29 prime!
    N, c = 3, 2
    b2, b1, b0 = -(N - 1), N * (N - 1), -(N ** 3 + c)  # x^3 - 2 x^2 + 6 x - 29, q = 29 prime
    coeffs = [-b0, -b1, -b2]
    # Plant a zero at k = 3 by choosing u_0, u_1, u_2 so that u_3 = 2 u_2 - 6 u_1 + 29 u_0 = 0, e.g. (0, 1, 3)
    initial = [0, 1, 3]
    lrs = LinearRecurrenceSequence(coeffs=coeffs, initial=initial)
    assert lrs.term(0) == 0 and lrs.term(3) == 0

    roots = mp.polyroots([mp.mpf(1), mp.mpf(b2), mp.mpf(b1), mp.mpf(b0)])
    # Solve Vandermonde sum_{i=1}^3 c_i mu_i^k = u_k for k = 0, 1, 2
    V = mp.matrix([[roots[j] ** k for j in range(3)] for k in range(3)])
    rhs = mp.matrix([mp.mpf(initial[k]) for k in range(3)])
    c_vec = mp.lu_solve(V, rhs)

    max_err = 0.0
    for k in range(8):
        x = c_vec[0] * (roots[0] ** k)
        y = c_vec[1] * (roots[1] ** k)
        z = c_vec[2] * (roots[2] ** k)
        lhs = (x + y) * (y + z) * (z + x)
        rhs_id = (x + y + z) * (x * y + y * z + z * x) - x * y * z
        max_err = max(max_err, float(abs(lhs - rhs_id)))

    # At k = 3 where u_3 = 0, check (x+y)(y+z)(z+x) == -c_1 c_2 c_3 (-b_0)^3
    k0 = 3
    x3, y3, z3 = [c_vec[j] * (roots[j] ** k0) for j in range(3)]
    norm_Z3 = (x3 + y3) * (y3 + z3) * (z3 + x3)
    monomial_val = -c_vec[0] * c_vec[1] * c_vec[2] * (mp.mpf(-b0) ** k0)
    zero_err = float(abs(norm_Z3 - monomial_val))
    return {
        "poly": (1, b2, b1, b0),
        "q": -b0,
        "max_identity_error": max_err,
        "zero_collapse_error_at_k3": zero_err,
    }


def verify_route_e2_g3pos2_trace_example() -> Dict[str, object]:
    """
    Route E2 Exact Regression Example (§4.6.4):
      g_{3,+2}(x) = x^3 - 2x^2 + 6x - 29 (q = 29 prime, k_29 = 2),
      trace sequence u_n = rho^n + alpha^n + bar(alpha)^n with (u_0, u_1, u_2) = (3, 2, -8)
      and u_{n+3} = 2 u_{n+2} - 6 u_{n+1} + 29 u_n.
    At p = 5, M = 62, ell = 12:
      F_{12}(z) / 5 == 2 + 4z (mod 5) has a unique 5-adic root lifting to
      (R=1: z=2, n=136), (R=2: z=7, n=446), (R=3: z=107, n=6646),
      (R=4: z=607, n=37646), (R=5: z=2482, n=153896),
      all rejected modulo q = 29 and certified globally zero-free by `e2_odd_order_trace_certificate`.
    """
    lrs = LinearRecurrenceSequence(coeffs=[29, -6, 2], initial=[3, 2, -8])
    p = 5
    M = lrs.find_period_M(p)
    assert M == 62, f"Expected M=62, got {M}"
    ell = 12
    expected_rows = [
        (1, 2, 136, 2, 17),
        (2, 7, 446, 3, 3),
        (3, 107, 6646, 4, 12),
        (4, 607, 37646, 5, 27),
        (5, 2482, 153896, 6, 24),
    ]
    rows = []
    for R, exp_z, exp_n, exp_v5, exp_mod29 in expected_rows:
        N_bound = M * (p ** R) + ell
        certs = lrs.zero_search_subsequence_certificates(ell=ell, M=M, p=p, N=N_bound, nu=R + 5)
        assert len(certs) == 1, f"Expected 1 certificate at R={R}, got {len(certs)}"
        cert = certs[0]
        val_5 = v_p(lrs.term(cert.n, mod=p ** (R + 4)), p, R + 4)
        mod_29 = lrs.term(cert.n, mod=29)
        assert (cert.R, cert.z, cert.n, val_5, mod_29) == (R, exp_z, exp_n, exp_v5, exp_mod29)
        assert cert.V == 1 and cert.m == 1 and cert.guaranteed_vp_bound == R + 1
        assert e2_large_prime_rejection_filter(lrs, cert.n, q=29) is False
        rows.append((cert.R, cert.z, cert.n, val_5, mod_29))

    odd_cert = e2_odd_order_trace_certificate(lrs, q=29)
    assert odd_cert is not None and odd_cert["m_odd"] == 7 and odd_cert["u0_mod_q"] == 3
    return {
        "M": M,
        "ell": ell,
        "rows": rows,
        "odd_order_certificate": odd_cert,
    }


def verify_route_e2_isolated_29sq_example() -> Dict[str, object]:
    """
    Route E2 Branch-Collision & Isolated 29^2-Divisible Candidate Example (§4.6.5):
      g_{3,+2}(x) = x^3 - 2x^2 + 6x - 29 (q = 29 prime, m_0 = 1),
      initial data (u_0, u_1, u_2) = (1, 0, 1), u_{n+3} = 2 u_{n+2} - 6 u_{n+1} + 29 u_n.
    At p = 5, M = 62, ell = 18:
      F_{18}(z) / 5 == 4 + 4z (mod 5) has a unique 5-adic root lifting across R = 5..9:
        R = 5: z_5 =    2244, n_5 =   139146, v_5(u_{n_5}) =  6, v_{29}(u_{n_5}) = 0
        R = 6: z_6 =   14744, n_6 =   914146, v_5(u_{n_6}) =  7, v_{29}(u_{n_6}) = 0 (u == 1 mod 29)
        R = 7: z_7 =   30369, n_7 =  1882896, v_5(u_{n_7}) =  8, v_{29}(u_{n_7}) = 2 (u == 1682 = 2*29^2 mod 29^3)
        R = 8: z_8 =  342869, n_8 = 21257896, v_5(u_{n_8}) =  9, v_{29}(u_{n_8}) = 0 (u == 28 mod 29)
        R = 9: z_9 =  733494, n_9 = 45476646, v_5(u_{n_9}) = 10, v_{29}(u_{n_9}) = 0
      Confirming the consecutive-active-lift theorem min(v_q(u_{n_old}), v_q(u_{n_new}), n_old) <= m_0 = 1
      and cached rejection of n_8 from n_7 without evaluating u_{n_8}.
    """
    b2, b1, b0 = -2, 6, -29
    lrs = LinearRecurrenceSequence(coeffs=[29, -6, 2], initial=[1, 0, 1])
    p, M, ell = 5, 62, 18
    m0_res = compute_m0_without_factoring(b2, b1, b0, q=29, K=4)
    assert m0_res is not None and m0_res["m0"] == 1 and m0_res["exact"] is True

    expected = [
        (5, 2244, 139146, 6, 0),
        (6, 14744, 914146, 7, 0),
        (7, 30369, 1882896, 8, 2),
        (8, 342869, 21257896, 9, 0),
        (9, 733494, 45476646, 10, 0),
    ]
    # Lift z_R directly via Hensel on F_{18}(z) to reach R = 9 rapidly, and also check ZeroSearch at R = 5
    certs_R5 = lrs.zero_search_subsequence_certificates(ell=ell, M=M, p=p, N=M * (p ** 5) + ell, nu=12)
    assert len(certs_R5) == 1 and (certs_R5[0].z, certs_R5[0].n) == (2244, 139146)

    rows = []
    for R, exp_z, exp_n, exp_v5, exp_v29 in expected:
        n_idx = M * exp_z + ell
        assert n_idx == exp_n
        val_5 = v_p(lrs.term(n_idx, mod=p ** (R + 3)), p, R + 3)
        val_29 = v_p(lrs.term(n_idx, mod=29 ** 4), 29, 4)
        assert (val_5, val_29) == (exp_v5, exp_v29), f"At R={R}: got {(val_5, val_29)}, expected {(exp_v5, exp_v29)}"
        rows.append((R, exp_z, n_idx, val_5, val_29))

    assert lrs.term(914146, mod=29) == 1
    assert lrs.term(1882896, mod=29 ** 3) == 1682 == 2 * (29 ** 2)
    assert lrs.term(21257896, mod=29) == 28

    # Consecutive active lift theorem check: min(v_29(u_{n_R}), v_29(u_{n_{R+1}})) <= m_0 = 1
    for i in range(len(rows) - 1):
        assert min(rows[i][4], rows[i + 1][4]) <= m0_res["m0"]

    # Cached collision rejection of n_8 from n_7 at m = 1 and m = 2 (without evaluating u_{n_8}):
    assert e2_cached_collision_reject(b2, b1, b0, q=29, m_prec=1, n_old=1882896, n_new=21257896) is False
    assert e2_cached_collision_reject(b2, b1, b0, q=29, m_prec=2, n_old=1882896, n_new=21257896) is False

    return {
        "m0": m0_res["m0"],
        "rows": rows,
        "u_n7_mod_29_cubed": lrs.term(1882896, mod=29 ** 3),
    }


def main() -> None:
    print("=" * 78)
    print("STEP B3 & B4: NEAR-EQUAL-MODULUS FAMILIES & OPEN-CLASS CONSTRUCTIONS")
    print("=" * 78)

    # 1. Family 1: f_N(x) = x(x - N)^2 - 1 (Order 3, D = 1, k_inf = 2)
    print("\n1. Family 1: f_N(x) = x(x - N)^2 - 1  (Order 3, D = 1, Smyth + 2-log Baker)")
    for N in [3, 5, 10, 20, 50]:
        b2, b1, b0 = -2 * N, N * N, -1
        coeffs = [-b0, -b1, -b2]
        mods, gaps = poly_root_moduli_and_gaps([b2, b1, b0])
        z_res = search_family_zeros(coeffs, box=4, max_k=300)
        p_res = search_planted_and_extra_zeros(coeffs, max_plant=25, max_scan=250)
        print(
            f"   N={N:2d}: gaps=({gaps[0]:.3e}, {gaps[1]:.4f}), "
            f"box_max_zero={z_res['max_zero_index']} (||u||~{z_res['bit_size']:2d}b), "
            f"planted max k/||u||={p_res['max_ratio_k_over_bits']:.3f}, "
            f"extra_zeros_beyond_plant={p_res['extra_zeros_count']}"
        )

    # 2. Family 2: h_N(x) = x(x - N)^3 - 1 (Order 4, D = 1, k_inf = 3 — Open Class)
    print("\n2. Family 2: h_N(x) = x(x - N)^3 - 1  (Order 4, D = 1, k_inf = 3 [Open])")
    for N in [3, 5, 10, 20, 50]:
        b3, b2, b1, b0 = -3 * N, 3 * N * N, -(N ** 3), -1
        coeffs = [-b0, -b1, -b2, -b3]
        info4 = order4_global_local_dichotomy(b3, b2, b1, b0)
        mods, gaps = poly_root_moduli_and_gaps([b3, b2, b1, b0])
        z_res = search_family_zeros(coeffs, box=2, max_k=250)
        p_res = search_planted_and_extra_zeros(coeffs, max_plant=25, max_scan=250)
        print(
            f"   N={N:2d}: D={info4['D']}, gaps=({gaps[0]:.3e}, {gaps[1]:.1e}, {gaps[2]:.4f}), "
            f"box_max_zero={z_res['max_zero_index']} (||u||~{z_res['bit_size']:2d}b), "
            f"planted max k/||u||={p_res['max_ratio_k_over_bits']:.3f}, "
            f"extra_zeros_beyond_plant={p_res['extra_zeros_count']}"
        )

    # 3. Family 3 (Step B4): Order-3 Open Class g_{N,c}(x) = (x - N)(x^2 + x + N^2) - c
    print("\n3. Family 3 (Step B4): Order-3 Open Class g_{N,c}(x) = (x - N)(x^2 + x + N^2) - c")
    records = verify_order3_open_class_family()
    for rec in records:
        coeffs = [-rec["b"][2], -rec["b"][1], -rec["b"][0]]
        p_res = search_planted_and_extra_zeros(coeffs, max_plant=20, max_scan=200)
        z_str = (
            f", box_max_z={rec['zero_search']['max_zero_index']}"
            if rec["zero_search"] is not None
            else ""
        )
        dom_type = "complex-pair > real" if rec["c"] < 0 else "real > complex-pair"
        print(
            f"   c={rec['c']:+d} ({dom_type}), N={rec['N']:2d}: q={rec['q']:6d} (prime, m0={rec['m0']}), "
            f"S={rec['S']}, D_{{k=1}}={rec['D_k_eq_1']}, D={rec['D']}, "
            f"max_gap={rec['max_consecutive_gap']:.3e} (asymp={rec['asymptotic_gap_c_over_4N3']:.3e})"
            f"{z_str}, max k/||u||={p_res['max_ratio_k_over_bits']:.3f}, extra_z={p_res['extra_zeros_count']}"
        )

    # 4. Step D9: Subfield norm identity verification
    norm_res = verify_norm_identity_on_k_q_eq_2()
    print("\n4. Step D9 Subfield Norm Identity Verification (q = 29, k_q = 2):")
    print(f"   max |(x+y)(y+z)(z+x) - ((x+y+z)(xy+yz+zx) - xyz)| = {norm_res['max_identity_error']:.2e}")
    print(f"   at zero u_3 = 0: |N_{{F/Q}}(Z_3) - (-c_1 c_2 c_3 (-b_0)^3)| = {norm_res['zero_collapse_error_at_k3']:.2e}")

    # 5. Route E2: g_{3,+2} trace sequence 5-adic candidate branch & mod-29 rejection
    e2_res = verify_route_e2_g3pos2_trace_example()
    print("\n5. Route E2 Regression Example 1: g_{3,+2}(x) = x^3 - 2x^2 + 6x - 29, u=(3,2,-8), p=5, M=62, ell=12:")
    for R, z, n_idx, val5, mod29 in e2_res["rows"]:
        print(f"   R={R}: z={z:4d}, n=62z+12={n_idx:6d}, v_5(u_n)={val5}, u_n mod 29={mod29:2d} (rejected!)")
    print(f"   Mod-29 odd-order trace certificate: {e2_res['odd_order_certificate']}")

    # 6. Route E2 Branch-Collision & Isolated 29^2-Divisible Candidate Example: u=(1,0,1), ell=18
    e2_coll = verify_route_e2_isolated_29sq_example()
    print(
        f"\n6. Route E2 Regression Example 2 (Branch Collision & Isolated 29^2 Candidate): "
        f"u=(1,0,1), p=5, M=62, ell=18, m0={e2_coll['m0']}:"
    )
    for R, z, n_idx, val5, val29 in e2_coll["rows"]:
        print(f"   R={R}: z={z:6d}, n=62z+18={n_idx:8d}, v_5(u_n)={val5:2d}, v_29(u_n)={val29}")
    print(
        f"   At R=7 (n=1,882,896): u_n mod 29^3 = {e2_coll['u_n7_mod_29_cubed']} = 2 * 29^2; "
        f"consecutive active lifts satisfy min(v_29(u_old), v_29(u_new)) <= m0 = 1!"
    )


if __name__ == "__main__":
    main()

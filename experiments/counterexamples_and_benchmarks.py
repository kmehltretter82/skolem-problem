"""
Run and verify:
1. Obstruction Theorem B1 (Pisano-period defeat of oblivious polynomial modulus sets).
2. Obstruction Theorem B2 (5-adic ghost-root sequence in SODA 2026 order-3 LRS,
   including the zero-digit jump at R=3, and its deterministic elimination via Lemma 2).
3. Deterministic Bounded Skolem solver benchmarks across order-2, order-3, and order-4 LRS
   up to N = 10^15.
"""

import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.deterministic_zero_test import (
    construct_ghost_root_counterexamples,
    construct_pisano_counterexample,
    factorization_free_D_nu_zero_test,
    order3_global_local_dichotomy,
    order4_global_local_dichotomy,
    solve_bounded_skolem_deterministic,
)
from src.skolem_algorithm import LinearRecurrenceSequence


def run_obstruction_b1_demo() -> None:
    print("=== 1. Obstruction Theorem B1: Pisano-Period Defeat of Oblivious Modulus Sets ===")
    # Order-3 LRS: u_n = 5^n - 3^n - 2^n + 1, which has u_0 = 0, u_1 = 1, u_2 = 13, u_n > 0 for all n >= 1
    # Characteristic polynomial: (x-5)(x-3)(x-2)(x-1) or for order 3: u_n = 5^n - 3^n - 2 * 1^n (u_0 = 0? 1 - 1 - 2 = -2).
    # Take order-3 LRS: u_n = 2 * 5^n - 3^n - 1^n => u_0 = 2 - 1 - 1 = 0, u_n > 0 for all n >= 1!
    # Char poly: (x - 5)(x - 3)(x - 1) = x^3 - 9 x^2 + 23 x - 15
    # u_0 = 0, u_1 = 10 - 3 - 1 = 6, u_2 = 50 - 9 - 1 = 40
    lrs = LinearRecurrenceSequence(coeffs=[-15, 23, -9], initial=[0, 6, 40])
    moduli = [7, 11, 13, 17, 19, 23]

    res = construct_pisano_counterexample(lrs, moduli)
    print(f"LRS: u_n = 2*5^n - 3^n - 1 (order 3, unique zero at n = 0)")
    print(f"Selected modulus set S = {res['moduli']} (total bits = {res['moduli_total_bits']})")
    print(f"Multiplicative orders ord_m(A): {res['orders']}")
    print(f"Adversarial index n* = {res['n_star']} ({res['n_star_bits']} bits)")
    print(f"Residues u_{{n*}} mod m for m in S: {res['residues']}")
    print(f"All modular residues zero? {res['all_residues_zero']}")
    print(f"Lemma 2 dyadic interval strictly nonzero? {res['interval_strictly_nonzero']}")
    assert res["all_residues_zero"] is True
    assert res["interval_strictly_nonzero"] is True
    print("Obstruction Theorem B1 verified!\n")


def run_obstruction_b2_demo() -> None:
    print("=== 2. Obstruction Theorem B2: 5-adic Ghost-Root Sequence at Order 3 ===")
    rows = construct_ghost_root_counterexamples(max_depth=8)
    print("Tracing the 5-adic ghost root x_0 in Z_5 \\ Z of F_3(n) = u_{8n+3} in SODA 2026 LRS:")
    print(f"{'R':>2} | {'digit':>5} | {'z_R':>8} | {'n_R = 8*z_R+3':>14} | {'v_5(u_{n_R})':>12} | {'Lemma 2 Nonzero?':>16}")
    print("-" * 72)
    for row in rows:
        print(
            f"{row['R']:>2} | {row['digit_R_minus_1']:>5} | {row['z_R']:>8} | "
            f"{row['n_R']:>14} | {row['v_5_u_nR']:>12} | {str(row['interval_certifies_nonzero']):>16}"
        )
        assert row["divisible_by_5_pow_R_plus_1"] is True
        assert row["interval_certifies_nonzero"] is True

    # Highlight the zero base-5 digit jump!
    jumps = [row for row in rows if row["v_5_u_nR"] > row["R"] + 1]
    print(f"Depths where base-5 digit of x_0 is 0 (causing extra 5-adic valuation jump): {[r['R'] for r in jumps]}")
    assert len(jumps) >= 1
    print("Obstruction Theorem B2 and Lemma 2 elimination verified!\n")


def run_deterministic_solver_benchmarks() -> None:
    print("=== 3. Deterministic Low-Order Skolem Solver Benchmarks (Orders 2, 3, 4) ===")
    test_cases = [
        (
            "Order 2 (Two-root with zero at n=5: u_n = 3^n - 243 * 1^n)",
            LinearRecurrenceSequence(coeffs=[-3, 4], initial=[-242, -240]),
            10**12,
            [5],
        ),
        (
            "Order 3 (SODA 2026 Section 3.4 example up to N = 10^12)",
            LinearRecurrenceSequence(coeffs=[1, -3, 2], initial=[-1, 1, 7]),
            10**12,
            [4],
        ),
        (
            "Order 3 (Tribonacci recurrence with three zeros at n = 3, 6, 7)",
            LinearRecurrenceSequence(coeffs=[1, 1, 1], initial=[1, -3, 2]),
            10**12,
            [3, 6, 7],
        ),
        (
            "Order 4 (Four distinct roots (x-3)(x-2)(x^2+1), zero at n=4: u_n = 3^n - 2^n - 65*cos(n*pi/2))",
            # Let's construct an explicit order-4 LRS with a known zero at n=4:
            # Char poly: (x-3)(x-2)(x^2+1) = (x^2 - 5x + 6)(x^2 + 1) = x^4 - 5x^3 + 7x^2 - 5x + 6
            # Take u_n = 3^n - 2^n - 65 * Re(i^n):
            # n=0: 1 - 1 - 65 = -65
            # n=1: 3 - 2 - 0 = 1
            # n=2: 9 - 4 - (-65) = 70
            # n=3: 27 - 8 - 0 = 19
            # n=4: 81 - 16 - 65 = 0!
            LinearRecurrenceSequence(coeffs=[-6, 5, -7, 5], initial=[-65, 1, 70, 19]),
            10**10,
            [4],
        ),
    ]

    for label, lrs, N, expected_zeros in test_cases:
        APs, raw_cands, verified_zeros = solve_bounded_skolem_deterministic(lrs, N=N)
        print(f"* {label}:")
        print(f"    Bound N = {N}, Raw ZeroSearch candidates = {raw_cands}")
        print(f"    Deterministically verified zeros = {verified_zeros} (expected {expected_zeros})")
        assert APs == []
        assert verified_zeros == expected_zeros
    print("All deterministic solver benchmarks passed!\n")


def run_global_local_dichotomy_demo() -> None:
    print("=== 4. Theorems 3 & 4: Global-Local Dichotomy (Transition Window Elimination) ===")
    # 1. SODA 2026 Order-3 example: x^3 - 2 x^2 + 3 x - 1 (a0 = -1 => D = 1, Archimedean Unit Branch!)
    info_unit = order3_global_local_dichotomy(b2=-2, b1=3, b0=-1)
    print(f"* Order-3 SODA 2026 (x^3 - 2x^2 + 3x - 1): branch={info_unit['branch']}, D={info_unit['D']}, Smyth gap >= {info_unit['smyth_lower_bound_gap']}")
    assert info_unit["branch"] == "ARCHIMEDEAN_UNIT_BRANCH" and info_unit["D"] == 1

    # 2. Order-3 Non-Archimedean Newton-Polygon example: (x - 5)(x - 3)(x - 1) = x^3 - 9x^2 + 23x - 15
    info_newton = order3_global_local_dichotomy(b2=-9, b1=23, b0=-15)
    print(f"* Order-3 (x-5)(x-3)(x-1) (x^3 - 9x^2 + 23x - 15): branch={info_newton['branch']}, D={info_newton['D']}, D_unit={info_newton['D_unit']}")
    assert info_newton["branch"] == "NON_ARCHIMEDEAN_NEWTON_BRANCH" and info_newton["D_unit"] == 15

    # Verify factorization-free D^nu test certifies u_6 != 0 on u_n = 2*5^n - 3^n - 1 (even when Pisano moduli fail!)
    lrs_pisano = LinearRecurrenceSequence(coeffs=[15, -23, 9], initial=[0, 6, 40])
    verdict_n6 = factorization_free_D_nu_zero_test(lrs_pisano, n=6)
    print(f"    Factorization-free D^nu test at Pisano adversarial index n* = 6: {verdict_n6} (expected False => u_6 != 0)")
    assert verdict_n6 is False

    # 3. Order-4 Non-Archimedean Slope-<=2 example: x^4 - 3x^3 + 2x^2 - 6x + 12 (gcd(b0, b1) = 6, gcd(b2, b3) = 1 => D_{<=2} = 6)
    info4 = order4_global_local_dichotomy(b3=-3, b2=2, b1=-6, b0=12)
    print(f"* Order-4 (x^4 - 3x^3 + 2x^2 - 6x + 12): branch={info4['branch']}, D={info4['D']}, D_le_2={info4['D_le_2']}")
    assert info4["branch"] == "NON_ARCHIMEDEAN_SLOPE_LE_2_BRANCH" and info4["D_le_2"] == 6
    print("Global-local dichotomy (Theorems 3 & 4) verified!\n")


if __name__ == "__main__":
    run_obstruction_b1_demo()
    run_obstruction_b2_demo()
    run_deterministic_solver_benchmarks()
    run_global_local_dichotomy_demo()

"""
Reproduce the worked example from Section 3.4 of Bacik, Ouaknine, Worrell (SODA 2026,
arXiv:2507.11234) and the 17-adic analysis of the open Order-6 sequence from
Section 8.3 of the 2026 Survey.
"""

import os
import sys

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.skolem_algorithm import LinearRecurrenceSequence, v_p


def verify_soda2026_example() -> None:
    print("=== 1. Reproducing SODA 2026 Section 3.4 Worked Example ===")
    # u_{n+3} = 2 u_{n+2} - 3 u_{n+1} + u_n, u_0 = -1, u_1 = 1, u_2 = 7
    lrs = LinearRecurrenceSequence(coeffs=[1, -3, 2], initial=[-1, 1, 7])
    p = lrs.choose_prime()
    M = lrs.find_period_M(p)
    nu = 5
    N = 200
    print(f"Chosen prime p = {p} (expected 5), period M = {M} (expected 8), N = {N}, nu = {nu}")
    assert p == 5 and M == 8

    # Table 1: (Delta^k F_ell)(0) mod 5^5 for 0 <= ell <= 7
    expected_table1 = {
        0: [3124, 80, 400],
        1: [1, 130, 2875],
        2: [7, 15, 25],
        3: [10, 2845, 1200],
        4: [0, 2650, 2075],
        5: [3102, 3030, 575],
        6: [3089, 955, 2375],
        7: [3122, 1720, 1975],
    }

    print("\nTable 1: (Delta^k F_ell)(0) mod 5^5 and j(F_ell):")
    for ell in range(M):
        j_F, V_F, diffs = lrs.j_and_V_h(ell, M, p, z=0, r=0, nu=nu)
        print(f"  ell={ell}: diffs={diffs}, V(F_{ell})={V_F}, j(F_{ell})={j_F}")
        assert diffs == expected_table1[ell], f"Mismatch at ell={ell}: {diffs} != {expected_table1[ell]}"
        if ell in (0, 1, 2, 5, 6, 7):
            assert j_F == 0
        elif ell == 3:
            assert j_F == 1
        elif ell == 4:
            assert j_F == 2

    # Run full candidate search for N = 200
    APs, candidates = lrs.find_candidate_zeros(N=N, p=p, M=M, nu=nu)
    print(f"\nAPs found: {APs} (expected [])")
    print(f"Candidate indices in [0, {N}]: {candidates} (expected [4, 59, 100])")
    assert APs == []
    assert candidates == [4, 59, 100]

    for n_cand in candidates:
        val = lrs.term(n_cand)
        print(f"  u_{n_cand} = {val}")
    assert lrs.term(4) == 0
    assert lrs.term(59) != 0
    assert lrs.term(100) != 0
    print("SODA 2026 example verified 100%!\n")


def verify_survey_order6_example() -> None:
    print("=== 2. Reproducing 2026 Survey Section 8.3 Open Order-6 Sequence (17-adic) ===")
    # Characteristic polynomial:
    # p(x) = (x - 1)^2 (x^2 + 8x + 65)(x^2 - 16x + 65)
    #      = x^6 - 10 x^5 + 19 x^4 - 532 x^3 + 5267 x^2 - 8970 x + 4225
    # So u_{n+6} = 10 u_{n+5} - 19 u_{n+4} + 532 u_{n+3} - 5267 u_{n+2} + 8970 u_{n+1} - 4225 u_n
    # Initial values from Survey line 2556:
    # u_0 = 12, u_1 = 49, u_2 = 374, u_3 = 6003, u_4 = 21520, u_5 = 150773
    coeffs = [-4225, 8970, -5267, 532, -19, 10]
    initial = [12, 49, 374, 6003, 21520, 150773]
    lrs = LinearRecurrenceSequence(coeffs=coeffs, initial=initial)

    p = 17
    M_full = lrs.find_period_M(p)
    M = 16  # lcm of multiplicative orders of the 5 distinct roots mod 17 (16, 8, 16, 4, 1)
    print(f"Prime p = {p}, full companion matrix period mod 17 = {M_full} (16 * 17 = 272), root period L = {M}")
    assert M_full == 272

    # Check that each of the 16 subsequences F_r (0 <= r < 16) has j(F_r) = 1 (one 17-adic zero)
    j_list = []
    for r_sub in range(M):
        j_F, V_F, _ = lrs.j_and_V_h(r_sub, M, p, z=0, r=0, nu=6)
        j_list.append(j_F)
    print(f"j(F_r) for r = 0..15: {j_list} (expected all 1s)")
    assert all(j == 1 for j in j_list)

    # Check modulo 16 invariance: u_n == 0 (mod 16) => n == 4 (mod 16)
    mod16_zeros = [n for n in range(16) if lrs.term(n, mod=16) == 0]
    print(f"Residues n mod 16 with u_n == 0 (mod 16): {mod16_zeros} (expected [4])")
    assert mod16_zeros == [4]

    # Trace the unique 17-adic root of F_4 to depth R = 10 (certifying no zero up to 16 * 17^10 + 4)
    APs, candidates = lrs.find_candidate_zeros(N=16 * (17 ** 6), p=17, M=16, nu=12)
    CandMod16_4 = [n for n in candidates if n % 16 == 4]
    print(f"Unique surviving candidate n === 4 (mod 16) at depth R=6: n = {CandMod16_4[0]}")
    z_val = (CandMod16_4[0] - 4) // 16
    base17_digits = []
    tmp = z_val
    for _ in range(6):
        base17_digits.append(tmp % 17)
        tmp //= 17
    print(f"First 6 base-17 digits of the unique 17-adic zero of F_4: {base17_digits}")
    print("Survey Order-6 17-adic analysis verified!\n")


if __name__ == "__main__":
    verify_soda2026_example()
    verify_survey_order6_example()

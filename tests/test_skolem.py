"""
Unit test suite for the low-order Skolem algorithm and deterministic zero-testing modules.
"""

import unittest

from src.deterministic_zero_test import (
    DyadicInterval,
    construct_ghost_root_counterexamples,
    construct_pisano_counterexample,
    coprime_base,
    dyadic_interval_zero_test,
    e2_large_prime_rejection_filter,
    e2_odd_order_trace_certificate,
    factorization_free_D_nu_zero_test,
    hensel_depth_extension_test,
    interval_eval_term,
    normalize_newton_polygon_coeffs,
    order3_global_local_dichotomy,
    order4_global_local_dichotomy,
    single_prime_power_zero_test,
    slope_normalize_lrs,
    solve_bounded_skolem_deterministic,
    unit_root_certificate,
    check_unit_root_certificate,
    unit_root_modulus,
    unit_root_zero_bound_test,
)
from src.skolem_algorithm import LinearRecurrenceSequence


class TestSkolemAlgorithm(unittest.TestCase):
    def test_soda2026_worked_example(self) -> None:
        lrs = LinearRecurrenceSequence(coeffs=[1, -3, 2], initial=[-1, 1, 7])
        p = lrs.choose_prime()
        M = lrs.find_period_M(p)
        self.assertEqual(p, 5)
        self.assertEqual(M, 8)
        APs, cands = lrs.find_candidate_zeros(N=200, p=p, M=M, nu=5)
        self.assertEqual(APs, [])
        self.assertEqual(cands, [4, 59, 100])
        self.assertEqual(lrs.term(4), 0)
        self.assertNotEqual(lrs.term(59), 0)
        self.assertNotEqual(lrs.term(100), 0)

    def test_periodic_zero_subsequence_detection(self) -> None:
        # u_n = 2^n - (-2)^n: zero for all even n (n = 2k)
        # Char poly: (x - 2)(x + 2) = x^2 - 4 => u_{n+2} = 4 u_n, u_0 = 0, u_1 = 4
        lrs = LinearRecurrenceSequence(coeffs=[4, 0], initial=[0, 4])
        APs, cands = lrs.find_candidate_zeros(N=500)
        # Every even subsequence ell (ell % 2 == 0) is identically zero since M is even
        self.assertTrue(len(APs) > 0)
        for M, ell in APs:
            self.assertEqual(ell % 2, 0)
        self.assertEqual(cands, [])

    def test_dyadic_interval_enclosure_rigor(self) -> None:
        lrs = LinearRecurrenceSequence(coeffs=[1, -3, 2], initial=[-1, 1, 7])
        for n in [0, 1, 2, 3, 4, 10, 59, 100]:
            exact = lrs.term(n)
            iv = interval_eval_term(lrs, n, prec=128)
            if iv.exp >= 0:
                lo_val = iv.lo << iv.exp
                hi_val = iv.hi << iv.exp
                self.assertLessEqual(lo_val, exact)
                self.assertLessEqual(exact, hi_val)
            else:
                k = -iv.exp
                self.assertLessEqual(iv.lo, exact << k)
                self.assertLessEqual(exact << k, iv.hi)
        self.assertIs(dyadic_interval_zero_test(lrs, 4, prec=128), True)
        self.assertIs(dyadic_interval_zero_test(lrs, 59, prec=128), False)
        self.assertIs(dyadic_interval_zero_test(lrs, 100, prec=128), False)

    def test_obstruction_b1_pisano_counterexample(self) -> None:
        lrs = LinearRecurrenceSequence(coeffs=[-15, 23, -9], initial=[0, 6, 40])
        res = construct_pisano_counterexample(lrs, [7, 11, 13])
        self.assertTrue(res["all_residues_zero"])
        self.assertTrue(res["interval_strictly_nonzero"])

    def test_obstruction_b2_ghost_roots(self) -> None:
        rows = construct_ghost_root_counterexamples(max_depth=5)
        self.assertEqual(len(rows), 5)
        for row in rows:
            self.assertTrue(row["divisible_by_5_pow_R_plus_1"])
            self.assertTrue(row["interval_certifies_nonzero"])
        # At R=3, the base-5 digit of x_0 is 0, causing v_5(u_{n_3}) = 5 >= R + 2
        self.assertEqual(rows[3]["digit_R_minus_1"], 0)
        self.assertGreaterEqual(rows[2]["v_5_u_nR"], 5)

    def test_deterministic_solver_up_to_order_4(self) -> None:
        lrs4 = LinearRecurrenceSequence(coeffs=[-6, 5, -7, 5], initial=[-65, 1, 70, 19])
        APs, raw_cands, verified = solve_bounded_skolem_deterministic(lrs4, N=10**8)
        self.assertEqual(APs, [])
        self.assertIn(4, raw_cands)
        self.assertEqual(verified, [4])

    def test_theorems_3_and_4_global_local_dichotomy(self) -> None:
        # Coprime-base normalization on [b2=16, b1=16, b0=64] -> S=4, hat_b=[4, 1, 1]
        S, hat_b = normalize_newton_polygon_coeffs([16, 16, 64])
        self.assertEqual(S, 4)
        self.assertEqual(hat_b, [4, 1, 1])

        # Theorem 3 Archimedean unit branch (D = 1)
        info_unit = order3_global_local_dichotomy(b2=-2, b1=3, b0=-1)
        self.assertEqual(info_unit["branch"], "ARCHIMEDEAN_UNIT_BRANCH")
        self.assertEqual(info_unit["D"], 1)

        # Theorem 3 Non-Archimedean Newton-polygon branch (D > 1) + factorization-free D^nu test
        info_newton = order3_global_local_dichotomy(b2=-9, b1=23, b0=-15)
        self.assertEqual(info_newton["branch"], "NON_ARCHIMEDEAN_NEWTON_BRANCH")
        self.assertEqual(info_newton["D_unit"], 15)
        lrs_pisano = LinearRecurrenceSequence(coeffs=[15, -23, 9], initial=[0, 6, 40])
        self.assertIs(factorization_free_D_nu_zero_test(lrs_pisano, n=6), False)
        self.assertIs(factorization_free_D_nu_zero_test(lrs_pisano, n=0), True)

        # Theorem 4 Order-4 slope-<=2 branch
        info4 = order4_global_local_dichotomy(b3=-3, b2=2, b1=-6, b0=12)
        self.assertEqual(info4["branch"], "NON_ARCHIMEDEAN_SLOPE_LE_2_BRANCH")
        self.assertEqual(info4["D_le_2"], 6)

    def test_theorems_5_and_6_unit_root_zero_bounds(self) -> None:
        # Lean example `unitRootExampleSeq`: chi = x^3 - x^2 + 15x + 15, composite q = 15, m = 0
        lrs = LinearRecurrenceSequence(coeffs=[-15, -15, 1], initial=[0, 0, 1])
        cert = unit_root_certificate(lrs)
        self.assertIsNotNone(cert)
        self.assertEqual(cert["q"], 15)
        self.assertEqual(cert["m"], 0)
        self.assertEqual(cert["zero_bound"], 2)
        self.assertTrue(check_unit_root_certificate(lrs, cert))
        for k in range(2, 200):
            self.assertNotEqual(lrs.term(k) % 15, 0)
        self.assertIs(unit_root_zero_bound_test(lrs, 0), True)
        self.assertIs(unit_root_zero_bound_test(lrs, 10**30), False)

        # Higher precision m > 0 (requires Hensel lifting of mu modulo q^(m+1))
        lrs_m = LinearRecurrenceSequence(coeffs=[-6, -6, 1], initial=[6, -6, 36])
        cert_m = unit_root_certificate(lrs_m)
        self.assertIsNotNone(cert_m)
        self.assertGreater(cert_m["m"], 0)
        self.assertTrue(check_unit_root_certificate(lrs_m, cert_m))
        Q = cert_m["q"] ** (cert_m["m"] + 1)
        for k in range(cert_m["zero_bound"], cert_m["zero_bound"] + 150):
            self.assertNotEqual(lrs_m.term(k) % Q, 0)

        # Order 4 (Theorem 6): chi = x^4 + 2x^3 + 10x^2 - 20x + 30, q = 10
        lrs4 = LinearRecurrenceSequence(coeffs=[-30, 20, -10, -2], initial=[1, 0, 0, 0])
        cert4 = unit_root_certificate(lrs4)
        self.assertIsNotNone(cert4)
        self.assertEqual(cert4["q"], 5)
        Q4 = cert4["q"] ** (cert4["m"] + 1)
        for k in range(cert4["zero_bound"], cert4["zero_bound"] + 150):
            self.assertNotEqual(lrs4.term(k) % Q4, 0)

        # No k_q = 1 modulus: q | b2 as well
        self.assertIsNone(unit_root_certificate(
            LinearRecurrenceSequence(coeffs=[-15, -15, 15], initial=[0, 0, 1])))

    def test_slope_normalized_unit_root_and_open_class(self) -> None:
        # 1. Slope-normalized sequence z_k = S^{d-1-k} v_k (matching `order3_slope_normalization_scaling`):
        # Take unitRootExampleSeq (chi = x^3 - x^2 + 15x + 15) scaled by S = 15:
        # b2 = -15, b1 = 3375, b0 = 50625 => coeffs = [-50625, -3375, 15], initial = [0, 0, 1]
        v_lrs = LinearRecurrenceSequence(coeffs=[-50625, -3375, 15], initial=[0, 0, 1])
        self.assertIsNone(unit_root_certificate(v_lrs))  # Raw b2=-15 shares all primes (3, 5) with b1, b0
        S, z_lrs = slope_normalize_lrs(v_lrs)
        self.assertEqual(S, 15)
        self.assertEqual(z_lrs.coeffs, [-15, -15, 1])
        for k in range(15):
            self.assertEqual((S ** 2) * v_lrs.term(k), (S ** k) * z_lrs.term(k))
        self.assertIs(unit_root_zero_bound_test(v_lrs, 0), True)
        self.assertIs(unit_root_zero_bound_test(v_lrs, 2), False)
        self.assertIs(unit_root_zero_bound_test(v_lrs, 10**20), False)

        # 2. Step B4 Order-3 open residual class instance:
        # g_{9, -2}(x) = (x - 9)(x^2 + x + 81) + 2 = x^3 - 8 x^2 + 72 x - 727 (q = 727 prime)
        N, c = 9, -2
        b2, b1, b0 = -(N - 1), N * (N - 1), -(N ** 3 + c)
        open_lrs = LinearRecurrenceSequence(coeffs=[-b0, -b1, -b2], initial=[0, 1, N])
        info = order3_global_local_dichotomy(b2, b1, b0)
        self.assertEqual(info["S"], 1)
        self.assertEqual(unit_root_modulus(open_lrs), 1)
        self.assertEqual(info["D"], 727 ** 2)

        # 3. Route E2 regression example: g_{3, +2}(x) = x^3 - 2 x^2 + 6 x - 29 (q = 29 prime)
        # Trace sequence u = (3, 2, -8), p = 5, M = 62, ell = 12
        g3_trace = LinearRecurrenceSequence(coeffs=[29, -6, 2], initial=[3, 2, -8])
        self.assertEqual(g3_trace.find_period_M(5), 62)
        expected = [
            (1, 2, 136, 17),
            (2, 7, 446, 3),
            (3, 107, 6646, 12),
            (4, 607, 37646, 27),
            (5, 2482, 153896, 24),
        ]
        for R, exp_z, exp_n, exp_mod29 in expected:
            certs = g3_trace.zero_search_subsequence_certificates(
                ell=12, M=62, p=5, N=62 * (5 ** R) + 12, nu=R + 5
            )
            self.assertEqual(len(certs), 1)
            cert = certs[0]
            self.assertEqual((cert.R, cert.z, cert.n, cert.V, cert.m), (R, exp_z, exp_n, 1, 1))
            self.assertEqual(cert.guaranteed_vp_bound, R + 1)
            self.assertEqual(g3_trace.term(cert.n, mod=29), exp_mod29)
            self.assertIs(e2_large_prime_rejection_filter(g3_trace, cert.n, q=29), False)

        odd_cert = e2_odd_order_trace_certificate(g3_trace, q=29)
        self.assertIsNotNone(odd_cert)
        self.assertEqual(odd_cert["m_odd"], 7)
        self.assertEqual(odd_cert["u0_mod_q"], 3)


if __name__ == "__main__":
    unittest.main()

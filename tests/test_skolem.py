"""
Unit test suite for the low-order Skolem algorithm and deterministic zero-testing modules.
"""

import unittest

from src.deterministic_zero_test import (
    DyadicInterval,
    construct_ghost_root_counterexamples,
    construct_pisano_counterexample,
    dyadic_interval_zero_test,
    hensel_depth_extension_test,
    interval_eval_term,
    single_prime_power_zero_test,
    solve_bounded_skolem_deterministic,
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


if __name__ == "__main__":
    unittest.main()

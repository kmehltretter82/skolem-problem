"""
Reference implementation of the Bacik-Ouaknine-Worrell (SODA 2026) algorithm
for the Bounded Skolem Problem (arXiv:2507.11234, Algorithm 1) and helper routines
for analyzing candidate zero-testing instances.
"""

from __future__ import annotations
import math
from dataclasses import dataclass
from typing import List, Optional, Tuple


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def v_p(x: int, p: int, cap: int) -> int:
    """Return min(v_p(x), cap)."""
    if x == 0:
        return cap
    x = abs(x)
    v = 0
    while v < cap and x % p == 0:
        x //= p
        v += 1
    return v


def mat_mul_mod(A: List[List[int]], B: List[List[int]], mod: Optional[int] = None) -> List[List[int]]:
    d = len(A)
    m = len(B[0])
    k_len = len(B)
    C = [[0] * m for _ in range(d)]
    for i in range(d):
        for k in range(k_len):
            aik = A[i][k]
            if aik == 0:
                continue
            for j in range(m):
                C[i][j] += aik * B[k][j]
        if mod is not None:
            for j in range(m):
                C[i][j] %= mod
    return C


def mat_pow_mod(A: List[List[int]], exp: int, mod: Optional[int] = None) -> List[List[int]]:
    d = len(A)
    res = [[1 if i == j else 0 for j in range(d)] for i in range(d)]
    base = [row[:] for row in A]
    e = exp
    while e > 0:
        if e & 1:
            res = mat_mul_mod(res, base, mod)
        base = mat_mul_mod(base, base, mod)
        e >>= 1
    return res


def is_identity_mod(A: List[List[int]], mod: int) -> bool:
    d = len(A)
    for i in range(d):
        for j in range(d):
            expected = 1 if i == j else 0
            if A[i][j] % mod != expected:
                return False
    return True


@dataclass
class LinearRecurrenceSequence:
    """
    Order-d integer LRS satisfying:
        u_{n+d} = a_{d-1} u_{n+d-1} + ... + a_0 u_n
    with initial values u_0, u_1, ..., u_{d-1}.
    Note: coeffs = [a_0, a_1, ..., a_{d-1}] in increasing index order.
    """
    coeffs: List[int]
    initial: List[int]

    def __post_init__(self) -> None:
        if len(self.coeffs) != len(self.initial):
            raise ValueError("Length of coeffs and initial values must match.")
        if len(self.coeffs) == 0 or self.coeffs[0] == 0:
            raise ValueError("Recurrence must have order d >= 1 and a_0 != 0.")

    @property
    def order(self) -> int:
        return len(self.coeffs)

    @property
    def a0(self) -> int:
        return self.coeffs[0]

    def companion_matrix(self) -> List[List[int]]:
        """
        Companion matrix A from Section 2.1 of arXiv:2507.11234:
            first row: [a_{d-1}, ..., a_1, a_0]
            subdiagonal of 1s below.
        With alpha = [0, ..., 0, 1] and beta = [u_{d-1}, ..., u_0]^T,
        u_n = alpha A^n beta.
        """
        d = self.order
        A = [[0] * d for _ in range(d)]
        for j in range(d):
            A[0][j] = self.coeffs[d - 1 - j]
        for i in range(1, d):
            A[i][i - 1] = 1
        return A

    def term(self, n: int, mod: Optional[int] = None) -> int:
        """Compute u_n (optionally modulo `mod`) using repeated squaring on A."""
        d = self.order
        A = self.companion_matrix()
        An = mat_pow_mod(A, n, mod)
        # alpha = [0, ..., 0, 1] selects the last row of A^n;
        # beta = [u_{d-1}, u_{d-2}, ..., u_0]^T
        last_row = An[d - 1]
        val = sum(last_row[j] * self.initial[d - 1 - j] for j in range(d))
        return val % mod if mod is not None else val

    def choose_prime(self, min_prime: Optional[int] = None) -> int:
        """Choose the smallest prime p >= max(d + 2, min_prime) such that p does not divide a_0."""
        p = max(self.order + 2, min_prime or 0)
        while True:
            if is_prime(p) and (self.a0 % p != 0):
                return p
            p += 1

    def find_period_M(self, p: int) -> int:
        """Find the smallest positive integer M < p^(d^2) such that A^M == I (mod p)."""
        A = self.companion_matrix()
        cur = [ [x % p for x in row] for row in A ]
        limit = p ** (self.order ** 2)
        for m in range(1, limit + 1):
            if is_identity_mod(cur, p):
                return m
            cur = mat_mul_mod(cur, A, p)
        raise RuntimeError(f"Failed to find multiplicative period M mod {p}")

    def delta_k_h(self, ell: int, M: int, p: int, z: int, r: int, k: int, mod: Optional[int] = None) -> int:
        """
        Compute (Delta^k h_{z,r})(0) for h_{z,r}(x) = F_ell(p^r x + z), where F_ell(n) = u_{Mn + ell}:
            (Delta^k h_{z,r})(0) = sum_{n=0}^k (-1)^{k-n} C(k, n) u_{M(p^r n + z) + ell}
        """
        pr = p ** r
        total = 0
        for n in range(k + 1):
            sign = -1 if ((k - n) & 1) else 1
            binom = math.comb(k, n)
            idx = M * (pr * n + z) + ell
            u_val = self.term(idx, mod)
            total += sign * binom * u_val
        return total % mod if mod is not None else total

    def j_and_V_h(
        self,
        ell: int,
        M: int,
        p: int,
        z: int,
        r: int,
        nu: int,
        max_k: Optional[int] = None,
    ) -> Tuple[int, int, List[int]]:
        """
        Compute j(h_{z,r}), V(h_{z,r}), and the list of (Delta^k h_{z,r})(0) mod p^nu
        for 0 <= k <= max_k (defaults to d - 1).
        """
        if max_k is None:
            max_k = self.order - 1
        mod = p ** nu
        diffs = [self.delta_k_h(ell, M, p, z, r, k, mod) for k in range(max_k + 1)]
        vals = [v_p(val, p, nu) for val in diffs]
        V = min(vals)
        j = max(k for k, v in enumerate(vals) if v == V)
        return j, V, diffs

    def zero_search_subsequence(
        self,
        ell: int,
        M: int,
        p: int,
        N: int,
        nu: int,
    ) -> List[int]:
        """
        Run Algorithm 1 (`ZeroSearch`) on subsequence F_ell(n) = u_{Mn + ell}.
        Returns the list of candidate indices z such that 0 <= Mz + ell <= N.
        """
        j_F, _, _ = self.j_and_V_h(ell, M, p, z=0, r=0, nu=nu)
        if j_F == 0:
            return []

        discs: List[Tuple[int, int, int]] = [(0, 0, j_F)]  # (z, r, parent_j_bound)
        zeros: List[int] = []

        while discs:
            next_discs: List[Tuple[int, int, int]] = []
            for z, r, j_bound in discs:
                pr = p ** r
                for a in range(p):
                    z_prime = z + pr * a
                    j_h, _, _ = self.j_and_V_h(ell, M, p, z=z_prime, r=r + 1, nu=nu, max_k=j_bound)
                    if j_h >= 1:
                        if (p ** (r + 1)) * M + ell >= N:
                            if M * z_prime + ell <= N:
                                zeros.append(z_prime)
                        else:
                            next_discs.append((z_prime, r + 1, j_h))
            discs = next_discs
        return zeros

    def find_candidate_zeros(
        self,
        N: int,
        p: Optional[int] = None,
        M: Optional[int] = None,
        nu: Optional[int] = None,
    ) -> Tuple[List[Tuple[int, int]], List[int]]:
        """
        Full Algorithm 1 from arXiv:2507.11234:
        Returns (APs, candidates) where:
          - APs is a list of (M, ell) for which u_{Mn + ell} == 0 for all n >= 0.
          - candidates is a sorted list of candidate indices n in [0, N] outside APs.
        """
        d = self.order
        if p is None:
            p = self.choose_prime()
        if M is None:
            M = self.find_period_M(p)

        APs: List[Tuple[int, int]] = []
        candidates: List[int] = []
        R = max(1, math.ceil(math.log(max(N, 2), p)))

        for ell in range(M):
            initial_subseq = [self.term(M * n + ell) for n in range(d)]
            if all(val == 0 for val in initial_subseq):
                APs.append((M, ell))
                continue

            if nu is None:
                # Lemma 3.3 bound: V(h_{z,r}) <= V(F_ell) + r(d-1)
                diffs_0 = [
                    sum((-1) ** (k - j) * math.comb(k, j) * initial_subseq[j] for j in range(k + 1))
                    for k in range(d)
                ]
                nonzero_vals = [v_p(val, p, 10**6) for val in diffs_0 if val != 0]
                v_F = min(nonzero_vals)
                nu_ell = v_F + (R + 1) * (d - 1) + 2
            else:
                nu_ell = nu

            z_list = self.zero_search_subsequence(ell, M, p, N, nu_ell)
            for z in z_list:
                n_cand = M * z + ell
                if 0 <= n_cand <= N:
                    candidates.append(n_cand)

        candidates.sort()
        return APs, candidates

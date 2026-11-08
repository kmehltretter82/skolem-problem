"""
Deterministic zero-testing algorithms and counterexample constructions for
low-order Skolem candidate indices u_n = alpha A^n beta (Deliverables 3 & 4).

Includes:
1. Rigorous dyadic floating-point interval arithmetic (`DyadicInterval`, `IntervalMatrix`)
   for Lemma 2 (Archimedean MSTV separation via O(log n) interval matrix squarings).
2. Single-prime-power modular test for Lemma 1 (<= 2 distinct roots).
3. Non-branching p-adic Hensel depth-extension filter (`hensel_depth_test`).
4. Counterexample generators for Obstruction Theorems B1 (Pisano-period collision)
   and B2 (p-adic ghost-root truncation).
5. Integrated deterministic Bounded Skolem solver (`solve_bounded_skolem_deterministic`).
"""

from __future__ import annotations
import math
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from src.skolem_algorithm import (
    LinearRecurrenceSequence,
    is_identity_mod,
    is_prime,
    mat_mul_mod,
    mat_pow_mod,
    v_p,
)


# ============================================================================
# 1. Rigorous Dyadic Ball / Interval Arithmetic for Matrix Exponentiation
# ============================================================================

@dataclass(frozen=True)
class DyadicInterval:
    """
    Represents the closed real interval [lo * 2^exp, hi * 2^exp] where lo <= hi
    are Python arbitrary-precision integers and exp is an integer exponent.
    Truncation/rounding to `prec` bits always rounds `lo` toward -infinity
    (floor shift) and `hi` toward +infinity (ceiling shift), guaranteeing
    rigorous enclosure: exact_value in [lo * 2^exp, hi * 2^exp].
    """
    lo: int
    hi: int
    exp: int = 0

    @staticmethod
    def from_int(val: int, prec: int = 128) -> "DyadicInterval":
        return DyadicInterval(val, val, 0).normalize(prec)

    def normalize(self, prec: int) -> "DyadicInterval":
        if self.lo == 0 and self.hi == 0:
            return DyadicInterval(0, 0, 0)
        max_abs = max(abs(self.lo), abs(self.hi))
        bl = max_abs.bit_length()
        if bl <= prec:
            return self
        shift = bl - prec
        # Floor division for lo, ceiling division for hi
        new_lo = self.lo >> shift
        new_hi = -((-self.hi) >> shift)
        return DyadicInterval(new_lo, new_hi, self.exp + shift)

    def contains_zero(self) -> bool:
        return self.lo <= 0 <= self.hi

    def strictly_nonzero(self) -> bool:
        return self.lo > 0 or self.hi < 0

    def sign(self) -> Optional[int]:
        """Return +1 if strictly positive, -1 if strictly negative, 0 if [0,0], None if ambiguous."""
        if self.lo > 0:
            return 1
        if self.hi < 0:
            return -1
        if self.lo == 0 and self.hi == 0:
            return 0
        return None

    def add(self, other: "DyadicInterval", prec: int) -> "DyadicInterval":
        if self.lo == 0 and self.hi == 0:
            return other.normalize(prec)
        if other.lo == 0 and other.hi == 0:
            return self.normalize(prec)

        # Align exponents; if exponent difference is huge compared to prec, round the smaller term
        if self.exp >= other.exp:
            a, b = self, other
        else:
            a, b = other, self

        diff = a.exp - b.exp
        max_shift = prec + 16
        if diff > max_shift:
            reduce_by = diff - max_shift
            b = DyadicInterval(
                b.lo >> reduce_by,
                -((-b.hi) >> reduce_by),
                b.exp + reduce_by,
            )
            diff = a.exp - b.exp

        lo = (a.lo << diff) + b.lo
        hi = (a.hi << diff) + b.hi
        return DyadicInterval(lo, hi, b.exp).normalize(prec)

    def mul(self, other: "DyadicInterval", prec: int) -> "DyadicInterval":
        if (self.lo == 0 and self.hi == 0) or (other.lo == 0 and other.hi == 0):
            return DyadicInterval(0, 0, 0)
        p1 = self.lo * other.lo
        p2 = self.lo * other.hi
        p3 = self.hi * other.lo
        p4 = self.hi * other.hi
        lo = min(p1, p2, p3, p4)
        hi = max(p1, p2, p3, p4)
        return DyadicInterval(lo, hi, self.exp + other.exp).normalize(prec)


def interval_mat_mul(
    A: List[List[DyadicInterval]],
    B: List[List[DyadicInterval]],
    prec: int,
) -> List[List[DyadicInterval]]:
    d = len(A)
    m = len(B[0])
    k_len = len(B)
    zero = DyadicInterval(0, 0, 0)
    C = [[zero for _ in range(m)] for _ in range(d)]
    for i in range(d):
        for j in range(m):
            acc = zero
            for k in range(k_len):
                prod = A[i][k].mul(B[k][j], prec)
                acc = acc.add(prod, prec)
            C[i][j] = acc
    return C


def interval_mat_pow(
    A_int: List[List[int]],
    exp: int,
    prec: int,
) -> List[List[DyadicInterval]]:
    d = len(A_int)
    res = [
        [DyadicInterval.from_int(1 if i == j else 0, prec) for j in range(d)]
        for i in range(d)
    ]
    base = [
        [DyadicInterval.from_int(A_int[i][j], prec) for j in range(d)]
        for i in range(d)
    ]
    e = exp
    while e > 0:
        if e & 1:
            res = interval_mat_mul(res, base, prec)
        base = interval_mat_mul(base, base, prec)
        e >>= 1
    return res


def interval_eval_term(lrs: LinearRecurrenceSequence, n: int, prec: int) -> DyadicInterval:
    """
    Rigorous dyadic interval evaluation of u_n = alpha A^n beta using O(log n)
    matrix multiplications at `prec` bits of significand precision.
    """
    d = lrs.order
    A = lrs.companion_matrix()
    An = interval_mat_pow(A, n, prec)
    last_row = An[d - 1]
    acc = DyadicInterval(0, 0, 0)
    for j in range(d):
        init_iv = DyadicInterval.from_int(lrs.initial[d - 1 - j], prec)
        acc = acc.add(last_row[j].mul(init_iv, prec), prec)
    return acc


# ============================================================================
# 2. Deterministic Zero-Testing Filters (Lemmas 1 & 2 + Hensel Extension)
# ============================================================================

def single_prime_power_zero_test(
    lrs: LinearRecurrenceSequence,
    n: int,
    p: Optional[int] = None,
    nu: Optional[int] = None,
) -> bool:
    """
    Lemma 1 Test: Check whether u_n == 0 (mod p^nu).
    Returns True if u_n == 0 (mod p^nu) (candidate survives), False if certified non-zero.
    """
    if p is None:
        p = lrs.choose_prime()
    if nu is None:
        bit_size = sum(abs(c).bit_length() + 1 for c in lrs.coeffs + lrs.initial)
        log_n = max(2, n.bit_length())
        nu = (lrs.order ** 2) * bit_size * (log_n ** 2) + 8
    return lrs.term(n, mod=p ** nu) == 0


def hensel_depth_extension_test(
    lrs: LinearRecurrenceSequence,
    n: int,
    p: int,
    M: int,
    R: int,
    extra_steps: int = 4,
    nu_base: Optional[int] = None,
) -> bool:
    """
    Non-branching p-adic depth extension (Restriction 5 of notes/eqslp_structure.md):
    For candidate n = M*z + ell with 0 <= z < p^R, the integer z has base-p digits 0
    at all positions r >= R. Thus z lies in D(z, R + extra_steps) without any branching.
    Checks whether j(h_{z, R + extra_steps}) >= 1.
    Returns True if candidate still survives at depth R + extra_steps, False if certified non-zero.
    """
    ell = n % M
    z = n // M
    r_ext = R + extra_steps
    if nu_base is None:
        bit_size = sum(abs(c).bit_length() + 1 for c in lrs.coeffs + lrs.initial)
        nu = bit_size * M * lrs.order + r_ext * lrs.order + 6
    else:
        nu = nu_base + extra_steps * lrs.order + 2
    j_ext, _, _ = lrs.j_and_V_h(ell, M, p, z=z, r=r_ext, nu=nu)
    return j_ext >= 1


def multi_prime_modular_test(
    lrs: LinearRecurrenceSequence,
    n: int,
    num_primes: int = 8,
    prime_power_exp: int = 4,
) -> bool:
    """
    Deterministic auxiliary prime-power filter: tests u_n == 0 (mod q_i^prime_power_exp)
    for the first `num_primes` primes q_i >= d+2 not dividing a_0.
    Returns False as soon as any modulus witnesses u_n != 0.
    """
    q = lrs.order + 2
    checked = 0
    while checked < num_primes:
        if is_prime(q) and (lrs.a0 % q != 0):
            if lrs.term(n, mod=q ** prime_power_exp) != 0:
                return False
            checked += 1
        q += 1
    return True


def dyadic_interval_zero_test(
    lrs: LinearRecurrenceSequence,
    n: int,
    prec: Optional[int] = None,
) -> Optional[bool]:
    """
    Lemma 2 Test: Evaluate u_n = alpha A^n beta in rigorous dyadic interval arithmetic.
    Returns:
      - False if 0 is strictly outside the enclosing interval (certifies u_n != 0),
      - True if the enclosing interval has width < 1 (hence contains a unique integer, 0),
      - None if 0 is inside the interval of width >= 1 at precision `prec`.
    """
    if prec is None:
        bit_size = sum(abs(c).bit_length() + 1 for c in lrs.coeffs + lrs.initial)
        log_n = max(2, n.bit_length())
        prec = max(128, 4 * bit_size * (log_n ** 2))

    iv = interval_eval_term(lrs, n, prec)
    if iv.strictly_nonzero():
        return False
    # Check if the interval width is strictly less than 1 (which forces the integer u_n to be 0)
    if iv.exp >= 0:
        width_lt_1 = (iv.lo == 0 and iv.hi == 0)
    else:
        # Interval is [lo * 2^-k, hi * 2^-k]; if |lo| < 2^k and |hi| < 2^k, the only integer inside is 0
        k = -iv.exp
        width_lt_1 = (abs(iv.lo) < (1 << k)) and (abs(iv.hi) < (1 << k))
    if width_lt_1 and iv.contains_zero():
        return True
    return None


# ============================================================================
# 2B. Theorems 3 & 4: Coprime-Base Normalization, Root-Power Unit Polynomials,
#     and Factorization-Free D^nu / D_{<=2}^nu Modular Zero Testing
# ============================================================================

def integer_kth_root(x: int, k: int) -> Optional[int]:
    """If x >= 2 is a perfect k-th power r^k, return r; otherwise return None."""
    if k <= 1 or x < 2:
        return x
    lo, hi = 2, 1 << ((x.bit_length() + k - 1) // k)
    while lo <= hi:
        mid = (lo + hi) // 2
        val = mid ** k
        if val == x:
            return mid
        elif val < x:
            lo = mid + 1
        else:
            hi = mid - 1
    return None


def reduce_perfect_powers(x: int) -> int:
    """
    Deterministic polynomial-time root extraction:
    Replaces x >= 2 by the smallest integer r such that x = r^k for some k >= 1.
    """
    x = abs(x)
    if x < 2:
        return x
    max_k = x.bit_length()
    for k in range(max_k, 1, -1):
        r = integer_kth_root(x, k)
        if r is not None:
            return r
    return x


def coprime_base(nums: List[int]) -> List[int]:
    """
    Deterministic polynomial-time Root-Closed Coprime Base Algorithm (Bernstein 2005):
    Given a list of integers, returns a pairwise coprime list of non-power integers >= 2
    over which every nonzero input integer factors completely, using only
    gcd, exact integer division, and exact integer root extraction (no factoring!).
    """
    base: List[int] = []
    queue = [reduce_perfect_powers(abs(x)) for x in nums if abs(x) >= 2]
    while queue:
        x = reduce_perfect_powers(queue.pop())
        if x < 2:
            continue
        new_base: List[int] = []
        for b in base:
            g = math.gcd(x, b)
            if g == 1:
                new_base.append(b)
            else:
                g_red = reduce_perfect_powers(g)
                while x % g == 0:
                    x //= g
                x = strip_common_prime_factors(x, g_red)
                b_rem = strip_common_prime_factors(b, g_red)
                if b_rem >= 2:
                    queue.append(reduce_perfect_powers(b_rem))
                if g_red >= 2:
                    queue.append(g_red)
        base = new_base
        if x >= 2:
            base.append(reduce_perfect_powers(x))
    return sorted(set(base))


def exact_base_valuation(n: int, c: int) -> int:
    """Largest integer k >= 0 such that c^k divides n (returns 10^9 if n == 0)."""
    if n == 0:
        return 10**9
    n_abs = abs(n)
    k = 0
    while n_abs % c == 0:
        n_abs //= c
        k += 1
    return k


def normalize_newton_polygon_coeffs(b_desc: List[int]) -> Tuple[int, List[int]]:
    """
    Given [b_{d-1}, b_{d-2}, ..., b_0] for chi(x) = x^d + b_{d-1} x^{d-1} + ... + b_0,
    computes the exact coprime-base scalar
        S = prod_{c in B} c^{min_{1 <= r <= d} floor(v_c(b_{d-r}) / r)}
    and returns (S, [hat_b_{d-1}, ..., hat_b_0]) where hat_b_{d-r} = b_{d-r} // S^r.
    """
    d = len(b_desc)
    base = coprime_base(b_desc)
    S = 1
    for c in base:
        exp_c = min(exact_base_valuation(b_desc[r - 1], c) // r for r in range(1, d + 1))
        if exp_c > 0:
            S *= c ** exp_c
    hat_b = [b_desc[r - 1] // (S ** r) for r in range(1, d + 1)]
    return S, hat_b


def strip_common_prime_factors(a: int, b: int) -> int:
    """
    Factorization-free removal of all prime factors of b from a:
    repeatedly divides a by gcd(a, b) until gcd(a, b) == 1.
    """
    a = abs(a)
    b = abs(b)
    if a == 0 or b <= 1:
        return a
    while True:
        g = math.gcd(a, b)
        if g == 1:
            return a
        a //= g


def order3_global_local_dichotomy(b2: int, b1: int, b0: int) -> Dict[str, object]:
    """
    Theorem 3 Global-Local Dichotomy for Order-3 polynomial x^3 + b2 x^2 + b1 x + b0:
    1. Applies coprime-base slope normalization to obtain (S, [hat_b2, hat_b1, hat_b0]).
    2. Computes the Root-Cube Unit Polynomial P_xi(t) = t^3 - (3 + r1) t^2 + (3 + r2) t - 1
       where xi_i = hat_mu_i^3 / (-hat_b0):
         r1 = hat_b2 * (hat_b2^2 - 3 * hat_b1) / hat_b0 = N1 / D1,
         r2 = hat_b1 * (hat_b1^2 - 3 * hat_b0 * hat_b2) / hat_b0^2 = N2 / D2.
    3. Computes D = lcm(D1, D2) and D_{<=2} = strip_common_prime_factors(D, hat_b2 if hat_b1 == 0 else math.gcd(hat_b2, hat_b1)).
       - If D == 1: 'ARCHIMEDEAN_UNIT_BRANCH' (Smyth's theorem guarantees spectral gap >= (1/4) log(theta_0) > 0.0702997).
       - If D > 1: 'NON_ARCHIMEDEAN_NEWTON_BRANCH' (every prime q | D has k_q in {1, 2} dominant roots).
    """
    S, (hb2, hb1, hb0) = normalize_newton_polygon_coeffs([b2, b1, b0])
    num1 = hb2 * (hb2 * hb2 - 3 * hb1)
    den1 = abs(hb0)
    g1 = math.gcd(abs(num1), den1)
    D1 = den1 // g1

    num2 = hb1 * (hb1 * hb1 - 3 * hb0 * hb2)
    den2 = hb0 * hb0
    g2 = math.gcd(abs(num2), den2)
    D2 = den2 // g2

    D = math.lcm(D1, D2)
    # Strip any residual factor shared with gcd(hb2, hb1) so v_q(hat_mu_1) = 0 for all q | D_unit
    D_unit = reduce_perfect_powers(strip_common_prime_factors(D, math.gcd(abs(hb2), abs(hb1))))
    branch = "ARCHIMEDEAN_UNIT_BRANCH" if D == 1 else "NON_ARCHIMEDEAN_NEWTON_BRANCH"
    return {
        "S": S,
        "normalized_coeffs": (hb2, hb1, hb0),
        "r1_num_den": (num1 // g1 if hb0 > 0 else -num1 // g1, D1),
        "r2_num_den": (num2 // g2, D2),
        "D": D,
        "D_unit": D_unit,
        "branch": branch,
        "smyth_lower_bound_gap": 0.0702997 if D == 1 else None,
    }


def order4_global_local_dichotomy(b3: int, b2: int, b1: int, b0: int) -> Dict[str, object]:
    """
    Theorem 4 Global-Local Dichotomy for Order-4 polynomial x^4 + b3 x^3 + b2 x^2 + b1 x + b0:
    1. Applies coprime-base slope normalization to obtain (S, [hb3, hb2, hb1, hb0]).
    2. Computes the 4th-power symmetric sums p_4(hb) and p_4(hb^{-1}) to form
       P_xi(t) = prod_{i=1}^4 (t - hat_mu_i^4 / hb0) = t^4 + r3 t^3 + r2 t^2 + r1 t + 1
       and its exact denominator D = lcm(denom(r3), denom(r2), denom(r1)).
    3. Computes the factorization-free slope-<=2 modulus:
       D_{<=2} = strip_common_prime_factors(gcd(hb0, hb1), gcd(hb2, hb3)).
       Every prime q | D_{<=2} has Newton polygon horizontal slope-0 length k_q in {1, 2}.
    """
    S, (hb3, hb2, hb1, hb0) = normalize_newton_polygon_coeffs([b3, b2, b1, b0])
    # Newton power sums for x^4 + hb3 x^3 + hb2 x^2 + hb1 x + hb0 = 0:
    # e1 = -hb3, e2 = hb2, e3 = -hb1, e4 = hb0
    e1, e2, e3, e4 = -hb3, hb2, -hb1, hb0
    p1 = e1
    p2 = e1 * p1 - 2 * e2
    p3 = e1 * p2 - e2 * p1 + 3 * e3
    p4 = e1 * p3 - e2 * p2 + e3 * p1 - 4 * e4
    # Sum of (mu_i * mu_j)^4 = (p4^2 - sum mu_i^8) / 2, or via e2(xi)
    # Using reciprocal roots mu_i^{-1} (whose e1' = -hb1/hb0, e2' = hb2/hb0, e3' = -hb3/hb0, e4' = 1/hb0):
    # e4 * sum(mu_i^{-4}):
    q1 = -hb1
    q2 = q1 * (-hb1) - 2 * hb2 * hb0
    q3 = (-hb1) * q2 - hb2 * hb0 * q1 - 3 * hb3 * (hb0 ** 2)
    q4 = (-hb1) * q3 - hb2 * hb0 * q2 - hb3 * (hb0 ** 2) * q1 - 4 * (hb0 ** 3)

    # r3 = -p4 / hb0, r1 = -q4 / hb0^3, and for r2 = sum_{i<j} mu_i^4 mu_j^4 / hb0^2:
    # Notice e2(mu^2) = hb2^2 - 2 hb1 hb3 + 2 hb0, e1(mu^2) = hb3^2 - 2 hb2, e3(mu^2) = hb1^2 - 2 hb0 hb2
    s2 = hb2 * hb2 - 2 * hb1 * hb3 + 2 * hb0
    s1 = hb3 * hb3 - 2 * hb2
    s3 = hb1 * hb1 - 2 * hb0 * hb2
    sum_mu4_pair = s2 * s2 - 2 * s1 * s3 + 2 * (hb0 * hb0)

    D3 = abs(hb0) // math.gcd(abs(p4), abs(hb0))
    D2 = (hb0 * hb0) // math.gcd(abs(sum_mu4_pair), hb0 * hb0)
    D1 = abs(hb0 ** 3) // math.gcd(abs(q4), abs(hb0 ** 3))
    D = math.lcm(D1, D2, D3)

    D_le_2 = strip_common_prime_factors(math.gcd(abs(hb0), abs(hb1)), math.gcd(abs(hb2), abs(hb3)))
    if D == 1:
        branch = "ARCHIMEDEAN_UNIT_BRANCH"
    elif D_le_2 > 1:
        branch = "NON_ARCHIMEDEAN_SLOPE_LE_2_BRANCH"
    else:
        branch = "NON_ARCHIMEDEAN_SLOPE_EQ_3_BRANCH"

    return {
        "S": S,
        "normalized_coeffs": (hb3, hb2, hb1, hb0),
        "D": D,
        "D_le_2": D_le_2,
        "branch": branch,
        "smyth_lower_bound_gap": 0.023433 if D == 1 else None,
    }


def factorization_free_D_nu_zero_test(
    lrs: LinearRecurrenceSequence,
    n: int,
) -> Optional[bool]:
    """
    Theorems 3 & 4 Factorization-Free D^nu / D_{<=2}^nu Modular Zero Test:
    For an Order-3 or Order-4 LRS in the non-Archimedean Newton-polygon branch
    (D_unit > 1 for Order 3, or D_{<=2} > 1 for Order 4), tests
        u_n == 0 (mod M_mod^nu)
    where M_mod = D_unit (Order 3) or D_{<=2} (Order 4) and nu = poly(||u||, log n).
    Returns False if u_n != 0 (mod M_mod^nu) (certifying u_n != 0 without factoring!).
    """
    d = lrs.order
    if d == 3:
        # chi_A(x) = x^3 - c2 x^2 - c1 x - c0 => b2 = -c2, b1 = -c1, b0 = -c0
        b2, b1, b0 = -lrs.coeffs[2], -lrs.coeffs[1], -lrs.coeffs[0]
        info = order3_global_local_dichotomy(b2, b1, b0)
        M_mod = int(info["D_unit"])
    elif d == 4:
        b3, b2, b1, b0 = -lrs.coeffs[3], -lrs.coeffs[2], -lrs.coeffs[1], -lrs.coeffs[0]
        info = order4_global_local_dichotomy(b3, b2, b1, b0)
        M_mod = int(info["D_le_2"])
    else:
        return None

    if M_mod <= 1:
        return None

    bit_size = sum(abs(c).bit_length() + 1 for c in lrs.coeffs + lrs.initial)
    log_n = max(2, n.bit_length())
    nu = max(8, 2 * bit_size * log_n)
    modulus = M_mod ** nu
    if lrs.term(n, mod=modulus) != 0:
        return False
    return True


def e2_large_prime_rejection_filter(
    lrs: LinearRecurrenceSequence,
    n: int,
    q: Optional[int] = None,
    m_prec: int = 1,
) -> Optional[bool]:
    """
    Route E2 Sound Large-Prime Rejection Filter (§4.6.4):
    Given a ZeroSearch candidate index `n`, evaluates the slope-normalized sequence `z_n`
    modulo `q^{m_prec}` (where `q` defaults to `D_unit` at order 3 or `D_{<=2}` at order 4).
      - Returns `False` (certifying `u_n != 0`) when `z_n != 0 (mod q^{m_prec})`.
      - Returns `None` (unresolved by the filter alone) when `z_n == 0 (mod q^{m_prec})`.
    """
    _, z_lrs = slope_normalize_lrs(lrs)
    if q is None:
        d = z_lrs.order
        if d == 3:
            b2, b1, b0 = -z_lrs.coeffs[2], -z_lrs.coeffs[1], -z_lrs.coeffs[0]
            q = int(order3_global_local_dichotomy(b2, b1, b0)["D_unit"])
        elif d == 4:
            b3, b2, b1, b0 = -z_lrs.coeffs[3], -z_lrs.coeffs[2], -z_lrs.coeffs[1], -z_lrs.coeffs[0]
            q = int(order4_global_local_dichotomy(b3, b2, b1, b0)["D_le_2"])
        else:
            return None
    if q is None or q <= 1:
        return None
    modulus = q ** max(1, m_prec)
    if z_lrs.term(n, mod=modulus) != 0:
        return False
    return None


def e2_odd_order_trace_certificate(
    lrs: LinearRecurrenceSequence,
    q: int,
) -> Optional[Dict[str, int]]:
    """
    Route E2 Reusable Odd-Order Residual Ratio Certificate for Trace-Like Sequences (§4.6.4):
    For an order-3 LRS with prime `q | b_0` and `gcd(b_1, q) = 1`:
      chi(x) = x^3 + b_2 x^2 + b_1 x + b_0 == x (x^2 + b_2 x + b_1) (mod q).
    If `x^2 + b_2 x + b_1 == (x - a)(x - b) (mod q)` splits into distinct nonzero roots `a, b (mod q)`,
    `u_1 == a + b (mod q)` and `u_2 == a^2 + b^2 (mod q)` (so `u_n == a^n + b^n (mod q)` for all `n >= 1`),
    and the residual root ratio `xi = a * b^{-1} (mod q)` satisfies
      xi^{m_odd} == 1 (mod q),   where m_odd = (q - 1) / 2^{v_2(q - 1)} is the odd part of q - 1,
    then `ord_q(xi)` divides `m_odd` and is therefore ODD, so `xi^n != -1 (mod q)` and
    `u_n == b^n (xi^n + 1) != 0 (mod q)` for every `n >= 1`!
    This check runs in O((log q)^3) time without factoring `q - 1` or enumerating powers.
    """
    if lrs.order != 3 or q <= 2 or q % 2 == 0:
        return None
    b2, b1, b0 = -lrs.coeffs[2], -lrs.coeffs[1], -lrs.coeffs[0]
    if b0 % q != 0 or math.gcd(b1, q) != 1:
        return None
    # Check initial state matches u_n == a^n + b^n (mod q) for n = 1, 2:
    # a + b == -b2 (mod q), a^2 + b^2 == b2^2 - 2*b1 (mod q)
    if (lrs.initial[1] - (-b2)) % q != 0:
        return None
    if (lrs.initial[2] - (b2 * b2 - 2 * b1)) % q != 0:
        return None
    disc = (b2 * b2 - 4 * b1) % q
    if disc == 0 or pow(disc, (q - 1) // 2, q) != 1:
        return None
    # Tonelli-Shanks square root of disc mod q
    Q_ts, S_ts = q - 1, 0
    while Q_ts % 2 == 0:
        Q_ts //= 2
        S_ts += 1
    z_nr = 2
    while pow(z_nr, (q - 1) // 2, q) != q - 1:
        z_nr += 1
    M_ts = S_ts
    c_ts = pow(z_nr, Q_ts, q)
    t_ts = pow(disc, Q_ts, q)
    R_ts = pow(disc, (Q_ts + 1) // 2, q)
    while t_ts != 1:
        i_ts = 1
        temp = (t_ts * t_ts) % q
        while temp != 1:
            temp = (temp * temp) % q
            i_ts += 1
        b_ts = pow(c_ts, 1 << (M_ts - i_ts - 1), q)
        M_ts = i_ts
        c_ts = (b_ts * b_ts) % q
        t_ts = (t_ts * c_ts) % q
        R_ts = (R_ts * b_ts) % q
    inv2 = (q + 1) // 2
    a_root = ((-b2 + R_ts) * inv2) % q
    b_root = ((-b2 - R_ts) * inv2) % q
    if a_root == 0 or b_root == 0:
        return None
    xi = (a_root * pow(b_root, -1, q)) % q
    # Odd part of q - 1 is Q_ts:
    m_odd = Q_ts
    if pow(xi, m_odd, q) != 1:
        return None
    return {
        "q": q,
        "a": a_root,
        "b": b_root,
        "xi": xi,
        "m_odd": m_odd,
        "u0_mod_q": lrs.initial[0] % q,
    }


def _lift_root_near_zero_and_quadratic_quotient(
    b2: int, b1: int, b0: int, q: int, K: int
) -> Optional[Tuple[int, int, int]]:
    """
    For g(x) = x^3 + b2 x^2 + b1 x + b0 with q | b0 and gcd(b1, q) = 1:
    Hensel-lifts the simple root r == 0 (mod q) to precision mod = q^K and factors
      g(x) == (x - r)(x^2 + a x + b) (mod q^K),
    returning `(r, a, b)` modulo `q^K`.
    """
    if K < 1 or q <= 2 or b0 % q != 0 or math.gcd(b1, q) != 1:
        return None
    mod = q ** K
    r = 0
    cur_prec = 1
    while cur_prec < K:
        cur_prec = min(K, cur_prec * 2)
        cur_mod = q ** cur_prec
        g_val = (r * r * r + b2 * r * r + b1 * r + b0) % cur_mod
        gp_val = (3 * r * r + 2 * b2 * r + b1) % cur_mod
        r = (r - g_val * pow(gp_val, -1, cur_mod)) % cur_mod
    a = (b2 + r) % mod
    b = (b1 + a * r) % mod
    return r, a, b


def _quad_quotient_pow(
    c0: int, c1: int, exp: int, a: int, b: int, mod: int
) -> Tuple[int, int]:
    """
    Compute `(c0 + c1 X)^exp` in `(Z/mod Z)[X] / (X^2 + a X + b)`.
    Since X^2 == -b - a X:
      (u0 + u1 X)(v0 + v1 X) = (u0 v0 - b u1 v1) + (u0 v1 + u1 v0 - a u1 v1) X.
    """
    r0, r1 = 1 % mod, 0
    u0, u1 = c0 % mod, c1 % mod
    e = exp
    while e > 0:
        if e & 1:
            nr0 = (r0 * u0 - b * r1 * u1) % mod
            nr1 = (r0 * u1 + r1 * u0 - a * r1 * u1) % mod
            r0, r1 = nr0, nr1
        nu0 = (u0 * u0 - b * u1 * u1) % mod
        nu1 = (2 * u0 * u1 - a * u1 * u1) % mod
        u0, u1 = nu0, nu1
        e >>= 1
    return r0, r1


def compute_m0_without_factoring(
    b2: int, b1: int, b0: int, q: int, K: int = 6
) -> Optional[Dict[str, object]]:
    """
    Route E2 Factorization-Free Computation of `m_0 = v_q(xi^T - 1)` (§4.6.5, Eq. 12):
    In `A_K = (Z/q^K Z)[X] / (X^2 + a X + b)`, the two unit roots are `X` and `-a - X`
    with product `b`, so their ratio is represented by
      xi = X / (-a - X) = X^2 / b == -1 - (a * b^{-1}) X (mod q^K).
    Because `T = ord(bar(xi))` divides `E = q^2 - 1` and `q ∤ (q^2 - 1)/T`, Eq. (2) gives
      v_q(xi^{q^2 - 1} - 1) = m_0
    up to precision `K`, without factoring `q - 1` or `q + 1` and without computing `T`!
    Returns `{'q': q, 'K': K, 'm0': m0, 'exact': m0 < K, 'xi_coeff': (xi0, xi1)}`.
    """
    lifted = _lift_root_near_zero_and_quadratic_quotient(b2, b1, b0, q, K)
    if lifted is None:
        return None
    r, a, b = lifted
    mod = q ** K
    if math.gcd(b, q) != 1:
        return None
    b_inv = pow(b, -1, mod)
    xi0 = (-1) % mod
    xi1 = (-a * b_inv) % mod
    E = q * q - 1
    p0, p1 = _quad_quotient_pow(xi0, xi1, E, a, b, mod)
    d0 = (p0 - 1) % mod
    d1 = p1 % mod
    m0 = min(v_p(d0, q, K), v_p(d1, q, K))
    return {
        "q": q,
        "K": K,
        "m0": m0,
        "exact": m0 < K,
        "r_mod_qK": r,
        "xi_coeff": (xi0, xi1),
    }


def e2_cached_collision_reject(
    b2: int,
    b1: int,
    b0: int,
    q: int,
    m_prec: int,
    n_old: int,
    n_new: int,
) -> Optional[bool]:
    """
    Route E2 Cached Candidate Rejection Rule (§4.6.5, Eq. 13):
    Suppose candidate `n_old` has already passed modulo `q^{m_prec}` (`q^{m_prec} | u_{n_old}`)
    with `1 <= m_prec <= min(n_old, n_new)` and unit Binet coefficients `c_1, c_2` at `q`.
    For a later candidate `n_new > n_old`, computes `xi^{n_new - n_old} - 1` in
    `A_{m_prec} = (Z/q^{m_prec} Z)[X] / (X^2 + a X + b)` in `O(log(n_new - n_old))` operations
    **without evaluating `u_{n_new}`**.
      - Returns `False` (certifying `u_{n_new} != 0`) if `xi^{n_new - n_old} != 1 (mod q^{m_prec})`.
      - Returns `None` if `xi^{n_new - n_old} == 1 (mod q^{m_prec})`.
    """
    if m_prec < 1 or n_new <= n_old or m_prec > min(n_old, n_new):
        return None
    lifted = _lift_root_near_zero_and_quadratic_quotient(b2, b1, b0, q, m_prec)
    if lifted is None:
        return None
    _, a, b = lifted
    mod = q ** m_prec
    b_inv = pow(b, -1, mod)
    xi0 = (-1) % mod
    xi1 = (-a * b_inv) % mod
    delta = n_new - n_old
    p0, p1 = _quad_quotient_pow(xi0, xi1, delta, a, b, mod)
    if (p0 - 1) % mod != 0 or p1 % mod != 0:
        return False
    return None


def deterministic_candidate_zero_test(
    lrs: LinearRecurrenceSequence,
    n: int,
    p: int,
    M: int,
    R: int,
    exact_threshold: int = 2000,
) -> bool:
    """
    Combined deterministic zero test for a candidate index n = M*z + ell produced by ZeroSearch:
    1. If n <= exact_threshold, evaluate u_n exactly.
    2. Run unconditional unit-root zero-bound test (Theorems 5 & 6, k_q = 1, Lean-verified).
    3. Run Route E2 sound large-prime rejection filter (z_n mod D_unit / D_{<=2}).
    4. Run non-branching p-adic Hensel depth extension (r = R + 3).
    5. Run dyadic interval matrix exponentiation (Lemma 2 & Archimedean Branch of Theorems 3-4).
    6. Run heuristic D^nu / D_{<=2}^nu modular check + multi-prime / single-prime-power checks.
    """
    if n <= exact_threshold:
        return lrs.term(n) == 0

    ur_verdict = unit_root_zero_bound_test(lrs, n)
    if ur_verdict is not None:
        return ur_verdict

    if e2_large_prime_rejection_filter(lrs, n) is False:
        return False

    if not hensel_depth_extension_test(lrs, n, p, M, R, extra_steps=3):
        return False

    iv_verdict = dyadic_interval_zero_test(lrs, n)
    if iv_verdict is not None:
        return iv_verdict

    d_nu_verdict = factorization_free_D_nu_zero_test(lrs, n)
    if d_nu_verdict is False:
        return False

    if not multi_prime_modular_test(lrs, n, num_primes=8, prime_power_exp=4):
        return False

    return single_prime_power_zero_test(lrs, n, p=p)


def solve_bounded_skolem_deterministic(
    lrs: LinearRecurrenceSequence,
    N: int,
) -> Tuple[List[Tuple[int, int]], List[int], List[int]]:
    """
    Deterministic Bounded Skolem solver:
    1. Runs deterministic Stage 1 (`ZeroSearch`) to obtain APs and <= (d-1)M candidates.
    2. Applies `deterministic_candidate_zero_test` to each candidate.
    Returns (APs, raw_candidates, verified_zeros).
    """
    p = lrs.choose_prime()
    M = lrs.find_period_M(p)
    R = max(1, math.ceil(math.log(max(N, 2), p)))
    APs, candidates = lrs.find_candidate_zeros(N=N, p=p, M=M)
    verified = [
        n for n in candidates
        if deterministic_candidate_zero_test(lrs, n, p=p, M=M, R=R)
    ]
    return APs, candidates, verified


# ============================================================================
# 3. Counterexample Generators (Obstruction Theorems B1 & B2)
# ============================================================================

def construct_pisano_counterexample(
    lrs: LinearRecurrenceSequence,
    moduli: List[int],
) -> Dict[str, object]:
    """
    Obstruction Theorem B1:
    Given an LRS with u_0 = 0 (and u_n != 0 for n >= 1) and a finite set of moduli S
    coprime to a_0, computes the explicit binary index
        n* = lcm_{m in S} ord_{GL_d(Z/mZ)}(A)
    and verifies that:
      - u_{n*} == 0 (mod m) for every m in S,
      - u_{n*} != 0 (certified by dyadic interval matrix exponentiation).
    """
    if lrs.term(0) != 0:
        raise ValueError("Obstruction B1 requires u_0 = 0.")

    A = lrs.companion_matrix()
    orders: Dict[int, int] = {}
    for m in moduli:
        if math.gcd(lrs.a0, m) != 1:
            raise ValueError(f"Modulus {m} is not coprime to a_0 = {lrs.a0}.")
        cur = [[x % m for x in row] for row in A]
        limit = m ** (lrs.order ** 2)
        for k in range(1, limit + 1):
            if is_identity_mod(cur, m):
                orders[m] = k
                break
            cur = mat_mul_mod(cur, A, m)
        else:
            raise RuntimeError(f"Failed to find matrix order mod {m}")

    n_star = 1
    for r_m in orders.values():
        n_star = math.lcm(n_star, r_m)

    residues = {m: lrs.term(n_star, mod=m) for m in moduli}
    iv = interval_eval_term(lrs, n_star, prec=128)

    return {
        "moduli": moduli,
        "orders": orders,
        "n_star": n_star,
        "n_star_bits": n_star.bit_length(),
        "moduli_total_bits": sum(m.bit_length() for m in moduli),
        "residues": residues,
        "all_residues_zero": all(r == 0 for r in residues.values()),
        "interval_strictly_nonzero": iv.strictly_nonzero(),
        "interval": iv,
    }


def construct_ghost_root_counterexamples(
    max_depth: int = 8,
) -> List[Dict[str, object]]:
    """
    Obstruction Theorem B2:
    Traces the unique 5-adic ghost root x_0 in Z_5 \\ Z of F_3(n) = u_{8n+3}
    in the SODA 2026 order-3 recurrence:
        u_{n+3} = 2 u_{n+2} - 3 u_{n+1} + u_n,  u_0 = -1, u_1 = 1, u_2 = 7
    across depths R = 1, ..., max_depth.
    At each depth R, returns the false candidate n_R = 8 z_R + 3, its 5-adic valuation
    v_5(u_{n_R}) >= R + 1, and verifies that both Lemma 2 (dyadic interval test)
    and Hensel depth extension deterministically reject n_R.
    """
    lrs = LinearRecurrenceSequence(coeffs=[1, -3, 2], initial=[-1, 1, 7])
    p = 5
    M = 8
    ell = 3
    nu = max_depth + 10

    # Lift the unique root z_R of F_3 mod 5^R using ZeroSearch on ell = 3
    results: List[Dict[str, object]] = []
    for R in range(1, max_depth + 1):
        N_R = M * (p ** R)
        z_cands = lrs.zero_search_subsequence(ell=ell, M=M, p=p, N=N_R, nu=nu)
        assert len(z_cands) == 1, f"Expected unique 5-adic root at depth {R}, got {z_cands}"
        z_R = z_cands[0]
        n_R = M * z_R + ell
        u_mod_p_nu = lrs.term(n_R, mod=p ** nu)
        val_5 = v_p(u_mod_p_nu, p, nu)
        iv = interval_eval_term(lrs, n_R, prec=128)
        results.append({
            "R": R,
            "z_R": z_R,
            "digit_R_minus_1": (z_R // (p ** (R - 1))) % p,
            "n_R": n_R,
            "v_5_u_nR": val_5,
            "divisible_by_5_pow_R_plus_1": val_5 >= R + 1,
            "interval_certifies_nonzero": iv.strictly_nonzero(),
        })
    return results


# ============================================================================
# 7. Theorems 5 & 6: Unconditional Unit-Root (k_q = 1) Zero Bounds
#    (mirrors Skolem/UnitRootDominance.lean)
# ============================================================================

def _char_poly_low_coeffs(lrs: LinearRecurrenceSequence) -> List[int]:
    """
    For u_{n+d} = a_{d-1} u_{n+d-1} + ... + a_0 u_n, return [b_0, ..., b_{d-1}] with
    chi(x) = x^d + b_{d-1} x^{d-1} + ... + b_0, i.e. b_i = -a_i.
    """
    return [-a for a in lrs.coeffs]


def unit_root_modulus(lrs: LinearRecurrenceSequence) -> int:
    """
    Factorization-free k_q = 1 modulus:
        q = Strip(gcd(b_0, ..., b_{d-2}), b_{d-1}),
    the largest divisor of gcd(b_0, ..., b_{d-2}) coprime to b_{d-1}.
    Every prime factor of q sees exactly one q-adic unit root (Newton polygon slope-0
    segment of length 1). Returns 1 if no such modulus exists.
    """
    b = _char_poly_low_coeffs(lrs)
    g = 0
    for bi in b[:-1]:
        g = math.gcd(g, abs(bi))
    if g == 0:
        return 1
    return strip_common_prime_factors(g, b[-1]) if b[-1] != 0 else 1


def _poly_eval_mod(coeffs_low: List[int], x: int, mod: int) -> int:
    """Evaluate monic x^d + sum_{i<d} c_i x^i modulo mod (coeffs_low = [c_0..c_{d-1}])."""
    acc = 1
    for c in reversed(coeffs_low):
        acc = (acc * x + c) % mod
    return acc


def _poly_deriv_eval_mod(coeffs_low: List[int], x: int, mod: int) -> int:
    d = len(coeffs_low)
    full = coeffs_low + [1]  # full[i] = coefficient of x^i
    acc = 0
    for i in range(d, 0, -1):
        acc = (acc * x + i * full[i]) % mod
    return acc


def unit_root_certificate(
    lrs: LinearRecurrenceSequence,
    q: Optional[int] = None,
    max_m: int = 256,
) -> Optional[Dict[str, object]]:
    """
    Compute the certificate consumed by `order3_unit_root_zero_bound` /
    `order4_unit_root_zero_bound` in Skolem/UnitRootDominance.lean:

        chi(x) == (x - mu) * (x^{d-1} + s_{d-2} x^{d-2} + ... + s_0)   (mod q^(m+1)),
        q | s_i,  gcd(mu, q) = 1,  q^m || w0 = u_{d-1} + sum_i s_i u_i.

    mu is obtained by Newton/Hensel lifting of the simple root mu_0 = -b_{d-1} (mod q);
    this works for composite q without factoring because chi'(mu_0) == mu_0^{d-1} (mod q)
    is a unit. Conclusion of the theorem: q^(m+1) does not divide u_k (so u_k != 0) for
    every k >= (d-1)(m+1).

    Returns None if q <= 1, or if q^(max_m+1) | w0 (the q-adic unit root is inactive
    to the tested precision, i.e. c_1 == 0 or v_q(c_1) > max_m).
    """
    d = lrs.order
    b = _char_poly_low_coeffs(lrs)
    if q is None:
        q = unit_root_modulus(lrs)
    q = abs(q)
    if q <= 1 or math.gcd(b[-1], q) != 1 or any(bi % q != 0 for bi in b[:-1]):
        return None

    mu = (-b[-1]) % q
    for M in range(1, max_m + 2):
        Q = q ** M
        # Newton lifting of mu to a root of chi modulo Q.
        mu %= Q
        for _ in range(4 * M.bit_length() + 8):
            fv = _poly_eval_mod(b, mu, Q)
            if fv == 0:
                break
            dv = _poly_deriv_eval_mod(b, mu, Q)
            mu = (mu - fv * pow(dv, -1, Q)) % Q
        if _poly_eval_mod(b, mu, Q) != 0:
            return None
        # Synthetic division chi(x) = (x - mu) g(x) + rem: g = x^{d-1} + s_{d-2} x^{d-2} + ... + s_0
        s = [0] * (d - 1)
        carry = 1
        for i in range(d - 2, -1, -1):
            carry = (b[i + 1] + mu * carry) % Q
            s[i] = carry
        w0 = lrs.initial[d - 1] + sum(s[i] * lrs.initial[i] for i in range(d - 1))
        if w0 % Q != 0:
            m = M - 1
            cert = {
                "q": q,
                "m": m,
                "mu": mu,
                "s": s,
                "w0": w0,
                "zero_bound": (d - 1) * (m + 1),
            }
            if not check_unit_root_certificate(lrs, cert):
                return None
            return cert
    return None


def check_unit_root_certificate(lrs: LinearRecurrenceSequence, cert: Dict[str, object]) -> bool:
    """
    Check exactly the hypotheses of the Lean theorems (Theorem 5 / Theorem 6):
      - q^(m+1) divides every coefficient of chi(x) - (x - mu) g(x),
      - q | s_i for all i, gcd(mu, q) = 1,
      - q^m | w0 and q^(m+1) does not divide w0.
    """
    d = lrs.order
    b = _char_poly_low_coeffs(lrs)
    q, m, mu, s = int(cert["q"]), int(cert["m"]), int(cert["mu"]), list(cert["s"])
    Q = q ** (m + 1)
    g = s + [1]  # g[i] = coefficient of x^i, degree d-1
    # (x - mu) g(x): coefficient of x^i is g[i-1] - mu g[i]
    prod = [(g[i - 1] if i >= 1 else 0) - mu * (g[i] if i < d else 0) for i in range(d)]
    if any((b[i] - prod[i]) % Q != 0 for i in range(d)):
        return False
    if any(si % q != 0 for si in s) or math.gcd(mu, q) != 1:
        return False
    w0 = lrs.initial[d - 1] + sum(s[i] * lrs.initial[i] for i in range(d - 1))
    return w0 % (q ** m) == 0 and w0 % Q != 0


def slope_normalize_lrs(lrs: LinearRecurrenceSequence) -> Tuple[int, LinearRecurrenceSequence]:
    """
    Section 4.1 / `order3_slope_normalization_scaling`:
    Given u_{n+d} = a_{d-1} u_{n+d-1} + ... + a_0 u_n (with b_i = -a_i),
    computes the coprime-base slope scalar S and the normalized integer sequence
        z_k = S^{d-1-k} u_k
    satisfying z_{k+d} = sum_i hat_a_i z_{k+i} (hat_b_{d-r} = b_{d-r} // S^r)
    with initial values z_j = S^{d-1-j} u_j for 0 <= j < d.
    Since S != 0, S^{d-1} u_k = S^k z_k implies u_k == 0 iff z_k == 0 for all k >= 0.
    """
    d = lrs.order
    b_low = _char_poly_low_coeffs(lrs)  # [b_0, ..., b_{d-1}]
    b_desc = list(reversed(b_low))      # [b_{d-1}, ..., b_0]
    S, hat_b_desc = normalize_newton_polygon_coeffs(b_desc)
    if S <= 1:
        return 1, lrs
    hat_b_low = list(reversed(hat_b_desc))
    hat_coeffs = [-hb for hb in hat_b_low]
    hat_initial = [(S ** (d - 1 - j)) * lrs.initial[j] for j in range(d)]
    return S, LinearRecurrenceSequence(coeffs=hat_coeffs, initial=hat_initial)


def unit_root_zero_bound_test(lrs: LinearRecurrenceSequence, n: int) -> Optional[bool]:
    """
    Deterministic zero test via Theorems 5/6 (and `order3_normalized_unit_root_zero_bound`):
    if a k_q = 1 certificate exists on `lrs` or on its slope-normalized sequence `z`,
    then u_n != 0 for n >= zero_bound, and for n < zero_bound we evaluate u_n exactly
    (zero_bound is polynomial in the input size, so u_n has polynomially many bits).
    Returns True iff u_n == 0, or None if no certificate is available.
    """
    cert = unit_root_certificate(lrs)
    if cert is None:
        S, z_lrs = slope_normalize_lrs(lrs)
        if S > 1:
            cert = unit_root_certificate(z_lrs)
    if cert is None:
        return None
    if n >= int(cert["zero_bound"]):
        return False
    return lrs.term(n) == 0

# Project Plan — Deterministic Skolem at Orders ≤ 4

_Last updated: 2026-11-08 (after commit `043a651`)._

The original brief is in [`idea.txt`](idea.txt). This file tracks **where we are** and **what comes next**.

## Goal

> Can Skolem for integer linear recurrences of order ≤ 4 be solved in **deterministic** polynomial time?

Bacik–Ouaknine–Worrell (SODA 2026, arXiv:2507.11234) place the problem in coRP. Randomness enters only when `ZeroSearch` checks its polynomially many candidates `u_n = αAⁿβ` (via EqSLP).

**Current strategy.** Avoid general EqSLP. Prove explicit **polynomial bounds on the largest zero** for as many root configurations as possible. A candidate `n` beyond the bound is then nonzero. Below the bound, `u_n` has polynomially many bits and is evaluated exactly. See [`notes/deterministic_zero_testing.md`](notes/deterministic_zero_testing.md), Part IV.

---

## Status of the four first-pass outputs (`idea.txt` §2)

| # | Output | Status | Where |
|---|---|---|---|
| 1 | Exact description of the arithmetic expressions produced by the algorithm | ✅ Done | `notes/eqslp_structure.md`, `notes/dependency_graph.md` |
| 2 | Reproduce the published algorithm on its examples | ✅ Done | `src/skolem_algorithm.py`, `experiments/reproduce_soda2026.py` |
| 3 | A candidate deterministic zero-testing lemma for a specified subclass | ✅ Done (several) | Notes Parts I and IV; `src/deterministic_zero_test.py` |
| 4 | Proof or counterexample for each candidate | ✅ Done | Obstructions B1/B2 (Part II); Theorems 5/6 proved in Lean |

## Results by status

| Branch / result | Status | Artifact |
|---|---|---|
| SODA 2026 structure: Mahler expansion, Thm 2.5, `ZeroSearch` lemmas, Skolem–Mahler–Lech decomposition | **Lean** (no `sorry`) | `Skolem/LRS.lean`, `Mahler.lean`, `ZeroSearch.lean` |
| Obstruction B1 (Pisano period) and B2 ($p$-adic ghost root), with concrete instances | **Lean** (`decide`) | `Skolem/DeterministicZeroTest.lean` |
| **Theorems 5/6 & General Order-$d$: unit-root branch $k_q = 1 \implies u_k \ne 0$ for $k \ge (d-1)(m+1)$**; works for composite $q$ and transfers across slope normalization $S^2 v_k = S^k z_k$ | **Lean, no external hypotheses** | `Skolem/UnitRootDominance.lean` (`order3_unit_root_zero_bound`, `order4_unit_root_zero_bound`, `order_d_unit_root_zero_bound`, `order3_slope_normalization_scaling`, `order3_normalized_unit_root_zero_bound`) |
| Lemma 1 ($\le 2$ distinct roots) | **Paper** (Weil height + Yu); **Lean** wrapper takes the height/Yu bound as hypothesis | Notes Part I; `Skolem/DeterministicZeroTest.lean` |
| Lemma 2 (interval arithmetic, MSTV separation) | **Paper** (Baker); **Lean** has the dyadic interval certification step | Notes Part I; `Skolem/DeterministicZeroTest.lean` |
| Order 3, $D = 1$ (unit branch): polynomial zero bound | **Paper** (Smyth + two-log Baker); **Lean** has the formal deduction from Baker + gap (`archimedean_gap_zero_bound`, `order3_unit_branch_smyth_baker_zero_bound`) | Notes §4.3; `Skolem/DeterministicZeroTest.lean` |
| Order 4, $D = 1$, largest gap at $j \in \{1,2\}$ | **Paper** (Smyth/Boyd + two-log Baker); **Lean** has `archimedean_gap_zero_bound` + `smyth_mahler_measure_consecutive_gap_order4` | Notes §4.5; `Skolem/DeterministicZeroTest.lean` |
| $k_q = 2$ at a prime $q \le \mathrm{poly}(\|\boldsymbol{u}\|)$ | **Paper** (Yu; constant grows like $q^f$); **Lean** has `padic_two_root_yu_zero_bound` | Notes §4.4–4.5; `Skolem/DeterministicZeroTest.lean` |
| Exact norm collapse of 2-root subsums $Z_k = c_1\hat{\mu}_1^k + c_2\hat{\mu}_2^k$ at $u_k = 0$ | **Lean** (`cubic_two_sum_norm_identity`, `cubic_two_sum_norm_at_zero`) + **Paper** | Notes §4.6.2; `Skolem/DeterministicZeroTest.lean` |
| **Residual: three roots cancel together with no 1- or 2-term split at any usable place** (Archimedean $k_\infty = 3$, e.g. $x(x-N)^3-1$; $q$-adic $k_q = 3$; $k_q = 2$ only at superpolynomially large $q$, e.g. $g_{N,c}(x) = (x-N)(x^2+x+N^2)-c$) | **Open** (structural obstructions analyzed in §4.6.1–4.6.2; numerical search in `experiments/near_equal_modulus_search.py`) | Notes §4.6; `experiments/near_equal_modulus_search.py` |

---

## Completed Roadmap Items (A1–D9)

### A. Due diligence before claiming anything new
1. ✅ **Literature check on bounds for the largest zero** of ternary/quaternary recurrences (MSTV 1984, Vereshchagin 1985, Beukers 1991, Schmidt 1999, Chonev–Ouaknine–Worrell 2016, Bilu 2025, 2026 MPI-SWS survey, SODA 2026). Documented in [`notes/deterministic_zero_testing.md`](notes/deterministic_zero_testing.md) §4.0.1: existing general bounds on the largest zero are exponential ($2^{\mathrm{poly}(\|\boldsymbol{u}\|)}$); the $k_q=1$ prime-place bound is classical via Liouville (Survey §5.3), whereas our composite-$q$ formulation over $\mathbb{Z}/q^{m+1}\mathbb{Z}$ (Theorems 5/6/`order_d_unit_root_zero_bound`) and the $D=1$ Smyth/Boyd root-power unit normalization are new to this repo.
2. ✅ **Overclaiming pass on `README.md` and Parts I–IV of the notes.** All claims in [`README.md`](README.md) and [`notes/deterministic_zero_testing.md`](notes/deterministic_zero_testing.md) now carry explicit **[Lean]**, **[Paper: ...]**, and **[Open]** status tags aligned with §4.0.

### B. Numerical experiments
3. ✅ **Search for large-index zeros** in near-equal-modulus families: implemented in [`experiments/near_equal_modulus_search.py`](experiments/near_equal_modulus_search.py) across $f_N(x) = x(x-N)^2 - 1$ (order 3, $D=1$), $h_N(x) = x(x-N)^3 - 1$ (order 4, $k_\infty = 3$, open class), and $g_{N,c}(x) = (x-N)(x^2+x+N^2)-c$ (order 3, open class). Across all families and initial/planted-zero states up to $k = 300$, `extra_zeros_beyond_plant = 0`.
4. ✅ **Constructed an explicit order-3 family in the open class**: $g_{N,c}(x) = (x-N)(x^2+x+N^2)-c = x^3 - (N-1)x^2 + N(N-1)x - (N^3+c)$ for $N \ge 2, c \in \{-2, +2\}$ (unconditionally irreducible over $\mathbb{Q}$, with odd $N, c=-2$ giving an infinite family with $S=1, D_{k=1}=1, k_p=2$ for all $p \mid (N^3-2)$, and prime $q = N^3+c$ giving $D = q^2$ with a single large prime factor $q = \Theta(N^3) = \Theta(2^{L_{\mathrm{coeff}}/2})$ and $q\,\delta_\infty \to \frac{1}{2}$). Documented in [`notes/deterministic_zero_testing.md`](notes/deterministic_zero_testing.md) §4.6 and verified in [`experiments/near_equal_modulus_search.py`](experiments/near_equal_modulus_search.py).

### C. Lean formalization
5. ✅ **Formalized the deductions "two-term Baker bound + gap $\implies$ zero bound" and "Yu $p$-adic bound + $k_q=2 \implies$ zero bound"**: `archimedean_gap_zero_bound`, `order3_unit_branch_smyth_baker_zero_bound`, and `padic_two_root_yu_zero_bound` in [`Skolem/DeterministicZeroTest.lean`](Skolem/DeterministicZeroTest.lean). Marked `factorization_free_composite_power_test_iff` and `order3_global_local_dichotomy_iff` as superseded in docstrings.
6. ✅ **General order-$d$ version of Theorems 5/6**: formalized as `order_d_unit_root_zero_bound` in [`Skolem/UnitRootDominance.lean`](Skolem/UnitRootDominance.lean) using `Finset.range` sums (`unitQuotCoeff`, `unitQuotShift`).
7. ✅ **Connected Theorem 5 to the slope-normalized sequence $z_k = S^{d-1-k} v_k$ inside Lean**: proved the polynomial-ring scaling identity $S^2 v_k = S^k z_k$ (`order3_slope_normalization_scaling`) and transferred the Theorem 5 zero bound directly to $v_k$ (`order3_normalized_unit_root_zero_bound`) in [`Skolem/UnitRootDominance.lean`](Skolem/UnitRootDominance.lean). Also implemented `slope_normalize_lrs` in [`src/deterministic_zero_test.py`](src/deterministic_zero_test.py).

### D. Research on the open class
8. ✅ **Three-term lower bound & why Beukers–Tijdeman circle intersection fails on a near-equal 3-cluster ($k_\infty = 3$)**: proved in [`notes/deterministic_zero_testing.md`](notes/deterministic_zero_testing.md) §4.6 that when $t = \min(\rho, R)/\max(\rho, R) = e^{-\delta_\infty}$, the circle radius scales by $t^n$; for the prime-$q$ family $g_{N,\pm 2}$, the exact Weil height is $h(t) = \frac{\log q + \delta_\infty}{3} = \log N + O(N^{-3})$ while $\delta_\infty \sim \frac{1}{2N^3} \sim \frac{1}{2q}$, so the intersection target $\varsigma_n$ has height $h(\varsigma_n) \ge \frac{n}{3}(\log q + \delta_\infty) - h(a)$, making 2-log Baker's lower bound $\exp(-C' n \log n) \ll e^{-n\delta_\infty}$.
9. ✅ **Large-prime norm bound vs. Yu for $k_q = 2$**: proved in [`notes/deterministic_zero_testing.md`](notes/deterministic_zero_testing.md) §4.6 and formalized in [`Skolem/DeterministicZeroTest.lean`](Skolem/DeterministicZeroTest.lean) (`cubic_two_sum_norm_identity`, `cubic_two_sum_norm_at_zero`) that for any irreducible cubic $\hat{\chi}(x) \in \mathbb{Z}[x]$ with $k_q = 2$ (where $x \equiv 0 \pmod q$ lifts by Hensel's lemma to $\hat{\mu}_3 \in \mathbb{Q}_q$), $Z_k = c_1\hat{\mu}_1^k + c_2\hat{\mu}_2^k = u_k - c_3\hat{\mu}_3^k$ lies in the degree-3 subfield $F = \mathbb{Q}(\hat{\mu}_3)$ with $f(\mathfrak{p}_3\mid q) = 1$, and at every zero $u_k = 0$ the field norm $N_{F/\mathbb{Q}}(Z_k) = u_k V_k - c_1 c_2 c_3 (-\hat{b}_0)^k$ collapses identically to the monomial $-c_1 c_2 c_3 (-\hat{b}_0)^k$.

### E. Next-Phase Research Targets & Deferred Items
10. **Attacking the four-relation obstruction ($\delta_\infty \sim \frac{1}{2q}$, $k_q = 2$, $h(r/R) = \frac{\log q + \delta_\infty}{3}$, $N_{F/\mathbb{Q}}(Z_k) = -C q^k$ at $u_k = 0$) in the residual class:**
    - *Route E1 (Multi-shift / Padé determinant at $q$):* Combine consecutive shifts $Z_k, Z_{k+1}$ or Padé approximants to $(1 - x)^k$ so the resulting determinant does not collapse to a monomial when $u_k = 0$, seeking a $q$-adic linear-forms bound $v_q(1 - \eta \xi^k) \le \mathrm{poly}(\|\boldsymbol{u}\|)(\log k)^A$ without Yu's $q^f$ factor.
    - *Route E2 (Algorithmic certificate for `ZeroSearch` candidates):* Rather than bounding all zeros unconditionally, exploit the extra $p$-adic disc certificate $n_i = M z_i + \ell$ ($u_{n_i} \equiv 0 \pmod{p^{V+R}}$ at the small prime $p \nmid b_0$) together with the $q$-adic relation $Z_k \equiv 0 \pmod{q^k}$ to test candidate indices directly.
11. **Prove2Me missions** (deferred by request): publish the Lean results, starting with Theorems 5/6/`order_d_unit_root_zero_bound` since they need no external hypotheses, and add the project to the "Theoretical Computer Science" category.
12. Long-term test case: the open order-6 sequence from the survey (`idea.txt` §3).

---

## Known technical debt
- `src/deterministic_zero_test.py :: factorization_free_D_nu_zero_test` is retained only for backwards compatibility; `unit_root_zero_bound_test` (with automatic `slope_normalize_lrs` when $S > 1$) is now the primary $k_q = 1$ verifier in `deterministic_candidate_zero_test`.
- `smyth_mahler_measure_consecutive_gap_order3/4`, `archimedean_gap_zero_bound`, and `padic_two_root_yu_zero_bound` take Smyth's bound and the Baker/Yu linear-forms inequalities as explicit hypotheses.
- `soda2026_ghost_root_verified` checks only `n = 4, 19` by `decide` (kernel recursion limits). Larger indices are checked in Python.

## Constraints
- Never commit `credentials.json` or `papers/`. Both are in `.gitignore`.
- Label every claim **Lean / Paper (which theorems) / Open**. Separate what Lean proves from hypotheses passed in.
- Verification before every push: `lake build`, `python3 -m unittest discover -s tests`, `python3 experiments/counterexamples_and_benchmarks.py`, `python3 experiments/unit_root_zero_bounds.py`, `python3 experiments/near_equal_modulus_search.py`.

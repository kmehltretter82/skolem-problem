# Project Plan — Deterministic Skolem at Orders ≤ 4

_Last updated: 2026-11-08 (after commit `3ecb53b`)._

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
| Obstruction B1 (Pisano period) and B2 (p-adic ghost root), with concrete instances | **Lean** (`decide`) | `Skolem/DeterministicZeroTest.lean` |
| **Theorems 5/6: unit-root branch `k_q = 1` ⇒ `u_k ≠ 0` for `k ≥ (d−1)(m+1)`**; works for composite `q` | **Lean, no external hypotheses** | `Skolem/UnitRootDominance.lean` |
| Lemma 1 (≤ 2 distinct roots) | Paper; Lean wrapper takes the height/Yu bound as a hypothesis | Notes Part I |
| Lemma 2 (interval arithmetic, MSTV separation) | Paper (Baker); Lean has the certification step only | Notes Part I |
| Order 3, `D = 1` (unit branch): polynomial zero bound | Paper (Smyth + two-log Baker) | Notes §4.3 |
| Order 4, `D = 1`, largest gap at `j ∈ {1,2}` | Paper (Smyth/Boyd + two-log Baker) | Notes §4.5 |
| `k_q = 2` at a prime `q ≤ poly` | Paper (Yu; constant grows like `q^f`) | Notes §4.4–4.5 |
| **Residual: three roots cancel together with no 1- or 2-term split at any usable place** (Archimedean `k_∞ = 3`, e.g. `x(x−N)³−1`; `q`-adic `k_q = 3`; `k_q = 2` only at superpolynomially large `q`) | **Open** | Notes §4.6 |

---

## Next steps (in priority order)

### A. Due diligence before claiming anything new
1. **Literature check on bounds for the largest zero** of ternary/quaternary recurrences: Mignotte–Shorey–Tijdeman, Beukers, Schlickewei–Schmidt, the 2026 MPI-SWS survey, and later papers. Question: are polynomial-in-height zero bounds already known for the `D = 1` or `k_q = 1` classes?
2. **Overclaiming pass on `README.md` and Parts I–III of the notes.** Parts I–III still contain older "zero transition window" / "derandomizes" wording written before the zero-bound reformulation. Align them with the status labels in §4.0.

### B. Numerical experiments
3. **Search for large-index zeros** in near-equal-modulus families: `x(x−N)²−1` (order 3, `D = 1`), `x(x−N)³−1` (order 4, `k_∞ = 3`), and order-3 cubics with `D > 1` whose three moduli are nearly equal. Measure the largest zero against `‖u‖`. Families in the open class are the most informative.
4. Try to **construct an order-3 instance in the open class** (three nearly equal moduli, `D_{k=1} = 1`, every prime of `D` large). A useful test object either way.

### C. Lean formalization
5. Formalize the **deduction "two-term Baker bound + gap ⇒ zero bound"** as a clean theorem. The Baker inequality stays an explicit hypothesis; the deduction itself is fully formal. Replace or deprecate the superseded wrappers (`factorization_free_composite_power_test_iff`, `order3_global_local_dichotomy_iff`).
6. Optional: a **general order-`d`** version of Theorems 5/6 using `Finset` sums (both currently follow from the generic `unit_ratio_order_frozen` and `window_climb_zero_bound`).
7. Optional: connect Theorem 5 to the normalized sequence `z_k = S^{d−1−k} v_k` inside Lean.

### D. Research on the open class
8. A **three-term lower bound** that is polynomial in the heights for the Archimedean `k_∞ = 3` cluster. This is the classical hard configuration (real root vs. complex pair of nearly equal modulus).
9. **Large-prime norm bound vs. Yu** for `k_q = 2`. A rough estimate falls short by a constant factor `≈ [K:ℚ]/(3f)`. Work out the exact constants and look for a refinement using conjugate primes above `q`.

### E. Later
10. **Prove2Me missions** (deferred by request): publish the Lean results, starting with Theorems 5/6 since they need no external hypotheses, and add the project to the "Theoretical Computer Science" category.
11. Long-term test case: the open order-6 sequence from the survey (`idea.txt` §3).

---

## Known technical debt
- `src/deterministic_zero_test.py :: factorization_free_D_nu_zero_test` uses a heuristic `ν` and is superseded by `unit_root_zero_bound_test`.
- `smyth_mahler_measure_consecutive_gap_order3/4` take Smyth's bound and the Mahler-measure inequality as hypotheses. The Lean content is linear arithmetic only.
- `soda2026_ghost_root_verified` checks only `n = 4, 19` by `decide` (kernel recursion limits). Larger indices are checked in Python.

## Constraints
- Never commit `credentials.json` or `papers/`. Both are in `.gitignore`.
- Label every claim **Lean / Paper (which theorems) / Open**. Separate what Lean proves from hypotheses passed in.
- Verification before every push: `lake build`, `python3 -m unittest discover -s tests`, `python3 experiments/counterexamples_and_benchmarks.py`, `python3 experiments/unit_root_zero_bounds.py`.

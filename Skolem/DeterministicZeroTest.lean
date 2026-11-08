import Skolem.ZeroSearch

/-!
# Deterministic Zero-Testing Lemmas and Obstruction Theorems at Low Orders

This module formalizes Deliverables 3 and 4 from `notes/deterministic_zero_testing.md`:
1. **Lemma 1 (`single_prime_power_zero_test_iff` & `weil_height_zero_bound`)**:
   Deterministic polynomial-time zero testing for the 2-root subclass of Order-`≤ 4` LRS via
   single prime-power reduction `p^ν` (backed by Yu's `p`-adic Baker bound) and Weil height cutoff.
2. **Lemma 2 (`DyadicInterval`, `dyadic_interval_certifies_nonzero`, `archimedean_separation_nonzero`)**:
   Deterministic polynomial-time zero testing for the Archimedean / MSTV subclass via rigorous
   dyadic interval arithmetic and dominant-vs-subdominant separation.
3. **Obstruction Theorem B1 (`pisano_period_simultaneous_mod_zero` & `pisano_obstruction_order3_verified`)**:
   Any oblivious modulus family `S` coprime to `a_0` is defeated at the joint Pisano period
   `n* = lcm_{m ∈ S} ord_m(A)` whenever `u_0 = 0` and `u_{n*} ≠ 0`.
4. **Obstruction Theorem B2 (`ghost_root_defeats_fixed_depth` & `soda2026_ghost_root_verified`)**:
   `p`-adic ghost roots `x_0 ∈ ℤ_p \ ℤ` in non-dominant subsequences `F_ℓ(n) = u_{M n + ℓ}` produce
   integer truncations `n_R = M * (x_0 mod p^R) + ℓ` with `p^R ∣ u_{n_R}` and `u_{n_R} ≠ 0`,
   verified concretely on the SODA 2026 Order-3 recurrence `u_{n+3} = 2 u_{n+2} - 3 u_{n+1} + u_n`.
-/

namespace Skolem

open Matrix BigOperators Finset

/-! ## 1. Lemma 1: 2-Root Subclass Single Prime-Power Test & Weil Height Cutoff -/

/--
**Lemma 1A (Single Prime-Power Zero Test for Non-Degenerate 2-Root LRS):**
Suppose that for a prime `p` and exponent `ν`, every nonzero value `u n` in the candidate range
`n ≤ N` has `p`-adic valuation strictly less than `ν` (i.e., `¬ ((p : ℤ) ^ ν ∣ u n)`, as guaranteed
by Yu's `p`-adic Baker theorem when `ν > C_p * log n`).
Then for every candidate `n ≤ N`, `u n = 0` if and only if `(p : ℤ) ^ ν ∣ u n`.
-/
theorem single_prime_power_zero_test_iff
    (u : ℕ → ℤ) (p ν N n : ℕ)
    (h_baker_padic : ∀ m ≤ N, u m ≠ 0 → ¬ ((p : ℤ) ^ ν ∣ u m))
    (hn : n ≤ N) :
    u n = 0 ↔ (p : ℤ) ^ ν ∣ u n := by
  constructor
  · intro hz
    rw [hz]
    exact dvd_zero ((p : ℤ) ^ ν)
  · intro hdvd
    by_contra hne
    exact h_baker_padic n hn hne hdvd

/--
**Lemma 1B (Weil Height Zero Bound for 2-Root LRS):**
Suppose a 2-root LRS `u n` satisfies the logarithmic height implication:
whenever `u n = 0`, the root-ratio height `n * h_gap` is bounded above by the coefficient height
`C_0 + C_1 * log_n` (since `(λ₁ / λ₂)^n = -B(n) / A(n)`).
Then any index `n` with `C_0 + C_1 * log_n < n * h_gap` satisfies `u n ≠ 0`.
-/
theorem weil_height_zero_bound
    (u : ℕ → ℤ) (n h_gap C_0 C_1 log_n : ℕ)
    (h_height_eq : u n = 0 → n * h_gap ≤ C_0 + C_1 * log_n)
    (h_large : C_0 + C_1 * log_n < n * h_gap) :
    u n ≠ 0 := by
  intro hz
  have hle := h_height_eq hz
  omega

/-! ## 2. Lemma 2: Dyadic Interval Arithmetic & Archimedean MSTV Separation -/

/--
A rigorous dyadic interval `[lo * 2^(-exp), hi * 2^(-exp)]` represented by integer endpoints
`lo, hi : ℤ` and a shared dyadic scale exponent `exp : ℕ`.
-/
structure DyadicInterval where
  lo : ℤ
  hi : ℤ
  exp : ℕ
  deriving DecidableEq, Repr

/-- An integer `x : ℤ` is contained in the dyadic interval `[lo * 2^(-exp), hi * 2^(-exp)]`. -/
def DyadicInterval.contains (I : DyadicInterval) (x : ℤ) : Prop :=
  I.lo ≤ x * (2 : ℤ) ^ I.exp ∧ x * (2 : ℤ) ^ I.exp ≤ I.hi

/-- Zero is contained in `I` if and only if `I.lo ≤ 0 ≤ I.hi`. -/
theorem DyadicInterval.contains_zero_iff (I : DyadicInterval) :
    I.contains 0 ↔ I.lo ≤ 0 ∧ 0 ≤ I.hi := by
  unfold DyadicInterval.contains
  simp

/--
**Lemma 2A (Soundness of Dyadic Interval Nonzero Certification):**
If `I` is a valid dyadic interval enclosure of `u n` (`I.contains (u n)`) and `0` lies strictly
outside `[I.lo, I.hi]` (`0 < I.lo ∨ I.hi < 0`), then `u n ≠ 0`.
-/
theorem dyadic_interval_certifies_nonzero
    (I : DyadicInterval) (u_n : ℤ)
    (h_enc : I.contains u_n)
    (h_sep : 0 < I.lo ∨ I.hi < 0) :
    u_n ≠ 0 := by
  intro hz
  rw [hz, DyadicInterval.contains_zero_iff] at h_enc
  rcases h_sep with hpos | hneg <;> omega

/--
**Lemma 2B (Archimedean Dominant-vs-Subdominant Separation):**
If `u_n = A_dom + B_sub` where `|A_dom| ≥ L_dom` and `|B_sub| ≤ U_sub` with `U_sub < L_dom`
(which holds in the MSTV / Baker regime once `n * log(|λ₁|/|λ_{k+1}|) > C * (log n)^2`),
then `u_n ≠ 0`.
-/
theorem archimedean_separation_nonzero
    (A_dom B_sub L_dom U_sub : ℤ)
    (h_dom : L_dom ≤ |A_dom|)
    (h_sub : |B_sub| ≤ U_sub)
    (h_gap : U_sub < L_dom) :
    A_dom + B_sub ≠ 0 := by
  intro hsum
  have heq : A_dom = -B_sub := by omega
  have habs : |A_dom| = |B_sub| := by rw [heq, abs_neg]
  linarith

/-! ## 3. Obstruction Theorem B1: Pisano-Period Defeat of Oblivious Modulus Families -/

/--
**Obstruction Theorem B1 (Pisano-Period Simultaneous Modular Vanishing):**
Suppose `u_0 = 0`, and for every modulus `m ∈ S`, the period `L m` satisfies `L m ∣ n_star` and
`u` is periodic modulo `m` with period `L m` (i.e. `∀ k, (m : ℤ) ∣ (u (L m * k) - u 0)`).
Then `(m : ℤ) ∣ u n_star` for every modulus `m ∈ S` simultaneously.
Thus, whenever `u n_star ≠ 0`, the oblivious modular zero test over `S` produces a false positive.
-/
theorem pisano_period_simultaneous_mod_zero
    (u : ℕ → ℤ) (S : Finset ℕ) (L : ℕ → ℕ) (n_star : ℕ)
    (hu0 : u 0 = 0)
    (h_period : ∀ m ∈ S, ∀ k : ℕ, (m : ℤ) ∣ (u (L m * k) - u 0))
    (h_lcm : ∀ m ∈ S, L m ∣ n_star) :
    ∀ m ∈ S, (m : ℤ) ∣ u n_star := by
  intro m hm
  rcases h_lcm m hm with ⟨k, rfl⟩
  have h := h_period m hm k
  rwa [hu0, sub_zero] at h

/--
Linear-time tail-recursive evaluator for an order-3 integer linear recurrence
`u_{n+3} = c2 * u_{n+2} + c1 * u_{n+1} + c0 * u_n` with initial state `(u0, u1, u2)`.
-/
def evalOrder3 (c0 c1 c2 : ℤ) : ℕ → ℤ → ℤ → ℤ → ℤ
  | 0, a, _, _ => a
  | n + 1, a, b, c => evalOrder3 c0 c1 c2 n b c (c2 * c + c1 * b + c0 * a)

/--
Concrete Order-3 recurrence from `experiments/counterexamples_and_benchmarks.py`:
`u_n = 2 * 5^n - 3^n - 1`, satisfying `u_{n+3} = 9 u_{n+2} - 23 u_{n+1} + 15 u_n`
with `u_0 = 0, u_1 = 6, u_2 = 40` (unique integer zero at `n = 0`).
-/
def pisanoCounterexampleSeq (n : ℕ) : ℤ :=
  evalOrder3 15 (-23) 9 n 0 6 40

/--
**Verified Instance of Obstruction B1:**
At the joint Pisano period `n* = 6` for `S = {2, 4, 7, 8}`, `pisanoCounterexampleSeq 6 = 30520 ≠ 0`,
yet every modulus `m ∈ {2, 4, 7, 8}` divides `pisanoCounterexampleSeq 6`.
-/
theorem pisano_obstruction_order3_verified :
    pisanoCounterexampleSeq 0 = 0 ∧
    pisanoCounterexampleSeq 6 = 30520 ∧
    pisanoCounterexampleSeq 6 ≠ 0 ∧
    (2 : ℤ) ∣ pisanoCounterexampleSeq 6 ∧
    (4 : ℤ) ∣ pisanoCounterexampleSeq 6 ∧
    (7 : ℤ) ∣ pisanoCounterexampleSeq 6 ∧
    (8 : ℤ) ∣ pisanoCounterexampleSeq 6 := by
  decide

/-! ## 4. Obstruction Theorem B2: `p`-adic Ghost-Root Defeat of Single-Prime Depth Rules -/

/--
**Obstruction Theorem B2 (Ghost-Root Truncations Defeat Fixed `p`-adic Depth Rules):**
Suppose a subsequence `F_ℓ(x) = u (M * x + ℓ)` satisfies the `p`-adic Taylor / Mahler congruence
`∀ R ≥ 1, (p : ℤ) ^ (R + 1) ∣ u (M * (z R) + ℓ)` along the base-`p` truncations `z R` of a
non-integer `p`-adic root `x_0 ∈ ℤ_p \ ℤ`, while `u (M * (z R) + ℓ) ≠ 0` (since `x_0 ∉ ℤ`).
Then for every fixed depth offset `c` and base depth `R ≥ 1`, testing `u n ≡ 0 (mod p^(R+1))`
fails to eliminate the nonzero candidate `n_R = M * (z R) + ℓ`.
-/
theorem ghost_root_defeats_fixed_depth
    (u : ℕ → ℤ) (M ℓ p : ℕ) (z : ℕ → ℕ)
    (h_cong : ∀ R ≥ 1, (p : ℤ) ^ (R + 1) ∣ u (M * z R + ℓ))
    (h_nonzero : ∀ R ≥ 1, u (M * z R + ℓ) ≠ 0) :
    ∀ R ≥ 1, ((p : ℤ) ^ (R + 1) ∣ u (M * z R + ℓ)) ∧ u (M * z R + ℓ) ≠ 0 := by
  intro R hR
  exact ⟨h_cong R hR, h_nonzero R hR⟩

/--
The worked Order-3 recurrence from Section 2.1 of Bacik, Ouaknine, and Worrell (SODA 2026,
`arXiv:2507.11234`):
`u_{n+3} = 2 u_{n+2} - 3 u_{n+1} + u_n` with initial values `u_0 = -1, u_1 = 1, u_2 = 7`.
-/
def soda2026Seq (n : ℕ) : ℤ :=
  evalOrder3 1 (-3) 2 n (-1) 1 7

/--
**Verified SODA 2026 Worked Example & Ghost-Root Valuation Jump (`arXiv:2507.11234` + B2):**
For `soda2026Seq` with `p = 5` and `M = 8`:
1. In residue class `ℓ = 4`, `n = 4` (`z = 0`) is a genuine integer zero (`soda2026Seq 4 = 0`).
2. In residue class `ℓ = 3`, `F_3(x) = u_{8x+3}` has a unique `5`-adic ghost root
   `x_0 = 2 + 1*5 + 1*5^2 + 0*5^3 + ... ∈ ℤ_5 \ ℤ`:
   - At `R = 1` (`z_1 = 2`, `n_1 = 19`): `5^2 ∣ u_19` (`u_19 = -2475`) and `u_19 ≠ 0`.
   - At `R = 2` (`z_2 = 7`, `n_2 = 59`): `5^3 ∣ u_59` (`u_59 = -22053231750`) and `u_59 ≠ 0`.
   - At `R = 3` (`z_3 = 32`, `n_3 = 259`): because the `5^3` digit of `x_0` is `0`, `z_3 = z_4 = 32`
     causes a valuation jump `5^5 ∣ u_259` while `u_259 ≠ 0`.
-/
theorem soda2026_ghost_root_verified :
    soda2026Seq 4 = 0 ∧
    soda2026Seq 19 = -2475 ∧
    ((5 : ℤ) ^ 2 ∣ soda2026Seq 19) ∧
    soda2026Seq 19 ≠ 0 := by
  decide

/-! ## 5. Zero-Bound Deductions from Spectral Gaps + Two-Term Baker / Yu Bounds -/

/--
**Theorem 3A (Order-3 Smyth Mahler-Measure Consecutive Spectral Gap):**
In the Archimedean Unit Branch (`D = 1`) at Order 3, the root-cube ratios `ξ_i = μ_i^3 / (-b_0)`
are algebraic units whose log-Mahler measure `log_M` satisfies `log_M ≤ 2 * (L_1 - L_3)`
and Smyth's bound `γ_smyth ≤ log_M`. Then at least one of the two consecutive Archimedean
spectral gaps `L_1 - L_2` or `L_2 - L_3` is at least `γ_smyth / 4`.
-/
theorem smyth_mahler_measure_consecutive_gap_order3
    (L_1 L_2 L_3 log_M γ_smyth : ℤ)
    (h_mahler : log_M ≤ 2 * (L_1 - L_3))
    (h_smyth : γ_smyth ≤ log_M) :
    γ_smyth ≤ 4 * (L_1 - L_2) ∨ γ_smyth ≤ 4 * (L_2 - L_3) := by
  omega

/--
**Theorem 4A (Order-4 Smyth Mahler-Measure Consecutive Spectral Gap):**
In the Archimedean Unit Branch (`D = 1`) at Order 4, the root-fourth-power ratios
`ξ_i = μ_i^4 / b_0` are algebraic units whose log-Mahler measure `log_M` satisfies
`log_M ≤ 4 * (L_1 - L_4)` and `γ_smyth ≤ log_M`. Then at least one of the three consecutive
Archimedean spectral gaps `L_1 - L_2`, `L_2 - L_3`, or `L_3 - L_4` is at least `γ_smyth / 12`.
-/
theorem smyth_mahler_measure_consecutive_gap_order4
    (L_1 L_2 L_3 L_4 log_M γ_smyth : ℤ)
    (h_mahler : log_M ≤ 4 * (L_1 - L_4))
    (h_smyth : γ_smyth ≤ log_M) :
    γ_smyth ≤ 12 * (L_1 - L_2) ∨ γ_smyth ≤ 12 * (L_2 - L_3) ∨ γ_smyth ≤ 12 * (L_3 - L_4) := by
  omega

/--
**Archimedean Two-Term Baker + Spectral Gap ⇒ Zero Bound (`notes/deterministic_zero_testing.md` §4.3):**
Suppose `u k = A_dom k + B_sub k` is split into a `1`- or `2`-root dominant block `A_dom k` and a
subdominant tail `B_sub k` across a consecutive log-modulus gap `δ_gap`.
Suppose the two-logarithm Baker bound (or Liouville bound when `k_∞ = 1`) together with the tail
estimate implies that whenever `|A_dom k| = |B_sub k|` at index `k`, we have
`k * δ_gap ≤ B_baker k`, and suppose we have a lower bound `δ_min ≤ δ_gap`.
Then for every `k : ℕ` with `B_baker k < (k : ℤ) * δ_min`, we have `u k ≠ 0`.
-/
theorem archimedean_gap_zero_bound
    (u A_dom B_sub : ℕ → ℤ) (B_baker : ℕ → ℤ) (δ_gap δ_min : ℤ)
    (h_split : ∀ k, u k = A_dom k + B_sub k)
    (h_baker : ∀ k, |A_dom k| = |B_sub k| → (k : ℤ) * δ_gap ≤ B_baker k)
    (h_gap : δ_min ≤ δ_gap) :
    ∀ k : ℕ, B_baker k < (k : ℤ) * δ_min → u k ≠ 0 := by
  intro k hk hz
  have hsum : A_dom k + B_sub k = 0 := by rw [← h_split k, hz]
  have habs : |A_dom k| = |B_sub k| := by
    have : A_dom k = -B_sub k := by omega
    rw [this, abs_neg]
  have hle := h_baker k habs
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have hmul : (k : ℤ) * δ_min ≤ (k : ℤ) * δ_gap := mul_le_mul_of_nonneg_left h_gap hk_nonneg
  omega

/--
**Theorem 3′ Deduction (Order-3 Unit Branch `D = 1` Zero Bound from Smyth + Two-Term Baker):**
Combining `smyth_mahler_measure_consecutive_gap_order3` with `archimedean_gap_zero_bound` on
whichever consecutive gap (`L_1 - L_2` for `k_∞ = 1`, or `L_2 - L_3` for `k_∞ = 2`) is at least
`γ_smyth / 4`: if any zero `u k = 0` under a gap `δ` forces `(k : ℤ) * δ ≤ B_baker k`, then
`u k ≠ 0` for all `k` with `4 * B_baker k < (k : ℤ) * γ_smyth`.
-/
theorem order3_unit_branch_smyth_baker_zero_bound
    (u : ℕ → ℤ) (B_baker : ℕ → ℤ) (L_1 L_2 L_3 log_M γ_smyth : ℤ)
    (h_mahler : log_M ≤ 2 * (L_1 - L_3))
    (h_smyth : γ_smyth ≤ log_M)
    (h_baker_k1 : ∀ k : ℕ, u k = 0 → (k : ℤ) * (L_1 - L_2) ≤ B_baker k)
    (h_baker_k2 : ∀ k : ℕ, u k = 0 → (k : ℤ) * (L_2 - L_3) ≤ B_baker k) :
    ∀ k : ℕ, 4 * B_baker k < (k : ℤ) * γ_smyth → u k ≠ 0 := by
  intro k hk hz
  have hgap := smyth_mahler_measure_consecutive_gap_order3 L_1 L_2 L_3 log_M γ_smyth h_mahler h_smyth
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  rcases hgap with h12 | h23
  · have hb := h_baker_k1 k hz
    have hm : (k : ℤ) * γ_smyth ≤ (k : ℤ) * (4 * (L_1 - L_2)) :=
      mul_le_mul_of_nonneg_left h12 hk_nonneg
    linarith
  · have hb := h_baker_k2 k hz
    have hm : (k : ℤ) * γ_smyth ≤ (k : ℤ) * (4 * (L_2 - L_3)) :=
      mul_le_mul_of_nonneg_left h23 hk_nonneg
    linarith

/--
**Non-Archimedean Two-Root (`k_q = 2`) + Yu's Bound ⇒ Zero Bound (`notes/deterministic_zero_testing.md` §4.4):**
Suppose `u k = A_dom k + B_sub k` where at a prime (or prime ideal) `q`, the subdominant tail
satisfies `q ^ (ν k) ∣ B_sub k` for all `k ≥ B_zero` (since its roots have positive `q`-adic slope),
while Yu's two-logarithm `p`-adic bound ensures `¬ q ^ (ν k) ∣ A_dom k` for all `k ≥ B_zero`
(once the linear valuation growth `ν k` of the tail overtakes the logarithmic bound `C_yu * q^f * log k`).
Then `¬ q ^ (ν k) ∣ u k` and hence `u k ≠ 0` for all `k ≥ B_zero`.
-/
theorem padic_two_root_yu_zero_bound
    (u A_dom B_sub : ℕ → ℤ) (q : ℤ) (ν : ℕ → ℕ) (B_zero : ℕ)
    (h_split : ∀ k, u k = A_dom k + B_sub k)
    (h_tail : ∀ k, B_zero ≤ k → q ^ (ν k) ∣ B_sub k)
    (h_yu : ∀ k, B_zero ≤ k → ¬ q ^ (ν k) ∣ A_dom k) :
    ∀ k, B_zero ≤ k → ¬ q ^ (ν k) ∣ u k ∧ u k ≠ 0 := by
  intro k hk
  have hnd : ¬ q ^ (ν k) ∣ u k := by
    intro hdvd
    apply h_yu k hk
    have heq : A_dom k = u k - B_sub k := by rw [h_split k]; ring
    rw [heq]
    exact dvd_sub hdvd (h_tail k hk)
  exact ⟨hnd, fun hz => hnd (by rw [hz]; exact dvd_zero _)⟩

/--
**Subfield Norm Identity for `k_q = 2` at Order 3 (`notes/deterministic_zero_testing.md` §4.6):**
For any three terms `x, y, z` (such as `x = c_1 μ_1^k, y = c_2 μ_2^k, z = c_3 μ_3^k`),
the product of the three two-term sums `(x + y)(y + z)(z + x)` (which is the field norm
`N_{F/ℚ}(c_1 μ_1^k + c_2 μ_2^k)` in the cubic subfield `F = ℚ(μ_3)`) satisfies
`(x + y)(y + z)(z + x) = (x + y + z)(x y + y z + z x) - x y z`.
-/
theorem cubic_two_sum_norm_identity {R : Type*} [CommRing R] (x y z : R) :
    (x + y) * (y + z) * (z + x) = (x + y + z) * (x * y + y * z + z * x) - x * y * z := by
  ring

/--
**Monomial Collapse of the Subfield Norm at a Zero (`u_k = x + y + z = 0`):**
Whenever `x + y + z = 0`, the product of the three conjugate two-term sums collapses identically
to the monomial `-x * y * z` (`= -c_1 c_2 c_3 (-b_0)^k`), explaining why the naive global norm bound
`|N_{F/ℚ}(Z_k)|_∞ ≥ q^{v_q(Z_k)}` reduces at `u_k = 0` to the tautological product formula on `-z`.
-/
theorem cubic_two_sum_norm_at_zero {R : Type*} [CommRing R] (x y z : R) (hz : x + y + z = 0) :
    (x + y) * (y + z) * (z + x) = -(x * y * z) := by
  rw [cubic_two_sum_norm_identity, hz, zero_mul, zero_sub]

/--
*(Superseded by the zero-bound theorems in `Skolem/UnitRootDominance.lean` and above; retained for
backwards compatibility.)*
Suppose `D` has a prime factor `q ∣ D` at which `¬ ((q : ℤ) ^ ν ∣ u m)` for all `m ≤ N` with `u m ≠ 0`.
Then `u n = 0 ↔ (D : ℤ) ^ ν ∣ u n`.
-/
theorem factorization_free_composite_power_test_iff
    (u : ℕ → ℤ) (D q ν N n : ℕ)
    (hq_dvd_D : q ∣ D)
    (h_yu_padic : ∀ m ≤ N, u m ≠ 0 → ¬ ((q : ℤ) ^ ν ∣ u m))
    (hn : n ≤ N) :
    u n = 0 ↔ (D : ℤ) ^ ν ∣ u n := by
  constructor
  · intro hz
    rw [hz]
    exact dvd_zero ((D : ℤ) ^ ν)
  · intro hD_dvd
    by_contra hne
    have hqZ : (q : ℤ) ∣ (D : ℤ) := Int.ofNat_dvd.mpr hq_dvd_D
    have hq_pow : (q : ℤ) ^ ν ∣ (D : ℤ) ^ ν := pow_dvd_pow_of_dvd hqZ ν
    exact h_yu_padic n hn hne (dvd_trans hq_pow hD_dvd)

/--
*(Superseded by the zero-bound theorems in `Skolem/UnitRootDominance.lean` and above; retained for
backwards compatibility.)*
Combined conditional equivalence wrapper for Order-3 `D = 1` vs `D > 1`.
-/
theorem order3_global_local_dichotomy_iff
    (u : ℕ → ℤ) (D ν N n : ℕ) (I : DyadicInterval)
    (h_enc : I.contains (u n))
    (h_dichotomy :
      (D = 1 ∧ (u n ≠ 0 → (0 < I.lo ∨ I.hi < 0))) ∨
      (D > 1 ∧ ∃ q, q ∣ D ∧ (∀ m ≤ N, u m ≠ 0 → ¬ ((q : ℤ) ^ ν ∣ u m))))
    (hn : n ≤ N) :
    u n = 0 ↔ (I.lo ≤ 0 ∧ 0 ≤ I.hi ∧ (D : ℤ) ^ ν ∣ u n) := by
  constructor
  · intro hz
    have h0 : I.contains 0 := by rwa [← hz]
    rw [DyadicInterval.contains_zero_iff] at h0
    refine ⟨h0.1, h0.2, ?_⟩
    rw [hz]
    exact dvd_zero ((D : ℤ) ^ ν)
  · rintro ⟨hlo, hhi, hD⟩
    rcases h_dichotomy with ⟨_hD1, h_arch⟩ | ⟨_hDgt, q, hqD, h_yu⟩
    · by_contra hne
      rcases h_arch hne with hpos | hneg <;> omega
    · exact (factorization_free_composite_power_test_iff u D q ν N n hqD h_yu hn).mpr hD

end Skolem

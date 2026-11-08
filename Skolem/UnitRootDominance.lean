import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Unconditional Zero Bounds from a Unique `q`-adic Unit Root (`k_q = 1`)

This module proves, **from first principles and without any external number-theoretic hypothesis**
(no Baker, no Yu, no Smyth), the `k_q = 1` branch of the global–local dichotomy in
`notes/deterministic_zero_testing.md`, reformulated as an explicit **zero bound** rather than a
modular zero test.

## Setting

Let `u` be an integer linear recurrence of order `d ∈ {3, 4}` with characteristic polynomial
`f(x) = x^d + b_{d-1} x^{d-1} + ⋯ + b_0`. Let `q` be **any** integer (prime *or composite* — no
factorization is ever needed) such that `f` factors modulo `Q = q^(m+1)` as

  `f(x) ≡ (x - μ) · g(x)  (mod Q)`,  with `g(x) = x^(d-1) + s_{d-2} x^(d-2) + ⋯ + s_0`,

where `μ` is coprime to `q` and every `s_i` is divisible by `q`. (This is exactly the situation
`q ∣ b_0, …, b_{d-2}` and `gcd(b_{d-1}, q) = 1`; the triple `(μ, s, Q)` is then produced by
Newton/Hensel lifting of the simple root `μ ≡ -b_{d-1} (mod q)` — see
`src/deterministic_zero_test.py :: unit_root_certificate`. Lean only has to *check* the
certificate.)

Define the "unit-root projection" `w k = u (k+d-1) + s_{d-2} u (k+d-2) + ⋯ + s_0 u k`.
If `q^m ∣ w 0` but `q^(m+1) ∤ w 0`, then

  **`q^(m+1) ∤ u k` (in particular `u k ≠ 0`) for every `k ≥ (d-1)(m+1)`.**

The proof is purely ultrametric: `w` is (mod `Q`) a geometric sequence with unit ratio `μ`, so its
`q`-order is frozen at `m`, while the remaining `d-1` roots are divisible by `q` and their
contribution gains one factor of `q` every `d-1` steps.

Note that `ord_q` for composite `q` is *not* a valuation (e.g. `ord_6 2 = ord_6 3 = 0` but
`ord_6 6 = 1`); this is harmless here because every step only uses divisibility and the
coprimality `IsCoprime μ q`.
-/

namespace Skolem

/-! ## 1. Generic lemmas -/

/--
**Frozen order of the unit-root projection.**
If `w (k+1) ≡ μ * w k (mod q^(m+1))` with `μ` coprime to `q`, and `q^m ∥ w 0`
(i.e. `q^m ∣ w 0`, `q^(m+1) ∤ w 0`), then `q^m ∥ w k` for every `k`.
-/
theorem unit_ratio_order_frozen
    (w : ℕ → ℤ) (μ q : ℤ) (m : ℕ)
    (hgeom : ∀ k, q ^ (m + 1) ∣ w (k + 1) - μ * w k)
    (hcop : IsCoprime μ q)
    (hw0 : q ^ m ∣ w 0) (hw0' : ¬ q ^ (m + 1) ∣ w 0) :
    ∀ k, q ^ m ∣ w k ∧ ¬ q ^ (m + 1) ∣ w k := by
  have hQm : q ^ m ∣ q ^ (m + 1) := pow_dvd_pow q (Nat.le_succ m)
  have hcopQ : IsCoprime μ (q ^ (m + 1)) := hcop.pow_right
  intro k
  induction k with
  | zero => exact ⟨hw0, hw0'⟩
  | succ k ih =>
    obtain ⟨ihm, ihm'⟩ := ih
    have hdiff := hgeom k
    have heq : w (k + 1) = (w (k + 1) - μ * w k) + μ * w k := by ring
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact dvd_add (dvd_trans hQm hdiff) (dvd_mul_of_dvd_right ihm μ)
    · intro hcontra
      apply ihm'
      have hμw : q ^ (m + 1) ∣ μ * w k := by
        have : μ * w k = w (k + 1) - (w (k + 1) - μ * w k) := by ring
        rw [this]
        exact dvd_sub hcontra hdiff
      exact hcopQ.symm.dvd_of_dvd_mul_left hμw

/--
**Window climbing lemma.**
Suppose that for every `k` and `j`, whenever `q^j` divides the whole window
`u k, …, u (k+r-1)`, the "error" `w k - u (k+r)` is divisible by `q^(j+1)`.
If `q^m ∥ w k` for every `k`, then `q^(m+1) ∤ u k` for all `k ≥ r * (m + 1)`.
-/
theorem window_climb_zero_bound
    (u w : ℕ → ℤ) (q : ℤ) (m r : ℕ)
    (hwin : ∀ k j, (∀ i < r, q ^ j ∣ u (k + i)) → q ^ (j + 1) ∣ w k - u (k + r))
    (hw : ∀ k, q ^ m ∣ w k ∧ ¬ q ^ (m + 1) ∣ w k) :
    ∀ k, r * (m + 1) ≤ k → ¬ q ^ (m + 1) ∣ u k := by
  -- Step 1: `q^j ∣ u k` for all `j ≤ m` and `k ≥ r * j`.
  have hclimb : ∀ j, j ≤ m → ∀ k, r * j ≤ k → q ^ j ∣ u k := by
    intro j
    induction j with
    | zero => intro _ k _; simp
    | succ j ih =>
      intro hj k hk
      have hk' : k = (k - r) + r := by
        have : r ≤ r * (j + 1) := Nat.le_mul_of_pos_right r (Nat.succ_pos j)
        omega
      have hwindow : ∀ i < r, q ^ j ∣ u (k - r + i) := by
        intro i _
        apply ih (Nat.le_of_succ_le hj)
        have : r * (j + 1) = r * j + r := by ring
        omega
      have herr := hwin (k - r) j hwindow
      have hwj : q ^ (j + 1) ∣ w (k - r) :=
        dvd_trans (pow_dvd_pow q hj) (hw (k - r)).1
      have heq : u k = w (k - r) - (w (k - r) - u (k - r + r)) := by
        rw [← hk']; ring
      rw [heq]
      exact dvd_sub hwj herr
  -- Step 2: at `k ≥ r * (m + 1)` the frozen `w` dominates.
  intro k hk hcontra
  have hk' : k = (k - r) + r := by
    have : r ≤ r * (m + 1) := Nat.le_mul_of_pos_right r (Nat.succ_pos m)
    omega
  have hwindow : ∀ i < r, q ^ m ∣ u (k - r + i) := by
    intro i _
    apply hclimb m le_rfl
    have : r * (m + 1) = r * m + r := by ring
    omega
  have herr := hwin (k - r) m hwindow
  apply (hw (k - r)).2
  have heq : w (k - r) = (w (k - r) - u (k - r + r)) + u k := by
    rw [← hk']; ring
  rw [heq]
  exact dvd_add herr hcontra

/-- Helper: `q ∣ s` and `q^j ∣ x` give `q^(j+1) ∣ s * x`. -/
theorem dvd_pow_succ_mul {q s x : ℤ} {j : ℕ} (hs : q ∣ s) (hx : q ^ j ∣ x) :
    q ^ (j + 1) ∣ s * x := by
  rw [pow_succ']
  exact mul_dvd_mul hs hx

/-! ## 2. Order 3 -/

/--
**Theorem 5 (Order-3 Unit-Root Zero Bound, unconditional & factorization-free).**
Let `u (k+3) = -(b2 * u (k+2) + b1 * u (k+1) + b0 * u k)` (characteristic polynomial
`x^3 + b2 x^2 + b1 x + b0`). Let `q, μ, s, t ∈ ℤ` and `m ∈ ℕ` satisfy the **checkable certificate**
- `x^3 + b2 x^2 + b1 x + b0 ≡ (x - μ)(x^2 + s x + t)  (mod q^(m+1))`, i.e.
  `q^(m+1) ∣ b2 - (s - μ)`, `q^(m+1) ∣ b1 - (t - μ s)`, `q^(m+1) ∣ b0 + μ t`;
- `q ∣ s`, `q ∣ t`, `IsCoprime μ q`;
- `q^m ∥ w0` where `w0 = u 2 + s * u 1 + t * u 0`.

Then `q^(m+1) ∤ u k`, and hence `u k ≠ 0`, for every `k ≥ 2 (m + 1)`.
-/
theorem order3_unit_root_zero_bound
    (u : ℕ → ℤ) (b2 b1 b0 q μ s t : ℤ) (m : ℕ)
    (hrec : ∀ k, u (k + 3) = -(b2 * u (k + 2) + b1 * u (k + 1) + b0 * u k))
    (hc2 : q ^ (m + 1) ∣ b2 - (s - μ))
    (hc1 : q ^ (m + 1) ∣ b1 - (t - μ * s))
    (hc0 : q ^ (m + 1) ∣ b0 + μ * t)
    (hs : q ∣ s) (ht : q ∣ t) (hcop : IsCoprime μ q)
    (hw0 : q ^ m ∣ u 2 + s * u 1 + t * u 0)
    (hw0' : ¬ q ^ (m + 1) ∣ u 2 + s * u 1 + t * u 0) :
    ∀ k, 2 * (m + 1) ≤ k → ¬ q ^ (m + 1) ∣ u k ∧ u k ≠ 0 := by
  set w : ℕ → ℤ := fun k => u (k + 2) + s * u (k + 1) + t * u k with hw_def
  have hgeom : ∀ k, q ^ (m + 1) ∣ w (k + 1) - μ * w k := by
    intro k
    have hid : w (k + 1) - μ * w k =
        -((b2 - (s - μ)) * u (k + 2) + (b1 - (t - μ * s)) * u (k + 1) + (b0 + μ * t) * u k) := by
      simp only [hw_def]
      rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring, hrec k]
      ring
    rw [hid]
    exact (dvd_add (dvd_add (dvd_mul_of_dvd_left hc2 _) (dvd_mul_of_dvd_left hc1 _))
      (dvd_mul_of_dvd_left hc0 _)).neg_right
  have hfrozen := unit_ratio_order_frozen w μ q m hgeom hcop hw0 hw0'
  have hwin : ∀ k j, (∀ i < 2, q ^ j ∣ u (k + i)) → q ^ (j + 1) ∣ w k - u (k + 2) := by
    intro k j hj
    have h0 : q ^ j ∣ u k := by simpa using hj 0 (by norm_num)
    have h1 : q ^ j ∣ u (k + 1) := hj 1 (by norm_num)
    have : w k - u (k + 2) = s * u (k + 1) + t * u k := by simp only [hw_def]; ring
    rw [this]
    exact dvd_add (dvd_pow_succ_mul hs h1) (dvd_pow_succ_mul ht h0)
  intro k hk
  have hnd := window_climb_zero_bound u w q m 2 hwin hfrozen k hk
  exact ⟨hnd, fun hz => hnd (by rw [hz]; exact dvd_zero _)⟩

/--
**Corollary 5′ (Order 3, precision `m = 0`, no lifting needed).**
If `q ∣ b1`, `q ∣ b0`, `IsCoprime b2 q` and `q ∤ u 2`, then `q ∤ u k` for all `k ≥ 2`.
Here `q` may be an arbitrary (e.g. unfactored composite) integer.
-/
theorem order3_unit_root_mod_q
    (u : ℕ → ℤ) (b2 b1 b0 q : ℤ)
    (hrec : ∀ k, u (k + 3) = -(b2 * u (k + 2) + b1 * u (k + 1) + b0 * u k))
    (hb1 : q ∣ b1) (hb0 : q ∣ b0) (hcop : IsCoprime b2 q) (hu2 : ¬ q ∣ u 2) :
    ∀ k, 2 ≤ k → ¬ q ∣ u k ∧ u k ≠ 0 := by
  have h := order3_unit_root_zero_bound u b2 b1 b0 q (-b2) 0 0 0 hrec
    (by simp) (by simpa using hb1) (by simpa using hb0)
    (dvd_zero q) (dvd_zero q) hcop.neg_left (by simp) (by simpa using hu2)
  intro k hk
  simpa using h k (by simpa using hk)

/-! ## 3. Order 4 -/

/--
**Theorem 6 (Order-4 Unit-Root Zero Bound, unconditional & factorization-free).**
Let `u (k+4) = -(b3 u (k+3) + b2 u (k+2) + b1 u (k+1) + b0 u k)`. If
`x^4 + b3 x^3 + b2 x^2 + b1 x + b0 ≡ (x - μ)(x^3 + s2 x^2 + s1 x + s0)  (mod q^(m+1))`
with `q ∣ s2, s1, s0`, `IsCoprime μ q`, and `q^m ∥ w0 = u 3 + s2 u 2 + s1 u 1 + s0 u 0`, then
`q^(m+1) ∤ u k` (so `u k ≠ 0`) for every `k ≥ 3 (m + 1)`.
-/
theorem order4_unit_root_zero_bound
    (u : ℕ → ℤ) (b3 b2 b1 b0 q μ s2 s1 s0 : ℤ) (m : ℕ)
    (hrec : ∀ k, u (k + 4) = -(b3 * u (k + 3) + b2 * u (k + 2) + b1 * u (k + 1) + b0 * u k))
    (hc3 : q ^ (m + 1) ∣ b3 - (s2 - μ))
    (hc2 : q ^ (m + 1) ∣ b2 - (s1 - μ * s2))
    (hc1 : q ^ (m + 1) ∣ b1 - (s0 - μ * s1))
    (hc0 : q ^ (m + 1) ∣ b0 + μ * s0)
    (hs2 : q ∣ s2) (hs1 : q ∣ s1) (hs0 : q ∣ s0) (hcop : IsCoprime μ q)
    (hw0 : q ^ m ∣ u 3 + s2 * u 2 + s1 * u 1 + s0 * u 0)
    (hw0' : ¬ q ^ (m + 1) ∣ u 3 + s2 * u 2 + s1 * u 1 + s0 * u 0) :
    ∀ k, 3 * (m + 1) ≤ k → ¬ q ^ (m + 1) ∣ u k ∧ u k ≠ 0 := by
  set w : ℕ → ℤ := fun k => u (k + 3) + s2 * u (k + 2) + s1 * u (k + 1) + s0 * u k with hw_def
  have hgeom : ∀ k, q ^ (m + 1) ∣ w (k + 1) - μ * w k := by
    intro k
    have hid : w (k + 1) - μ * w k =
        -((b3 - (s2 - μ)) * u (k + 3) + (b2 - (s1 - μ * s2)) * u (k + 2) +
          (b1 - (s0 - μ * s1)) * u (k + 1) + (b0 + μ * s0) * u k) := by
      simp only [hw_def]
      rw [show k + 1 + 3 = k + 4 by ring, show k + 1 + 2 = k + 3 by ring,
        show k + 1 + 1 = k + 2 by ring, hrec k]
      ring
    rw [hid]
    exact (dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_left hc3 _) (dvd_mul_of_dvd_left hc2 _))
      (dvd_mul_of_dvd_left hc1 _)) (dvd_mul_of_dvd_left hc0 _)).neg_right
  have hfrozen := unit_ratio_order_frozen w μ q m hgeom hcop hw0 hw0'
  have hwin : ∀ k j, (∀ i < 3, q ^ j ∣ u (k + i)) → q ^ (j + 1) ∣ w k - u (k + 3) := by
    intro k j hj
    have h0 : q ^ j ∣ u k := by simpa using hj 0 (by norm_num)
    have h1 : q ^ j ∣ u (k + 1) := hj 1 (by norm_num)
    have h2 : q ^ j ∣ u (k + 2) := hj 2 (by norm_num)
    have : w k - u (k + 3) = s2 * u (k + 2) + s1 * u (k + 1) + s0 * u k := by
      simp only [hw_def]; ring
    rw [this]
    exact dvd_add (dvd_add (dvd_pow_succ_mul hs2 h2) (dvd_pow_succ_mul hs1 h1))
      (dvd_pow_succ_mul hs0 h0)
  intro k hk
  have hnd := window_climb_zero_bound u w q m 3 hwin hfrozen k hk
  exact ⟨hnd, fun hz => hnd (by rw [hz]; exact dvd_zero _)⟩

/-! ## 4. A concrete factorization-free instance (composite `q = 15`) -/

/--
`u (k+3) = u (k+2) - 15 u (k+1) - 15 u k`, `u 0 = 0, u 1 = 0, u 2 = 1`
(characteristic polynomial `x^3 - x^2 + 15 x + 15`, irreducible over `ℚ`).
-/
def unitRootExampleSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (k + 3) => unitRootExampleSeq (k + 2) - 15 * unitRootExampleSeq (k + 1) -
      15 * unitRootExampleSeq k

/--
For the composite modulus `q = 15` (never factored), `15 ∤ u k` and hence `u k ≠ 0` for all
`k ≥ 2`: the sequence has **no zeros beyond index 1**, proved for *all* `k` with no
external hypothesis.
-/
theorem unitRootExample_no_late_zeros :
    ∀ k, 2 ≤ k → ¬ (15 : ℤ) ∣ unitRootExampleSeq k ∧ unitRootExampleSeq k ≠ 0 := by
  apply order3_unit_root_mod_q unitRootExampleSeq (-1) 15 15 15
  · intro k
    show unitRootExampleSeq (k + 3) = _
    simp only [unitRootExampleSeq]
    ring
  · exact dvd_refl _
  · exact dvd_refl _
  · exact ⟨-1, 0, by ring⟩
  · decide

end Skolem

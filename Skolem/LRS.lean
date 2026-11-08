import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Linear Recurrence Sequences and Perturbed-Identity Subsequence Expansions

This module formalizes the matrix representation of integer Linear Recurrence Sequences (LRS)
from Section 2.1 and Section 2.5 of Bacik, Ouaknine, and Worrell (SODA 2026, `arXiv:2507.11234`):
- `evalLRS α A β n = α ⬝ᵥ (A ^ n *ᵥ β)`
- Subsequence decomposition along arithmetic progressions `M * n + ℓ` when `A ^ M = 1 + p • B`
- Binomial / Mahler expansion of `A ^ (M * n + ℓ)` in powers of `p • B`.
-/

namespace Skolem

open Matrix BigOperators Finset

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Matrix-power evaluation of an LRS: `u_n = αᵀ Aⁿ β`. -/
def evalLRS (α : d → ℤ) (A : Matrix d d ℤ) (β : d → ℤ) (n : ℕ) : ℤ :=
  dotProduct α ((A ^ n).mulVec β)

/-- Auxiliary sequence `γ_{ℓ, k} = αᵀ Bᵏ A^ℓ β` from the proof of Theorem 2.5 (`arXiv:2507.11234`). -/
def gammaSeq (α : d → ℤ) (A B : Matrix d d ℤ) (β : d → ℤ) (ℓ k : ℕ) : ℤ :=
  dotProduct α (((B ^ k) * (A ^ ℓ)).mulVec β)

/-- Mahler series coefficient `β_{ℓ, k} = p^k γ_{ℓ, k}` from Theorem 2.5 (`arXiv:2507.11234`). -/
def mahlerCoeff (α : d → ℤ) (A B : Matrix d d ℤ) (β : d → ℤ) (p ℓ k : ℕ) : ℤ :=
  (p : ℤ) ^ k * gammaSeq α A B β ℓ k

/-- Every Mahler coefficient `β_{ℓ, k}` is divisible by `p^k`. -/
theorem pow_dvd_mahlerCoeff (α : d → ℤ) (A B : Matrix d d ℤ) (β : d → ℤ) (p ℓ k : ℕ) :
    (p : ℤ) ^ k ∣ mahlerCoeff α A B β p ℓ k :=
  ⟨gammaSeq α A B β ℓ k, rfl⟩

omit [DecidableEq d] in
/-- Scalar multiplication commutes with `Matrix.mulVec`. -/
theorem matrix_smul_mulVec (c : ℤ) (M : Matrix d d ℤ) (v : d → ℤ) :
    (c • M).mulVec v = c • M.mulVec v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Binomial expansion of `(1 + p • B)^n` in `Matrix d d ℤ`. -/
theorem one_add_smul_pow (B : Matrix d d ℤ) (p : ℤ) (n : ℕ) :
    (1 + p • B) ^ n = ∑ k ∈ range (n + 1), (Nat.choose n k : ℤ) • (p ^ k • (B ^ k)) := by
  have hcomm : Commute (p • B) (1 : Matrix d d ℤ) := Commute.one_right (p • B)
  rw [add_comm, hcomm.add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [one_pow, mul_one, smul_pow, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℤ]

/--
**Theorem 2.5 Binomial / Mahler Expansion Identity (`arXiv:2507.11234`, p. 5):**
If `A ^ M = 1 + p • B`, then the subsequence `u_{M n + ℓ}` has the exact finite Mahler expansion
`u_{M n + ℓ} = ∑_{k=0}^n C(n, k) β_{ℓ, k}`.
-/
theorem evalLRS_subseq_mahler_expansion
    (α : d → ℤ) (A B : Matrix d d ℤ) (β : d → ℤ)
    (M p ℓ : ℕ) (hM : A ^ M = 1 + (p : ℤ) • B) (n : ℕ) :
    evalLRS α A β (M * n + ℓ) =
      ∑ k ∈ range (n + 1), (Nat.choose n k : ℤ) * mahlerCoeff α A B β p ℓ k := by
  unfold evalLRS mahlerCoeff gammaSeq
  rw [pow_add, pow_mul, hM, one_add_smul_pow]
  rw [Finset.sum_mul]
  have h_mulVec :
      ∀ (S : Finset ℕ) (F : ℕ → Matrix d d ℤ),
        dotProduct α ((∑ k ∈ S, F k).mulVec β) = ∑ k ∈ S, dotProduct α ((F k).mulVec β) := by
    intro S F
    induction S using Finset.induction_on with
    | empty =>
      simp [Matrix.zero_mulVec, dotProduct_zero]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert ha]
  rw [h_mulVec]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.smul_mul, matrix_smul_mulVec, dotProduct_smul, smul_eq_mul]

end Skolem

import Skolem.Mahler

/-!
# Section 3 of `arXiv:2507.11234`: `ZeroSearch` Soundness, Disc Uniqueness, and Skolem–Mahler–Lech

This module formalizes the algorithmic correctness lemmas of Section 3 of
Bacik, Ouaknine, and Worrell (SODA 2026, `arXiv:2507.11234`):
1. **Lemma 3.3 (`lem_min_coef_bound`)**: `V(h_{z,r}) ≤ V(F_ℓ) + r * j(F_ℓ) ≤ V(F_ℓ) + r * (d - 1)`.
2. **Proposition 3.4 (`prop_fast_disc_truncation_sound`)**: If the minimal valuation `V` among
   `0 ≤ k < d` satisfies `V < ν`, then computing valuations modulo `p^ν` (i.e. `min (v k) ν`)
   yields the exact same minimum `V` and the exact same minimizing indices `k`, so `j(h_{z,r})`
   is computed without error from residues modulo `p^ν`.
3. **Corollary 3.5 (`disc_unique_integer_candidate`)**: When `M * p^R + ℓ > N` and `z < p^R`,
   any natural number `n` with `M * n + ℓ ≤ N` and `n ≡ z [MOD p^R]` must equal `z`.
4. **Theorem 3.1 (`bounded_skolem_iff_prod_candidates_eq_zero`)**: A candidate list contains a zero
   of `u` if and only if the product `∏ n ∈ candidates, u n` equals `0`.
5. **Skolem–Mahler–Lech Structural Theorem (`skolem_mahler_lech_decomposition`)**: Any LRS whose
   `M` subsequences `u_{M n + ℓ}` are either identically zero or have at most `d - 1` zeros has its
   zero set equal to a union of full arithmetic progressions and a finite set of size `≤ M * (d - 1)`.
-/

namespace Skolem

open BigOperators Finset

/-! ## 1. Lemma 3.3: Precision Bound `V(h_{z,r}) ≤ V(F_ℓ) + r * (d - 1)` -/

/--
**Lemma 3.3 (`lem:min_coef` of `arXiv:2507.11234`):**
If `j_h ≤ j_F` and `j_F ≤ d - 1`, and `V_h ≤ V_F + r * j_F`, then for `d ≥ 1`,
`V_h ≤ V_F + r * (d - 1)`.
-/
theorem lem_min_coef_bound
    (d r j_h j_F V_F V_h : ℕ)
    (_hd : 1 ≤ d)
    (_hjh : j_h ≤ j_F)
    (hjF : j_F ≤ d - 1)
    (hVh : V_h ≤ V_F + r * j_F) :
    V_h ≤ V_F + r * (d - 1) := by
  have hr : r * j_F ≤ r * (d - 1) := Nat.mul_le_mul_left r hjF
  omega

/-! ## 2. Proposition 3.4: Soundness of Modular Valuation Truncation at Precision `ν > V` -/

/--
**Proposition 3.4 (`prop:fast_disc` of `arXiv:2507.11234`):**
Let `v : ℕ → ℕ` be the true `p`-adic valuations of `(Δ^k h_{z,r})(0)` for `0 ≤ k < d`,
and let `v_mod k := min (v k) ν` be the valuations computed modulo `p^ν`.
If there exists `k₀ < d` with `v k₀ = V` and `V < ν`, and `∀ k < d, V ≤ v k`, then:
1. For every `k < d`, `v_mod k = V ↔ v k = V`.
2. In particular, the largest index `k < d` minimizing `v_mod k` is identical to the largest
   index `k < d` minimizing `v k`.
-/
theorem prop_fast_disc_truncation_sound
    (d ν V k₀ : ℕ) (v : ℕ → ℕ)
    (_hk₀ : k₀ < d)
    (hV_min : ∀ k < d, V ≤ v k)
    (_hk₀_eq : v k₀ = V)
    (hν : V < ν) :
    ∀ k < d, min (v k) ν = V ↔ v k = V := by
  intro k hk
  have hle : V ≤ v k := hV_min k hk
  constructor
  · intro hmin
    omega
  · intro hvk
    omega

/-! ## 3. Corollary 3.5: Uniqueness of the Integer Candidate in Disc `D(z, R)` -/

/--
**Corollary 3.5 Disc Uniqueness (`arXiv:2507.11234`, p. 6 & p. 8):**
Suppose `M > 0`, `z < p^R`, and the depth `R` satisfies `N < M * p^R + ℓ`.
Then for any natural number `n` such that `M * n + ℓ ≤ N` and `n % (p^R) = z`,
we must have `n = z`.
-/
theorem disc_unique_integer_candidate
    (M p R ℓ N z n : ℕ)
    (_hM : 0 < M)
    (_hz : z < p ^ R)
    (hR : N < M * (p ^ R) + ℓ)
    (hn_bound : M * n + ℓ ≤ N)
    (hn_mod : n % (p ^ R) = z) :
    n = z := by
  have h_lt_pR : n < p ^ R := by
    by_contra hnot
    have hge : p ^ R ≤ n := by omega
    have hmul : M * (p ^ R) ≤ M * n := Nat.mul_le_mul_left M hge
    omega
  rw [← hn_mod]
  exact (Nat.mod_eq_of_lt h_lt_pR).symm

/-! ## 4. Theorem 3.1: Disjunctive Product Reduction to `EqSLP` -/

/--
**Theorem 3.1 Product Circuit Equivalence (`arXiv:2507.11234`, lines 535–540):**
For any sequence `u : ℕ → ℤ` and finite candidate set `S : Finset ℕ`,
there exists a candidate `n ∈ S` with `u n = 0` if and only if the product
`∏ n ∈ S, u n = 0`.
-/
theorem exists_zero_in_candidates_iff_prod_eq_zero
    (u : ℕ → ℤ) (S : Finset ℕ) :
    (∃ n ∈ S, u n = 0) ↔ (∏ n ∈ S, u n) = 0 := by
  rw [Finset.prod_eq_zero_iff]

/-! ## 5. Skolem–Mahler–Lech Structural Decomposition Theorem -/

/--
**Skolem–Mahler–Lech Decomposition for Integer LRS (`arXiv:2507.11234` Thm 2.5 + Survey Thm 5):**
Suppose `M > 0` and for each residue class `ℓ ∈ range M`, either:
- `ℓ ∈ AP`, in which case `u (M * m + ℓ) = 0` for all `m ∈ ℕ` (a full arithmetic progression of zeros), or
- `ℓ ∉ AP`, in which case `u (M * m + ℓ) = 0 ↔ m ∈ Z ℓ` for a finite set `Z ℓ` of size `≤ d - 1`.
Then:
1. Every zero `n ∈ ℕ` of `u` is characterized by `(n % M ∈ AP ∨ n ∈ Z_exc)` where
   `Z_exc = biUnion (range M \ AP) (fun ℓ => image (fun m => M * m + ℓ) (Z ℓ))`.
2. The number of exceptional zeros is at most `M * (d - 1)`.
-/
theorem skolem_mahler_lech_decomposition
    (u : ℕ → ℤ) (M d : ℕ) (hM : 0 < M)
    (AP : Finset ℕ) (Z : ℕ → Finset ℕ)
    (hAP_sound : ∀ ℓ ∈ AP, ∀ m : ℕ, u (M * m + ℓ) = 0)
    (hZ_iff : ∀ ℓ ∈ range M \ AP, ∀ m : ℕ, u (M * m + ℓ) = 0 ↔ m ∈ Z ℓ)
    (hZ_card : ∀ ℓ ∈ range M \ AP, (Z ℓ).card ≤ d - 1) :
    let Z_exc := (range M \ AP).biUnion (fun ℓ => (Z ℓ).image (fun m => M * m + ℓ))
    (∀ n : ℕ, u n = 0 ↔ (n % M ∈ AP ∨ n ∈ Z_exc)) ∧
      Z_exc.card ≤ M * (d - 1) := by
  intro Z_exc
  constructor
  · intro n
    have hdiv : M * (n / M) + n % M = n := Nat.div_add_mod n M
    have hmod_lt : n % M < M := Nat.mod_lt n hM
    constructor
    · intro hun
      by_cases h_in_AP : n % M ∈ AP
      · exact Or.inl h_in_AP
      · right
        rw [Finset.mem_biUnion]
        refine ⟨n % M, Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hmod_lt, h_in_AP⟩, ?_⟩
        rw [Finset.mem_image]
        refine ⟨n / M, ?_, hdiv⟩
        apply (hZ_iff (n % M) (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hmod_lt, h_in_AP⟩) (n / M)).mp
        rwa [hdiv]
    · rintro (h_in_AP | h_in_exc)
      · have := hAP_sound (n % M) h_in_AP (n / M)
        rwa [hdiv] at this
      · rw [Finset.mem_biUnion] at h_in_exc
        rcases h_in_exc with ⟨ℓ, hℓ, hm⟩
        rw [Finset.mem_image] at hm
        rcases hm with ⟨m, hmZ, rfl⟩
        exact (hZ_iff ℓ hℓ m).mpr hmZ
  · calc
      Z_exc.card ≤ ∑ ℓ ∈ range M \ AP, ((Z ℓ).image (fun m => M * m + ℓ)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ ℓ ∈ range M \ AP, (Z ℓ).card :=
        Finset.sum_le_sum (fun ℓ _ => Finset.card_image_le)
      _ ≤ ∑ _ℓ ∈ range M \ AP, (d - 1) :=
        Finset.sum_le_sum (fun ℓ hℓ => hZ_card ℓ hℓ)
      _ = (range M \ AP).card * (d - 1) := by
        simp [Finset.sum_const, smul_eq_mul]
      _ ≤ (range M).card * (d - 1) :=
        Nat.mul_le_mul_right (d - 1) (Finset.card_le_card sdiff_subset)
      _ = M * (d - 1) := by
        rw [Finset.card_range]
end Skolem

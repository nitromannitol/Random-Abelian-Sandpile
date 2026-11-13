import Mathlib

/-! # Step L2-C, part 2: eigenvalue bounds

A symmetric operator `T` on a `n`-dimensional real inner product space with quadratic form in
`[-L|v|², 0]` has `|det T| ≤ Lⁿ`, and if `|det T| ≥ α` then `⟪Tv, v⟫ ≤ -(α / L^{n-1}) |v|²`:
each eigenvalue `λ_j ∈ [-L, 0]` satisfies `|λ_j| L^{n-1} ≥ ∏ |λ_i| = |det T| ≥ α`. -/

open Module

namespace RandomSandpile

namespace UniformConcavity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem eigenvalues_mem {n : ℕ} (hn : finrank ℝ E = n) {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {L : ℝ} (hlo : ∀ v, -L * ‖v‖ ^ 2 ≤ inner ℝ (T v) v) (hhi : ∀ v, inner ℝ (T v) v ≤ 0)
    (i : Fin n) : -L ≤ hT.eigenvalues hn i ∧ hT.eigenvalues hn i ≤ 0 := by
  have hb := hT.apply_eigenvectorBasis hn i
  have hnorm : ‖hT.eigenvectorBasis hn i‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.1 i
  have heq : inner ℝ (T (hT.eigenvectorBasis hn i)) (hT.eigenvectorBasis hn i) =
      hT.eigenvalues hn i := by
    rw [hb, inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
    simp
  have h1 := hlo (hT.eigenvectorBasis hn i)
  have h2 := hhi (hT.eigenvectorBasis hn i)
  rw [heq, hnorm] at h1
  rw [heq] at h2
  exact ⟨by linarith, h2⟩

theorem abs_det_eq_prod {n : ℕ} (hn : finrank ℝ E = n) {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) :
    |LinearMap.det T| = ∏ i, |hT.eigenvalues hn i| := by
  rw [hT.det_eq_prod_eigenvalues hn, Finset.abs_prod]
  simp

theorem abs_det_le {n : ℕ} (hn : finrank ℝ E = n) {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {L : ℝ} (hlo : ∀ v, -L * ‖v‖ ^ 2 ≤ inner ℝ (T v) v) (hhi : ∀ v, inner ℝ (T v) v ≤ 0) :
    |LinearMap.det T| ≤ L ^ n := by
  rw [abs_det_eq_prod hn hT]
  calc ∏ i, |hT.eigenvalues hn i| ≤ ∏ _i : Fin n, L := by
        refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
        obtain ⟨h1, h2⟩ := eigenvalues_mem hn hT hlo hhi i
        rw [abs_of_nonpos h2]; linarith
    _ = L ^ n := by simp

theorem inner_le_of_abs_det {n : ℕ} (hn : finrank ℝ E = n) {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {L α : ℝ} (hL : 0 < L) (hlo : ∀ v, -L * ‖v‖ ^ 2 ≤ inner ℝ (T v) v)
    (hhi : ∀ v, inner ℝ (T v) v ≤ 0) (hdet : α ≤ |LinearMap.det T|) (v : E) :
    inner ℝ (T v) v ≤ -(α / L ^ (n - 1)) * ‖v‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  set lam := hT.eigenvalues hn
  set c := α / L ^ (n - 1)
  -- each eigenvalue is `≤ -c`
  have hlam : ∀ j, lam j ≤ -c := by
    intro j
    obtain ⟨h1, h2⟩ := eigenvalues_mem hn hT hlo hhi j
    have hprod : |LinearMap.det T| = |lam j| * ∏ i ∈ Finset.univ.erase j, |lam i| := by
      rw [abs_det_eq_prod hn hT]
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
    have hle : ∏ i ∈ Finset.univ.erase j, |lam i| ≤ L ^ (n - 1) := by
      calc ∏ i ∈ Finset.univ.erase j, |lam i| ≤ ∏ _i ∈ Finset.univ.erase j, L := by
            refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
            obtain ⟨h1, h2⟩ := eigenvalues_mem hn hT hlo hhi i
            rw [abs_of_nonpos h2]; linarith
        _ = L ^ (n - 1) := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
              Finset.card_univ, Fintype.card_fin]
    have hLp : 0 < L ^ (n - 1) := pow_pos hL _
    have : α ≤ |lam j| * L ^ (n - 1) :=
      hdet.trans (hprod ▸ mul_le_mul_of_nonneg_left hle (abs_nonneg _))
    have hc : c ≤ |lam j| := by
      simp only [c]; rw [div_le_iff₀ hLp]; exact this
    rw [abs_of_nonpos h2] at hc
    linarith
  -- expansion in the eigenbasis
  have hexp : inner ℝ (T v) v = ∑ i, lam i * (inner ℝ v (b i) * inner ℝ (b i) v) := by
    rw [← b.sum_inner_mul_inner (T v) v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hT v (b i), hT.apply_eigenvectorBasis hn i]
    simp only [inner_smul_right, b, lam]
    simp only [RCLike.ofReal_real_eq_id, id]
    ring
  have hnorm : ‖v‖ ^ 2 = ∑ i, inner ℝ v (b i) * inner ℝ (b i) v := by
    rw [b.sum_inner_mul_inner v v, real_inner_self_eq_norm_sq]
  rw [hexp, hnorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hs : 0 ≤ inner ℝ v (b i) * inner ℝ (b i) v := by
    rw [real_inner_comm v (b i)]; exact mul_self_nonneg _
  nlinarith [hlam i]

end UniformConcavity

end RandomSandpile

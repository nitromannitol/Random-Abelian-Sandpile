import RandomSandpile.Proofs.Sec9.SingleSourceD2Loop

/-!
# Theorem 9.2 in dimension two: comparison with equation quadratics

SIMPLE-PROOF Lemma 2.1, first paragraph. Let `F` have the shift identity and `Q` be a paraboloid
with `F(D²Q) = 0`. On a bounded open set `C`, a viscosity subsolution `u ∈ C(C̄)` of `F = 0` with
`u ≤ Q` on `∂C` satisfies `u ≤ Q` in `C` (`le_quadratic_of_sub`), and a viscosity supersolution with
`Q ≤ u` on `∂C` satisfies `Q ≤ u` in `C` (`quadratic_le_of_super`). The proof perturbs `Q` by
`±δ(R² - |x|²)`, whose Hessian `D²Q ∓ 2δI` has `F = ±4δ`, and tests at an interior extremum.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

/-- The paraboloid `c + p·(x - a) + q_N(x - a)` plus `t(R² - |x|²)` is again a paraboloid. -/
theorem paraboloid_add_sq (c t R : ℝ) (p a : Rd 2) (N : Matrix (Fin 2) (Fin 2) ℝ) (x : Rd 2) :
    c + inner ℝ p (x - a) + qM N (x - a) + t * (R ^ 2 - ‖x‖ ^ 2) =
      (c + t * R ^ 2 - t * ‖a‖ ^ 2) + innerSL ℝ (p - (2 * t) • a) (x - a) +
        qM (N + (-(2 * t)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (x - a) := by
  rw [qM_add_smul_one, innerSL_apply_apply, inner_sub_left, real_inner_smul_left]
  have h : ‖x‖ ^ 2 = ‖x - a‖ ^ 2 + 2 * inner ℝ (x - a) a + ‖a‖ ^ 2 := by
    have := norm_add_sq_real (x - a) a
    rwa [sub_add_cancel] at this
  rw [h, real_inner_comm a (x - a)]
  ring

/-- **(C1), subsolution half.** -/
theorem le_quadratic_of_sub {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hshift : HasTraceShift F)
    {C : Set (Rd 2)} (hC : IsOpen C) (hCb : Bornology.IsBounded C) {u : Rd 2 → ℝ}
    (hu : ContinuousOn u (closure C)) (hsub : ViscFromAboveLE F C u) {c : ℝ} {p a : Rd 2}
    {N : Matrix (Fin 2) (Fin 2) ℝ} (hN : N.IsSymm) (hFN : F N = 0)
    (hbd : ∀ x ∈ frontier C, u x ≤ c + inner ℝ p (x - a) + qM N (x - a)) :
    ∀ x ∈ C, u x ≤ c + inner ℝ p (x - a) + qM N (x - a) := by
  intro x₀ hx₀
  by_contra hgt
  have hm : 0 < u x₀ - (c + inner ℝ p (x₀ - a) + qM N (x₀ - a)) := by linarith [not_le.mp hgt]
  set m := u x₀ - (c + inner ℝ p (x₀ - a) + qM N (x₀ - a)) with hmdef
  obtain ⟨R, hR⟩ := hCb.subset_closedBall 0
  have hcl : closure C ⊆ closedBall 0 R := closure_minimal hR isClosed_closedBall
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = m / (2 * (R ^ 2 + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδR : δ * R ^ 2 ≤ m / 2 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set c₁ := c + δ * R ^ 2 - δ * ‖a‖ ^ 2
  set p₁ := p - (2 * δ) • a
  set N₁ := N + (-(2 * δ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  set φ : Rd 2 → ℝ := fun z => c₁ + innerSL ℝ p₁ (z - a) + qM N₁ (z - a) with hφ
  have hφeq : ∀ z, φ z = c + inner ℝ p (z - a) + qM N (z - a) + δ * (R ^ 2 - ‖z‖ ^ 2) :=
    fun z => (paraboloid_add_sq c δ R p a N z).symm
  have hφc : Continuous φ := (contDiff_paraboloid c₁ p₁ a N₁ (n := 0)).continuous
  obtain ⟨y, hycl, hymax⟩ := hCb.isCompact_closure.exists_isMaxOn ⟨x₀, subset_closure hx₀⟩
    (hu.sub hφc.continuousOn)
  have hR2 : ∀ z ∈ closure C, ‖z‖ ^ 2 ≤ R ^ 2 := fun z hz => by
    have := mem_closedBall_zero_iff.1 (hcl hz)
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith
  have hx₀v : 0 < u x₀ - φ x₀ := by
    rw [hφeq]
    have h1 := hR2 x₀ (subset_closure hx₀)
    have h2 : 0 ≤ δ * ‖x₀‖ ^ 2 := by positivity
    linarith
  have hyv : 0 < u y - φ y := lt_of_lt_of_le hx₀v (isMaxOn_iff.mp hymax x₀ (subset_closure hx₀))
  have hyC : y ∈ C := by
    by_contra hyC
    have hyf : y ∈ frontier C := ⟨hycl, by rwa [hC.interior_eq]⟩
    have h1 := hbd y hyf
    have h2 := hR2 y hycl
    rw [hφeq] at hyv
    have h3 : 0 ≤ δ * (R ^ 2 - ‖y‖ ^ 2) := mul_nonneg hδ.le (by linarith)
    linarith
  have hloc : IsLocalMax (fun z => u z - φ z) y :=
    hymax.isLocalMax (Filter.mem_of_superset (hC.mem_nhds hyC) subset_closure)
  have h := hsub y hyC φ (contDiff_paraboloid c₁ p₁ a N₁).contDiffAt hloc
  rw [hφ, hessian_paraboloid, hessian_qM_of_isSymm (hN.add (Matrix.isSymm_one.smul _)),
    hshift N hN, hFN] at h
  linarith

/-- **(C1), supersolution half.** -/
theorem quadratic_le_of_super {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hshift : HasTraceShift F)
    {C : Set (Rd 2)} (hC : IsOpen C) (hCb : Bornology.IsBounded C) {u : Rd 2 → ℝ}
    (hu : ContinuousOn u (closure C)) (hsup : ViscFromBelowGE F C u) {c : ℝ} {p a : Rd 2}
    {N : Matrix (Fin 2) (Fin 2) ℝ} (hN : N.IsSymm) (hFN : F N = 0)
    (hbd : ∀ x ∈ frontier C, c + inner ℝ p (x - a) + qM N (x - a) ≤ u x) :
    ∀ x ∈ C, c + inner ℝ p (x - a) + qM N (x - a) ≤ u x := by
  intro x₀ hx₀
  by_contra hgt
  have hm : 0 < c + inner ℝ p (x₀ - a) + qM N (x₀ - a) - u x₀ := by linarith [not_le.mp hgt]
  set m := c + inner ℝ p (x₀ - a) + qM N (x₀ - a) - u x₀ with hmdef
  obtain ⟨R, hR⟩ := hCb.subset_closedBall 0
  have hcl : closure C ⊆ closedBall 0 R := closure_minimal hR isClosed_closedBall
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = m / (2 * (R ^ 2 + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδR : δ * R ^ 2 ≤ m / 2 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set c₁ := c + (-δ) * R ^ 2 - (-δ) * ‖a‖ ^ 2
  set p₁ := p - (2 * (-δ)) • a
  set N₁ := N + (-(2 * (-δ))) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  set φ : Rd 2 → ℝ := fun z => c₁ + innerSL ℝ p₁ (z - a) + qM N₁ (z - a) with hφ
  have hφeq : ∀ z, φ z = c + inner ℝ p (z - a) + qM N (z - a) + (-δ) * (R ^ 2 - ‖z‖ ^ 2) :=
    fun z => (paraboloid_add_sq c (-δ) R p a N z).symm
  have hφc : Continuous φ := (contDiff_paraboloid c₁ p₁ a N₁ (n := 0)).continuous
  obtain ⟨y, hycl, hymax⟩ := hCb.isCompact_closure.exists_isMaxOn ⟨x₀, subset_closure hx₀⟩
    (hφc.continuousOn.sub hu)
  have hR2 : ∀ z ∈ closure C, ‖z‖ ^ 2 ≤ R ^ 2 := fun z hz => by
    have := mem_closedBall_zero_iff.1 (hcl hz)
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith
  have hx₀v : 0 < φ x₀ - u x₀ := by
    rw [hφeq]
    have h1 := hR2 x₀ (subset_closure hx₀)
    have h2 : 0 ≤ δ * ‖x₀‖ ^ 2 := by positivity
    linarith
  have hyv : 0 < φ y - u y := lt_of_lt_of_le hx₀v (isMaxOn_iff.mp hymax x₀ (subset_closure hx₀))
  have hyC : y ∈ C := by
    by_contra hyC
    have hyf : y ∈ frontier C := ⟨hycl, by rwa [hC.interior_eq]⟩
    have h1 := hbd y hyf
    have h2 := hR2 y hycl
    rw [hφeq] at hyv
    have h3 : 0 ≤ δ * (R ^ 2 - ‖y‖ ^ 2) := mul_nonneg hδ.le (by linarith)
    linarith
  have hloc : IsLocalMin (fun z => u z - φ z) y := by
    have h := hymax.isLocalMax (Filter.mem_of_superset (hC.mem_nhds hyC) subset_closure)
    unfold IsLocalMax IsMaxFilter at h
    unfold IsLocalMin IsMinFilter
    filter_upwards [h] with z hz
    simp only [Pi.sub_apply] at hz
    show u y - φ y ≤ u z - φ z
    linarith
  have h := hsup y hyC φ (contDiff_paraboloid c₁ p₁ a N₁).contDiffAt hloc
  rw [hφ, hessian_paraboloid, hessian_qM_of_isSymm (hN.add (Matrix.isSymm_one.smul _)),
    hshift N hN, hFN] at h
  linarith

end SingleSourceD2

end RandomSandpile

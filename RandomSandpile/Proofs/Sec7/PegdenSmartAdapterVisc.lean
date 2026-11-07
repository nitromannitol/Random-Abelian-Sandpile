import RandomSandpile.Proofs.Sec7.PegdenSmartAdapterPeano
import RandomSandpile.Proofs.Sec9.SingleSourceLimitMinimal
import RandomSandpile.Proofs.Sec7.LimitObstacleGamma

/-!
# Viscosity bounds `|Δu| ≤ K` under quadratic shifts and affine changes

In the terminology of Crandall-Ishii-Lions, `ViscFromAboveGE (fun X => X.trace + K) U u` says that `u`
is a viscosity subsolution of `-Δu - K = 0` (`Δu ≥ -K`) and `ViscFromBelowLE (fun X => X.trace - K)
U u` that it is a viscosity supersolution of `-Δu + K = 0` (`Δu ≤ K`).

* `viscAboveGE_add_sq`, `viscBelowLE_add_sq`: adding `c |x - b|²` shifts the bounds by `2dc`;
* `viscAboveGE_comp_affine`, `viscBelowLE_comp_affine`: `y ↦ u(x₁ + ρ y)`, `ρ > 0`, satisfies the
  bounds with `ρ² K` on the preimage of `U`;
* `viscAboveGE_mono`, `viscBelowLE_mono`: monotonicity in `K`.
-/

noncomputable section

open Filter Topology

namespace RandomSandpile

variable {d : ℕ}

namespace PegdenSmartAdapter

/-- The Hessian of a sum of functions that are `C²` near `x`. -/
theorem hessian_add_of_contDiffAt {φ g : Rd d → ℝ} {x : Rd d} (hφ : ContDiffAt ℝ 2 φ x)
    (hg : ContDiffAt ℝ 2 g x) :
    hessian (fun y => φ y + g y) x = hessian φ x + hessian g x := by
  have hevφ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hevg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun y => φ y + g y) =ᶠ[𝓝 x] fun y => fderiv ℝ φ y + fderiv ℝ g y := by
    filter_upwards [hevφ, hevg] with y h1 h2
    exact (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv
  have hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fun y => fderiv ℝ φ y + fderiv ℝ g y) x =
      fderiv ℝ (fderiv ℝ φ) x + fderiv ℝ (fderiv ℝ g) x :=
    (hDφ.hasFDerivAt.add hDg.hasFDerivAt).fderiv
  ext i j
  rw [hessian_apply, h1.fderiv_eq, h2]
  simp only [add_apply, Matrix.add_apply, hessian_apply]

theorem sq_norm_sub_eq (c : ℝ) (b : Rd d) :
    (fun z : Rd d => c * ‖z - b‖ ^ 2) = fun z =>
      0 + innerSL ℝ (0 : Rd d) (z - b) + qM ((2 * c) • (1 : Matrix (Fin d) (Fin d) ℝ)) (z - b) := by
  funext z
  rw [qM_smul_one]
  simp only [map_zero, zero_apply, zero_add]
  ring

/-- The Hessian of `z ↦ c |z - b|²` is `2c I`. -/
theorem hessian_sq_norm_sub (c : ℝ) (b y : Rd d) :
    hessian (fun z : Rd d => c * ‖z - b‖ ^ 2) y = (2 * c) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hsymm : ((2 * c) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm
    simp
  rw [sq_norm_sub_eq, hessian_quadratic 0 0 b hsymm y]

theorem contDiff_sq_norm_sub (c : ℝ) (b : Rd d) :
    ContDiff ℝ 2 (fun z : Rd d => c * ‖z - b‖ ^ 2) :=
  contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)

theorem viscAboveGE_mono {U : Set (Rd d)} {K K' : ℝ} {u : Rd d → ℝ}
    (h : ViscFromAboveGE (fun X => X.trace + K) U u) (hK : K ≤ K') :
    ViscFromAboveGE (fun X => X.trace + K') U u := fun x hx φ hφ hloc => by
  have h' : 0 ≤ (hessian φ x).trace + K := h x hx φ hφ hloc
  show 0 ≤ (hessian φ x).trace + K'
  linarith

theorem viscBelowLE_mono {U : Set (Rd d)} {K K' : ℝ} {u : Rd d → ℝ}
    (h : ViscFromBelowLE (fun X => X.trace - K) U u) (hK : K ≤ K') :
    ViscFromBelowLE (fun X => X.trace - K') U u := fun x hx φ hφ hloc => by
  have h' : (hessian φ x).trace - K ≤ 0 := h x hx φ hφ hloc
  show (hessian φ x).trace - K' ≤ 0
  linarith

/-- Adding `c |x - b|²`: `Δu ≥ -K` becomes `Δ(u + c|x - b|²) ≥ -(K - 2dc)`. -/
theorem viscAboveGE_add_sq {U : Set (Rd d)} {K : ℝ} {u : Rd d → ℝ}
    (hu : ViscFromAboveGE (fun X => X.trace + K) U u) (c : ℝ) (b : Rd d) :
    ViscFromAboveGE (fun X => X.trace + (K - 2 * d * c)) U
      (fun x => u x + c * ‖x - b‖ ^ 2) := by
  intro x hx φ hφ hloc
  have hq : ContDiffAt ℝ 2 (fun z : Rd d => (-c) * ‖z - b‖ ^ 2) x :=
    (contDiff_sq_norm_sub (-c) b).contDiffAt
  have hψ : ContDiffAt ℝ 2 (fun z => φ z + (-c) * ‖z - b‖ ^ 2) x := hφ.add hq
  have hloc' : IsLocalMax (fun z => u z - (φ z + (-c) * ‖z - b‖ ^ 2)) x := by
    refine hloc.congr (Eventually.of_forall fun z => ?_); ring
  have h : 0 ≤ (hessian (fun z => φ z + (-c) * ‖z - b‖ ^ 2) x).trace + K := hu x hx _ hψ hloc'
  rw [hessian_add_of_contDiffAt hφ hq, hessian_sq_norm_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at h
  show 0 ≤ (hessian φ x).trace + (K - 2 * d * c)
  linarith

/-- Adding `c |x - b|²`: `Δu ≤ K` becomes `Δ(u + c|x - b|²) ≤ K + 2dc`. -/
theorem viscBelowLE_add_sq {U : Set (Rd d)} {K : ℝ} {u : Rd d → ℝ}
    (hu : ViscFromBelowLE (fun X => X.trace - K) U u) (c : ℝ) (b : Rd d) :
    ViscFromBelowLE (fun X => X.trace - (K + 2 * d * c)) U
      (fun x => u x + c * ‖x - b‖ ^ 2) := by
  intro x hx φ hφ hloc
  have hq : ContDiffAt ℝ 2 (fun z : Rd d => (-c) * ‖z - b‖ ^ 2) x :=
    (contDiff_sq_norm_sub (-c) b).contDiffAt
  have hψ : ContDiffAt ℝ 2 (fun z => φ z + (-c) * ‖z - b‖ ^ 2) x := hφ.add hq
  have hloc' : IsLocalMin (fun z => u z - (φ z + (-c) * ‖z - b‖ ^ 2)) x := by
    refine hloc.congr (Eventually.of_forall fun z => ?_); ring
  have h : (hessian (fun z => φ z + (-c) * ‖z - b‖ ^ 2) x).trace - K ≤ 0 := hu x hx _ hψ hloc'
  rw [hessian_add_of_contDiffAt hφ hq, hessian_sq_norm_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at h
  show (hessian φ x).trace - (K + 2 * d * c) ≤ 0
  linarith

/-- Shared part of the affine change: the test function `x ↦ φ(ρ⁻¹ x + c)`, `c = -ρ⁻¹ x₁`. -/
theorem affine_test {φ : Rd d → ℝ} {x₁ y : Rd d} {ρ : ℝ} (hρ : 0 < ρ)
    (hφ : ContDiffAt ℝ 2 φ y) :
    ContDiffAt ℝ 2 (fun x => 1 * φ (ρ⁻¹ • x + -(ρ⁻¹ • x₁))) (x₁ + ρ • y) ∧
      hessian (fun x => 1 * φ (ρ⁻¹ • x + -(ρ⁻¹ • x₁))) (x₁ + ρ • y) =
        (ρ⁻¹ ^ 2) • hessian φ y ∧
      ∀ z : Rd d, x₁ + ρ • (ρ⁻¹ • z + -(ρ⁻¹ • x₁)) = z := by
  have hpt : ρ⁻¹ • (x₁ + ρ • y) + -(ρ⁻¹ • x₁) = y := by
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    abel
  have hφ' : ContDiffAt ℝ 2 φ (ρ⁻¹ • (x₁ + ρ • y) + -(ρ⁻¹ • x₁)) := by rw [hpt]; exact hφ
  have hφc : ContDiffAt ℝ 2 (fun z => φ (z + -(ρ⁻¹ • x₁))) (ρ⁻¹ • (x₁ + ρ • y)) :=
    ContDiffAt.comp_add_right' hφ'
  refine ⟨contDiffAt_const.mul (hφc.comp (x₁ + ρ • y) (contDiffAt_id.const_smul ρ⁻¹)), ?_,
    fun z => ?_⟩
  · rw [SingleSourceLimitMinimal.hessian_const_mul_comp_smul 1 ρ⁻¹ hφc, hessian_comp_add_right,
      hpt, one_mul]
  · simp only [smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
    abel

/-- `y ↦ u(x₁ + ρ y)`: `Δu ≥ -K` becomes `≥ -ρ² K`. -/
theorem viscAboveGE_comp_affine {U : Set (Rd d)} {K : ℝ} {u : Rd d → ℝ}
    (hu : ViscFromAboveGE (fun X => X.trace + K) U u) (x₁ : Rd d) {ρ : ℝ} (hρ : 0 < ρ) :
    ViscFromAboveGE (fun X => X.trace + ρ ^ 2 * K) {y | x₁ + ρ • y ∈ U}
      (fun y => u (x₁ + ρ • y)) := by
  intro y hy φ hφ hloc
  obtain ⟨hψ, hH, e⟩ := affine_test (x₁ := x₁) hρ hφ
  have hloc' : IsLocalMax (fun x => u x - 1 * φ (ρ⁻¹ • x + -(ρ⁻¹ • x₁))) (x₁ + ρ • y) := by
    have hg : ContinuousAt (fun x : Rd d => ρ⁻¹ • x + -(ρ⁻¹ • x₁)) (x₁ + ρ • y) :=
      ((continuous_const_smul ρ⁻¹).add continuous_const).continuousAt
    have hpt : ρ⁻¹ • (x₁ + ρ • y) + -(ρ⁻¹ • x₁) = y := by
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
      abel
    unfold IsLocalMax IsMaxFilter at hloc ⊢
    rw [← hpt] at hloc
    have h1 := Filter.Tendsto.eventually hg hloc
    filter_upwards [h1] with x hx
    simp only [e, one_mul] at hx ⊢
    exact hx
  have h : 0 ≤ (hessian (fun x => 1 * φ (ρ⁻¹ • x + -(ρ⁻¹ • x₁))) (x₁ + ρ • y)).trace + K :=
    hu (x₁ + ρ • y) hy _ hψ hloc'
  rw [hH, Matrix.trace_smul, smul_eq_mul] at h
  show 0 ≤ (hessian φ y).trace + ρ ^ 2 * K
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hρ2' : ρ ^ 2 * (ρ⁻¹ ^ 2 * (hessian φ y).trace) = (hessian φ y).trace := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ.ne', one_pow, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h hρ2.le]

/-- `y ↦ u(x₁ + ρ y)`: `Δu ≤ K` becomes `≤ ρ² K`. -/
theorem viscBelowLE_comp_affine {U : Set (Rd d)} {K : ℝ} {u : Rd d → ℝ}
    (hu : ViscFromBelowLE (fun X => X.trace - K) U u) (x₁ : Rd d) {ρ : ℝ} (hρ : 0 < ρ) :
    ViscFromBelowLE (fun X => X.trace - ρ ^ 2 * K) {y | x₁ + ρ • y ∈ U}
      (fun y => u (x₁ + ρ • y)) := by
  intro y hy φ hφ hloc
  obtain ⟨hψ, hH, e⟩ := affine_test (x₁ := x₁) hρ hφ
  have hloc' : IsLocalMin (fun x => u x - 1 * φ (ρ⁻¹ • x + -(ρ⁻¹ • x₁))) (x₁ + ρ • y) := by
    have hg : ContinuousAt (fun x : Rd d => ρ⁻¹ • x + -(ρ⁻¹ • x₁)) (x₁ + ρ • y) :=
      ((continuous_const_smul ρ⁻¹).add continuous_const).continuousAt
    have hpt : ρ⁻¹ • (x₁ + ρ • y) + -(ρ⁻¹ • x₁) = y := by
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
      abel
    unfold IsLocalMin IsMinFilter at hloc ⊢
    rw [← hpt] at hloc
    have h1 := Filter.Tendsto.eventually hg hloc
    filter_upwards [h1] with x hx
    simp only [e, one_mul] at hx ⊢
    exact hx
  have h : (hessian (fun x => 1 * φ (ρ⁻¹ • x + -(ρ⁻¹ • x₁))) (x₁ + ρ • y)).trace - K ≤ 0 :=
    hu (x₁ + ρ • y) hy _ hψ hloc'
  rw [hH, Matrix.trace_smul, smul_eq_mul] at h
  show (hessian φ y).trace - ρ ^ 2 * K ≤ 0
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hρ2' : ρ ^ 2 * (ρ⁻¹ ^ 2 * (hessian φ y).trace) = (hessian φ y).trace := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ.ne', one_pow, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h hρ2.le]

end PegdenSmartAdapter

end RandomSandpile

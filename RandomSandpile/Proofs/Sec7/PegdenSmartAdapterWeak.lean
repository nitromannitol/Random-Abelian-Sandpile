import RandomSandpile.Inputs.PegdenSmartProp25
import RandomSandpile.Proofs.Sec7.MainTheoremWeakStar

/-!
# Weak solutions of `Δu = s`: linearity

`isWeakSolutionLaplace_sub`: the difference of weak solutions (`IsWeakSolutionLaplace`)
of `Δu = s₁` and `Δv = s₂` with `u, v ∈ C(U)` and bounded measurable `s₁, s₂` is a weak solution of
`Δ(u - v) = s₁ - s₂`. The integrals are finite: `u Δφ` is continuous with compact support for
`φ ∈ C_0^∞(U)` (`integrable_mul_trace_hessian`).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace RandomSandpile

variable {d : ℕ}

namespace PegdenSmartAdapter

/-- The Hessian of a function vanishes off its topological support. -/
theorem hessian_eq_zero_of_not_mem_tsupport {φ : Rd d → ℝ} {x : Rd d} (hx : x ∉ tsupport φ) :
    hessian φ x = 0 := by
  have h : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
    by_contra hne
    exact hy (subset_tsupport φ hne)
  exact hessian_eq_zero_of_eventuallyEq_const h

/-- `x ↦ Δφ(x) = tr D²φ(x)` is continuous for `φ ∈ C²`. -/
theorem continuous_trace_hessian {φ : Rd d → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous fun x => Matrix.trace (hessian φ x) := by
  have hD : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  simp only [Matrix.trace, Matrix.diag, hessian_apply]
  exact continuous_finsetSum _ fun i _ =>
    (hD.clm_apply continuous_const).clm_apply continuous_const

/-- `u Δφ` is integrable for `u ∈ C(U)` and `φ ∈ C²` with compact support in `U`. -/
theorem integrable_mul_trace_hessian {U : Set (Rd d)} (hU : IsOpen U) {u φ : Rd d → ℝ}
    (hu : ContinuousOn u U) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    Integrable (fun x => u x * Matrix.trace (hessian φ x)) := by
  have hcont : Continuous fun x => u x * Matrix.trace (hessian φ x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact (hu.continuousAt (hU.mem_nhds (hφU hx))).mul
        (continuous_trace_hessian hφ).continuousAt
    · have h0 : (fun y => u y * Matrix.trace (hessian φ y)) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
        rw [hessian_eq_zero_of_not_mem_tsupport hy, Matrix.trace_zero, mul_zero]
      exact continuousAt_const.congr h0.symm
  refine hcont.integrable_of_hasCompactSupport (hφc.mono' fun x hx => ?_)
  by_contra hx'
  apply hx
  show u x * Matrix.trace (hessian φ x) = 0
  rw [hessian_eq_zero_of_not_mem_tsupport hx', Matrix.trace_zero, mul_zero]

/-- **Linearity of weak solutions.** -/
theorem isWeakSolutionLaplace_sub {U : Set (Rd d)} (hU : IsOpen U) {u v s₁ s₂ : Rd d → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U) (hs₁ : Measurable s₁) (hs₂ : Measurable s₂)
    {C : ℝ} (hC₁ : ∀ x, |s₁ x| ≤ C) (hC₂ : ∀ x, |s₂ x| ≤ C)
    (h₁ : IsWeakSolutionLaplace U u s₁) (h₂ : IsWeakSolutionLaplace U v s₂) :
    IsWeakSolutionLaplace U (fun x => u x - v x) (fun x => s₁ x - s₂ x) := by
  intro φ hφ hφc hφU
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  show ∫ x, (u x - v x) * Matrix.trace (hessian φ x) = ∫ x, (s₁ x - s₂ x) * φ x
  have e1 : ∫ x, (u x - v x) * Matrix.trace (hessian φ x) =
      (∫ x, u x * Matrix.trace (hessian φ x)) - ∫ x, v x * Matrix.trace (hessian φ x) := by
    rw [← integral_sub (integrable_mul_trace_hessian hU hu hφ2 hφc hφU)
      (integrable_mul_trace_hessian hU hv hφ2 hφc hφU)]
    congr 1; funext x; ring
  have e2 : ∫ x, (s₁ x - s₂ x) * φ x = (∫ x, s₁ x * φ x) - ∫ x, s₂ x * φ x := by
    rw [← integral_sub (integrable_mul_of_abs_le hs₁ hC₁ hφi)
      (integrable_mul_of_abs_le hs₂ hC₂ hφi)]
    congr 1; funext x; ring
  rw [e1, e2, h₁ φ hφ hφc hφU, h₂ φ hφ hφc hφU]

end PegdenSmartAdapter

end RandomSandpile

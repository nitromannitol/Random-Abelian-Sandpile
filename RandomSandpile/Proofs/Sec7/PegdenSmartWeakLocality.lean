import RandomSandpile.Proofs.Sec7.PegdenSmartAdapterWeak

/-! # Locality of weak solutions

The weak Laplace equation depends only on the values of the solution and density on the domain.
-/

noncomputable section

open MeasureTheory Filter

namespace RandomSandpile

/-- Changes outside the unit ball, and almost-everywhere changes of the density inside it,
leave the weak Laplace equation unchanged. -/
theorem isWeakSolutionLaplace_ball_congr {d : ℕ} {u u' s s' : Rd d → ℝ}
    (hu : ∀ x ∈ Metric.ball (0 : Rd d) 1, u x = u' x)
    (hs : s =ᵐ[volume.restrict (Metric.ball (0 : Rd d) 1)] s') :
    IsWeakSolutionLaplace (Metric.ball 0 1) u s ↔
      IsWeakSolutionLaplace (Metric.ball 0 1) u' s' := by
  have hs' : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Rd d) 1 → s x = s' x :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).1 hs
  have heq (φ : Rd d → ℝ) (hφ : tsupport φ ⊆ Metric.ball (0 : Rd d) 1) :
      (∫ x, u x * Matrix.trace (hessian φ x)) =
          ∫ x, u' x * Matrix.trace (hessian φ x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Metric.ball (0 : Rd d) 1
    · rw [hu x hx]
    · have hxt : x ∉ tsupport φ := fun h => hx (hφ h)
      rw [PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport hxt, Matrix.trace_zero,
        mul_zero, mul_zero]
  have heqs (φ : Rd d → ℝ) (hφ : tsupport φ ⊆ Metric.ball (0 : Rd d) 1) :
      (∫ x, s x * φ x) = ∫ x, s' x * φ x := by
    apply integral_congr_ae
    filter_upwards [hs'] with x hx
    by_cases hxb : x ∈ Metric.ball (0 : Rd d) 1
    · rw [hx hxb]
    · have hxt : x ∉ tsupport φ := fun h => hxb (hφ h)
      rw [image_eq_zero_of_notMem_tsupport hxt, mul_zero, mul_zero]
  constructor <;> intro h φ hφ hφc hφU
  · rw [← heq φ hφU, ← heqs φ hφU]
    exact h φ hφ hφc hφU
  · rw [heq φ hφU, heqs φ hφU]
    exact h φ hφ hφc hφU

end RandomSandpile

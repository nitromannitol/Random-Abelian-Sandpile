import RandomSandpile.Proofs.Sec7.PegdenSmartSmoothPairingRestriction

/-!
# Subtraction of weak solutions with locally bounded densities

Weak solutions with continuous potentials and locally essentially bounded densities are
closed under subtraction.
-/

noncomputable section

open MeasureTheory

namespace RandomSandpile.PegdenSmartAdapter

variable {d : ℕ}

/-- The difference of weak solutions is a weak solution for the difference of their densities. -/
theorem isWeakSolutionLaplace_sub_of_memLp_top {U : Set (Rd d)} (hU : IsOpen U)
    {u v s₁ s₂ : Rd d → ℝ} (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (hs₁ : MemLp s₁ ⊤ (volume.restrict U)) (hs₂ : MemLp s₂ ⊤ (volume.restrict U))
    (h₁ : IsWeakSolutionLaplace U u s₁) (h₂ : IsWeakSolutionLaplace U v s₂) :
    IsWeakSolutionLaplace U (fun x => u x - v x) (fun x => s₁ x - s₂ x) := by
  intro φ hφ hφc hφU
  have e₁ : ∫ x, (u x - v x) * Matrix.trace (hessian φ x) =
      (∫ x, u x * Matrix.trace (hessian φ x)) - ∫ x, v x * Matrix.trace (hessian φ x) := by
    rw [← integral_sub (integrable_and_integral_mul_trace_hessian_smooth_eq hU hu hφ hφc hφU).1
      (integrable_and_integral_mul_trace_hessian_smooth_eq hU hv hφ hφc hφU).1]
    congr 1
    funext x
    ring
  have e₂ : ∫ x, (s₁ x - s₂ x) * φ x =
      (∫ x, s₁ x * φ x) - ∫ x, s₂ x * φ x := by
    rw [← integral_sub (integrable_and_integral_mul_smooth_test_eq hs₁ hφ hφc hφU).1
      (integrable_and_integral_mul_smooth_test_eq hs₂ hφ hφc hφU).1]
    congr 1
    funext x
    ring
  rw [e₁, e₂, h₁ φ hφ hφc hφU, h₂ φ hφ hφc hφU]

end RandomSandpile.PegdenSmartAdapter

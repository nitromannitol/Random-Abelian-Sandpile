import RandomSandpile.Proofs.Sec7.PegdenSmartLocalTestHessianEntry

/-! # Trace of the Hessian of a zero extension

The diagonal sum of the nested local derivative is the trace of the ambient Hessian. -/

open TopologicalSpace
open scoped Manifold ContDiff

namespace RandomSandpile

/-- The diagonal sum of the nested local derivative is the trace of the Hessian of its
zero extension. -/
theorem trace_hessian_zeroExtension {d : ℕ} (U : Opens (Rd d)) (g : U → ℝ)
    (hg : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (x : U) :
    (∑ i : Fin d, (mvfderiv 𝓘(ℝ, Rd d)
      (show U → (Rd d →L[ℝ] ℝ) from fun y => mvfderiv 𝓘(ℝ, Rd d) g y) x)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
      Matrix.trace (hessian (Subtype.val.extend g 0) x.val) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  exact hessian_zeroExtension_apply U g hg hc x i i

end RandomSandpile

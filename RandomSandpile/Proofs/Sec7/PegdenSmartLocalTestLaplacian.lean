import RandomSandpile.Proofs.Sec7.PegdenSmartLocalTestHessianTrace
import RandomSandpile.Proofs.PegdenSmart

/-! # Laplacian of a zero extension

The diagonal sum of the nested local derivative is the Laplacian of the zero extension. -/

open TopologicalSpace
open scoped Manifold ContDiff Laplacian

namespace RandomSandpile

/-- The diagonal sum of the nested local derivative is the Laplacian of its zero extension. -/
theorem laplacian_zeroExtension {d : ℕ} (U : Opens (Rd d)) (g : U → ℝ)
    (hg : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (x : U) :
    (∑ i : Fin d, (mvfderiv 𝓘(ℝ, Rd d)
      (show U → (Rd d →L[ℝ] ℝ) from fun y => mvfderiv 𝓘(ℝ, Rd d) g y) x)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
      Δ (Subtype.val.extend g 0) x.val := by
  rw [trace_hessian_zeroExtension U g hg hc x, trace_hessian_eq_laplacian]

end RandomSandpile

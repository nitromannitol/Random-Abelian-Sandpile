import RandomSandpile.Proofs.Sec7.PegdenSmartLocalTestHessianEntry
import RandomSandpile.Proofs.Sec7.PegdenSmartAdapterWeak

/-! # Support of the Hessian of a zero-extended local test

The ambient Hessian vanishes outside the open domain of a compactly supported local test. -/

open Function Set TopologicalSpace
open scoped Manifold ContDiff

namespace RandomSandpile

/-- The Hessian of a zero-extended local test vanishes outside its domain. -/
theorem hessian_zeroExtension_eq_zero_of_not_mem {d : ℕ} (U : Opens (Rd d)) (g : U → ℝ)
    (_hg : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) {x : Rd d} (hx : x ∉ U) :
    hessian (Subtype.val.extend g 0) x = 0 := by
  have hs : tsupport (Subtype.val.extend g 0) ⊆ (U : Set (Rd d)) :=
    (hc.tsupport_extend_zero_subset continuous_subtype_val).trans (Subtype.coe_image_subset _ _)
  exact PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport (fun h => hx (hs h))

/-- Each Hessian entry of a zero-extended local test vanishes outside its domain. -/
theorem hessian_zeroExtension_apply_eq_zero_of_not_mem {d : ℕ} (U : Opens (Rd d))
    (g : U → ℝ) (hg : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) {x : Rd d} (hx : x ∉ U) (i j : Fin d) :
    hessian (Subtype.val.extend g 0) x i j = 0 := by
  rw [hessian_zeroExtension_eq_zero_of_not_mem U g hg hc hx]
  rfl

end RandomSandpile

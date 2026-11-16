import RandomSandpile.Defs.Viscosity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Hessian entries of zero-extended smooth functions

The ordered entries of the ambient Hessian agree with the nested manifold derivative. -/

open Function Set TopologicalSpace
open scoped Manifold ContDiff

namespace LocalTestFirstDerivative

variable {d : ℕ} (U : Opens (EuclideanSpace ℝ (Fin d)))

private theorem inclusionDerivative (x : U) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) x.val).toContinuousLinearMap.comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
          𝓘(ℝ, EuclideanSpace ℝ (Fin d)) Subtype.val x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
  have hi := (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (U := U) (n := (⊤ : ℕ∞))).mdifferentiable (by simp)
  have h := (hi x).mvfderiv
  have he := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq (H := EuclideanSpace ℝ (Fin d)) U (x := x)
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply] at he
  simp only [mvfderiv, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    chartAt_self_eq, OpenPartialHomeomorph.refl_apply, Function.id_comp,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Set.range_id, fderivWithin_univ] at h
  have hx : chartAt (EuclideanSpace ℝ (Fin d)) x x = x.val := rfl
  rw [hx] at h
  change (id : EuclideanSpace ℝ (Fin d) → _) =ᶠ[nhds x.val]
    (Subtype.val ∘ (chartAt (EuclideanSpace ℝ (Fin d)) x).symm) at he
  rw [← he.fderiv_eq (𝕜 := ℝ)] at h
  simpa using h

private theorem zeroExtension (g : U → ℝ)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (x : U) :
    mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) g x =
      (mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) (Subtype.val.extend g 0) x.val).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
          𝓘(ℝ, EuclideanSpace ℝ (Fin d)) Subtype.val x) ∧
    mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) g x =
      (fderiv ℝ (Subtype.val.extend g 0) x.val).comp
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x.val).toContinuousLinearMap.comp
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
            𝓘(ℝ, EuclideanSpace ℝ (Fin d)) Subtype.val x)) ∧
    mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) g x =
      fderiv ℝ (Subtype.val.extend g 0) x.val := by
  have heq : (Subtype.val.extend g 0) ∘ (Subtype.val : U → EuclideanSpace ℝ (Fin d)) = g := by
    funext y
    exact Subtype.val_injective.extend_apply g 0 y
  have hF := (hg.extend_zero hc).mdifferentiable (by simp)
  have hi := (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d))) (U := U) (n := (⊤ : ℕ∞))).mdifferentiable (by simp)
  have h := mvfderiv_comp x (hF x.val) (hi x)
  rw [heq] at h
  refine ⟨h, ?_, ?_⟩
  · rw [h, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_assoc]
  · rw [h, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_assoc, inclusionDerivative U x]
    ext v
    rfl


end LocalTestFirstDerivative

namespace LocalTestSecondDerivative

variable {d : ℕ} (U : Opens (EuclideanSpace ℝ (Fin d)))

private theorem zeroExtension (g : U → ℝ)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (x : U) :
    mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
      (show U → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) from
        fun y => mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) g y) x =
      (fderiv ℝ (fderiv ℝ (Subtype.val.extend g 0)) x.val).comp
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x.val).toContinuousLinearMap.comp
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
            𝓘(ℝ, EuclideanSpace ℝ (Fin d)) Subtype.val x)) := by
  have heq : (show U → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) from
      fun y => mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) g y) =
      (fderiv ℝ (Subtype.val.extend g 0)) ∘ Subtype.val := by
    funext y
    exact (LocalTestFirstDerivative.zeroExtension U g hg hc y).2.2
  have hF : ContDiff ℝ 1 (fderiv ℝ (Subtype.val.extend g 0)) :=
    (contMDiff_iff_contDiff.mp (hg.extend_zero hc)).fderiv_right (by simp)
  have hF' := (contMDiff_iff_contDiff.mpr hF).mdifferentiable (by simp)
  have hi := (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (U := U) (n := (⊤ : ℕ∞))).mdifferentiable (by simp)
  rw [heq, mvfderiv_comp x (hF' x.val) (hi x), mvfderiv_eq_fderiv,
    ContinuousLinearMap.comp_assoc]

end LocalTestSecondDerivative

namespace RandomSandpile

/-- The ordered Hessian entry of the zero extension agrees with the nested local derivative. -/
theorem hessian_zeroExtension_apply {d : ℕ} (U : Opens (Rd d)) (g : U → ℝ)
    (hg : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (x : U) (i j : Fin d) :
    (mvfderiv 𝓘(ℝ, Rd d)
      (show U → (Rd d →L[ℝ] ℝ) from fun y => mvfderiv 𝓘(ℝ, Rd d) g y) x)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      hessian (Subtype.val.extend g 0) x.val i j := by
  have h := LocalTestSecondDerivative.zeroExtension U g hg hc x
  rw [LocalTestFirstDerivative.inclusionDerivative U x] at h
  have he := congrArg (fun f => f (EuclideanSpace.single i 1)
    (EuclideanSpace.single j 1)) h
  exact he

end RandomSandpile

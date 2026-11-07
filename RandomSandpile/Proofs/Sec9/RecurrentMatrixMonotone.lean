import RandomSandpile.Proofs.Sec9.RecurrentOperatorShift
import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasic

/-! Matrix monotonicity of finite-volume recurrent curvature measures. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal
noncomputable section
namespace RandomSandpile
open EffectiveOperatorBasic MuLipschitz
variable {d : ℕ}

/-- Adding a positive semidefinite matrix raises the upper recurrent measure
and lowers the lower recurrent measure. -/
theorem recurrent_matrix_monotone (B : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    muRecurrent B η l M ≤ muRecurrent B η l (M + A) ∧
      muStarRecurrent B η l (M + A) ≤ muStarRecurrent B η l M := by
  have hs : ∀ {w : Site d → ℝ}, w ∈ recurrentPerturbed B η l M →
      w - qMZ A ∈ recurrentPerturbed B η l (M + A) := by
    intro w hw
    obtain ⟨r, hr, rfl⟩ := hw
    refine ⟨r, hr, ?_⟩
    funext x; simp only [Pi.sub_apply, qMZ_add]; ring
  have ht : ∀ {w : Site d → ℝ}, w ∈ recurrentPerturbed B η l (M + A) →
      w + qMZ A ∈ recurrentPerturbed B η l M := by
    intro w hw
    obtain ⟨r, hr, rfl⟩ := hw
    refine ⟨r, hr, ?_⟩
    funext x; simp only [Pi.add_apply, qMZ_add]; ring
  constructor
  · refine iSup₂_le fun w hw => ?_
    refine le_trans ?_ (le_iSup₂_of_le (w - qMZ A) (hs hw) le_rfl)
    refine volume_supGradSet_le_of_shift supGradSetVolume (fun x => -gradQ A x)
      fun x _ p hp y hy => ?_
    have h1 := hp y hy
    have h2 := qMZ_convex hA x y
    simp only [Pi.sub_apply, ← sub_eq_add_neg, inner_sub_left]
    linarith
  · refine iSup₂_le fun w hw => ?_
    refine le_trans ?_ (le_iSup₂_of_le (w + qMZ A) (ht hw) le_rfl)
    refine volume_subGradSet_le_of_shift supGradSetVolume (fun x => gradQ A x)
      fun x _ p hp y hy => ?_
    have h1 := hp y hy
    have h2 := qMZ_convex hA x y
    simp only [Pi.add_apply, inner_add_left]
    linarith

end RandomSandpile

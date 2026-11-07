import RandomSandpile.Proofs.Sec5.ABP
import RandomSandpile.Defs.Recurrent

/-! The discrete Alexandroff-Bakelman-Pucci estimates for recurrent perturbations. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal

namespace RandomSandpile
open ABP

/-- Both contact measures control recurrent perturbations on a lattice ball. -/
theorem recurrent_abp (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
        (muRecurrent (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
          ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
            w x ≤ sSup (w '' bdry (ballZ0 (n : ℝ))) +
              C * n * (muRecurrent (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / (d : ℝ))) ∧
        (muStarRecurrent (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
          ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
            sInf (w '' bdry (ballZ0 (n : ℝ))) ≤
              w x + C * n * (muStarRecurrent (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / (d : ℝ))) := by
  obtain ⟨c, hc, hrad⟩ := ballVolumeRadius d (by omega)
  refine ⟨3 * c, by positivity, fun n η l M => ⟨fun hμ w hw x hx => ?_, fun hμ w hw x hx => ?_⟩⟩
  · have hfin : (w '' bdry (ballZ0 (d := d) (n : ℝ))).Finite :=
      ((dClosure_finite (ballZ0_finite _)).subset (bdry_subset_dClosure _)).image w
    refine abp_supGrad_of_steps tiltedPlaneAbove slidePlane closureBallDiam hc hrad n w _
      (fun z hz => le_csSup hfin.bddAbove (Set.mem_image_of_mem w hz)) _ ?_ hμ x hx
    exact le_iSup₂ (f := fun w _ => volume (supGradSet w (ballZ0 (d := d) (n : ℝ)))) w hw
  · have hfin : (w '' bdry (ballZ0 (d := d) (n : ℝ))).Finite :=
      ((dClosure_finite (ballZ0_finite _)).subset (bdry_subset_dClosure _)).image w
    have hV : volume (supGradSet (fun z => -w z) (ballZ0 (d := d) (n : ℝ))) ≤
        muStarRecurrent (ballZ0 (n : ℝ)) η l M := by
      rw [← subGradNegVolume]
      exact le_iSup₂ (f := fun w _ => volume (subGradSet w (ballZ0 (d := d) (n : ℝ)))) w hw
    have h := abp_supGrad_of_steps tiltedPlaneAbove slidePlane closureBallDiam hc hrad n (fun z => -w z)
      (-sInf (w '' bdry (ballZ0 (n : ℝ))))
      (fun z hz => neg_le_neg (csInf_le hfin.bddBelow (Set.mem_image_of_mem w hz))) _ hV hμ x hx
    linarith

end RandomSandpile

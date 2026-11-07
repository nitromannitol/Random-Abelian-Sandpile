import RandomSandpile.Proofs.Sec9.RecurrentLowerConvergence
import RandomSandpile.Proofs.Sec9.RecurrentMu
import RandomSandpile.Proofs.Sec6.MuMonotone
import RandomSandpile.Steps.Sec6.EffectiveOperatorBasic

/-! Monotonicity of recurrent gradient measures in the scalar curvature. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal Pointwise Matrix
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- Increasing scalar curvature increases the recurrent upper measure. -/
theorem muRecurrent_le_add (A : Set (Site d)) (η : Site d → ℤ)
    (l s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hs : 0 ≤ s) :
    muRecurrent A η l M ≤ muRecurrent A η (l + s) M := by
  refine iSup₂_le fun w hw => ?_
  obtain ⟨r, hr, rfl⟩ := hw
  let w : Site d → ℝ := fun x => (r x : ℝ) - (qlZ l x + qMZ M x)
  have hw' : w - qlZ s ∈ recurrentPerturbed A η (l + s) M := by
    refine ⟨r, hr, ?_⟩
    funext x
    simp only [Pi.sub_apply, w, qlZ_add]
    ring
  refine le_trans ?_ (le_iSup₂_of_le (w - qlZ s) hw' le_rfl)
  refine volume_supGradSet_le_of_shift supGradSetVolume (fun x => -((s / d) • toE x))
    fun x _ p hp => ?_
  simpa [sub_eq_add_neg] using (supGradShift d w x A s hs).1 p hp

/-- Decreasing scalar curvature increases the recurrent lower measure. -/
theorem muStarRecurrent_le_sub (A : Set (Site d)) (η : Site d → ℤ)
    (l s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hs : 0 ≤ s) :
    muStarRecurrent A η l M ≤ muStarRecurrent A η (l - s) M := by
  refine iSup₂_le fun w hw => ?_
  obtain ⟨r, hr, rfl⟩ := hw
  let w : Site d → ℝ := fun x => (r x : ℝ) - (qlZ l x + qMZ M x)
  have hw' : w + qlZ s ∈ recurrentPerturbed A η (l - s) M := by
    refine ⟨r, hr, ?_⟩
    funext x
    simp only [Pi.add_apply, w, qlZ_sub]
    ring
  refine le_trans ?_ (le_iSup₂_of_le (w + qlZ s) hw' le_rfl)
  exact volume_subGradSet_le_of_shift supGradSetVolume (fun x => (s / d) • toE x)
    fun x _ p hp => (supGradShift d w x A s hs).2 p hp

/-- The recurrent upper density is bounded by the ordinary upper density. -/
theorem muRecurrentBar_le_muBar (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : muRecurrentBar E l M ≤ muBar E l M := by
  unfold muRecurrentBar muBar
  refine ENNReal.toReal_mono (EffectiveOperatorBasic.lintegral_mu_ne_top (by omega) E l M)
    (lintegral_mono fun η => ?_)
  exact limsup_le_limsup (Eventually.of_forall fun n => ENNReal.div_le_div_right
    (recurrentMuLe d hd _ (ABP.ballZ0_finite _) η l M) _)

/-- At sufficiently negative curvature, the recurrent upper density vanishes. -/
theorem muRecurrentBar_eq_zero (hd : 2 ≤ d) (E : RandomEnvironment d) {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hl : l ≤ -(E.ηmax : ℝ) - M.trace) :
    muRecurrentBar E l M = 0 := by
  have h := (muRecurrent_convergence hd E l M).2.1
  rw [max_eq_right (by linarith), zero_div, zero_pow (by omega)] at h
  exact le_antisymm h (muRecurrent_convergence hd E l M).1

/-- The upper density is monotone in the scalar curvature. -/
theorem muRecurrentBar_mono (hd : 2 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) : Monotone (fun l => muRecurrentBar E l M) := by
  intro a b hab
  have hfinite : (∫⁻ η, limsup (fun n : ℕ => muRecurrent (ballZ0 (n : ℝ)) η b M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (EffectiveOperatorBasic.lintegral_mu_ne_top (by omega) E b M) ?_
    refine lintegral_mono fun η => ?_
    exact limsup_le_limsup (Eventually.of_forall fun n => ENNReal.div_le_div_right
      (recurrentMuLe d hd _ (ABP.ballZ0_finite _) η b M) _)
  unfold muRecurrentBar
  refine ENNReal.toReal_mono hfinite (lintegral_mono fun η => ?_)
  refine limsup_le_limsup (Eventually.of_forall fun n => ENNReal.div_le_div_right ?_ _)
  simpa using muRecurrent_le_add (ballZ0 (n : ℝ)) η a (b - a) M (sub_nonneg.mpr hab)

/-- The lower density is antitone in the scalar curvature. -/
theorem muStarRecurrentBar_anti (hd : 2 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) : Antitone (fun l => muStarRecurrentBar E l M) := by
  intro a b hab
  dsimp only
  rw [muStarRecurrentBar_eq hd E b M, muStarRecurrentBar_eq hd E a M]
  exact EffectiveOperatorBasic.muStarBar_anti muMonotone (by omega) E M hab

end RandomSandpile

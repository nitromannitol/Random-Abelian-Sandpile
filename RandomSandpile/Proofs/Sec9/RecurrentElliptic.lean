import RandomSandpile.Proofs.Sec9.RecurrentMatrixMonotone
import RandomSandpile.Proofs.Sec9.RecurrentMonotone

/-! Degenerate ellipticity of the recurrent effective operator. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal
noncomputable section
namespace RandomSandpile
open EffectiveOperatorBasic MuLipschitz
variable {d : ℕ}

/-- The upper recurrent density is monotone in positive semidefinite increments. -/
theorem muRecurrentBar_matrix_mono (hd : 2 ≤ d) (E : RandomEnvironment d) (l : ℝ)
    (M A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    muRecurrentBar E l M ≤ muRecurrentBar E l (M + A) := by
  have hfinite : (∫⁻ η, limsup (fun n : ℕ => muRecurrent (ballZ0 (n : ℝ)) η l (M + A) /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (lintegral_mu_ne_top (by omega) E l (M + A)) ?_
    refine lintegral_mono fun η => ?_
    exact limsup_le_limsup (Eventually.of_forall fun n => ENNReal.div_le_div_right
      (recurrentMuLe d hd _ (ABP.ballZ0_finite _) η l (M + A)) _)
  unfold muRecurrentBar
  refine ENNReal.toReal_mono hfinite (lintegral_mono fun η => ?_)
  exact limsup_le_limsup (Eventually.of_forall fun n => ENNReal.div_le_div_right
    (recurrent_matrix_monotone (ballZ0 (n : ℝ)) η l M A hA).1 _)

/-- The recurrent effective operator is degenerate elliptic in the
Crandall-Ishii-Lions convention. -/
theorem recurrent_degenerateElliptic (hd : 2 ≤ d) (E : RandomEnvironment d) :
    DegenerateElliptic (effOpRecurrent E) := by
  intro M N _ _ hNM
  let a := effOpRecurrent E M
  let b := effOpRecurrent E N
  have ha := recurrentCommonZero_at_operator recurrent_common_zero hd E M
  have hb := recurrentCommonZero_at_operator recurrent_common_zero hd E N
  change muRecurrentBar E a M = 0 ∧ muStarRecurrentBar E a M = 0 at ha
  change muRecurrentBar E b N = 0 ∧ muStarRecurrentBar E b N = 0 at hb
  by_contra h
  have hab : a < b := lt_of_not_ge h
  have hzeroM : muRecurrentBar E b M = 0 := by
    have hmatb := muRecurrentBar_matrix_mono hd E b M (N - M) hNM
    rw [add_sub_cancel, hb.1] at hmatb
    exact le_antisymm hmatb ENNReal.toReal_nonneg
  have hanti := muStarRecurrentBar_anti hd E M hab.le
  have hzeroS : muStarRecurrentBar E b M = 0 :=
    le_antisymm (by simpa [ha.2] using hanti) ENNReal.toReal_nonneg
  obtain ⟨l, hl, hu⟩ := recurrent_common_zero d hd E M
  have hal : a = l := hu a ha
  have hbl : b = l := hu b ⟨hzeroM, hzeroS⟩
  linarith

end RandomSandpile

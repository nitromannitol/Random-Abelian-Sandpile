import RandomSandpile.Proofs.Sec9.RecurrentOperatorBasic
import RandomSandpile.Proofs.Sec7.FlatTiltedZero
import RandomSandpile.Steps.Sec9.RecurrentZeroBackground

/-! # Distinguishing the recurrent operator on low backgrounds -/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal

namespace RandomSandpile

/-- On backgrounds bounded above by `d - 1`, the recurrent operator at zero
is at least `d`. -/
theorem le_effOpRecurrent_zero_of_low {d : ℕ} (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hE : ∀ᵐ η ∂E.P, ∀ x, η x ≤ (d : ℤ) - 1) :
    (d : ℝ) ≤ effOpRecurrent E 0 := by
  by_contra h
  have hpos := muStarBar_zero_pos (by omega) E hE (not_le.mp h)
  have hzero := (recurrentCommonZero_at_operator recurrent_common_zero hd E 0).2
  rw [muStarRecurrentBar_eq hd E] at hzero
  linarith

/-- For backgrounds bounded above by `d - 1`, the printed equality-level
operator is strictly smaller than the recurrent operator at zero. -/
theorem effOp_zero_lt_effOpRecurrent_of_low {d : ℕ} (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hE : ∀ᵐ η ∂E.P, ∀ x, η x ≤ (d : ℤ) - 1) :
    effOp E 0 < effOpRecurrent E 0 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrpos : 0 < effOpRecurrent E 0 :=
    hdpos.trans_le (le_effOpRecurrent_zero_of_low hd E hE)
  have hmupos := muBar_zero_pos (by omega) E hrpos
  have hzero := (recurrentCommonZero_at_operator recurrent_common_zero hd E 0).2
  rw [muStarRecurrentBar_eq hd E] at hzero
  have heq : muBar E (effOp E 0) 0 = muStarBar E (effOp E 0) 0 :=
    (isGreatest_effOp muConvergence_unconditional hd E Matrix.isSymm_zero).1
  by_contra h
  have hle : effOpRecurrent E 0 ≤ effOp E 0 := not_lt.mp h
  have hupper := EffectiveOperatorBasic.muBar_mono muMonotone (by omega) E 0 hle
  have hlower := EffectiveOperatorBasic.muStarBar_anti muMonotone (by omega) E 0 hle
  linarith

/-- The recurrent and printed operators differ at the zero background. -/
theorem recurrentOperatorZeroBackgroundDifference :
    RecurrentOperatorZeroBackgroundDifferenceStmt := by
  intro d hd E hzero
  have hE : ∀ᵐ η ∂E.P, ∀ x, η x ≤ (d : ℤ) - 1 := by
    filter_upwards [hzero] with η hη x
    rw [hη]
    have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    simp only [Pi.zero_apply]
    omega
  exact ne_of_gt (effOp_zero_lt_effOpRecurrent_of_low hd E hE)

end RandomSandpile

import RandomSandpile.Steps.Sec9.Recurrent
import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessOuter

/-! # Vanishing tails from the Fey–Levine–Peres outer bound -/

open MeasureTheory Filter LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- The outer support bound implies C13's vanishing-tail condition. -/
theorem recurrentSSTail_of_outerBound (hout : SSOuterBoundStmt) :
    RecurrentSSTailFromHeightStmt := by
  intro d hd E hmax
  obtain ⟨R, hR, hRbound⟩ := hout d hd E.ηmin
  have hpow : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have hb := ae_all_iff.2 E.bounded
  filter_upwards [hb] with η hη
  intro ε hε
  refine ⟨R * (2 : ℝ) ^ (1 / (d : ℝ)) + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  intro z hz
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hbase hpow
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)] at hp
  have hr : R * ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ ‖toE z‖ := by
    have hs : 0 ≤ (n : ℝ) ^ (1 / (d : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    nlinarith [mul_le_mul_of_nonneg_left hp hR.le]
  have hz0 := hRbound η (fun x => ⟨(hη x).1, (hη x).2.trans hmax⟩) n z hr
  rw [hz0]
  simp only [Int.cast_zero, mul_zero]
  exact hε.le

/-- FLP Theorem 1.1 supplies the support estimate used in the height-bound theorem. -/
theorem recurrentSSTail_of_flp (hFLP : External.FeyLevinePeresRadius) :
    RecurrentSSTailFromHeightStmt :=
  recurrentSSTail_of_outerBound (ssOuterBound_of_flp hFLP)

/-- The corrected height-bound theorem, with the FLP literature input explicit. -/
theorem singleSourceRecurrent_of_flp_steps (hFLP : External.FeyLevinePeresRadius)
    (hc : RecurrentSSCompactnessStmt) (ha : RecurrentSSAdmissibilityStmt)
    (hm : RecurrentSSMinimalityStmt) : SingleSourceTheoremRecurrentStmt :=
  singleSourceRecurrent_of_steps hc ha hm (recurrentSSTail_of_flp hFLP)

end RandomSandpile

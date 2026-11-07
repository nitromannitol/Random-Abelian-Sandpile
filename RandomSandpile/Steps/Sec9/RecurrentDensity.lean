import RandomSandpile.Steps.Sec9.RecurrentViscosity
import RandomSandpile.Steps.Sec5.ABP

/-! # From finite-volume recurrentization to limiting lower density -/

open MeasureTheory Filter LatticeProb LatticeProb.Sandpile
open scoped ENNReal

namespace RandomSandpile

/-- Finite-volume equality passes to the deterministic normalized lower densities. -/
theorem muStarRecurrentBar_eq_of_finiteEquality (h : RecurrentMuStarEqualityStmt)
    {d : ℕ} (hd : 2 ≤ d) (E : RandomEnvironment d) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : muStarRecurrentBar E l M = muStarBar E l M := by
  have heq : ∀ η : Site d → ℤ, ∀ n : ℕ,
      muStarRecurrent (ballZ0 (n : ℝ)) η l M = muStar (ballZ0 (n : ℝ)) η l M :=
    fun η n => h d hd _ (ABP.ballZ0_finite _) η l M
  unfold muStarRecurrentBar muStarBar
  congr 1
  apply lintegral_congr
  intro η
  congr 1
  funext n
  rw [heq η n]

/-- The lower density of the original class vanishes at the recurrent common zero. -/
theorem muStarBar_eq_zero_at_recurrent_operator (heq : RecurrentMuStarEqualityStmt)
    (hzero : RecurrentCommonZeroStmt) {d : ℕ} (hd : 2 ≤ d)
    (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStarBar E (effOpRecurrent E M) M = 0 := by
  rw [← muStarRecurrentBar_eq_of_finiteEquality heq hd]
  exact (recurrentCommonZero_at_operator hzero hd E M).2

end RandomSandpile

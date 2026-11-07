import RandomSandpile.Steps.Sec9.RecurrentIdentificationFinite

/-! # Distinguishing the operators at the zero background -/

open MeasureTheory Filter LatticeProb

namespace RandomSandpile

/-- The recurrent quadratic of C13 gives the recurrent operator value at zero. -/
def RecurrentZeroBackgroundValueStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    (∀ᵐ η ∂E.P, η = 0) → effOpRecurrent E 0 = (d : ℝ)

/-- The original legal and stabilizing densities cross strictly below `d`. -/
def OriginalZeroBackgroundUpperBoundStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    (∀ᵐ η ∂E.P, η = 0) → effOp E 0 < (d : ℝ)

/-- The explicit zero-background values imply the difference asserted in C13. -/
theorem recurrentOperatorZeroBackgroundDifference_of_steps
    (hr : RecurrentZeroBackgroundValueStmt) (ho : OriginalZeroBackgroundUpperBoundStmt) :
    RecurrentOperatorZeroBackgroundDifferenceStmt := by
  intro d hd E hzero
  have h := ho d hd E hzero
  rw [hr d hd E hzero]
  exact ne_of_gt h

end RandomSandpile

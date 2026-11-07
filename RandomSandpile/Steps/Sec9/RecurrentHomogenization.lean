import RandomSandpile.Steps.Sec9.RecurrentDensity

/-! # Finite recurrentization and recurrent effective-operator properties -/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Fixed-boundary recurrentization: a signed stabilizing function admits a least signed
stabilizing competitor with the same boundary values, and that competitor is recurrent. -/
def RecurrentizeFixedBoundaryStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (A : Set (Site d)), A.Finite →
    ∀ (η v : Site d → ℤ),
      (∀ x ∈ A, lap v x + η x ≤ 2 * (d : ℤ) - 1) →
      ∃ r : Site d → ℤ, IsRecurrentFunction η A r ∧
        (∀ x ∈ bdry A, r x = v x) ∧
        (∀ w : Site d → ℤ, (∀ x ∈ bdry A, w x = v x) →
          (∀ x ∈ A, lap w x + η x ≤ 2 * (d : ℤ) - 1) → ∀ x ∈ A, r x ≤ w x)

/-- The recurrent operator is continuous, degenerate elliptic, and has the trace shift in C13. -/
def RecurrentOperatorBasicStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    Continuous (effOpRecurrent E) ∧ DegenerateElliptic (effOpRecurrent E) ∧
      ∀ (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ),
        effOpRecurrent E (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) =
          effOpRecurrent E M - (d : ℝ) * t

end RandomSandpile

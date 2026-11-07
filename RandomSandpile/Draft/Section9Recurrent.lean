import RandomSandpile.Defs.Recurrent
import RandomSandpile.Defs.Obstacle
import RandomSandpile.Defs.Odometer

/-! # Corrected single-source theorem (C13)

`fundamentalSolution` has the convention `ΔG = -δ₀`. The inequalities and convergence are on
punctured space, while the regular part of the limit is continuous on all of space.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- The recurrent single-source obstacle class, in the Crandall–Ishii–Lions sense. -/
def recurrentSingleSourceObstacleSet (E : RandomEnvironment d) : Set (Rd d → ℝ) :=
  {v | Continuous v ∧ (∀ x : Rd d, x ≠ 0 → 0 ≤ v x + fundamentalSolution d x) ∧
    ViscFromBelowGE (effOpRecurrent E) {x : Rd d | x ≠ 0}
      (fun x => v x + fundamentalSolution d x)}

/-- All single-source piles admit stabilizing toppling functions. -/
def SingleSourceFinite (η : Site d → ℤ) : Prop :=
  ∀ n : ℕ, (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty

/-- Vanishing tail (VT), written with eventual bounds and an arbitrary positive error. -/
def SingleSourceVanishingTail (η : Site d → ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
    ∀ z : Site d, R * (n : ℝ) ^ (1 / (d : ℝ)) ≤ ‖toE z‖ →
      (n : ℝ) ^ (-(2 / (d : ℝ))) * (singleSourceOdometer η n z : ℝ) ≤ ε

/-- The common conclusion of the two versions of the corrected single-source theorem. -/
def SingleSourceRecurrentConclusion (E : RandomEnvironment d) : Prop :=
  ∃ v : Rd d → ℝ, IsLeast (recurrentSingleSourceObstacleSet E) v ∧
    ∀ᵐ η ∂E.P, SingleSourceFinite η ∧
      TendstoLocallyUniformlyOn
        (fun n : ℕ => rescaleSingleSource (singleSourceOdometer η n) n)
        (fun x => v x + fundamentalSolution d x) atTop {x : Rd d | x ≠ 0}

/-- Corrected Theorem 9.2, with the printed upper bound `η ≤ 2d - 2`. -/
def SingleSourceTheoremRecurrentStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    E.ηmax ≤ 2 * (d : ℤ) - 2 → SingleSourceRecurrentConclusion E

/-- The finite-odometer and vanishing-tail extension in C13. -/
def SingleSourceTheoremRecurrentVTStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    (∀ᵐ η ∂E.P, SingleSourceFinite η ∧ SingleSourceVanishingTail η) →
      SingleSourceRecurrentConclusion E

/-- For backgrounds recurrent on every finite set, the recurrent and original operators agree. -/
def RecurrentOperatorIdentificationStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    (∀ᵐ η ∂E.P, ∀ A : Set (Site d), A.Finite → IsRecurrentOn η A) →
      effOpRecurrent E = effOp E

/-- At the zero background the two operators take different values at the zero matrix. -/
def RecurrentOperatorZeroBackgroundDifferenceStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    (∀ᵐ η ∂E.P, η = 0) → effOpRecurrent E 0 ≠ effOp E 0

end RandomSandpile

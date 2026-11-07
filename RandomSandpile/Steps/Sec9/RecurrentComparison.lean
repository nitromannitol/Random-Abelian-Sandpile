import RandomSandpile.Steps.Sec9.RecurrentViscosity

/-! # The positivity-set and far-field comparison steps for C13 -/

open MeasureTheory Filter LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- A function has zero upper limit at infinity. -/
def VanishesAboveAtInfinity {d : ℕ} (u : Rd d → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : Rd d, R ≤ ‖x‖ → u x ≤ ε

/-- On the positivity set, eventual toppling and recurrent correctors yield the other inequality. -/
def RecurrentSSPositiveSubsolutionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ᵐ η ∂E.P, SingleSourceFinite η → SingleSourceVanishingTail η →
      ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
        ViscFromAboveLE (effOpRecurrent E) {x : Rd d | x ≠ 0 ∧ 0 < u x} u

/-- The lattice vanishing tail passes to every locally uniform subsequential limit. -/
def RecurrentSSLimitDecayStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ᵐ η ∂E.P, SingleSourceFinite η → SingleSourceVanishingTail η →
      ∀ u : Rd d → ℝ, IsSSSubseqLimit η u → VanishesAboveAtInfinity u

/-- Punctured-domain comparison with the Green singularity and zero upper limit at infinity. -/
def RecurrentSSComparisonStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ v : Rd d → ℝ, Continuous v →
      (∀ x : Rd d, x ≠ 0 → 0 ≤ v x + fundamentalSolution d x) →
      ViscFromAboveLE (effOpRecurrent E)
        {x : Rd d | x ≠ 0 ∧ 0 < v x + fundamentalSolution d x}
        (fun x => v x + fundamentalSolution d x) →
      VanishesAboveAtInfinity (fun x => v x + fundamentalSolution d x) →
        ∀ w ∈ recurrentSingleSourceObstacleSet E, ∀ x, v x ≤ w x

/-- The limiting comparison and the two independent limit properties imply minimality. -/
theorem recurrentSSMinimality_of_comparison (hp : RecurrentSSPositiveSubsolutionStmt)
    (ht : RecurrentSSLimitDecayStmt) (hc : RecurrentSSComparisonStmt) :
    RecurrentSSMinimalityStmt := by
  intro d hd E
  filter_upwards [hp d hd E, ht d hd E] with η hpη htη
  intro hfinite htail v hvc hv
  exact hc d hd E v hvc (fun x hx => hv.nonneg hx)
    (hpη hfinite htail _ hv) (htη hfinite htail _ hv)

end RandomSandpile

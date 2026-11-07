import RandomSandpile.Steps.Sec9.RecurrentIdentification

/-! # Finite-volume reduction for operator identification -/

open MeasureTheory Filter LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Upper measures agree on finite domains for backgrounds recurrent on every finite set.
This formulation also covers backgrounds which are not stable. -/
def RecurrentMuEqualityGlobalStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (η : Site d → ℤ),
    (∀ A : Set (Site d), A.Finite → IsRecurrentOn η A) →
      ∀ (A : Set (Site d)), A.Finite → ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
        muRecurrent A η l M = mu A η l M

/-- Finite-volume comparison gives equality of the limiting upper densities. -/
theorem recurrentUpperDensityEquality_of_finite (hmu : RecurrentMuEqualityGlobalStmt) :
    RecurrentUpperDensityEqualityStmt := by
  intro d hd E hrec l M
  unfold muRecurrentBar muBar
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hrec] with η hη
  congr 1
  funext n
  rw [hmu d hd η hη _ (ABP.ballZ0_finite _) l M]

/-- The full operator identification from finite-volume measure equalities and common zero. -/
theorem recurrentOperatorIdentification_of_finiteSteps (hupper : RecurrentMuEqualityGlobalStmt)
    (hlower : RecurrentMuStarEqualityStmt) (hzero : RecurrentCommonZeroStmt) :
    RecurrentOperatorIdentificationStmt :=
  recurrentOperatorIdentification_of_densitySteps (recurrentUpperDensityEquality_of_finite hupper)
    hlower hzero

end RandomSandpile

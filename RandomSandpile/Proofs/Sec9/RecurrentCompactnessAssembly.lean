import RandomSandpile.Proofs.Sec9.RecurrentCorrectorEquicontinuity
import RandomSandpile.Proofs.Sec9.RecurrentReducedAssembly

/-! # Recurrent single-source convergence reduced to viscosity inequalities -/

open LatticeProb

namespace RandomSandpile

/-- The VT convergence theorem follows from Alexandrov's theorem and the two
recurrent viscosity inequalities. -/
theorem singleSourceRecurrentVT_of_viscosity (hA : AlexandrovStmt)
    (hsuper : RecurrentSSSupersolutionStmt) (hsub : RecurrentSSPositiveSubsolutionStmt) :
    SingleSourceTheoremRecurrentVTStmt :=
  singleSourceRecurrentVT_of_viscositySteps hA recurrentSSCompactness hsuper hsub

/-- The height-bound convergence theorem additionally uses the explicit
Fey–Levine–Peres outer-radius input. -/
theorem singleSourceRecurrent_of_viscosity (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (hsuper : RecurrentSSSupersolutionStmt)
    (hsub : RecurrentSSPositiveSubsolutionStmt) : SingleSourceTheoremRecurrentStmt :=
  singleSourceRecurrent_of_viscositySteps hFLP hA recurrentSSCompactness hsuper hsub

end RandomSandpile

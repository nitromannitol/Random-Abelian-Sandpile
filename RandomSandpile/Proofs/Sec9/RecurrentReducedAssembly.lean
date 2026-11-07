import RandomSandpile.Proofs.Sec9.RecurrentDecayComparison
import RandomSandpile.Steps.Sec9.RecurrentAssembly

/-! # C13 assembly with decay and comparison discharged -/

open LatticeProb

namespace RandomSandpile

/-- The VT theorem reduces to compactness and the two viscosity inequalities. -/
theorem singleSourceRecurrentVT_of_viscositySteps (hA : AlexandrovStmt)
    (hcompact : RecurrentSSCompactnessStmt) (hsuper : RecurrentSSSupersolutionStmt)
    (hsub : RecurrentSSPositiveSubsolutionStmt) : SingleSourceTheoremRecurrentVTStmt :=
  singleSourceRecurrentVT_of_comparisonSteps hcompact hsuper hsub recurrentSSLimitDecay
    (recurrentSSComparison_of_alexandrov hA)

/-- The height-bound theorem uses the explicit FLP and Alexandrov inputs. -/
theorem singleSourceRecurrent_of_viscositySteps (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (hcompact : RecurrentSSCompactnessStmt)
    (hsuper : RecurrentSSSupersolutionStmt) (hsub : RecurrentSSPositiveSubsolutionStmt) :
    SingleSourceTheoremRecurrentStmt :=
  singleSourceRecurrent_of_comparisonSteps hFLP hcompact hsuper hsub recurrentSSLimitDecay
    (recurrentSSComparison_of_alexandrov hA)

end RandomSandpile

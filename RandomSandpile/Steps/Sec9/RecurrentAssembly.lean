import RandomSandpile.Steps.Sec9.RecurrentTail
import RandomSandpile.Steps.Sec9.RecurrentComparison

/-! # Assembly of the C13 single-source theorem from its comparison steps -/

open LatticeProb

namespace RandomSandpile

/-- The VT theorem from compactness, both viscosity inequalities, decay and comparison. -/
theorem singleSourceRecurrentVT_of_comparisonSteps (hcompact : RecurrentSSCompactnessStmt)
    (hsuper : RecurrentSSSupersolutionStmt) (hsub : RecurrentSSPositiveSubsolutionStmt)
    (hdecay : RecurrentSSLimitDecayStmt) (hcompare : RecurrentSSComparisonStmt) :
    SingleSourceTheoremRecurrentVTStmt :=
  singleSourceRecurrentVT_of_steps hcompact (recurrentSSAdmissibility_of_supersolution hsuper)
    (recurrentSSMinimality_of_comparison hsub hdecay hcompare)

/-- The height-bound theorem with Fey–Levine–Peres Theorem 1.1 as an explicit input. -/
theorem singleSourceRecurrent_of_comparisonSteps (hFLP : External.FeyLevinePeresRadius)
    (hcompact : RecurrentSSCompactnessStmt) (hsuper : RecurrentSSSupersolutionStmt)
    (hsub : RecurrentSSPositiveSubsolutionStmt) (hdecay : RecurrentSSLimitDecayStmt)
    (hcompare : RecurrentSSComparisonStmt) : SingleSourceTheoremRecurrentStmt :=
  singleSourceRecurrent_of_flp_steps hFLP hcompact
    (recurrentSSAdmissibility_of_supersolution hsuper)
    (recurrentSSMinimality_of_comparison hsub hdecay hcompare)

end RandomSandpile

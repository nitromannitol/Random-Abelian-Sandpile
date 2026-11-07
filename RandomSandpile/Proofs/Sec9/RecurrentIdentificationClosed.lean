import RandomSandpile.Proofs.Sec9.RecurrentMuEquality

/-! Operator identification after the finite-volume measure results. -/

namespace RandomSandpile

/-- Once the recurrent densities have a unique common zero, the recurrent and
original operators agree on recurrent backgrounds. -/
theorem recurrentOperatorIdentification_of_commonZero (hzero : RecurrentCommonZeroStmt) :
    RecurrentOperatorIdentificationStmt :=
  recurrentOperatorIdentification_of_finiteSteps recurrentMuEqualityGlobal
    recurrentMuStarEquality hzero

end RandomSandpile

import RandomSandpile.Proofs.Sec9.RecurrentIdentificationClosed
import RandomSandpile.Proofs.Sec9.RecurrentCommonZero

/-! Identification of the recurrent effective operator on recurrent backgrounds. -/

namespace RandomSandpile

/-- The recurrent and ordinary effective operators agree on recurrent backgrounds. -/
theorem recurrentOperatorIdentification : RecurrentOperatorIdentificationStmt :=
  recurrentOperatorIdentification_of_commonZero recurrent_common_zero

end RandomSandpile

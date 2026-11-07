import Mathlib
import RandomSandpile.Proofs.FinalSteps
import RandomSandpile.Proofs.Sec7.PegdenSmartAdapter
import RandomSandpileAudit.MainTheorem.SolutionBasic
import RandomSandpileAudit.MainTheorem.Bridge

/-!
# Solution: the main theorem from the library

Proves `RandomSandpile.StatementAudit.MainTheorem.mainTheorem`, with the statement of
`RandomSandpileAudit/MainTheorem/Challenge.lean`, from the library. The five hypotheses are sent to the
library's propositions by the equalities of `Bridge.lean`. The library's `mainTheorem_closed` takes the
Alexandrov and Lawler-Limic inputs and `PegdenSmartTouchingStmt`, which `pegdenSmartTouching_of_ps13`
derives from the two Pegden-Smart propositions and the viscosity input. Its conclusion is transported back
to the restated statement by `mainTheoremStmt_of_lib`.
-/

namespace RandomSandpile.StatementAudit.MainTheorem

theorem mainTheorem
    (hAlexandrov : AlexandrovStmt)
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS25 : PegdenSmartProp25Stmt)
    (hPS24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) :
    MainTheoremStmt := by
  have hA : _root_.RandomSandpile.AlexandrovStmt := by
    rw [← AlexandrovStmt_eq]; exact hAlexandrov
  have hL : _root_.RandomSandpile.LawlerLimicHarmonicDifferenceStmt := by
    rw [← LawlerLimicHarmonicDifferenceStmt_eq]; exact hLawlerLimicHarmonicDifference
  have h25 : _root_.RandomSandpile.PegdenSmartProp25Stmt := by
    rw [← PegdenSmartProp25Stmt_eq]; exact hPS25
  have h24 : _root_.RandomSandpile.PegdenSmartProp24Stmt := by
    rw [← PegdenSmartProp24Stmt_eq]; exact hPS24
  have hV : _root_.RandomSandpile.ViscosityWeakLaplaceStmt := by
    rw [← ViscosityWeakLaplaceStmt_eq]; exact hVW
  exact mainTheoremStmt_of_lib
    (_root_.RandomSandpile.mainTheorem_closed hA hL
      (_root_.RandomSandpile.pegdenSmartTouching_of_ps13 h25 h24 hV))

end RandomSandpile.StatementAudit.MainTheorem

import Mathlib
import RandomSandpile.Assembly.Main
import RandomSandpileAudit.MainTheorem.SolutionBasic
import RandomSandpileAudit.MainTheorem.Bridge

/-!
# Solution: the main theorem with no literature input

Proves `RandomSandpile.StatementAudit.MainTheorem.mainTheoremFinal`, with the statement of
`RandomSandpileAudit/MainTheoremFinal/Challenge.lean`, from `RandomSandpile.mainTheorem_final`
(`RandomSandpile/Assembly/Main.lean`), which applies the proved literature inputs. The vocabulary is
that of `RandomSandpileAudit/MainTheorem/SolutionBasic.lean`, and `mainTheoremStmt_of_lib` of
`RandomSandpileAudit/MainTheorem/Bridge.lean` transports the conclusion to the restated statement.
-/

namespace RandomSandpile.StatementAudit.MainTheorem

/-- **Theorem 1.1**, with the corrections [C3] and [C12], and with no literature input as a
hypothesis. -/
theorem mainTheoremFinal : MainTheoremStmt :=
  mainTheoremStmt_of_lib _root_.RandomSandpile.mainTheorem_final

end RandomSandpile.StatementAudit.MainTheorem

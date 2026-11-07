import Mathlib
import RandomSandpile.Assembly.Main
import RandomSandpileAudit.SingleSource.SolutionBasic
import RandomSandpileAudit.SingleSource.Bridge

/-!
# Solution: the recurrent single-source theorem (Theorem 9.2, corrected)

The challenge module `RandomSandpileAudit/SingleSource/Challenge.lean` imports only Mathlib and
states `singleSourceRecurrent` with its one intentional proof gap. This solution imports the
library `RandomSandpile` together with `SolutionBasic`, a verbatim copy of the challenge's
vocabulary, and proves the byte-identical statement from
`RandomSandpile.singleSourceTheoremRecurrent_final` (`RandomSandpile/Assembly/Main.lean`) through
the identifications of `Bridge.lean`.

The transport is definitional: each audit definition is a token-for-token copy of the library
definition, and the random environment is repacked by `toLibEnv`, whose fields are the audit
fields. The two cited inputs are passed on unchanged.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal Matrix

namespace RandomSandpile
namespace StatementAudit
namespace SingleSource

/-- **Theorem 9.2 (corrected, C13), recurrent single-source theorem.** Given the Fey–Levine–Peres
radius bound and Alexandrov's theorem, every random environment `E` on `ℤ^d` (`d ≥ 2`) with
`η_max ≤ 2d - 2` satisfies `SingleSourceRecurrentConclusion`. -/
theorem singleSourceRecurrent (hFLP : FeyLevinePeresRadius) (hA : AlexandrovStmt) :
    ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
      E.ηmax ≤ 2 * (d : ℤ) - 2 → SingleSourceRecurrentConclusion E := by
  intro d hd E hE
  have hFLP' : _root_.LatticeProb.External.FeyLevinePeresRadius := by
    rw [← FeyLevinePeresRadius_eq]
    exact hFLP
  have hA' : _root_.RandomSandpile.AlexandrovStmt := by
    rw [← AlexandrovStmt_eq]
    exact hA
  exact (singleSourceRecurrentConclusion_iff E).2
    (_root_.RandomSandpile.singleSourceTheoremRecurrent_final hFLP' hA' d hd (toLibEnv E) hE)

end SingleSource
end StatementAudit
end RandomSandpile

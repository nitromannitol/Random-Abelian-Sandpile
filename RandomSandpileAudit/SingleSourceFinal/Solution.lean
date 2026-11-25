import Mathlib
import RandomSandpile.Assembly.Main
import RandomSandpileAudit.SingleSource.SolutionBasic
import RandomSandpileAudit.SingleSource.Bridge

/-!
# Solution: the recurrent single-source theorem (Theorem 9.2, corrected) with no literature input

Proves `RandomSandpile.StatementAudit.SingleSource.singleSourceRecurrentFinal`, with the statement of
`RandomSandpileAudit/SingleSourceFinal/Challenge.lean`, from
`RandomSandpile.singleSourceTheoremRecurrent_final` (`RandomSandpile/Assembly/Main.lean`), which applies
the proved Fey–Levine–Peres radius bound and Alexandrov's theorem. The vocabulary is that of
`RandomSandpileAudit/SingleSource/SolutionBasic.lean`; the random environment is repacked by `toLibEnv`
and the conclusion transported by `singleSourceRecurrentConclusion_iff`
(`RandomSandpileAudit/SingleSource/Bridge.lean`).
-/

namespace RandomSandpile
namespace StatementAudit
namespace SingleSource

/-- **Theorem 9.2 (corrected, C13), recurrent single-source theorem**, with no literature input as a
hypothesis: every random environment `E` on `ℤ^d` (`d ≥ 2`) with `η_max ≤ 2d - 2` satisfies
`SingleSourceRecurrentConclusion`. -/
theorem singleSourceRecurrentFinal :
    ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
      E.ηmax ≤ 2 * (d : ℤ) - 2 → SingleSourceRecurrentConclusion E := by
  intro d hd E hE
  exact (singleSourceRecurrentConclusion_iff E).2
    (_root_.RandomSandpile.singleSourceTheoremRecurrent_final d hd (toLibEnv E) hE)

end SingleSource
end StatementAudit
end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceFstarSub
import RandomSandpile.Proofs.Sec7.PegdenSmartAdapter
import RandomSandpile.Inputs.PegdenSmartProp25

/-!
# Theorem 9.2, `F*`-variant, from Pegden-Smart's Propositions 2.4-2.5

`singleSourceTheoremFstar_ps13`: `singleSourceTheoremFstar` with the touching input
(`PegdenSmartTouchingStmt`) replaced by the verbatim Pegden-Smart inputs
(`Inputs/PegdenSmartProp25.lean`) through the adapter `pegdenSmartTouching_of_ps13`
(`Proofs/Sec7/PegdenSmartAdapter.lean`). The remaining hypotheses are the step
`SSCompactnessStmt`, the outer bound `SSOuterBoundStmt` (requested input) and Alexandrov's
theorem `AlexandrovStmt`.
-/

namespace RandomSandpile

namespace SingleSourceFstar

open PegdenSmartAdapter in
/-- **Theorem 9.2, `F*`-variant**, from compactness, the outer bound, Pegden-Smart's Propositions 2.4 and 2.5
(with `ViscosityWeakLaplaceStmt`) and Alexandrov's theorem. -/
theorem singleSourceTheoremFstar_ps13 (hComp : SSCompactnessStmt) (hOB : SSOuterBoundStmt)
    (h25 : PegdenSmartProp25Stmt) (h24 : PegdenSmartProp24Stmt) (hVW : ViscosityWeakLaplaceStmt)
    (hA : AlexandrovStmt) : SingleSourceTheoremStarStmt :=
  singleSourceTheoremFstar hComp hOB (pegdenSmartTouching_of_ps13 h25 h24 hVW) hA

end SingleSourceFstar

end RandomSandpile

import RandomSandpile.Infra.SubadditiveCentredBoxes
import RandomSandpile.Proofs.Sec5.SubadditiveErgodic

/-!
# Proposition 5.3 and Lemma 5.5

`SubadditiveErgodicStmt` (Proposition 5.3) and `MuConvergenceStmt` (Lemma 5.5) hold unconditionally: the box statement `SubadditiveRationalBoxesStmt` is proved in
`Infra/SubadditiveCentredBoxes.lean` (`subadditiveRationalBoxes`), from the Akcoglu-Krengel
theorem along the centred cubes (`Infra/SubadditiveCentred.lean`, `ae_tendsto_centredCube`) and
the rectangle ergodic theorem along every box (`rectangleErgodicAll`). The reductions are
`subadditiveErgodic_of_boxes` and `muConvergence_of_boxes` (`Proofs/Sec5/SubadditiveErgodic.lean`).
-/

namespace RandomSandpile

/-- **Proposition 5.3**: the multiparameter subadditive ergodic theorem on bounded
Lipschitz domains. -/
theorem subadditiveErgodic : SubadditiveErgodicStmt :=
  subadditiveErgodic_of_boxes subadditiveRationalBoxes

/-- **Lemma 5.5**. -/
theorem muConvergence_unconditional : MuConvergenceStmt :=
  muConvergence_of_boxes subadditiveRationalBoxes

end RandomSandpile

import RandomSandpile.Infra.SubadditiveLipschitz
import RandomSandpile.Proofs.Sec5.MuConvergence

/-!
# Proposition 5.3 and Lemma 5.5 from the subadditive ergodic theorem on rational boxes

`SubadditiveErgodicStmt` (Proposition 5.3) for bounded Lipschitz domains follows
from its version on half-open boxes with rational corners, `SubadditiveRationalBoxesStmt`
(`Infra/SubadditiveCubes.lean`), by the Dal Maso-Modica approximation
(`SubadditiveLipschitz.subadditiveErgodic_of_rationalBoxes`, `Infra/SubadditiveLipschitz.lean`).
Lemma 5.5 (`MuConvergenceStmt`) then follows by `muConvergence`.

The box statement is proved in `Infra/SubadditiveCubes.lean` for boxes in the closed positive
orthant (`subadditiveOrthantBoxes`); boxes meeting both sides of a coordinate hyperplane through
the origin need the Akcoglu-Krengel theorem along centred cubes (`SubadditiveCentredCubesStmt`),
which is the remaining input.
-/

namespace RandomSandpile

/-- **Proposition 5.3** from the box statement. -/
theorem subadditiveErgodic_of_boxes (h : SubadditiveRationalBoxesStmt) : SubadditiveErgodicStmt :=
  SubadditiveLipschitz.subadditiveErgodic_of_rationalBoxes h

/-- **Lemma 5.5** from the box statement. -/
theorem muConvergence_of_boxes (h : SubadditiveRationalBoxesStmt) : MuConvergenceStmt :=
  muConvergence (subadditiveErgodic_of_boxes h)

end RandomSandpile

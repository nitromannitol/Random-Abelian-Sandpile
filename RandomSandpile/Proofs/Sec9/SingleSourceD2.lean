import RandomSandpile.Proofs.Sec9.SingleSourceD2Steps
import RandomSandpile.Proofs.Sec9.SingleSourceCompactness
import RandomSandpile.Proofs.Sec9.OpenBoundaryComparison

/-!
# Theorem 9.2 in dimension two: assembly

`singleSourceTheoremD2_of_steps`: `SingleSourceTheoremD2Stmt` from
* the literature inputs already admitted for the starred theorem: Fey-Levine-Peres 2010
  Theorem 1.1 (`External.FeyLevinePeresRadius`, compactness and outer bound) and Alexandrov's
  theorem (`AlexandrovStmt`, comparison principle);
* the subsolution step in dimension two `SSLimitSubStarD2Stmt` (proved in
  `SingleSourceD2SubStar.lean`, `ssLimitSubStarD2`);
* the remaining steps of `SingleSourceD2Steps.lean`: and.
-/

open LatticeProb

namespace RandomSandpile

namespace SingleSourceD2

/-- **Theorem 9.2 in dimension two** from the admitted inputs (FLP Theorem 1.1, Alexandrov), the
subsolution step in dimension two and the steps. -/
theorem singleSourceTheoremD2_of_steps (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (hS : SSLimitSubStarD2Stmt) (hOP1 : EffOpLeStarD2Stmt)
    (hF2 : SSLimitSuperEffD2Stmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_star
    (singleSourceTheoremStarD2_of_sub (ssCompactness_of_flp hFLP)
      (ssOuterBound_of_flp hFLP) hS (shiftComparison_of_alexandrov hA)) hOP1 hF2

end SingleSourceD2

end RandomSandpile

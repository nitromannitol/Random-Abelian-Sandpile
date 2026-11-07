import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainCubes
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainGradient
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainBoundaryExit
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainErgodic
import RandomSandpile.Proofs.Sec8.DivisibleTheorem

/-! # Lemma 8.1 and Theorem 8.2 from the Lawler-Limic input

decomposition `divisibleHomogenizeDomain_of_steps` (754d674) with every step proved:
* `cubeErgodicReal` (c6);
* `greenDomainHomogenize_of_steps` from
  the boundary layer (`greenDomainBoundaryLayer_of_exit` with `greenDomainBoundaryExit`) and the
  summed gradient bound (`greenDomainGradientSum_of_lawlerLimic`, uses Lawler-Limic).
Theorem 8.2 then follows by `divisibleTheorem_of_homogenizeDomain` (0a59081). -/

namespace RandomSandpile

open DivisibleHomogenizeDomain

/-- The deterministic core of Lemma 8.1 from the Lawler-Limic input. -/
theorem greenDomainHomogenize_of_lawlerLimic (hLL : LawlerLimicHarmonicDifferenceStmt) :
    GreenDomainHomogenizeStmt :=
  greenDomainHomogenize_of_steps (greenDomainBoundaryLayer_of_exit greenDomainBoundaryExit)
    (greenDomainGradientSum_of_lawlerLimic hLL)

/-- **Lemma 8.1** (`DivisibleHomogenizeDomainStmt`) from the Lawler-Limic input. -/
theorem divisibleHomogenizeDomain_of_lawlerLimic (hLL : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleHomogenizeDomainStmt :=
  divisibleHomogenizeDomain_of_steps cubeErgodicReal (greenDomainHomogenize_of_lawlerLimic hLL)

/-- **Theorem 8.2** (`DivisibleTheoremStmt`) from the Lawler-Limic input. -/
theorem divisibleTheorem_of_lawlerLimic (hLL : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleTheoremStmt :=
  divisibleTheorem_of_homogenizeDomain (divisibleHomogenizeDomain_of_lawlerLimic hLL)

end RandomSandpile

import RandomSandpile.Proofs.Sec9.OpenBoundaryCompactness
import RandomSandpile.Proofs.Sec9.OpenBoundaryVanish
import RandomSandpile.Proofs.Sec9.OpenBoundaryMaxPrinciple
import RandomSandpile.Proofs.Sec9.OpenBoundaryComparison
import RandomSandpile.Proofs.Sec9.OpenBoundaryLapLipschitz
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainBoundaryExit

/-! # Theorem 9.1 (`OpenBoundaryTheoremStmt`): assembly

Every step of `openBoundaryTheorem_of_analyticSteps` is proved:
* Lemma 6.4: `effectiveOperatorBasic_of_muConvergence` (Lemma 5.5);
* `lapLipschitzInterior`, `greenDomainBoundaryExit` (no input), hence
  `openCompactness_of_steps`;
* `muVanish_of_muConvergence` (Lemma 5.5, Lemma 7.5 via Lemmas 7.3-7.4 and Lawler-Limic);
*, `openInteriorMaxPrinciple_of_muConvergence`, `openInteriorMinPrinciple_of_muConvergence`
  (Lemma 5.5);
* `effShift_of_muConvergence` (Lemma 5.5);
* `shiftComparison_of_alexandrov`.

The remaining hypotheses:
* `MuConvergenceStmt` (Lemma 5.5), proved modulo Proposition 5.3, i.e. modulo
  `SubadditiveRationalBoxesStmt` (`openBoundaryTheorem_of_boxes`);
* the literature inputs `LawlerLimicHarmonicDifferenceStmt` and `AlexandrovStmt`. -/

namespace RandomSandpile

/-- **Theorem 9.1** from Lemma 5.5 and the literature inputs Lawler-Limic and Alexandrov
(Alexandrov). -/
theorem openBoundaryTheorem_of_muConvergence (hconv : MuConvergenceStmt)
    (hLL : LawlerLimicHarmonicDifferenceStmt) (hA : AlexandrovStmt) : OpenBoundaryTheoremStmt :=
  openBoundaryTheorem_of_analyticSteps (effectiveOperatorBasic_of_muConvergence hconv)
    lapLipschitzInterior greenDomainBoundaryExit (muVanish_of_muConvergence hconv hLL)
    (openInteriorMaxPrinciple_of_muConvergence hconv
      (openCompactness_of_steps lapLipschitzInterior greenDomainBoundaryExit))
    (openInteriorMinPrinciple_of_muConvergence hconv
      (openCompactness_of_steps lapLipschitzInterior greenDomainBoundaryExit))
    (effShift_of_muConvergence hconv) (shiftComparison_of_alexandrov hA)

/-- **Theorem 9.1** from the rational-box form of Proposition 5.3 and the two inputs. -/
theorem openBoundaryTheorem_of_boxes (h : SubadditiveRationalBoxesStmt)
    (hLL : LawlerLimicHarmonicDifferenceStmt) (hA : AlexandrovStmt) : OpenBoundaryTheoremStmt :=
  openBoundaryTheorem_of_muConvergence (muConvergence_of_boxes h) hLL hA

end RandomSandpile

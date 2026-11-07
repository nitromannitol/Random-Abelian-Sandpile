import RandomSandpile.Proofs.Sec7.MainTheoremUExteriorSub
import RandomSandpile.Proofs.Sec7.MainTheorem
import RandomSandpile.Proofs.Sec7.SandpileSupport
import RandomSandpile.Proofs.Sec9.OpenBoundaryVanish
import RandomSandpile.Proofs.Sec5.SubadditiveErgodicFinal
import RandomSandpile.Proofs.Sec7.SplitTouching

/-! # Theorem 1.1 from the literature inputs

All steps of `mainTheorem_of_remainingSteps` (`Proofs/Sec7/MainTheorem.lean`) are discharged except,
for the printed radius, `SandpileSupportStmt`:

* Lemma 6.4 and from Lemma 5.5 (`muConvergence_unconditional`) and the Lawler-Limic input
  (`muVanish_of_muConvergence`);
* and `LimitTraceInteriorStmt` from Pegden-Smart's Proposition 2.5
  (`exteriorSupersolution_of_touching`, `limitTraceInterior_of_touching`);
* `exteriorSubsolution`, `interiorMax/MinPrinciple_of_muConvergence`, and
  `freeOdometerLimitRegular`: no input;
* `SplitTouchingStmt` from Alexandrov's theorem.

`mainTheorem_lawRadius` is Theorem 1.1 with the radius chosen after the law from the three
literature inputs Lawler-Limic, Pegden-Smart (Proposition 2.5) and Alexandrov. -/

namespace RandomSandpile

/-- **Theorem 1.1 with the radius chosen after the law** from the inputs Lawler-Limic
(Lawler-Limic) and Pegden-Smart (Proposition 2.5) and the step `SplitTouchingStmt`. -/
theorem mainTheorem_lawRadius_of_inputs (hLL : LawlerLimicHarmonicDifferenceStmt)
    (hT : PegdenSmartTouchingStmt) (hSplit : SplitTouchingStmt) : MainTheoremLawRadiusStmt :=
  mainTheorem_lawRadius_of_remainingSteps
    (effectiveOperatorBasic_of_muConvergence muConvergence_unconditional) hT
    freeOdometerLimitRegular (muVanish_of_muConvergence muConvergence_unconditional hLL)
    (exteriorSupersolution_of_touching hT) exteriorSubsolution
    (interiorMaxPrinciple_of_muConvergence muConvergence_unconditional)
    (interiorMinPrinciple_of_muConvergence muConvergence_unconditional)
    (limitTraceInterior_of_touching hT) hSplit

/-- **Theorem 1.1** (printed radius) from the same inputs and `SandpileSupportStmt`. -/
theorem mainTheorem_of_inputs (hLL : LawlerLimicHarmonicDifferenceStmt)
    (hT : PegdenSmartTouchingStmt) (hSplit : SplitTouchingStmt)
    (hSupp : SandpileSupportStmt) : MainTheoremPrintedStmt :=
  mainTheorem_of_remainingSteps
    (effectiveOperatorBasic_of_muConvergence muConvergence_unconditional) hT
    freeOdometerLimitRegular (muVanish_of_muConvergence muConvergence_unconditional hLL)
    (exteriorSupersolution_of_touching hT) exteriorSubsolution
    (interiorMaxPrinciple_of_muConvergence muConvergence_unconditional)
    (interiorMinPrinciple_of_muConvergence muConvergence_unconditional)
    (limitTraceInterior_of_touching hT) hSplit hSupp

/-- **Theorem 1.1 with the radius chosen after the law** from the literature inputs
Lawler-Limic, Pegden-Smart (Proposition 2.5) and Alexandrov only. -/
theorem mainTheorem_lawRadius (hLL : LawlerLimicHarmonicDifferenceStmt)
    (hT : PegdenSmartTouchingStmt) (hAlex : AlexandrovStmt) : MainTheoremLawRadiusStmt :=
  mainTheorem_lawRadius_of_inputs hLL hT (splitTouching_of_alexandrov hAlex)

/-- **Theorem 1.1** (printed radius) from the literature inputs Lawler-Limic, Pegden-Smart and Alexandrov and
`SandpileSupportStmt`. -/
theorem mainTheorem_of_literature (hLL : LawlerLimicHarmonicDifferenceStmt)
    (hT : PegdenSmartTouchingStmt) (hAlex : AlexandrovStmt) (hSupp : SandpileSupportStmt) :
    MainTheoremPrintedStmt :=
  mainTheorem_of_inputs hLL hT (splitTouching_of_alexandrov hAlex) hSupp

end RandomSandpile

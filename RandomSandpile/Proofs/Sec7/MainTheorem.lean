import RandomSandpile.Proofs.Sec7.Compactness
import RandomSandpile.Proofs.Sec7.MainTheoremUniqueness
import RandomSandpile.Proofs.Sec7.MainTheoremSandpile
import RandomSandpile.Proofs.Sec7.MainTheoremViscEff
import RandomSandpile.Proofs.Sec7.MainTheoremLap
import RandomSandpile.Proofs.Sec7.MainTheoremWeakStar
import RandomSandpile.Proofs.Sec7.MainTheoremEnvLimit
import RandomSandpile.Proofs.Sec7.LimitObstacle
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularity

/-!
# Theorem 1.1 from the steps

Assembly of `mainTheorem_of_steps` with the proved inputs: Lemma 7.2 (`compactness`), the bounds of
its proof (`freeOdometerUpperBound_of_oneDim oneDimToppling`, `freeOdometerLapBound`), the
reductions `limitComparison_of_steps`, `limitViscEff_of_steps` and
`sandpileLimit_of_steps`, and the proved sandpile steps `envWeakStar`,
`rescaledLapWeak`, `weakStarRepresentation`. The hypotheses are the steps that remain open and
the Statements of Lemmas 6.4 and 7.6; the conclusion is the printed form
`MainTheoremPrintedStmt` (the corrected Theorem 1.1, [C12], is `mainTheorem_etaMaxRadius`,
`Proofs/Sec7/MainTheoremC12.lean`).

`mainTheorem_of_remainingSteps` further unfolds Lemma 7.6 (`pegdenSmartRegularity_of_touching_regular`,
from Pegden-Smart's Proposition 2.5 `PegdenSmartTouchingStmt`) and the identification steps,
 (`limitViscZero_of_steps`, `limitMinimal_of_steps`), with `LipschitzDomainFrontierNullStmt`
proved (`lipschitzDomainFrontierNull`).
-/

namespace RandomSandpile

/-- The boundary of a Lipschitz domain is Lebesgue null (`volume_frontier_of_isLipschitzDomain`). -/
theorem lipschitzDomainFrontierNull : LipschitzDomainFrontierNullStmt :=
  fun _ _ _ hW => volume_frontier_of_isLipschitzDomain hW

/-- **Theorem 1.1** from the steps-, and Lemmas 6.4, 7.6. -/
theorem mainTheorem_of_openSteps (h64 : EffectiveOperatorBasicStmt)
    (h76 : PegdenSmartRegularityStmt) (hVan : MuVanishStmt)
    (hExtSup : ExteriorSupersolutionStmt) (hExtSub : ExteriorSubsolutionStmt)
    (hMax : InteriorMaxPrincipleStmt) (hMin : InteriorMinPrincipleStmt)
    (hZero : LimitViscZeroStmt) (hMinimal : LimitMinimalStmt)
    (hSupp : SandpileSupportStmt) : MainTheoremPrintedStmt :=
  mainTheorem_of_steps compactness h64
    (limitComparison_of_steps h76 hVan hExtSup hExtSub hMax hMin)
    (limitViscEff_of_steps h64 hVan hMin) hZero hMinimal
    (sandpileLimit_of_steps (freeOdometerUpperBound_of_oneDim oneDimToppling)
      freeOdometerLapBound envWeakStar rescaledLapWeak weakStarRepresentation hSupp)

/-- **Theorem 1.1** from the finest steps: Lemma 6.4 (`EffectiveOperatorBasicStmt`),
Pegden-Smart's Proposition 2.5 (`PegdenSmartTouchingStmt`), the regularity of limits
(`FreeOdometerLimitRegularStmt`),-, the interior trace bound at touching quadratics
(`LimitTraceInteriorStmt`), Jensen's lemma at split points (`SplitTouchingStmt`) and the support
radius. -/
theorem mainTheorem_of_remainingSteps (h64 : EffectiveOperatorBasicStmt)
    (hT : PegdenSmartTouchingStmt) (hReg : FreeOdometerLimitRegularStmt) (hVan : MuVanishStmt)
    (hExtSup : ExteriorSupersolutionStmt) (hExtSub : ExteriorSubsolutionStmt)
    (hMax : InteriorMaxPrincipleStmt) (hMin : InteriorMinPrincipleStmt)
    (hTr : LimitTraceInteriorStmt) (hSplit : SplitTouchingStmt)
    (hSupp : SandpileSupportStmt) : MainTheoremPrintedStmt :=
  mainTheorem_of_openSteps h64
    (pegdenSmartRegularity_of_touching_regular hT hReg lipschitzDomainFrontierNull) hVan
    hExtSup hExtSub hMax hMin
    (limitViscZero_of_steps hExtSup hTr hReg lipschitzDomainFrontierNull hSplit)
    (limitMinimal_of_steps h64 hVan hMax hExtSub hReg lipschitzDomainFrontierNull hSplit) hSupp

end RandomSandpile

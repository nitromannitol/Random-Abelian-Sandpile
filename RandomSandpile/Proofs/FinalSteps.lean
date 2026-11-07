import RandomSandpile.Infra.ConcaveEnvelope
import RandomSandpile.Infra.SubadditiveCentredBoxes
import RandomSandpile.Proofs.FinalSingleSource
import RandomSandpile.Proofs.Sec3.Abelian
import RandomSandpile.Proofs.Sec3.Burning
import RandomSandpile.Proofs.Sec3.LeastAction
import RandomSandpile.Proofs.Sec3.RecurrentOfToppled
import RandomSandpile.Proofs.Sec5.ABP
import RandomSandpile.Proofs.Sec5.HarnackQuadratic
import RandomSandpile.Proofs.Sec5.MongeAmpereRep
import RandomSandpile.Proofs.Sec5.MuBounded
import RandomSandpile.Proofs.Sec5.StabilizingLegal
import RandomSandpile.Proofs.Sec5.SubadditiveErgodicFinal
import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasicFinal
import RandomSandpile.Proofs.Sec6.MuLipschitzShell
import RandomSandpile.Proofs.Sec6.MuMonotone
import RandomSandpile.Proofs.Sec6.StrictConcavityFinal
import RandomSandpile.Proofs.Sec7.Compactness
import RandomSandpile.Proofs.Sec7.DivisibleHomogenize
import RandomSandpile.Proofs.Sec7.FreeOdometerLimitRegular
import RandomSandpile.Proofs.Sec7.MainTheorem
import RandomSandpile.Proofs.Sec7.MainTheoremUAssembly
import RandomSandpile.Proofs.Sec7.MainTheoremC12
import RandomSandpile.Proofs.Sec7.OdometerLowerBound
import RandomSandpile.Proofs.Sec7.OneDimToppling
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularity
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainFinal
import RandomSandpile.Proofs.Sec8.DivisibleLeastAction
import RandomSandpile.Proofs.Sec9.OpenBoundaryFinal
import RandomSandpile.Proofs.Sec9.OpenBoundaryVanish
import RandomSandpile.Proofs.Sec9.SingleSource
import RandomSandpile.Proofs.Sec9.SingleSourceMinPrinciple

/-! # Closures of the steps (generated from the theorem graph)

For every numbered result and every decomposed step it uses, the theorem `<step>_closed` applies the
reduction with the fewest open hypotheses available in the repository, discharging each hypothesis
by the closure of that step. The remaining hypotheses are exactly the leaves: admitted literature
inputs (`RandomSandpile/Inputs`) and steps that are still open. The table of leaves per result is in
`RandomSandpile/Assembly/Audit.lean`; the numbered results are restated in
`RandomSandpile/Assembly/Main.lean`.
-/

namespace RandomSandpile

theorem mainTheorem_closed (hAlexandrov : RandomSandpile.AlexandrovStmt) (hLawlerLimicHarmonicDifference : RandomSandpile.LawlerLimicHarmonicDifferenceStmt) (hPegdenSmartTouching : RandomSandpile.PegdenSmartTouchingStmt) :
    RandomSandpile.MainTheoremStmt :=
  RandomSandpile.mainTheorem_etaMaxRadius hLawlerLimicHarmonicDifference hPegdenSmartTouching hAlexandrov

theorem mainTheoremPrinted_closed (hAlexandrov : RandomSandpile.AlexandrovStmt) (hLawlerLimicHarmonicDifference : RandomSandpile.LawlerLimicHarmonicDifferenceStmt) (hPegdenSmartTouching : RandomSandpile.PegdenSmartTouchingStmt) (hSandpileSupport : RandomSandpile.SandpileSupportStmt) :
    RandomSandpile.MainTheoremPrintedStmt :=
  RandomSandpile.mainTheorem_of_literature hLawlerLimicHarmonicDifference hPegdenSmartTouching hAlexandrov hSandpileSupport

theorem mainTheoremLawRadius_closed (hAlexandrov : RandomSandpile.AlexandrovStmt) (hLawlerLimicHarmonicDifference : RandomSandpile.LawlerLimicHarmonicDifferenceStmt) (hPegdenSmartTouching : RandomSandpile.PegdenSmartTouchingStmt) :
    RandomSandpile.MainTheoremLawRadiusStmt :=
  RandomSandpile.mainTheorem_lawRadius hLawlerLimicHarmonicDifference hPegdenSmartTouching hAlexandrov

theorem leastAction_closed :
    RandomSandpile.LeastActionStmt :=
  RandomSandpile.leastAction

theorem abelianDecomposition_closed :
    RandomSandpile.AbelianDecompositionStmt :=
  RandomSandpile.abelianDecomposition

theorem burning_closed :
    RandomSandpile.BurningStmt :=
  RandomSandpile.burning

theorem recurrentOfToppled_closed :
    RandomSandpile.RecurrentOfToppledStmt :=
  RandomSandpile.recurrentOfToppled

theorem stabilizingLegal_closed :
    RandomSandpile.StabilizingLegalStmt :=
  RandomSandpile.stabilizingLegal

theorem abp_closed :
    RandomSandpile.ABPStmt :=
  RandomSandpile.abp

theorem concaveEnvelopeRep_closed :
    RandomSandpile.ConcaveEnvelopeRepStmt :=
  RandomSandpile.concaveEnvelopeRep

theorem mongeAmpereRep_closed :
    RandomSandpile.MongeAmpereRepStmt :=
  RandomSandpile.mongeAmpereRep

theorem muBounded_closed :
    RandomSandpile.MuBoundedStmt :=
  RandomSandpile.muBounded

theorem harnackQuadratic_closed :
    RandomSandpile.HarnackQuadraticStmt :=
  RandomSandpile.harnackQuadratic

theorem subadditiveErgodic_closed :
    RandomSandpile.SubadditiveErgodicStmt :=
  RandomSandpile.subadditiveErgodic

theorem muConvergence_closed :
    RandomSandpile.MuConvergenceStmt :=
  RandomSandpile.muConvergence_unconditional

theorem muMonotone_closed :
    RandomSandpile.MuMonotoneStmt :=
  RandomSandpile.muMonotone

theorem subadditiveRationalBoxes_closed :
    RandomSandpile.SubadditiveRationalBoxesStmt :=
  RandomSandpile.subadditiveRationalBoxes

theorem muLipschitz_closed :
    RandomSandpile.MuLipschitzStmt :=
  RandomSandpile.muLipschitz_of_boxes (subadditiveRationalBoxes_closed)

theorem effectiveOperatorBasic_closed :
    RandomSandpile.EffectiveOperatorBasicStmt :=
  RandomSandpile.effectiveOperatorBasic_of_boxes (subadditiveRationalBoxes_closed)

theorem oneDimToppling_closed :
    RandomSandpile.OneDimTopplingStmt :=
  RandomSandpile.oneDimToppling

theorem compactness_closed :
    RandomSandpile.CompactnessStmt :=
  RandomSandpile.compactness

theorem divisibleHomogenize_closed (hLawlerLimicHarmonicDifference : RandomSandpile.LawlerLimicHarmonicDifferenceStmt) :
    RandomSandpile.DivisibleHomogenizeStmt :=
  RandomSandpile.divisibleHomogenize_of_lawlerLimic hLawlerLimicHarmonicDifference

theorem odometerLowerBound_closed (hLawlerLimicHarmonicDifference : RandomSandpile.LawlerLimicHarmonicDifferenceStmt) :
    RandomSandpile.OdometerLowerBoundStmt :=
  RandomSandpile.odometerLowerBound_of_divisibleHomogenize (divisibleHomogenize_closed hLawlerLimicHarmonicDifference)

theorem flat_closed (hLawlerLimicHarmonicDifference : RandomSandpile.LawlerLimicHarmonicDifferenceStmt) :
    RandomSandpile.FlatStmt :=
  RandomSandpile.flat_of_muConvergence (muConvergence_closed) hLawlerLimicHarmonicDifference

theorem freeOdometerLimitRegular_closed :
    RandomSandpile.FreeOdometerLimitRegularStmt :=
  RandomSandpile.freeOdometerLimitRegular

theorem lipschitzDomainFrontierNull_closed :
    RandomSandpile.LipschitzDomainFrontierNullStmt :=
  RandomSandpile.lipschitzDomainFrontierNull

theorem pegdenSmartRegularity_closed (hPegdenSmartTouching : RandomSandpile.PegdenSmartTouchingStmt) :
    RandomSandpile.PegdenSmartRegularityStmt :=
  RandomSandpile.pegdenSmartRegularity_of_touching_regular hPegdenSmartTouching (freeOdometerLimitRegular_closed) (lipschitzDomainFrontierNull_closed)

theorem divisibleLeastAction_closed :
    RandomSandpile.DivisibleLeastActionStmt :=
  RandomSandpile.divisibleLeastAction

theorem divisibleHomogenizeDomain_closed (hLawlerLimicHarmonicDifference : RandomSandpile.LawlerLimicHarmonicDifferenceStmt) :
    RandomSandpile.DivisibleHomogenizeDomainStmt :=
  RandomSandpile.divisibleHomogenizeDomain_of_lawlerLimic hLawlerLimicHarmonicDifference

theorem divisibleTheorem_closed (hLawlerLimicHarmonicDifference : RandomSandpile.LawlerLimicHarmonicDifferenceStmt) :
    RandomSandpile.DivisibleTheoremStmt :=
  RandomSandpile.divisibleTheorem_of_lawlerLimic hLawlerLimicHarmonicDifference

theorem openBoundaryTheorem_closed (hAlexandrov : RandomSandpile.AlexandrovStmt) (hLawlerLimicHarmonicDifference : RandomSandpile.LawlerLimicHarmonicDifferenceStmt) :
    RandomSandpile.OpenBoundaryTheoremStmt :=
  RandomSandpile.openBoundaryTheorem_of_muConvergence (muConvergence_closed) hLawlerLimicHarmonicDifference hAlexandrov

theorem muVanishFlat_closed :
    RandomSandpile.MuVanishFlatStmt :=
  RandomSandpile.muVanishFlat

theorem ssInteriorMinPrinciple_closed (hSSCompactness : RandomSandpile.SSCompactnessStmt) :
    RandomSandpile.SSInteriorMinPrincipleStmt :=
  RandomSandpile.ssInteriorMinPrinciple_of_compactness (muConvergence_closed) hSSCompactness

theorem ssLimitSupersolution_closed (hSSCompactness : RandomSandpile.SSCompactnessStmt) :
    RandomSandpile.SSLimitSupersolutionStmt :=
  RandomSandpile.ssLimitSupersolution_of_steps (effectiveOperatorBasic_closed) (muVanishFlat_closed) (ssInteriorMinPrinciple_closed hSSCompactness)

theorem singleSourceTheoremFlat_closed (hSSCompactness : RandomSandpile.SSCompactnessStmt) (hSSLimitMinimal : RandomSandpile.SSLimitMinimalStmt) :
    RandomSandpile.SingleSourceTheoremFlatStmt :=
  RandomSandpile.singleSourceTheoremFlat_of_steps hSSCompactness (ssLimitSupersolution_closed hSSCompactness) hSSLimitMinimal

theorem nearMaxBending_closed :
    RandomSandpile.NearMaxBendingStmt :=
  RandomSandpile.nearMaxBending_of_muConvergence (muConvergence_closed)

theorem strictConcavityBeta_closed :
    RandomSandpile.StrictConcavityBetaStmt :=
  RandomSandpile.strictConcavityBeta_of_bending_of_muConvergence (nearMaxBending_closed) (muConvergence_closed)

/-- Lemma 6.2 with [C11]: the Draft `StrictConcavityStmt` has the body of
`StrictConcavityBetaStmt`, so the two Props are definitionally equal. -/
theorem strictConcavity_closed :
    RandomSandpile.StrictConcavityStmt :=
  strictConcavityBeta_closed

end RandomSandpile

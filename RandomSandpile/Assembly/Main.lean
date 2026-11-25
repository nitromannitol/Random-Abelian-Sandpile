import RandomSandpile.Inputs.LawlerLimicHarmonicDifference
import RandomSandpile.Inputs.PegdenSmartProp25
import RandomSandpile.Proofs.Alexandrov
import RandomSandpile.Proofs.FinalSteps
import RandomSandpile.Proofs.Sec7.ConfinementSupport
import RandomSandpile.Proofs.PegdenSmart
import RandomSandpile.Proofs.PegdenSmartProp24
import RandomSandpile.Proofs.Sec7.PegdenSmartAdapter
import RandomSandpile.Proofs.Sec9.RecurrentViscositySuper
import RandomSandpile.Proofs.Sec9.RecurrentIdentificationFinal
import RandomSandpile.Proofs.Sec9.RecurrentZeroComparison
import RandomSandpile.Proofs.ViscosityWeakLaplace
import LatticeProb.External.FeyLevinePeresRadiusProved
import RandomSandpile.Proofs.Sec9.SingleSourceSignCorrected

/-! # Main results of "Convergence of the random Abelian sandpile"

Bou-Rabee, *Convergence of the random Abelian sandpile*, Ann. Probab. 49 (2021), arXiv:1909.07849.
This file states the main results of the paper as theorems `<name>_final`, following the corrected
`paper/random_piles-corrected.tex`. The statements are the `Draft` definitions. A theorem has no
hypotheses for the literature inputs used in their proofs. The six formalized inputs are proved:
Alexandrov's theorem, the weak form of viscosity solutions, Pegden–Smart Propositions 2.4 and 2.5,
the Fey–Levine–Peres radius bound, and the Lawler–Limic harmonic difference estimate
(`lawlerLimicHarmonicDifference`). The formalized Prop. 2.4 statement omits the source's
almost-everywhere Laplacian trace identification.

Counts (28 numbered results, 33 theorems): all are proved without literature-input hypotheses.
Theorem 1.1 and Lemma 6.2 have two theorems each, and Theorem 9.2 has four.
The table of statements is in `RandomSandpile/Assembly/Audit.lean`, and the axiom report of every
theorem is in `RandomSandpileAudit/Axioms.lean`.
-/

namespace RandomSandpile

/-- **Theorem 1.1, weaker form** (`MainTheoremLawRadiusStmt`), implied by `MainTheoremStmt`
(correction C12: `R = R(W, d, η_max)`). Proved using `lawlerLimicHarmonicDifference`
(Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8).
The other inputs of the proof are also proved, including the formalized Peano expansion
(`pegden_smart_prop24_stmt`): Alexandrov's theorem
(`alexandrovStmt_proved`; Evans–Gariepy, *Measure Theory and Fine Properties of Functions*, CRC Press
1992, Section 6.4, Theorem 1), Pegden–Smart Prop. 2.5 (`pegdenSmartProp25Stmt_of_prop24`, from
Prop. 2.4) and the weak form of viscosity solutions (`viscosityWeakLaplace`; Ishii, *On the
equivalence of two notions of weak solutions, viscosity solutions and distribution solutions*,
Funkcial. Ekvac. 38 (1995) 101–120). -/
theorem mainTheoremLawRadius_final :
    MainTheoremLawRadiusStmt :=
  mainTheoremLawRadius_closed alexandrovStmt_proved lawlerLimicHarmonicDifference
    (pegdenSmartTouching_of_ps13 (pegdenSmartProp25Stmt_of_prop24 pegden_smart_prop24_stmt)
      pegden_smart_prop24_stmt viscosityWeakLaplace)

/-- **Theorem 1.1** (`MainTheoremStmt`, with corrections C3 and C12: the support radius `R` depends
on `W`, `d` and `η_max`). Proved using `lawlerLimicHarmonicDifference`
(Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). The other inputs of the proof
are also proved, including the formalized Peano expansion (`pegden_smart_prop24_stmt`): Alexandrov's theorem
(`alexandrovStmt_proved`; Evans–Gariepy,
*Measure Theory and Fine Properties of Functions*, CRC Press 1992, Section 6.4, Theorem 1),
Pegden–Smart Prop. 2.5 (`pegdenSmartProp25Stmt_of_prop24`, from Prop. 2.4) and the weak form of
viscosity solutions (`viscosityWeakLaplace`; Ishii, *On the equivalence of two notions of weak
solutions, viscosity solutions and distribution solutions*, Funkcial. Ekvac. 38 (1995) 101–120). -/
theorem mainTheorem_final :
    MainTheoremStmt :=
  mainTheorem_closed alexandrovStmt_proved lawlerLimicHarmonicDifference
    (pegdenSmartTouching_of_ps13 (pegdenSmartProp25Stmt_of_prop24 pegden_smart_prop24_stmt)
      pegden_smart_prop24_stmt viscosityWeakLaplace)

/-- **Theorem 1.1 with the printed support radius** (`MainTheoremPrintedStmt`): the radius `R`
depends only on `W`, `d` and `E η(0)`, chosen before the law. The radius step is
`sandpileSupport` (`Proofs/Sec7/ConfinementSupport.lean`). -/
theorem mainTheoremPrinted_final :
    MainTheoremPrintedStmt :=
  mainTheoremPrinted_closed alexandrovStmt_proved lawlerLimicHarmonicDifference
    (pegdenSmartTouching_of_ps13 (pegdenSmartProp25Stmt_of_prop24 pegden_smart_prop24_stmt)
      pegden_smart_prop24_stmt viscosityWeakLaplace) sandpileSupport

/-- **Proposition 3.1** (`LeastActionStmt`). Proved. -/
theorem leastAction_final :
    LeastActionStmt :=
  leastAction_closed

/-- **Proposition 3.2** (`AbelianDecompositionStmt`). Proved. -/
theorem abelianDecomposition_final :
    AbelianDecompositionStmt :=
  abelianDecomposition_closed

/-- **Proposition 3.3** (`BurningStmt`). Proved. -/
theorem burning_final :
    BurningStmt :=
  burning_closed

/-- **Proposition 3.4** (`RecurrentOfToppledStmt`). Proved. -/
theorem recurrentOfToppled_final :
    RecurrentOfToppledStmt :=
  recurrentOfToppled_closed

/-- **Lemma 5.1** (`StabilizingLegalStmt`). Proved. -/
theorem stabilizingLegal_final :
    StabilizingLegalStmt :=
  stabilizingLegal_closed

/-- **Lemma 5.2** (`ABPStmt`). Proved. -/
theorem abp_final :
    ABPStmt :=
  abp_closed

/-- **Proposition 5.1** (`ConcaveEnvelopeRepStmt`). Proved. -/
theorem concaveEnvelopeRep_final :
    ConcaveEnvelopeRepStmt :=
  concaveEnvelopeRep_closed

/-- **Lemma 5.3** (`MongeAmpereRepStmt`). Proved. -/
theorem mongeAmpereRep_final :
    MongeAmpereRepStmt :=
  mongeAmpereRep_closed

/-- **Lemma 5.4** (`MuBoundedStmt`). Proved. -/
theorem muBounded_final :
    MuBoundedStmt :=
  muBounded_closed

/-- **Proposition 5.2** (`HarnackQuadraticStmt`). Proved. -/
theorem harnackQuadratic_final :
    HarnackQuadraticStmt :=
  harnackQuadratic_closed

/-- **Proposition 5.3** (`SubadditiveErgodicStmt`). Proved. -/
theorem subadditiveErgodic_final :
    SubadditiveErgodicStmt :=
  subadditiveErgodic_closed

/-- **Lemma 5.5** (`MuConvergenceStmt`). Proved. -/
theorem muConvergence_final :
    MuConvergenceStmt :=
  muConvergence_closed

/-- **Lemma 6.1** (`MuMonotoneStmt`). Proved. -/
theorem muMonotone_final :
    MuMonotoneStmt :=
  muMonotone_closed

/-- **Lemma 6.2**, with the constant `C(β) = c(1-β)²` (`StrictConcavityBetaStmt`, correction C11).
Proved. -/
theorem strictConcavityBeta_final :
    StrictConcavityBetaStmt :=
  strictConcavityBeta_closed

/-- **Lemma 6.2** (`StrictConcavityStmt`, with corrections C2, C4 and C11: the constant depends on
`β`, `C(β) = c(1-β)²`). Proved. -/
theorem strictConcavity_final :
    StrictConcavityStmt :=
  strictConcavity_closed

/-- **Lemma 6.3** (`MuLipschitzStmt`). Proved. -/
theorem muLipschitz_final :
    MuLipschitzStmt :=
  muLipschitz_closed

/-- **Lemma 6.4** (`EffectiveOperatorBasicStmt`). Proved. -/
theorem effectiveOperatorBasic_final :
    EffectiveOperatorBasicStmt :=
  effectiveOperatorBasic_closed

/-- **Lemma 7.1** (`OneDimTopplingStmt`). Proved. -/
theorem oneDimToppling_final :
    OneDimTopplingStmt :=
  oneDimToppling_closed

/-- **Lemma 7.2** (`CompactnessStmt`). Proved. -/
theorem compactness_final :
    CompactnessStmt :=
  compactness_closed

/-- **Lemma 7.3** (`DivisibleHomogenizeStmt`). Proved using `lawlerLimicHarmonicDifference`
(Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem divisibleHomogenize_final :
    DivisibleHomogenizeStmt :=
  divisibleHomogenize_closed lawlerLimicHarmonicDifference

/-- **Lemma 7.4** (`OdometerLowerBoundStmt`). Proved using `lawlerLimicHarmonicDifference`
(Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem odometerLowerBound_final :
    OdometerLowerBoundStmt :=
  odometerLowerBound_closed lawlerLimicHarmonicDifference

/-- **Lemma 7.5** (`FlatStmt`). Proved using `lawlerLimicHarmonicDifference`
(Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem flat_final :
    FlatStmt :=
  flat_closed lawlerLimicHarmonicDifference

/-- **Lemma 7.6** (`PegdenSmartRegularityStmt`). Proved, using the formalized Peano expansion
(`pegden_smart_prop24_stmt`). The other inputs of the proof are proved: Pegden–Smart Prop. 2.5
(`pegdenSmartProp25Stmt_of_prop24`, from Prop. 2.4) and the weak form of viscosity solutions
(`viscosityWeakLaplace`; Ishii, *On the equivalence of two notions of weak solutions, viscosity
solutions and distribution solutions*, Funkcial. Ekvac. 38 (1995) 101–120). -/
theorem pegdenSmartRegularity_final :
    PegdenSmartRegularityStmt :=
  pegdenSmartRegularity_closed
    (pegdenSmartTouching_of_ps13 (pegdenSmartProp25Stmt_of_prop24 pegden_smart_prop24_stmt)
      pegden_smart_prop24_stmt viscosityWeakLaplace)

/-- **Proposition 8.1** (`DivisibleLeastActionStmt`). Proved. -/
theorem divisibleLeastAction_final :
    DivisibleLeastActionStmt :=
  divisibleLeastAction_closed

/-- **Lemma 8.1** (`DivisibleHomogenizeDomainStmt`). Proved using `lawlerLimicHarmonicDifference`
(Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem divisibleHomogenizeDomain_final :
    DivisibleHomogenizeDomainStmt :=
  divisibleHomogenizeDomain_closed lawlerLimicHarmonicDifference

/-- **Theorem 8.2** (`DivisibleTheoremStmt`). Proved using `lawlerLimicHarmonicDifference`
(Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem divisibleTheorem_final :
    DivisibleTheoremStmt :=
  divisibleTheorem_closed lawlerLimicHarmonicDifference

/-- **Theorem 9.1** (`OpenBoundaryTheoremStmt`). Proved using `lawlerLimicHarmonicDifference`
(Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8).
Alexandrov's theorem, also used, is proved (`alexandrovStmt_proved`; Evans–Gariepy, *Measure Theory
and Fine Properties of Functions*, CRC Press 1992, Section 6.4, Theorem 1). -/
theorem openBoundaryTheorem_final :
    OpenBoundaryTheoremStmt :=
  openBoundaryTheorem_closed alexandrovStmt_proved lawlerLimicHarmonicDifference

/-- **Theorem 9.2**, height-bound form (correction C13; `SingleSourceTheoremRecurrentStmt`). Proved.
The proof uses the Fey–Levine–Peres radius bound (`LatticeProb.External.feyLevinePeresRadius_holds`;
Fey–Levine–Peres, *Growth rates and explosions in sandpiles*, J. Stat. Phys. 138 (2010), Thm 1.1) and
Alexandrov's theorem (`alexandrovStmt_proved`; Evans–Gariepy, *Measure Theory and Fine Properties of
Functions*, CRC Press 1992, Section 6.4, Theorem 1), both proved. -/
theorem singleSourceTheoremRecurrent_final : SingleSourceTheoremRecurrentStmt :=
  singleSourceRecurrent LatticeProb.External.feyLevinePeresRadius_holds alexandrovStmt_proved

/-- **Theorem 9.2**, vanishing-tail extension (correction C13; `SingleSourceTheoremRecurrentVTStmt`).
Proved. The proof uses Alexandrov's theorem (`alexandrovStmt_proved`; Evans–Gariepy, *Measure Theory
and Fine Properties of Functions*, CRC Press 1992, Section 6.4, Theorem 1), which is proved. -/
theorem singleSourceTheoremRecurrentVT_final : SingleSourceTheoremRecurrentVTStmt :=
  singleSourceRecurrentVT alexandrovStmt_proved

/-- **Theorem 9.2**, identification of the operators on recurrent backgrounds (correction C13;
`RecurrentOperatorIdentificationStmt`). Proved. -/
theorem recurrentOperatorIdentification_final : RecurrentOperatorIdentificationStmt :=
  recurrentOperatorIdentification

/-- **Theorem 9.2**, distinction of the operators at zero background (correction C13;
`RecurrentOperatorZeroBackgroundDifferenceStmt`). Proved. -/
theorem recurrentOperatorZeroBackgroundDifference_final :
    RecurrentOperatorZeroBackgroundDifferenceStmt :=
  recurrentOperatorZeroBackgroundDifference

/-- **Theorem 9.2 in dimension two with the original operator** (correction C3 alone;
`SingleSourceD2.SingleSourceTheoremD2Stmt`). Proved. -/
theorem singleSourceTheoremD2_final : SingleSourceD2.SingleSourceTheoremD2Stmt :=
  singleSourceTheorem_d2_final

end RandomSandpile

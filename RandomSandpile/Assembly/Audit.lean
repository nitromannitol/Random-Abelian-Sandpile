import RandomSandpile.Assembly.Main

/-! # Audit of the formalization

The table has one row for each theorem of `RandomSandpile/Assembly/Main.lean`, with the statement
(a `Draft` definition), the theorem and how it is proved. Together the rows give the 28 numbered results of
the paper: Theorem 1.1 and Lemma 6.2 have two forms each, and Theorem 9.2 has four parts. Below, one
`example` per theorem restates it with exactly the hypotheses that it takes, and `#print axioms`
reports its axioms. Each report lists only `propext`, `Classical.choice` and `Quot.sound`.

Counts (28 numbered results, 33 theorems): 19 results proved outright and 9 proved from admitted
literature inputs only.

| Result | Statement | Theorem | Proof |
|---|---|---|---|
| Theorem 1.1, weaker form | `MainTheoremLawRadiusStmt` | `mainTheoremLawRadius_final` | Proved from `AlexandrovStmt` (Evans–Gariepy, Section 6.4, Theorem 1), `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, Thm 6.3.8(a)), `PegdenSmartProp25Stmt` (Pegden–Smart, Prop. 2.5), `PegdenSmartProp24Stmt` (Pegden–Smart, Prop. 2.4) and `ViscosityWeakLaplaceStmt` (Ishii, 1995, Theorem 1) |
| Theorem 1.1, corrections C3 and C12 | `MainTheoremStmt` | `mainTheorem_final` | Proved from `AlexandrovStmt` (Evans–Gariepy, Section 6.4, Theorem 1), `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, Thm 6.3.8(a)), `PegdenSmartProp25Stmt` (Pegden–Smart, Prop. 2.5), `PegdenSmartProp24Stmt` (Pegden–Smart, Prop. 2.4) and `ViscosityWeakLaplaceStmt` (Ishii, 1995, Theorem 1) |
| Proposition 3.1 | `LeastActionStmt` | `leastAction_final` | Proved. |
| Proposition 3.2 | `AbelianDecompositionStmt` | `abelianDecomposition_final` | Proved. |
| Proposition 3.3 | `BurningStmt` | `burning_final` | Proved. |
| Proposition 3.4 | `RecurrentOfToppledStmt` | `recurrentOfToppled_final` | Proved. |
| Lemma 5.1 | `StabilizingLegalStmt` | `stabilizingLegal_final` | Proved. |
| Lemma 5.2 | `ABPStmt` | `abp_final` | Proved. |
| Proposition 5.1 | `ConcaveEnvelopeRepStmt` | `concaveEnvelopeRep_final` | Proved. |
| Lemma 5.3 | `MongeAmpereRepStmt` | `mongeAmpereRep_final` | Proved. |
| Lemma 5.4 | `MuBoundedStmt` | `muBounded_final` | Proved. |
| Proposition 5.2 | `HarnackQuadraticStmt` | `harnackQuadratic_final` | Proved. |
| Proposition 5.3 | `SubadditiveErgodicStmt` | `subadditiveErgodic_final` | Proved. |
| Lemma 5.5 | `MuConvergenceStmt` | `muConvergence_final` | Proved. |
| Lemma 6.1 | `MuMonotoneStmt` | `muMonotone_final` | Proved. |
| Lemma 6.2, with C(β) = c(1-β)² (correction C11) | `StrictConcavityBetaStmt` | `strictConcavityBeta_final` | Proved. |
| Lemma 6.2 (corrections C2, C4 and C11) | `StrictConcavityStmt` | `strictConcavity_final` | Proved. |
| Lemma 6.3 | `MuLipschitzStmt` | `muLipschitz_final` | Proved. |
| Lemma 6.4 | `EffectiveOperatorBasicStmt` | `effectiveOperatorBasic_final` | Proved. |
| Lemma 7.1 | `OneDimTopplingStmt` | `oneDimToppling_final` | Proved. |
| Lemma 7.2 | `CompactnessStmt` | `compactness_final` | Proved. |
| Lemma 7.3 | `DivisibleHomogenizeStmt` | `divisibleHomogenize_final` | Proved from `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, Thm 6.3.8(a)). |
| Lemma 7.4 | `OdometerLowerBoundStmt` | `odometerLowerBound_final` | Proved from `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, Thm 6.3.8(a)). |
| Lemma 7.5 | `FlatStmt` | `flat_final` | Proved from `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, Thm 6.3.8(a)). |
| Lemma 7.6 | `PegdenSmartRegularityStmt` | `pegdenSmartRegularity_final` | Proved from `PegdenSmartProp25Stmt` (Pegden–Smart, Prop. 2.5), `PegdenSmartProp24Stmt` (Pegden–Smart, Prop. 2.4) and `ViscosityWeakLaplaceStmt` (Ishii, 1995, Theorem 1). |
| Proposition 8.1 | `DivisibleLeastActionStmt` | `divisibleLeastAction_final` | Proved. |
| Lemma 8.1 | `DivisibleHomogenizeDomainStmt` | `divisibleHomogenizeDomain_final` | Proved from `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, Thm 6.3.8(a)). |
| Theorem 8.2 | `DivisibleTheoremStmt` | `divisibleTheorem_final` | Proved from `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, Thm 6.3.8(a)). |
| Theorem 9.1 | `OpenBoundaryTheoremStmt` | `openBoundaryTheorem_final` | Proved from `AlexandrovStmt` (Evans–Gariepy, Section 6.4, Theorem 1) and `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, Thm 6.3.8(a)). |
| Theorem 9.2, height-bound form (correction C13) | `SingleSourceTheoremRecurrentStmt` | `singleSourceTheoremRecurrent_final` | Proved from `AlexandrovStmt` (Evans–Gariepy, Section 6.4, Theorem 1) and `LatticeProb.External.FeyLevinePeresRadius` (Fey–Levine–Peres, Thm 1.1). |
| Theorem 9.2, vanishing-tail extension (correction C13) | `SingleSourceTheoremRecurrentVTStmt` | `singleSourceTheoremRecurrentVT_final` | Proved from `AlexandrovStmt` (Evans–Gariepy, Section 6.4, Theorem 1). |
| Theorem 9.2, identification of the operators on recurrent backgrounds (correction C13) | `RecurrentOperatorIdentificationStmt` | `recurrentOperatorIdentification_final` | Proved. |
| Theorem 9.2, distinction of the operators at zero background (correction C13) | `RecurrentOperatorZeroBackgroundDifferenceStmt` | `recurrentOperatorZeroBackgroundDifference_final` | Proved. |
-/

namespace RandomSandpile

example
    (hAlexandrov : AlexandrovStmt)
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS25 : PegdenSmartProp25Stmt) (hPS24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) :
    MainTheoremLawRadiusStmt :=
  mainTheoremLawRadius_final hAlexandrov hLawlerLimicHarmonicDifference hPS25 hPS24 hVW
#print axioms mainTheoremLawRadius_final

example
    (hAlexandrov : AlexandrovStmt)
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS25 : PegdenSmartProp25Stmt) (hPS24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) :
    MainTheoremStmt :=
  mainTheorem_final hAlexandrov hLawlerLimicHarmonicDifference hPS25 hPS24 hVW
#print axioms mainTheorem_final

example :
    LeastActionStmt :=
  leastAction_final
#print axioms leastAction_final

example :
    AbelianDecompositionStmt :=
  abelianDecomposition_final
#print axioms abelianDecomposition_final

example :
    BurningStmt :=
  burning_final
#print axioms burning_final

example :
    RecurrentOfToppledStmt :=
  recurrentOfToppled_final
#print axioms recurrentOfToppled_final

example :
    StabilizingLegalStmt :=
  stabilizingLegal_final
#print axioms stabilizingLegal_final

example :
    ABPStmt :=
  abp_final
#print axioms abp_final

example :
    ConcaveEnvelopeRepStmt :=
  concaveEnvelopeRep_final
#print axioms concaveEnvelopeRep_final

example :
    MongeAmpereRepStmt :=
  mongeAmpereRep_final
#print axioms mongeAmpereRep_final

example :
    MuBoundedStmt :=
  muBounded_final
#print axioms muBounded_final

example :
    HarnackQuadraticStmt :=
  harnackQuadratic_final
#print axioms harnackQuadratic_final

example :
    SubadditiveErgodicStmt :=
  subadditiveErgodic_final
#print axioms subadditiveErgodic_final

example :
    MuConvergenceStmt :=
  muConvergence_final
#print axioms muConvergence_final

example :
    MuMonotoneStmt :=
  muMonotone_final
#print axioms muMonotone_final

example :
    StrictConcavityBetaStmt :=
  strictConcavityBeta_final
#print axioms strictConcavityBeta_final

example :
    StrictConcavityStmt :=
  strictConcavity_final
#print axioms strictConcavity_final

example :
    MuLipschitzStmt :=
  muLipschitz_final
#print axioms muLipschitz_final

example :
    EffectiveOperatorBasicStmt :=
  effectiveOperatorBasic_final
#print axioms effectiveOperatorBasic_final

example :
    OneDimTopplingStmt :=
  oneDimToppling_final
#print axioms oneDimToppling_final

example :
    CompactnessStmt :=
  compactness_final
#print axioms compactness_final

example
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleHomogenizeStmt :=
  divisibleHomogenize_final hLawlerLimicHarmonicDifference
#print axioms divisibleHomogenize_final

example
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    OdometerLowerBoundStmt :=
  odometerLowerBound_final hLawlerLimicHarmonicDifference
#print axioms odometerLowerBound_final

example
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    FlatStmt :=
  flat_final hLawlerLimicHarmonicDifference
#print axioms flat_final

example
    (hPS25 : PegdenSmartProp25Stmt) (hPS24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) :
    PegdenSmartRegularityStmt :=
  pegdenSmartRegularity_final hPS25 hPS24 hVW
#print axioms pegdenSmartRegularity_final

example :
    DivisibleLeastActionStmt :=
  divisibleLeastAction_final
#print axioms divisibleLeastAction_final

example
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleHomogenizeDomainStmt :=
  divisibleHomogenizeDomain_final hLawlerLimicHarmonicDifference
#print axioms divisibleHomogenizeDomain_final

example
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleTheoremStmt :=
  divisibleTheorem_final hLawlerLimicHarmonicDifference
#print axioms divisibleTheorem_final

example
    (hAlexandrov : AlexandrovStmt)
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    OpenBoundaryTheoremStmt :=
  openBoundaryTheorem_final hAlexandrov hLawlerLimicHarmonicDifference
#print axioms openBoundaryTheorem_final

example (hFLP : LatticeProb.External.FeyLevinePeresRadius) (hAlexandrov : AlexandrovStmt) :
    SingleSourceTheoremRecurrentStmt := singleSourceTheoremRecurrent_final hFLP hAlexandrov
#print axioms singleSourceTheoremRecurrent_final

example (hAlexandrov : AlexandrovStmt) : SingleSourceTheoremRecurrentVTStmt :=
  singleSourceTheoremRecurrentVT_final hAlexandrov
#print axioms singleSourceTheoremRecurrentVT_final

example : RecurrentOperatorIdentificationStmt := recurrentOperatorIdentification_final
#print axioms recurrentOperatorIdentification_final

example : RecurrentOperatorZeroBackgroundDifferenceStmt :=
  recurrentOperatorZeroBackgroundDifference_final
#print axioms recurrentOperatorZeroBackgroundDifference_final

end RandomSandpile

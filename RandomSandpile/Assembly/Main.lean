import RandomSandpile.Inputs.PegdenSmartProp25
import RandomSandpile.Proofs.FinalSteps
import RandomSandpile.Proofs.Sec7.PegdenSmartAdapter
import RandomSandpile.Proofs.Sec9.RecurrentViscositySuper
import RandomSandpile.Proofs.Sec9.RecurrentIdentificationFinal
import RandomSandpile.Proofs.Sec9.RecurrentZeroComparison

/-! # Main results of "Convergence of the random Abelian sandpile"

Bou-Rabee, *Convergence of the random Abelian sandpile*, Ann. Probab. 49 (2021), arXiv:1909.07849.
This file states the main results of the paper as theorems `<name>_final`, following the corrected
`paper/random_piles-corrected.tex`. The statements are the `Draft` definitions. A theorem has no
hypotheses when its result is proved outright. Otherwise its hypotheses are literature inputs
(`RandomSandpile/Inputs`), and its docstring names each one with its source.

Counts (28 numbered results, 33 theorems): 19 results proved outright and 9 proved from admitted
literature inputs only. Theorem 1.1 and Lemma 6.2 have two theorems each, and Theorem 9.2 has four.
The table of statements is in `RandomSandpile/Assembly/Audit.lean`, and the axiom report of every
theorem is in `RandomSandpileAudit/Axioms.lean`.
-/

namespace RandomSandpile

/-- **Theorem 1.1, weaker form** (`MainTheoremLawRadiusStmt`), implied by `MainTheoremStmt`
(correction C12: `R = R(W, d, η_max)`). Proved from the literature inputs `AlexandrovStmt`
(Alexandrov's theorem; Evans–Gariepy, *Measure Theory and Fine Properties of Functions*, CRC Press 1992, Section 6.4, Theorem 1), `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, *Random Walk: A Modern
Introduction*, Thm 6.3.8), `PegdenSmartProp25Stmt` (Pegden–Smart, *Convergence of the Abelian
sandpile*, Duke Math. J. 162 (2013), Prop. 2.5), `PegdenSmartProp24Stmt` (Pegden–Smart, the same
paper, Prop. 2.4) and `ViscosityWeakLaplaceStmt` (Ishii, *On the equivalence of two notions of weak
solutions, viscosity solutions and distribution solutions*, Funkcial. Ekvac. 38 (1995) 101–120). -/
theorem mainTheoremLawRadius_final
    (hAlexandrov : AlexandrovStmt)
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS25 : PegdenSmartProp25Stmt) (hPS24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) :
    MainTheoremLawRadiusStmt :=
  mainTheoremLawRadius_closed hAlexandrov hLawlerLimicHarmonicDifference
    (pegdenSmartTouching_of_ps13 hPS25 hPS24 hVW)

/-- **Theorem 1.1** (`MainTheoremStmt`, with corrections C3 and C12: the support radius `R` depends
on `W`, `d` and `η_max`). Proved from the literature inputs `AlexandrovStmt` (Alexandrov's theorem;
Evans–Gariepy, *Measure Theory and Fine Properties of Functions*, CRC Press 1992, Section 6.4, Theorem 1),
`LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8),
`PegdenSmartProp25Stmt` (Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162
(2013), Prop. 2.5), `PegdenSmartProp24Stmt` (Pegden–Smart, the same paper, Prop. 2.4) and
`ViscosityWeakLaplaceStmt` (Ishii, *On the equivalence of two notions of weak solutions, viscosity
solutions and distribution solutions*, Funkcial. Ekvac. 38 (1995) 101–120). -/
theorem mainTheorem_final
    (hAlexandrov : AlexandrovStmt)
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS25 : PegdenSmartProp25Stmt) (hPS24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) :
    MainTheoremStmt :=
  mainTheorem_closed hAlexandrov hLawlerLimicHarmonicDifference
    (pegdenSmartTouching_of_ps13 hPS25 hPS24 hVW)

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

/-- **Lemma 7.3** (`DivisibleHomogenizeStmt`). Proved from the literature input
`LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem divisibleHomogenize_final
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleHomogenizeStmt :=
  divisibleHomogenize_closed hLawlerLimicHarmonicDifference

/-- **Lemma 7.4** (`OdometerLowerBoundStmt`). Proved from the literature input
`LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem odometerLowerBound_final
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    OdometerLowerBoundStmt :=
  odometerLowerBound_closed hLawlerLimicHarmonicDifference

/-- **Lemma 7.5** (`FlatStmt`). Proved from the literature input
`LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem flat_final
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    FlatStmt :=
  flat_closed hLawlerLimicHarmonicDifference

/-- **Lemma 7.6** (`PegdenSmartRegularityStmt`). Proved from the literature inputs `PegdenSmartProp25Stmt`
(Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013), Prop. 2.5),
`PegdenSmartProp24Stmt` (Pegden–Smart, the same paper, Prop. 2.4) and `ViscosityWeakLaplaceStmt`
(Ishii, *On the equivalence of two notions of weak solutions, viscosity solutions and distribution
solutions*, Funkcial. Ekvac. 38 (1995) 101–120). -/
theorem pegdenSmartRegularity_final
    (hPS25 : PegdenSmartProp25Stmt) (hPS24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) :
    PegdenSmartRegularityStmt :=
  pegdenSmartRegularity_closed (pegdenSmartTouching_of_ps13 hPS25 hPS24 hVW)

/-- **Proposition 8.1** (`DivisibleLeastActionStmt`). Proved. -/
theorem divisibleLeastAction_final :
    DivisibleLeastActionStmt :=
  divisibleLeastAction_closed

/-- **Lemma 8.1** (`DivisibleHomogenizeDomainStmt`). Proved from the literature input
`LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem divisibleHomogenizeDomain_final
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleHomogenizeDomainStmt :=
  divisibleHomogenizeDomain_closed hLawlerLimicHarmonicDifference

/-- **Theorem 8.2** (`DivisibleTheoremStmt`). Proved from the literature input
`LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8). -/
theorem divisibleTheorem_final
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleTheoremStmt :=
  divisibleTheorem_closed hLawlerLimicHarmonicDifference

/-- **Theorem 9.1** (`OpenBoundaryTheoremStmt`). Proved from the literature inputs `AlexandrovStmt`
(Alexandrov's theorem; Evans–Gariepy, *Measure Theory and Fine Properties of Functions*, CRC Press 1992, Section 6.4, Theorem 1) and `LawlerLimicHarmonicDifferenceStmt` (Lawler–Limic, *Random Walk: A Modern
Introduction*, Thm 6.3.8). -/
theorem openBoundaryTheorem_final
    (hAlexandrov : AlexandrovStmt)
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt) :
    OpenBoundaryTheoremStmt :=
  openBoundaryTheorem_closed hAlexandrov hLawlerLimicHarmonicDifference

/-- **Theorem 9.2**, height-bound form (correction C13; `SingleSourceTheoremRecurrentStmt`). Proved
from the literature inputs `AlexandrovStmt` (Alexandrov's theorem; Evans–Gariepy, *Measure Theory and
Fine Properties of Functions*, CRC Press 1992, Section 6.4, Theorem 1) and `LatticeProb.External.FeyLevinePeresRadius`
(Fey–Levine–Peres, *Growth rates and explosions in sandpiles*, J. Stat. Phys. 138 (2010), Thm 1.1). -/
theorem singleSourceTheoremRecurrent_final
    (hFLP : LatticeProb.External.FeyLevinePeresRadius) (hAlexandrov : AlexandrovStmt) :
    SingleSourceTheoremRecurrentStmt :=
  singleSourceRecurrent hFLP hAlexandrov

/-- **Theorem 9.2**, vanishing-tail extension (correction C13; `SingleSourceTheoremRecurrentVTStmt`).
Proved from the literature input `AlexandrovStmt` (Alexandrov's theorem; Evans–Gariepy, *Measure
Theory and Fine Properties of Functions*, CRC Press 1992, Section 6.4, Theorem 1). -/
theorem singleSourceTheoremRecurrentVT_final (hAlexandrov : AlexandrovStmt) :
    SingleSourceTheoremRecurrentVTStmt :=
  singleSourceRecurrentVT hAlexandrov

/-- **Theorem 9.2**, identification of the operators on recurrent backgrounds (correction C13;
`RecurrentOperatorIdentificationStmt`). Proved. -/
theorem recurrentOperatorIdentification_final : RecurrentOperatorIdentificationStmt :=
  recurrentOperatorIdentification

/-- **Theorem 9.2**, distinction of the operators at zero background (correction C13;
`RecurrentOperatorZeroBackgroundDifferenceStmt`). Proved. -/
theorem recurrentOperatorZeroBackgroundDifference_final :
    RecurrentOperatorZeroBackgroundDifferenceStmt :=
  recurrentOperatorZeroBackgroundDifference

end RandomSandpile

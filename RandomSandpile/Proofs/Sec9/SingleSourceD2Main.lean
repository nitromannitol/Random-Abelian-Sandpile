import RandomSandpile.Proofs.Sec9.SingleSourceD2
import RandomSandpile.Proofs.Sec9.SingleSourceD2Lower
import RandomSandpile.Proofs.Sec9.SingleSourceD2Loop
import RandomSandpile.Proofs.Sec9.SingleSourceD2Label
import RandomSandpile.Proofs.Sec9.SingleSourceD2Rays
import RandomSandpile.Proofs.Sec9.SingleSourceD2TraceLower
import RandomSandpile.Proofs.Sec9.SingleSourceD2Operator
import RandomSandpile.Proofs.Sec9.SingleSourceD2Critical
import RandomSandpile.Proofs.Sec9.SingleSourceD2CriticalProof
import RandomSandpile.Proofs.Sec9.SingleSourceD2WeakLap
import RandomSandpile.Proofs.Sec9.SingleSourceD2Approx
import RandomSandpile.Proofs.Sec9.SingleSourceD2Dilation
import RandomSandpile.Proofs.Sec9.SingleSourceD2Stability
import RandomSandpile.Proofs.Sec9.SingleSourceD2Ascoli
import RandomSandpile.Proofs.Sec9.SingleSourceD2ViscWeakRep
import RandomSandpile.Proofs.Sec9.SingleSourceD2Equicont
import RandomSandpile.Proofs.Sec9.SingleSourceD2Family
import RandomSandpile.Proofs.Sec9.SingleSourceD2SubStar

/-!
# Theorem 9.2 in dimension two: assembly from the steps

`singleSourceTheoremD2_of_openSteps`: `SingleSourceTheoremD2Stmt` from
* admitted literature inputs: Fey-Levine-Peres 2010 Theorem 1.1, Alexandrov's theorem, Pegden-Smart
  Proposition 2.5 (verbatim);
* the subsolution step in dimension two `SSLimitSubStarD2Stmt` (proved: `ssLimitSubStarD2`,
  used in `singleSourceTheorem_d2`);
* the remaining steps.
Everything else (C6, C7) is proved.
-/

open LatticeProb

namespace RandomSandpile

namespace SingleSourceD2

/-- **Theorem 9.2 in dimension two** from the admitted inputs and the steps. -/
theorem singleSourceTheoremD2_of_openSteps (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hOP1 : EffOpLeStarD2Stmt) (hOP2 : EffOpEqStarOfNotPosDefD2Stmt)
    (hE1 : SSLimitWeakLaplaceD2Stmt) (hB1 : EffOpStarTraceBoundsD2Stmt)
    (hC5 : PlanarExclusionStmt) (hD7 : SourceApproximationStmt) : SingleSourceTheoremD2Stmt := by
  have hStar : SingleSourceTheoremStarD2Stmt :=
    singleSourceTheoremStarD2_of_sub (ssCompactness_of_flp hFLP)
      (ssOuterBound_of_flp hFLP) hS (shiftComparison_of_alexandrov hA)
  have hPS : PS25ParaboloidStmt := ps25Paraboloid_of_ps25 h25
  have hF1 : SSNoPosDefLowerTestD2Stmt :=
    ssNoPosDefLowerTest_of_steps hStar hS (ssOuterBound_of_flp hFLP) hE1 hB1 hC5 hD7
      (shiftComparison_of_alexandrov hA) hPS
  exact singleSourceTheoremD2_of_star hStar hOP1
    (ssLimitSuperEffD2_of_steps hStar hPS hOP2 hF1 (ssStarWeakLaplace_of_E1 hStar hE1))

/-- **Theorem 9.2 in dimension two** with (C5) replaced by its planar steps,
(`planarExclusion_of_steps`). -/
theorem singleSourceTheoremD2_of_planarSteps (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hOP1 : EffOpLeStarD2Stmt) (hOP2 : EffOpEqStarOfNotPosDefD2Stmt)
    (hE1 : SSLimitWeakLaplaceD2Stmt) (hB1 : EffOpStarTraceBoundsD2Stmt)
    (hC2 : ComponentBoundStmt) (hC3 : AlternatingRaysStmt) (hC4 : SourceLabelOpenStmt)
    (hD7 : SourceApproximationStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_openSteps hFLP hA h25 hS hOP1 hOP2 hE1 hB1
    (planarExclusion_of_steps hC2 hC3 hC4) hD7

/-- **Theorem 9.2 in dimension two** with (C2) `componentBound` and (C4) `sourceLabelOpen` proved:
the remaining planar step is the alternating-rays lemma. -/
theorem singleSourceTheoremD2_of_remaining (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hOP1 : EffOpLeStarD2Stmt) (hOP2 : EffOpEqStarOfNotPosDefD2Stmt)
    (hE1 : SSLimitWeakLaplaceD2Stmt) (hB1 : EffOpStarTraceBoundsD2Stmt)
    (hC3 : AlternatingRaysStmt) (hD7 : SourceApproximationStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_planarSteps hFLP hA h25 hS hOP1 hOP2 hE1 hB1 componentBound hC3
    sourceLabelOpen hD7

/-- **Theorem 9.2 in dimension two** with the whole planar part (C1-C5)
proved: remaining are the operator facts, the trace-graph bounds, the weak
Laplacian of the limits, the regularized source solutions, and r4's step. -/
theorem singleSourceTheoremD2_of_nonplanar (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hOP1 : EffOpLeStarD2Stmt) (hOP2 : EffOpEqStarOfNotPosDefD2Stmt)
    (hE1 : SSLimitWeakLaplaceD2Stmt) (hB1 : EffOpStarTraceBoundsD2Stmt)
    (hD7 : SourceApproximationStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_remaining hFLP hA h25 hS hOP1 hOP2 hE1 hB1 alternatingRays hD7

/-- **Theorem 9.2 in dimension two** with the planar part and the trace-graph bounds (B1,
`effOpStarTraceBounds`) proved: remaining is r4's step. -/
theorem singleSourceTheoremD2_of_open (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hOP1 : EffOpLeStarD2Stmt) (hOP2 : EffOpEqStarOfNotPosDefD2Stmt)
    (hE1 : SSLimitWeakLaplaceD2Stmt) (hD7 : SourceApproximationStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_nonplanar hFLP hA h25 hS hOP1 hOP2 hE1 effOpStarTraceBounds hD7

/-- **Theorem 9.2 in dimension two** with `effOpLeStar` also proved: remaining is r4's step. -/
theorem singleSourceTheoremD2_of_open' (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hOP2 : EffOpEqStarOfNotPosDefD2Stmt) (hE1 : SSLimitWeakLaplaceD2Stmt)
    (hD7 : SourceApproximationStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_open hFLP hA h25 hS effOpLeStar hOP2 hE1 hD7

/-- **Theorem 9.2 in dimension two** with reduced to flatness at critical matrices (D2-PROOF
Lemma 4.1): remaining are `CriticalFlatD2Stmt`, and r4's step. -/
theorem singleSourceTheoremD2_of_critical (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hCF : CriticalFlatD2Stmt) (hE1 : SSLimitWeakLaplaceD2Stmt)
    (hD7 : SourceApproximationStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_open' hFLP hA h25 hS (effOpEqStar_of_criticalFlat hCF) hE1 hD7

/-- **Theorem 9.2 in dimension two** with the operator facts, proved (flatness at
critical matrices, `criticalFlat`): remaining is r4's step. -/
theorem singleSourceTheoremD2_of_E1_D7 (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hE1 : SSLimitWeakLaplaceD2Stmt) (hD7 : SourceApproximationStmt) :
    SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_critical hFLP hA h25 hS criticalFlat hE1 hD7

/-- **Theorem 9.2 in dimension two** with `ssLimitWeakLaplace` also proved: remaining are the
regularized source solutions and r4's step. -/
theorem singleSourceTheoremD2_of_D7 (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hD7 : SourceApproximationStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_E1_D7 hFLP hA h25 hS ssLimitWeakLaplace hD7

/-- **Theorem 9.2 in dimension two** with decomposed into its steps (SIMPLE-PROOF §7,
`sourceApproximation_of_steps`). -/
theorem singleSourceTheoremD2_of_approxSteps (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (h1 : RegularizedFamilyStmt) (h2 : ViscLaplaceEquicontStmt) (h3 : LocalArzelaAscoliStmt)
    (h4 : ViscSuperStabilityStmt) (h5 : DilationLeastStmt) (h6 : ViscLaplaceWeakStmt) :
    SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_D7 hFLP hA h25 hS (sourceApproximation_of_steps h1 h2 h3 h4 h5 h6)

/-- **Theorem 9.2 in dimension two** with the stability step (`viscSuperStability`) and the
leastness by dilation (`dilationLeast`) proved: remaining are the regularized family, the
equicontinuity, the Arzelà-Ascoli theorem off the origin, the viscosity-to-weak step and r4's
step. -/
theorem singleSourceTheoremD2_of_approxSteps' (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (h1 : RegularizedFamilyStmt) (h2 : ViscLaplaceEquicontStmt) (h3 : LocalArzelaAscoliStmt)
    (h6 : ViscLaplaceWeakStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_approxSteps hFLP hA h25 hS h1 h2 h3 viscSuperStability dilationLeast h6

/-- **Theorem 9.2 in dimension two** with the Arzelà-Ascoli step off the origin also proved
(`localArzelaAscoli`): remaining are the regularized family, the equicontinuity, the
viscosity-to-weak step and r4's step. -/
theorem singleSourceTheoremD2_of_approxSteps'' (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (h1 : RegularizedFamilyStmt) (h2 : ViscLaplaceEquicontStmt) (h6 : ViscLaplaceWeakStmt) :
    SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_approxSteps' hFLP hA h25 hS h1 h2 localArzelaAscoli h6

/-- **Theorem 9.2 in dimension two** with the viscosity-to-weak step also proved
(`viscLaplaceWeak`, from Alexandrov's theorem): remaining are the regularized family
(`RegularizedFamilyStmt`), the equicontinuity (`ViscLaplaceEquicontStmt`) and r4's step. -/
theorem singleSourceTheoremD2_of_family (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (h1 : RegularizedFamilyStmt) (h2 : ViscLaplaceEquicontStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_approxSteps'' hFLP hA h25 hS h1 h2 (viscLaplaceWeak hA)

/-- **Theorem 9.2 in dimension two** with the equicontinuity step also proved
(`viscLaplaceEquicont`, dyadic annular averages, from Alexandrov's theorem): remaining are the
regularized family (`RegularizedFamilyStmt`) and r4's step. -/
theorem singleSourceTheoremD2_of_regFamily (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (h1 : RegularizedFamilyStmt) : SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_family hFLP hA h25 hS h1 (viscLaplaceEquicont hA)

/-- **Theorem 9.2 in dimension two** (corrected sign) from the admitted inputs and the step
in dimension two as a hypothesis. The regularized family is
`regularizedFamily`. -/
theorem singleSourceTheorem_d2_of_sub (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (hS : SSLimitSubStarD2Stmt)
    (hTS : CrandallIshiiLions.CILTheoremOfSumsStmt) (hP : CrandallIshiiLions.CILPerronStmt) :
    SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_regFamily hFLP hA h25 hS (regularizedFamily hTS hP hA)

/-- **Theorem 9.2 in dimension two** (corrected sign) from the admitted inputs only: the
Fey-Levine-Peres radius bound, Alexandrov's theorem, Pegden-Smart Proposition 2.5 and
Crandall-Ishii-Lions Theorems 3.2 (theorem of sums) and 4.1 (Perron's method). The step in
dimension two is `ssLimitSubStarD2` (from the compactness `ssCompactness_of_flp` and Pegden-Smart
Proposition 2.5), the regularized family is `regularizedFamily`. -/
theorem singleSourceTheorem_d2 (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt)
    (hTS : CrandallIshiiLions.CILTheoremOfSumsStmt) (hP : CrandallIshiiLions.CILPerronStmt) :
    SingleSourceTheoremD2Stmt :=
  singleSourceTheorem_d2_of_sub hFLP hA h25 (ssLimitSubStarD2 (ssCompactness_of_flp hFLP) h25)
    hTS hP

end SingleSourceD2

end RandomSandpile

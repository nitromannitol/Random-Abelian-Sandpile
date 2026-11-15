import RandomSandpile.Assembly.Main
import RandomSandpile.Proofs.Alexandrov
import RandomSandpile.Proofs.PegdenSmart
import RandomSandpile.Proofs.ViscosityWeakLaplace

/-! # Main results from reduced literature inputs

The main theorem and Pegden–Smart regularity with the available literature inputs discharged.
-/

namespace RandomSandpile

/-- The weaker form of Theorem 1.1, assuming Lawler–Limic, *Random Walk: A Modern Introduction*,
Thm 6.3.8, and Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013),
Prop. 2.4. -/
theorem mainTheoremLawRadius_of_lawlerLimic_ps24
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS24 : PegdenSmartProp24Stmt) : MainTheoremLawRadiusStmt :=
  mainTheoremLawRadius_final alexandrovStmt_proved hLawlerLimicHarmonicDifference
    (pegdenSmartProp25Stmt_of_prop24 hPS24) hPS24 viscosityWeakLaplace

/-- Theorem 1.1, assuming Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8, and
Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013), Prop. 2.4. -/
theorem mainTheorem_of_lawlerLimic_ps24
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS24 : PegdenSmartProp24Stmt) : MainTheoremStmt :=
  mainTheorem_final alexandrovStmt_proved hLawlerLimicHarmonicDifference
    (pegdenSmartProp25Stmt_of_prop24 hPS24) hPS24 viscosityWeakLaplace

/-- Lemma 7.6, assuming Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162
(2013), Prop. 2.4. -/
theorem pegdenSmartRegularity_of_ps24 (hPS24 : PegdenSmartProp24Stmt) :
    PegdenSmartRegularityStmt :=
  pegdenSmartRegularity_final (pegdenSmartProp25Stmt_of_prop24 hPS24) hPS24 viscosityWeakLaplace

end RandomSandpile

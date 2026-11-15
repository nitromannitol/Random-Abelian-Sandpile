import RandomSandpile.Assembly.Main

/-! # Main results from reduced literature inputs

The main theorem and Pegden–Smart regularity from the two literature inputs that remain
hypotheses. These are the theorems `mainTheoremLawRadius_final`, `mainTheorem_final` and
`pegdenSmartRegularity_final` of `RandomSandpile/Assembly/Main.lean`, which take the same inputs.
-/

namespace RandomSandpile

/-- The weaker form of Theorem 1.1, assuming Lawler–Limic, *Random Walk: A Modern Introduction*,
Thm 6.3.8, and Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013),
Prop. 2.4. -/
theorem mainTheoremLawRadius_of_lawlerLimic_ps24
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS24 : PegdenSmartProp24Stmt) : MainTheoremLawRadiusStmt :=
  mainTheoremLawRadius_final hLawlerLimicHarmonicDifference

/-- Theorem 1.1, assuming Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8, and
Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013), Prop. 2.4. -/
theorem mainTheorem_of_lawlerLimic_ps24
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS24 : PegdenSmartProp24Stmt) : MainTheoremStmt :=
  mainTheorem_final hLawlerLimicHarmonicDifference

/-- Lemma 7.6, assuming Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162
(2013), Prop. 2.4. -/
theorem pegdenSmartRegularity_of_ps24 (hPS24 : PegdenSmartProp24Stmt) :
    PegdenSmartRegularityStmt :=
  pegdenSmartRegularity_final

end RandomSandpile

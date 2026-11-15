import RandomSandpile.Assembly.Main

/-! # Main results from reduced literature inputs

Compatibility forms of the main theorem and Pegden–Smart regularity with their earlier literature
inputs. In `RandomSandpile/Assembly/Main.lean`, `mainTheoremLawRadius_final` and `mainTheorem_final`
take only `LawlerLimicHarmonicDifferenceStmt`, and `pegdenSmartRegularity_final` takes no literature
input. The Pegden–Smart hypothesis retained below is redundant.
-/

namespace RandomSandpile

/-- The weaker form of Theorem 1.1, assuming Lawler–Limic, *Random Walk: A Modern Introduction*,
Thm 6.3.8, and Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013),
Prop. 2.4. -/
theorem mainTheoremLawRadius_of_lawlerLimic_ps24
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS24 : PegdenSmartProp24Stmt) : MainTheoremLawRadiusStmt :=
  (fun (_ : PegdenSmartProp24Stmt) => mainTheoremLawRadius_final hLawlerLimicHarmonicDifference) hPS24

/-- Theorem 1.1, assuming Lawler–Limic, *Random Walk: A Modern Introduction*, Thm 6.3.8, and
Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013), Prop. 2.4. -/
theorem mainTheorem_of_lawlerLimic_ps24
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS24 : PegdenSmartProp24Stmt) : MainTheoremStmt :=
  (fun (_ : PegdenSmartProp24Stmt) => mainTheorem_final hLawlerLimicHarmonicDifference) hPS24

/-- Lemma 7.6, assuming Pegden–Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162
(2013), Prop. 2.4. -/
theorem pegdenSmartRegularity_of_ps24 (hPS24 : PegdenSmartProp24Stmt) :
    PegdenSmartRegularityStmt :=
  (fun (_ : PegdenSmartProp24Stmt) => pegdenSmartRegularity_final) hPS24

end RandomSandpile

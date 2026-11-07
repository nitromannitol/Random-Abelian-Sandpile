import RandomSandpile.Proofs.Sec5.MuConvergenceRestrict
import RandomSandpile.Proofs.Sec5.MuConvergenceStationary
import RandomSandpile.Proofs.Sec5.MuConvergenceBall

/-!
# Proof of Lemma 5.5 (almost sure convergence of `μ` and `μ*`) from Proposition 5.3

Assembles the steps of `RandomSandpile/Steps/Sec5/MuConvergence.lean`, all proved:

* `muSubadditive` (Step 1) from `locLegalRestrict` and `stabilizingRestrict`
  (`Proofs/Sec5/MuConvergenceRestrict.lean`);
* `muStationary` (Step 2, `Proofs/Sec5/MuConvergenceStationary.lean`);
* `locLegalLocal` (Step 3, `Proofs/Sec5/MuConvergenceRestrict.lean`);
* `unitBallLipschitz`, `discretizeFinite` (Steps 4-5, `Proofs/Sec5/MuConvergenceBall.lean`).

The multiparameter subadditive ergodic theorem (Proposition 5.3, `SubadditiveErgodicStmt`,
Akcoglu-Krengel and Dal Maso-Modica, as stated in Armstrong-Smart) is cited by the paper and enters
`muConvergence` as an explicit hypothesis.
-/

namespace RandomSandpile

/-- **Step 1**: subadditivity of `μ` and `μ*` over finite covers. -/
theorem muSubadditive : MuSubadditiveStmt :=
  muSubadditive_of_steps locLegalRestrict stabilizingRestrict

/-- **Lemma 5.5** (sub-additive-ergodic), from Proposition 5.3. -/
theorem muConvergence (hSE : SubadditiveErgodicStmt) : MuConvergenceStmt :=
  muConvergence_of_steps hSE muSubadditive muStationary locLegalLocal unitBallLipschitz
    discretizeFinite

end RandomSandpile

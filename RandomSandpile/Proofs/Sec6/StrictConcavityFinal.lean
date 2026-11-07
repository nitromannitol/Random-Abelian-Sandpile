import RandomSandpile.Proofs.Sec6.StrictConcavitySemiconvex
import RandomSandpile.Proofs.Sec6.StrictConcavityUniform
import RandomSandpile.Proofs.Sec5.SubadditiveErgodic

/-! # Lemmas 6.2' and 6.3 from Lemma 5.5

The four steps of `LimitUniformConcavityStmt` are proved without literature inputs:
`limitBasic` (L2-0), `limitSemiconvex` (L2-A, from Proposition 5.2), `limitSlopeMass` (L2-B) and
`concaveUniformConcavity`. Hence, from Lemma 5.5 (`MuConvergenceStmt`) alone:
* `nearMaxBendingStabilizing_of_muConvergence`: Lemma 6.2' with a locally legal and stabilizing
  witness, the input of Lemma 7.5 (`NearMaxBendingStabilizingStmt`);
* `nearMaxBending_of_muConvergence`: Lemma 6.2' (`NearMaxBendingStmt`);
* `muLipschitz_of_muConvergence`: Lemma 6.3 as drafted (`MuLipschitzStmt`, with [C1]);
* `strictConcavityBeta_of_muConvergence`: Lemma 6.2 with `C = C(β)` (`StrictConcavityBetaStmt`).
The `_of_boxes` versions take the rational-box form of Proposition 5.3 instead. -/

namespace RandomSandpile

/-- **Uniform concavity of limits of rescaled envelopes** (step N2a-2). -/
theorem limitUniformConcavity : LimitUniformConcavityStmt :=
  limitUniformConcavity_of_steps limitBasic limitSemiconvex limitSlopeMass concaveUniformConcavity

/-- **Lemma 6.2'** with a locally legal and stabilizing witness, from Lemma 5.5. -/
theorem nearMaxBendingStabilizing_of_muConvergence (hconv : MuConvergenceStmt) :
    NearMaxBendingStabilizingStmt :=
  nearMaxBendingStabilizing_of_uniformConcavity hconv limitUniformConcavity

/-- **Lemma 6.2'** from Lemma 5.5. -/
theorem nearMaxBending_of_muConvergence (hconv : MuConvergenceStmt) : NearMaxBendingStmt :=
  Flat.nearMaxBending_of_stabilizing (nearMaxBendingStabilizing_of_muConvergence hconv)

/-- **Lemma 6.3** (`MuLipschitzStmt`, with [C1]) from Lemma 5.5. -/
theorem muLipschitz_of_muConvergence (hconv : MuConvergenceStmt) : MuLipschitzStmt :=
  muLipschitz_of_uniformConcavity hconv limitUniformConcavity

/-- **Lemma 6.2 with `C = C(β)`** from Lemma 5.5. -/
theorem strictConcavityBeta_of_muConvergence (hconv : MuConvergenceStmt) :
    StrictConcavityBetaStmt :=
  strictConcavityBeta_of_uniformConcavity hconv limitUniformConcavity

/-- **Lemma 6.3** from the rational-box form of Proposition 5.3. -/
theorem muLipschitz_of_boxes (h : SubadditiveRationalBoxesStmt) : MuLipschitzStmt :=
  muLipschitz_of_muConvergence (muConvergence_of_boxes h)

/-- **Lemma 6.2'** (stabilizing witness) from the rational-box form of Proposition 5.3. -/
theorem nearMaxBendingStabilizing_of_boxes (h : SubadditiveRationalBoxesStmt) :
    NearMaxBendingStabilizingStmt :=
  nearMaxBendingStabilizing_of_muConvergence (muConvergence_of_boxes h)

end RandomSandpile

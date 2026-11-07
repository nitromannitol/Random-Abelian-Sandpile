import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasicPos
import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasicLip
import RandomSandpile.Proofs.Sec5.SubadditiveErgodic

/-! # Lemma 6.4 (`EffectiveOperatorBasicStmt`) from Lemma 5.5

All steps of `effectiveOperatorBasic_of_steps` are proved: `muMonotone` (Lemma 6.1),
`muMatrixMonotone`, `muShift`, `muPositive` (deterministic) and `muLipschitzLoc_of_muConvergence`
(Lemma 6.3, locally uniform in `l`, from Lemma 5.5). Hence Lemma 6.4, with `C = d`, from
`MuConvergenceStmt`, and the shift identity `F̄_η(M + tI) = F̄_η(M) - d t`
(`effOp_add_smul_one`). -/

namespace RandomSandpile

open EffectiveOperatorBasic

/-- **Lemma 6.4** from the locally uniform Lemma 6.3. -/
theorem effectiveOperatorBasic_of_muLipschitzLoc (hlip : MuLipschitzLocStmt) :
    EffectiveOperatorBasicStmt :=
  effectiveOperatorBasic_of_steps muMonotone muMatrixMonotone muShift hlip muPositive

/-- **Lemma 6.4** from Lemma 5.5. -/
theorem effectiveOperatorBasic_of_muConvergence (hconv : MuConvergenceStmt) :
    EffectiveOperatorBasicStmt :=
  effectiveOperatorBasic_of_muLipschitzLoc (muLipschitzLoc_of_muConvergence hconv)

/-- **Lemma 6.4** from the rational-box form of Proposition 5.3. -/
theorem effectiveOperatorBasic_of_boxes (h : SubadditiveRationalBoxesStmt) :
    EffectiveOperatorBasicStmt :=
  effectiveOperatorBasic_of_muConvergence (muConvergence_of_boxes h)

/-- **Lemma 6.4(3)** for every symmetric `M`, from Lemma 5.5. -/
theorem isGreatest_effOp (hconv : MuConvergenceStmt) {d : ℕ} (hd : 2 ≤ d)
    (E : RandomEnvironment d) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) :
    IsGreatest (muEqSet E M) (effOp E M) :=
  isGreatest_muEqSet muMonotone (muLipschitzLoc_of_muConvergence hconv) muPositive hd E hM

/-- **Shift identity** `F̄_η(M + tI) = F̄_η(M) - d t`, from Lemma 5.5. -/
theorem effOp_add_smul_one (hconv : MuConvergenceStmt) {d : ℕ} (hd : 2 ≤ d)
    (E : RandomEnvironment d) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (t : ℝ) :
    effOp E (M + t • 1) = effOp E M - d * t :=
  effOp_add_smul_one_of_isGreatest muShift (by omega) E (isGreatest_effOp hconv hd E hM) t

end RandomSandpile

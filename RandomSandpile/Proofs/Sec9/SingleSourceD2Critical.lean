import RandomSandpile.Proofs.Sec9.SingleSourceD2Operator

/-!
# Theorem 9.2 in dimension two: flatness at critical matrices

D2-PROOF Lemma 4.1 and (4.4). `CriticalFlatD2Stmt`: if `F̄(Q) = 0` and `Q` is not positive definite,
then `μ̄*(0, Q) = 0` (proof: near-maximizers, the bounded-Laplacian growth estimate (1.8), the
recurrent minimum principle (1.5)-(1.6) and the dual bending lemma, D2-PROOF §4).
`effOpEqStar_of_criticalFlat`: from it, by the scalar shift `Q = M + F̄(M) I/2`,
`μ̄*(0, Q) = μ̄*(F̄(M), M)`, monotonicity of `μ̄*` and.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter

namespace RandomSandpile

open EffectiveOperatorBasic MuLipschitz

namespace SingleSourceD2

/-- **Flatness at a critical matrix**. -/
def CriticalFlatD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Q.IsSymm → effOp E Q = 0 → ¬ Q.PosDef →
      muStarBar E 0 Q = 0

/-- from flatness at critical matrices and. -/
theorem effOpEqStar_of_criticalFlat (h : CriticalFlatD2Stmt) : EffOpEqStarOfNotPosDefD2Stmt := by
  intro E hE M hM hnot
  have hE1 : E.ηmax ≤ 2 * ((2 : ℕ) : ℤ) - 1 := by rw [hE]; norm_num
  have hQs : (M + (effOp E M / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm :=
    hM.add (Matrix.isSymm_one.smul _)
  have hFQ : effOp E (M + (effOp E M / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by
    rw [effOp_add_smul_one muConvergence_unconditional le_rfl E hM]
    push_cast
    ring
  have h0 := h E hE _ hQs hFQ hnot
  have h1 : muStarBar E (effOp E M) M = 0 := by
    have hs := (muBar_shift muShift (by norm_num) E 0 (effOp E M / 2) M).2
    rw [hs] at h0
    have e : (0 : ℝ) + ((2 : ℕ) : ℝ) * (effOp E M / 2) = effOp E M := by push_cast; ring
    rwa [e] at h0
  have hle : effOpStar E M ≤ effOp E M := by
    refine csSup_le (effOpStar_set_nonempty (by norm_num) E hE1 hM) fun l hl => ?_
    by_contra hlt
    have hanti := muStarBar_anti muMonotone (by norm_num) E M (not_le.mp hlt).le
    simp only at hanti
    rw [h1] at hanti
    exact absurd hl (not_lt.2 hanti)
  exact le_antisymm (effOpLeStar E hE M hM) hle

end SingleSourceD2

end RandomSandpile

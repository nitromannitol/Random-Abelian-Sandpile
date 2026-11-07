import RandomSandpile.Proofs.Sec9.SingleSourceH0Operator
import RandomSandpile.Proofs.Sec9.SingleSourceThresholdZero
import RandomSandpile.Proofs.Sec9.SingleSourceFlatnessStar

/-!
# Theorem 9.2 for `d ≥ 3` with `H(0) = 0`: `F̄ = F*`

`OPERATOR_COMPARISON` shows `F̄ = H = F*` once `H(0) = 0`. This file
proves the reduction to the one non-formalized operator fact of that note, (11):

* `NonPosDefLegalFlatStmt d`: (11), `μ̄(0, Q) = 0` whenever `Q` is not positive definite and
  `F*(Q) ≥ 0` (the operator comparison (11); paper proof by envelope compactness,
  Monge-Ampère measures and a competing stabilizer). Taken as an explicit hypothesis.
* `effOpStar_not_posDef`: under `StabThresholdZero E`, no matrix with `F*(Q) ≥ 0` is positive
  definite (`F*(Q) ≤ F*(cI) = F*(0) - dc < 0`).
* `effOp_eq_effOpStar`: under `StabThresholdZero E` and (11), `F̄_η = F*_η` on symmetric matrices
  (`F̄ ≤ F*` is `effOpLeStar_gen`; `F*(M) ∈ muEqSet` by the shift `Q = M + (F*(M)/d) I`).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric
open scoped Matrix

namespace RandomSandpile

open EffectiveOperatorBasic

namespace SingleSourceH0

variable {d : ℕ}

/-- **(11) of the operator comparison**: if `Q` is not positive definite and `F*(Q) ≥ 0`
(`H(Q) ≥ 0`), then `μ̄(0, Q) = 0`. Not formalized (paper proof audited CORRECT). -/
def NonPosDefLegalFlatStmt (d : ℕ) : Prop :=
  ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 → ∀ Q : Matrix (Fin d) (Fin d) ℝ,
    Q.IsSymm → ¬ Q.PosDef → 0 ≤ effOpStar E Q → muBar E 0 Q = 0

/-- A positive definite matrix has `q_Y(h) ≥ c|h|²` for some `c > 0`. -/
theorem exists_qM_ge_of_posDef_gen (hd : 0 < d) {Y : Matrix (Fin d) (Fin d) ℝ} (hY : Y.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : Rd d, c * ‖h‖ ^ 2 ≤ qM Y h := by
  have hne : (sphere (0 : Rd d) 1).Nonempty :=
    ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by simp⟩
  obtain ⟨h₀, hh₀, hmin⟩ := (isCompact_sphere (0 : Rd d) 1).exists_isMinOn hne
    (contDiff_qM Y (n := 0)).continuous.continuousOn
  have hn₀ : ‖h₀‖ = 1 := by simpa using hh₀
  have hpos : 0 < qM Y h₀ := by
    have hne0 : WithLp.ofLp h₀ ≠ 0 := by
      intro h0
      have h00 : ‖h₀‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        simp [h0]
      rw [h00] at hn₀
      exact zero_ne_one hn₀
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 hY).2 hne0
    simp only [star_trivial] at this
    simp only [qM]
    linarith
  refine ⟨qM Y h₀, hpos, fun h => ?_⟩
  by_cases h0 : h = 0
  · subst h0; simp [qM]
  · have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
    have hk : ‖h‖⁻¹ • h ∈ sphere (0 : Rd d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 := isMinOn_iff.mp hmin _ hk
    have h2 : qM Y h = ‖h‖ ^ 2 * qM Y (‖h‖⁻¹ • h) := by
      rw [qM_smul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn.ne', one_pow, one_mul]
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖h‖)]

/-- Under `H(0) = 0`, no positive definite matrix has `F*(Q) ≥ 0`. -/
theorem not_posDef_of_effOpStar_nonneg (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax = 2 * (d : ℤ) - 2) (hZ : StabThresholdZero E)
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsSymm) (h0 : 0 ≤ effOpStar E Q) : ¬ Q.PosDef := by
  intro hpd
  have hE1 : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hE]; omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨c, hc, hqc⟩ := exists_qM_ge_of_posDef_gen (by omega) hpd
  have hF0 : effOpStar E 0 ≤ 0 := (effOpStar_nonpos_iff (by omega) E hE1 Matrix.isSymm_zero).2 hZ
  have hcI : (c • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := Matrix.isSymm_one.smul _
  have hPSD : (Q - c • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
    · exact Matrix.isHermitian_iff_isSymm.2 (hQ.sub hcI)
    · have h1 := hqc (WithLp.toLp 2 w)
      have h2 : 0 ≤ qM (Q - c • (1 : Matrix (Fin d) (Fin d) ℝ)) (WithLp.toLp 2 w) := by
        rw [qM_sub_mat, qM_smul_one_eq]
        nlinarith [sq_nonneg ‖(WithLp.toLp 2 w : Rd d)‖]
      unfold qM at h2
      simp only [star_trivial]
      simpa using h2
  have hel := degenerateElliptic_effOpStar (by omega) E hE1 _ _ hcI hQ hPSD
  have hsh := effOpStar_add_smul_one (by omega) E hE1 (M := (0 : Matrix (Fin d) (Fin d) ℝ))
    Matrix.isSymm_zero c
  rw [zero_add] at hsh
  nlinarith

/-- `μ̄*(0, Q) = 0` when `F*(Q) ≤ 0`. -/
theorem muStarBar_zero_of_effOpStar_nonpos (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax = 2 * (d : ℤ) - 2) {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsSymm)
    (h : effOpStar E Q ≤ 0) : muStarBar E 0 Q = 0 := by
  have hE1 : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hE]; omega
  have hz := (effOpStar_nonpos_iff (by omega) E hE1 hQ).1 h
  have hcont := continuous_muStarBar muMonotone
    (muLipschitzLoc_of_muConvergence muConvergence_unconditional) hd E Q
  have hclosed : IsClosed {l : ℝ | muStarBar E l Q = 0} := isClosed_eq hcont continuous_const
  have hsub : Set.Ioi (0 : ℝ) ⊆ {l : ℝ | muStarBar E l Q = 0} := fun l hl => hz l hl
  have := closure_minimal hsub hclosed
  rw [closure_Ioi] at this
  exact this (Set.mem_Ici.2 le_rfl)

/-- **`F̄_η = F*_η`** when `H_η(0) = 0`, from (11). -/
theorem effOp_eq_effOpStar (hd : 2 ≤ d) (h11 : NonPosDefLegalFlatStmt d)
    (E : RandomEnvironment d) (hE : E.ηmax = 2 * (d : ℤ) - 2) (hZ : StabThresholdZero E)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) : effOp E M = effOpStar E M := by
  have hE1 : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hE]; omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine le_antisymm (effOpLeStar_gen hd E hM) ?_
  set s := effOpStar E M with hs
  set Q : Matrix (Fin d) (Fin d) ℝ := M + (s / d) • (1 : Matrix (Fin d) (Fin d) ℝ) with hQdef
  have hQ : Q.IsSymm := hM.add (Matrix.isSymm_one.smul _)
  have hFQ : effOpStar E Q = 0 := by
    rw [hQdef, effOpStar_add_smul_one (by omega) E hE1 hM]
    field_simp
    ring
  have hnot := not_posDef_of_effOpStar_nonneg hd E hE hZ hQ hFQ.ge
  have h1 : muBar E 0 Q = 0 := h11 E hE Q hQ hnot hFQ.ge
  have h2 : muStarBar E 0 Q = 0 := muStarBar_zero_of_effOpStar_nonpos hd E hE hQ hFQ.le
  have hsh := muBar_shift muShift (by omega) E 0 (s / d) M
  have e : (0 : ℝ) + d * (s / d) = s := by field_simp; ring
  rw [e] at hsh
  have hG := isGreatest_effOp muConvergence_unconditional hd E hM
  refine hG.2 ?_
  show muBar E s M = muStarBar E s M
  rw [← hsh.1, ← hsh.2]
  rw [h1, h2]

end SingleSourceH0

end RandomSandpile

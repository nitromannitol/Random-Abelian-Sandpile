import RandomSandpile.Inputs.PegdenSmartProp25
import LatticeProb.Analysis.PegdenSmart

/-! # Pegden-Smart, Proposition 2.5, from Proposition 2.4

`PegdenSmartProp25Stmt` follows from `PegdenSmartProp24Stmt` and Lattice-Probability's
`LatticeProb.PegdenSmart.pegdenSmart_prop25_of_peano` on `Rd d` with Lebesgue measure. The three
translations are:

* the weak solutions agree: the trace of the matrix Hessian `hessian φ x` of a test function is
  Mathlib's Laplacian `Δ φ x`, and the test functions are the same;
* a twice differentiable point of `PeanoTwiceDifferentiableAt` (symmetric matrix `X`) is a point with a
  second-order expansion with the self-adjoint operator of `X`, whose quadratic form is `qM X v = ½ ⟪B v, v⟫`;
* conversely the operator `B` of the conclusion is replaced by its symmetric matrix `X`, and
  `⟪B v, v⟫ < 0` for `v ≠ 0` is `(-X).PosDef`. -/

open MeasureTheory Filter Topology Asymptotics
open scoped InnerProductSpace Laplacian

namespace RandomSandpile

variable {d : ℕ}

/-- The trace of the matrix Hessian is Mathlib's Laplacian. -/
theorem trace_hessian_eq_laplacian (φ : Rd d → ℝ) (x : Rd d) :
    Matrix.trace (hessian φ x) = Δ φ x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp [Matrix.trace, hessian_apply, iteratedFDeriv_two_apply]

/-- The weak solutions of `Δ u = s` of this repository are those of Lattice-Probability. -/
theorem isWeakSolutionLaplace_iff (U : Set (Rd d)) (u s : Rd d → ℝ) :
    IsWeakSolutionLaplace U u s ↔
      LatticeProb.PegdenSmart.IsWeakSolutionLaplace (volume : Measure (Rd d)) U u s := by
  unfold IsWeakSolutionLaplace LatticeProb.PegdenSmart.IsWeakSolutionLaplace
  simp_rw [trace_hessian_eq_laplacian]

/-- A symmetric matrix is the matrix of a self-adjoint operator whose quadratic form is `qM`. -/
theorem exists_operator_of_isSymm (X : Matrix (Fin d) (Fin d) ℝ) (hX : X.IsSymm) :
    ∃ B : Rd d →L[ℝ] Rd d, IsSelfAdjoint B ∧ ∀ v : Rd d, qM X v = 1 / 2 * ⟪B v, v⟫_ℝ := by
  have hH : X.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hX
  refine ⟨LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X), ?_, fun v => ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    exact Matrix.isSymmetric_toEuclideanLin_iff.2 hH
  · have hBv : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)) v =
        Matrix.toEuclideanLin X v := rfl
    rw [qM, hBv, EuclideanSpace.inner_eq_star_dotProduct]
    simp

/-- A self-adjoint operator is given by a symmetric matrix whose quadratic form is `qM`. -/
theorem exists_matrix_of_isSelfAdjoint (B : Rd d →L[ℝ] Rd d) (hB : IsSelfAdjoint B) :
    ∃ X : Matrix (Fin d) (Fin d) ℝ, X.IsSymm ∧ ∀ v : Rd d, qM X v = 1 / 2 * ⟪B v, v⟫_ℝ := by
  set X : Matrix (Fin d) (Fin d) ℝ := Matrix.toEuclideanLin.symm (B : Rd d →ₗ[ℝ] Rd d) with hXdef
  have hXB : Matrix.toEuclideanLin X = (B : Rd d →ₗ[ℝ] Rd d) := by
    rw [hXdef]
    exact LinearEquiv.apply_symm_apply _ _
  refine ⟨X, ?_, fun v => ?_⟩
  · have hsymm : (Matrix.toEuclideanLin X).IsSymmetric := by
      rw [hXB]
      exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hB
    have hH := Matrix.isSymmetric_toEuclideanLin_iff.1 hsymm
    show X.transpose = X
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hH.eq
  · have hBv : B v = Matrix.toEuclideanLin X v := by
      rw [hXB]
      rfl
    rw [qM, hBv, EuclideanSpace.inner_eq_star_dotProduct]
    simp

/-- A symmetric matrix whose quadratic form is negative away from `0` is negative definite. -/
theorem neg_posDef_of_qM_neg {X : Matrix (Fin d) (Fin d) ℝ} (hX : X.IsSymm)
    (h : ∀ v : Rd d, v ≠ 0 → qM X v < 0) : (-X).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · have hH : X.IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hX
    exact hH.neg
  · have h0 : (WithLp.toLp 2 x : Rd d) ≠ 0 := fun h0 => hx (by simpa using congrArg WithLp.ofLp h0)
    have := h _ h0
    simp only [qM] at this
    simp only [star_trivial, Matrix.neg_mulVec, dotProduct_neg]
    linarith

/-- **Pegden-Smart, Proposition 2.5, from Proposition 2.4.** -/
theorem pegdenSmartProp25Stmt_of_prop24 (h24 : PegdenSmartProp24Stmt) : PegdenSmartProp25Stmt := by
  intro d hd s u hs hu hweak hlt
  have hP : ∀ s u : Rd d → ℝ, MemLp s ⊤ ((volume : Measure (Rd d)).restrict
        (Metric.ball (0 : Rd d) 1)) → ContinuousOn u (Metric.ball 0 1) →
      LatticeProb.PegdenSmart.IsWeakSolutionLaplace (volume : Measure (Rd d)) (Metric.ball 0 1) u s →
        ∀ᵐ x ∂((volume : Measure (Rd d)).restrict (Metric.ball (0 : Rd d) 1)),
          ∃ (p : Rd d) (B : Rd d →L[ℝ] Rd d), IsSelfAdjoint B ∧
            (fun y => u y - u x - ⟪p, y - x⟫_ℝ - 1 / 2 * ⟪B (y - x), y - x⟫_ℝ) =o[𝓝 x]
              fun y => ‖y - x‖ ^ 2 := by
    intro s u hs hu hweak
    filter_upwards [h24 d hd s u hs hu ((isWeakSolutionLaplace_iff _ u s).2 hweak)]
      with x ⟨p, X, hX, hT⟩
    obtain ⟨B, hB, hq⟩ := exists_operator_of_isSymm X hX
    refine ⟨p, B, hB, ?_⟩
    unfold HasSecondOrderTaylorAt at hT
    simp_rw [hq] at hT
    exact hT
  have key := LatticeProb.PegdenSmart.pegdenSmart_prop25_of_peano (volume : Measure (Rd d)) hP s u
    hs hu ((isWeakSolutionLaplace_iff _ u s).1 hweak) hlt
  refine lt_of_lt_of_le key (measure_mono ?_)
  rintro x ⟨hxb, hxs, p, B, hB, hexp, hneg⟩
  obtain ⟨X, hX, hq⟩ := exists_matrix_of_isSelfAdjoint B hB
  refine ⟨hxb, hxs, p, X, hX, ?_, neg_posDef_of_qM_neg hX fun v hv => ?_⟩
  · unfold HasSecondOrderTaylorAt
    simp_rw [hq]
    exact hexp
  · rw [hq]
    linarith [hneg v hv]

end RandomSandpile

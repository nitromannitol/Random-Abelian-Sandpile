import RandomSandpile.Inputs.Alexandrov
import LatticeProb.Analysis.Alexandrov

/-! # Alexandrov's theorem, proved

`AlexandrovStmt` follows from Lattice-Probability's `LatticeProb.ConvexAnalysis.alexandrov_ae` on
`Rd d` with Lebesgue measure. That theorem gives, at almost every point `x`, a gradient `p` and a
self-adjoint operator `B` with
`f y = f x + ⟪p, y - x⟫ + ½ ⟪B (y - x), y - x⟫ + o(‖y - x‖²)`.
The matrix `X` of `B` in the standard basis is symmetric because `B` is self-adjoint, and its
quadratic form is `qM X v = ½ ⟪B v, v⟫`, so the expansion is `HasSecondOrderTaylorAt f x p X`. -/

open MeasureTheory
open scoped InnerProductSpace

namespace RandomSandpile

/-- **Alexandrov's theorem**: a convex function on `ℝ^d` has, at Lebesgue-almost every point, a
second-order Taylor expansion with a symmetric matrix and a Peano remainder. -/
theorem alexandrovStmt_proved : AlexandrovStmt := by
  intro d f hf
  filter_upwards [LatticeProb.ConvexAnalysis.alexandrov_ae (volume : Measure (Rd d)) hf]
    with x ⟨p, B, hB, ho⟩
  set X : Matrix (Fin d) (Fin d) ℝ := Matrix.toEuclideanLin.symm (B : Rd d →ₗ[ℝ] Rd d) with hXdef
  have hXB : Matrix.toEuclideanLin X = (B : Rd d →ₗ[ℝ] Rd d) := by
    rw [hXdef]
    exact LinearEquiv.apply_symm_apply _ _
  refine ⟨p, X, ?_, ?_⟩
  · have hsymm : (Matrix.toEuclideanLin X).IsSymmetric := by
      rw [hXB]
      exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hB
    have hH := Matrix.isSymmetric_toEuclideanLin_iff.1 hsymm
    show X.transpose = X
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hH.eq
  · have hq : ∀ v : Rd d, qM X v = 1 / 2 * ⟪B v, v⟫_ℝ := by
      intro v
      have hBv : B v = Matrix.toEuclideanLin X v := by
        rw [hXB]
        rfl
      rw [qM, hBv, EuclideanSpace.inner_eq_star_dotProduct]
      simp
    unfold HasSecondOrderTaylorAt
    simp_rw [hq]
    exact ho

end RandomSandpile

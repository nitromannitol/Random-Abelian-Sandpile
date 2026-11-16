import RandomSandpile.Proofs.PegdenSmart
import Mathlib.Analysis.InnerProductSpace.Trace

/-! # Symmetric bilinear forms and matrices

A symmetric continuous bilinear form on Euclidean space is represented by a symmetric matrix
with the same quadratic form and trace.
-/

open scoped InnerProductSpace

namespace RandomSandpile

/-- The matrix of a symmetric bilinear form represents its quadratic form and trace. -/
theorem exists_matrix_of_symmetric_bilinear {d : ℕ} (H : Rd d →L[ℝ] Rd d →L[ℝ] ℝ)
    (hH : ∀ v w, H v w = H w v) :
    ∃ X : Matrix (Fin d) (Fin d) ℝ, X.IsSymm ∧
      (∀ v : Rd d, qM X v = 1 / 2 * H v v) ∧
      Matrix.trace X =
        ∑ i, H (stdOrthonormalBasis ℝ (Rd d) i) (stdOrthonormalBasis ℝ (Rd d) i) := by
  let B := InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) H
  have hB : IsSelfAdjoint B := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro v w
    rw [ContinuousLinearMap.coe_coe, InnerProductSpace.continuousLinearMapOfBilin_apply,
      real_inner_comm, InnerProductSpace.continuousLinearMapOfBilin_apply]
    exact hH v w
  let X : Matrix (Fin d) (Fin d) ℝ := Matrix.toEuclideanLin.symm (B : Rd d →ₗ[ℝ] Rd d)
  have hXB : Matrix.toEuclideanLin X = (B : Rd d →ₗ[ℝ] Rd d) := by
    exact LinearEquiv.apply_symm_apply _ _
  have hX : X.IsSymm := by
    have hsymm : (Matrix.toEuclideanLin X).IsSymmetric := by
      rw [hXB]
      exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hB
    have hherm := Matrix.isSymmetric_toEuclideanLin_iff.1 hsymm
    show X.transpose = X
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hherm.eq
  have hq (v : Rd d) : qM X v = 1 / 2 * H v v := by
    have hBv : B v = Matrix.toEuclideanLin X v := by rw [hXB]; rfl
    rw [← InnerProductSpace.continuousLinearMapOfBilin_apply (𝕜 := ℝ) H v v]
    rw [qM, hBv, EuclideanSpace.inner_eq_star_dotProduct]
    simp
  have h1 : (B : Rd d →ₗ[ℝ] Rd d).trace ℝ (Rd d) =
      ∑ i, H (stdOrthonormalBasis ℝ (Rd d) i) (stdOrthonormalBasis ℝ (Rd d) i) := by
    rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (Rd d))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
    exact InnerProductSpace.continuousLinearMapOfBilin_apply H _ _
  have h2 : (B : Rd d →ₗ[ℝ] Rd d).trace ℝ (Rd d) = Matrix.trace X := by
    rw [← hXB, LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact ⟨X, hX, hq, h2.symm.trans h1⟩

end RandomSandpile

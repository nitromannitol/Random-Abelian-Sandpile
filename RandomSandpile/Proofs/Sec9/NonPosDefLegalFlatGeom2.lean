import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatGeom

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

/-- The quadratic-plus-linear function on coordinate vectors. -/
def gq (A : Matrix (Fin d) (Fin d) ℝ) (p u : Fin d → ℝ) : ℝ :=
  1 / 2 * (u ⬝ᵥ A *ᵥ u) + p ⬝ᵥ u

theorem gq_add (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm) (p u h : Fin d → ℝ) :
    gq A p (u + h) = gq A p u + h ⬝ᵥ (A *ᵥ u + p) + 1 / 2 * (h ⬝ᵥ A *ᵥ h) := by
  have hs : u ⬝ᵥ A *ᵥ h = h ⬝ᵥ A *ᵥ u := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]
  have hs' : h ⬝ᵥ A *ᵥ u = u ⬝ᵥ A *ᵥ h := hs.symm
  simp only [gq, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  have hp : h ⬝ᵥ p = p ⬝ᵥ h := dotProduct_comm _ _
  rw [hs', hp]
  ring

/-- Euclidean norm of a coordinate vector. -/
def nv (v : Fin d → ℝ) : ℝ := ‖(WithLp.toLp 2 v : Rd d)‖

theorem abs_dot_le (v w : Fin d → ℝ) : |v ⬝ᵥ w| ≤ nv v * nv w := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 v : Rd d) (WithLp.toLp 2 w)
  have e : inner ℝ (WithLp.toLp 2 v : Rd d) (WithLp.toLp 2 w) = w ⬝ᵥ v := by
    simp [PiLp.inner_apply, dotProduct]
  rw [e, dotProduct_comm] at h
  exact h

/-- Crude operator bound constant. -/
def opC (A : Matrix (Fin d) (Fin d) ℝ) : ℝ := ∑ i, ∑ j, |A i j|

theorem opC_nonneg (A : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ opC A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem nv_mulVec_le (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : nv (A *ᵥ v) ≤ opC A * nv v := by
  have hcoord : ∀ j, |v j| ≤ nv v := fun j => by
    have := PiLp.norm_apply_le (WithLp.toLp 2 v : Rd d) j
    simpa [Real.norm_eq_abs, nv] using this
  have := norm_le_sum_abs (WithLp.toLp 2 (A *ᵥ v) : Rd d)
  unfold nv
  refine this.trans ?_
  calc ∑ i, |(WithLp.toLp 2 (A *ᵥ v) : Rd d) i| = ∑ i, |(A *ᵥ v) i| := rfl
    _ ≤ ∑ i, ∑ j, |A i j| * nv v := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Matrix.mulVec, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcoord j) (abs_nonneg _)
    _ = opC A * nv v := by
        simp only [opC, ← Finset.sum_mul]

theorem abs_quad_le (A : Matrix (Fin d) (Fin d) ℝ) (h : Fin d → ℝ) :
    |h ⬝ᵥ A *ᵥ h| ≤ opC A * nv h ^ 2 := by
  refine (abs_dot_le h (A *ᵥ h)).trans ?_
  calc nv h * nv (A *ᵥ h) ≤ nv h * (opC A * nv h) :=
        mul_le_mul_of_nonneg_left (nv_mulVec_le A h) (by unfold nv; positivity)
    _ = opC A * nv h ^ 2 := by ring

end SingleSourceH0

end RandomSandpile

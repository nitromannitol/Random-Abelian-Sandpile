import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatGeom2
import RandomSandpile.Proofs.Sec3.Burning

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

theorem nv_sq (v : Fin d → ℝ) : nv v ^ 2 = v ⬝ᵥ v := by
  unfold nv
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, sq]

theorem nv_smul (c : ℝ) (v : Fin d → ℝ) : nv (c • v) = |c| * nv v := by
  unfold nv
  rw [show (WithLp.toLp 2 (c • v) : Rd d) = c • (WithLp.toLp 2 v : Rd d) from rfl, norm_smul,
    Real.norm_eq_abs]

theorem nv_nonneg (v : Fin d → ℝ) : 0 ≤ nv v := norm_nonneg _

/-- A symmetric non-positive-definite matrix has a unit vector with `eᵀ A e ≤ 0`. -/
theorem exists_unit_nonpos {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm) (hnot : ¬ A.PosDef) :
    ∃ e : Fin d → ℝ, nv e = 1 ∧ e ⬝ᵥ A *ᵥ e ≤ 0 := by
  have hH : A.IsHermitian := Matrix.isHermitian_iff_isSymm.2 hA
  have : ∃ w : Fin d → ℝ, w ≠ 0 ∧ ¬ 0 < w ⬝ᵥ A *ᵥ w := by
    by_contra hc
    push Not at hc
    exact hnot (Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun w hw => by simpa using hc w hw⟩)
  obtain ⟨w, hw, hle⟩ := this
  have hnw : 0 < nv w := by
    unfold nv
    exact norm_pos_iff.2 (by simpa using hw)
  refine ⟨(nv w)⁻¹ • w, ?_, ?_⟩
  · rw [nv_smul, abs_of_pos (inv_pos.2 hnw)]
    field_simp
  · simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    have : w ⬝ᵥ A *ᵥ w ≤ 0 := not_lt.1 hle
    have h2 : 0 ≤ ((nv w)⁻¹) * ((nv w)⁻¹) := by positivity
    nlinarith

/-- Coordinates of a site as a real vector. -/
def xv (y : Site d) : Fin d → ℝ := fun i => (y i : ℝ)

theorem xv_add_unit (x : Site d) (i : Fin d) : xv (x + unit i) = xv x + Pi.single i (1 : ℝ) :=
  ofLp_toE_add_unit x i

theorem xv_sub_unit (x : Site d) (i : Fin d) : xv (x - unit i) = xv x + -Pi.single i (1 : ℝ) := by
  rw [← sub_eq_add_neg]; exact ofLp_toE_sub_unit x i

theorem gS_eq (A : Matrix (Fin d) (Fin d) ℝ) (p : Rd d) (y : Site d) :
    qMZ A y + inner ℝ p (toE y) = gq A (WithLp.ofLp p) (xv y) := by
  have h1 : qMZ A y = 1 / 2 * (xv y ⬝ᵥ A *ᵥ xv y) := rfl
  have h2 : ∑ i, (y i : ℝ) * p i = (WithLp.ofLp p) ⬝ᵥ xv y := by
    simp [dotProduct, xv, mul_comm]
  rw [inner_toE_eq_sum, h1, h2]
  rfl

theorem nv_xv_le {R : ℝ} {y : Site d} (hy : y ∈ ballZ0 (d := d) R) : nv (xv y) ≤ R := by
  rw [MuLipschitz.mem_ballZ0] at hy
  exact hy.le

/-- Interior minimum: the gradient is bounded by the diagonal of `A`. -/
theorem grad_bound {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm) (p : Fin d → ℝ) {B : Set (Site d)}
    {x : Site d} (hx : x ∈ B) (hmin : ∀ y ∈ dClosure B, gq A p (xv x) ≤ gq A p (xv y)) (i : Fin d) :
    |(A *ᵥ xv x + p) i| ≤ A i i / 2 := by
  have h1 := hmin (x + unit i) (add_unit_mem_dClosure hx i)
  have h2 := hmin (x - unit i) (sub_unit_mem_dClosure hx i)
  rw [xv_add_unit, gq_add A hA] at h1
  rw [xv_sub_unit, gq_add A hA] at h2
  have a1 : (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ (A *ᵥ xv x + p) = (A *ᵥ xv x + p) i := by
    simp [single_dotProduct]
  have a2 := single_quad A i
  have a3 : (-(Pi.single i (1 : ℝ)) : Fin d → ℝ) ⬝ᵥ (A *ᵥ xv x + p) = -((A *ᵥ xv x + p) i) := by
    rw [neg_dotProduct, a1]
  have a4 : (-(Pi.single i (1 : ℝ)) : Fin d → ℝ) ⬝ᵥ A *ᵥ (-(Pi.single i (1 : ℝ))) = A i i := by
    rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]; exact a2
  rw [abs_le]
  constructor <;> linarith

theorem dClosure_union_bdry {B : Set (Site d)} {y : Site d} (hy : y ∈ dClosure B) :
    y ∈ B ∨ y ∈ bdry B := by
  rw [dClosure_eq] at hy; exact hy

end SingleSourceH0

end RandomSandpile

import LatticeProb.Walk.Harmonic

/-! # Finite-volume Poisson decomposition -/

noncomputable section
open LatticeProb
open scoped Matrix

namespace RandomSandpile

/-- Every lattice function splits on a finite set into a harmonic function and a
zero-boundary function carrying its Laplacian. -/
theorem finite_poisson_decomposition {d : ℕ} (hd : 0 < d)
    (A : Finset (Site d)) (f : Site d → ℝ) :
    ∃ p : Site d → ℝ, (∀ x, x ∉ A → p x = 0) ∧
      ∀ x ∈ A, (∑ a : Dir d, p (x + dirVec a)) - 2 * d * p x =
        (∑ a : Dir d, f (x + dirVec a)) - 2 * d * f x := by
  let b : A → ℝ := fun x =>
    (∑ a : Dir d, f ((x : Site d) + dirVec a)) - 2 * d * f x
  let v : A → ℝ := (dirichletLaplacian A)⁻¹ *ᵥ b
  refine ⟨extendZero A v, fun x hx => extendZero_of_notMem A v hx, ?_⟩
  intro x hx
  have hv : dirichletLaplacian A *ᵥ v = b := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (dirichletLaplacian_isUnit hd A),
      Matrix.one_mulVec]
  have h := dirichletLaplacian_mulVec_apply A v ⟨x, hx⟩
  rw [hv] at h
  rw [← extendZero_coe A v ⟨x, hx⟩] at h
  simpa [b] using h.symm

/-- A zero-boundary Poisson solution is controlled by the exit-time potential. -/
theorem finite_poisson_abs_le_exit {d : ℕ} (hd : 0 < d)
    (A : Finset (Site d)) (p : Site d → ℝ) (M : ℝ)
    (hp : ∀ x, x ∉ A → p x = 0)
    (hM : ∀ x ∈ A, |(∑ a : Dir d, p (x + dirVec a)) - 2 * d * p x| ≤ M) :
    ∀ x ∈ A, |p x| ≤ M * LatticeProb.u A x := by
  let v : A → ℝ := fun x => p x
  let t : A → ℝ := fun x => LatticeProb.u A x
  have hext : extendZero A v = p := by
    funext x
    by_cases hx : x ∈ A
    · exact extendZero_coe A v ⟨x, hx⟩
    · rw [extendZero_of_notMem A v hx, hp x hx]
  have hbound : ∀ x : A, |(dirichletLaplacian A *ᵥ v) x| ≤ M := by
    intro x
    rw [dirichletLaplacian_mulVec_apply, hext]
    exact hM x x.2
  have ht : dirichletLaplacian A *ᵥ t = fun _ => (-1 : ℝ) := u_mulVec hd A
  have hupper : ∀ x : A, (v - M • t) x ≤ 0 := by
    apply maximum_principle hd A
    intro x
    have hb := (abs_le.mp (hbound x)).1
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, ht]
    linarith
  have hlower : ∀ x : A, (-v - M • t) x ≤ 0 := by
    apply maximum_principle hd A
    intro x
    have hb := (abs_le.mp (hbound x)).2
    simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_smul, Pi.sub_apply,
      Pi.neg_apply, Pi.smul_apply, smul_eq_mul, ht]
    linarith
  intro x hx
  rw [abs_le]
  have h1 := hupper ⟨x, hx⟩
  have h2 := hlower ⟨x, hx⟩
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, v, t] at h1 h2
  constructor <;> linarith

end RandomSandpile

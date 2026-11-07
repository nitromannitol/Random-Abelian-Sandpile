import RandomSandpile.Proofs.Sec9.RecurrentPoissonDecomposition
import LatticeProb.Walk.ExitBox

/-! # Boundary control for lattice Poisson equations -/

noncomputable section
open LatticeProb
open scoped Matrix
namespace RandomSandpile

/-- A harmonic function bounded above on the external vertex boundary is bounded above inside. -/
theorem finite_harmonic_le_boundary {d : ℕ} (hd : 0 < d)
    (A : Finset (Site d)) (f : Site d → ℝ) (B : ℝ)
    (hboundary : ∀ x ∈ A, ∀ a : Dir d, x + dirVec a ∉ A → f (x + dirVec a) ≤ B)
    (hharm : ∀ x ∈ A, (∑ a : Dir d, f (x + dirVec a)) - 2 * d * f x = 0) :
    ∀ x ∈ A, f x ≤ B := by
  let v : A → ℝ := fun x => f x - B
  have hv : ∀ x : A, 0 ≤ (dirichletLaplacian A *ᵥ v) x := by
    intro x
    rw [dirichletLaplacian_mulVec_apply]
    have hsum : (∑ a : Dir d, (f ((x : Site d) + dirVec a) - B)) ≤
        ∑ a : Dir d, extendZero A v ((x : Site d) + dirVec a) :=
      Finset.sum_le_sum fun a _ => by
        by_cases hz : (x : Site d) + dirVec a ∈ A
        · rw [extendZero_coe A v ⟨(x : Site d) + dirVec a, hz⟩]
        · rw [extendZero_of_notMem A v hz]
          linarith [hboundary x x.2 a hz]
    have hconst : (∑ _a : Dir d, B) = 2 * (d : ℝ) * B := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [Finset.sum_sub_distrib, hconst] at hsum
    have hh := hharm x x.2
    dsimp [v]
    linarith
  intro x hx
  have := maximum_principle hd A v hv ⟨x, hx⟩
  dsimp [v] at this
  linarith

/-- The interior absolute value is controlled by exterior data and the exit-time
potential for a bounded lattice Laplacian. -/
theorem finite_poisson_abs_le_boundary {d : ℕ} (hd : 0 < d)
    (A : Finset (Site d)) (f : Site d → ℝ) (B M : ℝ)
    (hboundary : ∀ x ∈ A, ∀ a : Dir d, x + dirVec a ∉ A → |f (x + dirVec a)| ≤ B)
    (hlap : ∀ x ∈ A, |(∑ a : Dir d, f (x + dirVec a)) - 2 * d * f x| ≤ M) :
    ∀ x ∈ A, |f x| ≤ B + M * LatticeProb.u A x := by
  obtain ⟨p, hp, hplap⟩ := finite_poisson_decomposition hd A f
  have hpbound : ∀ x ∈ A, |p x| ≤ M * LatticeProb.u A x :=
    finite_poisson_abs_le_exit hd A p M hp (by
      intro x hx
      rw [hplap x hx]
      exact hlap x hx)
  let h : Site d → ℝ := fun x => f x - p x
  have hh : ∀ x ∈ A, (∑ a : Dir d, h (x + dirVec a)) - 2 * d * h x = 0 := by
    intro x hx
    have h_eq := hplap x hx
    dsimp [h]
    rw [Finset.sum_sub_distrib]
    linarith
  have hpos := finite_harmonic_le_boundary hd A h B (by
    intro x hx a ha
    dsimp [h]
    rw [hp _ ha, sub_zero]
    exact (abs_le.1 (hboundary x hx a ha)).2) hh
  have hneg := finite_harmonic_le_boundary hd A (fun x => -h x) B (by
    intro x hx a ha
    dsimp [h]
    rw [hp _ ha, sub_zero]
    linarith [(abs_le.1 (hboundary x hx a ha)).1]) (by
    intro x hx
    simp only [Finset.sum_neg_distrib]
    have := hh x hx
    linarith)
  intro x hx
  have hp' := abs_le.1 (hpbound x hx)
  have h1 := hpos x hx
  have h2 := hneg x hx
  dsimp [h] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- The bounded-Laplacian maximum estimate on a lattice box has quadratic
dependence on its radius. -/
theorem originBox_poisson_abs_le_boundary {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℕ) (f : Site d → ℝ) (B M : ℝ), 0 ≤ M →
      (∀ x ∈ originBox d R, ∀ a : Dir d, x + dirVec a ∉ originBox d R →
        |f (x + dirVec a)| ≤ B) →
      (∀ x ∈ originBox d R,
        |(∑ a : Dir d, f (x + dirVec a)) - 2 * d * f x| ≤ M) →
      ∀ x ∈ originBox d R, |f x| ≤ B + C * M * ((2 * R + 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨C, hC, hExit⟩ := u_originBox_le hd
  refine ⟨C, hC, ?_⟩
  intro R f B M hM hboundary hlap x hx
  have h := finite_poisson_abs_le_boundary hd (originBox d R) f B M hboundary hlap x hx
  have he := mul_le_mul_of_nonneg_left (hExit R x) hM
  nlinarith

end RandomSandpile

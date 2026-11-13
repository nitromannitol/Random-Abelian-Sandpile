import RandomSandpile.Defs.Lattice

/-!
# The lattice cross-polytope

A point within `ℓ¹`-distance `R` of a lattice point `c` is a convex combination of the `2d`
vertices `c ± R e_i`, each of which is at Euclidean distance exactly `R` from `c`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile
namespace StrictConcavityCross

/-- The vertices `c ± R e_i` of the lattice cross-polytope of radius `R` centred at `c`. -/
def crossVertex {d : ℕ} (c : Site d) (R : ℕ) (j : Fin d × Bool) : Site d :=
  if j.2 then c + (R : ℤ) • unit j.1 else c - (R : ℤ) • unit j.1

theorem crossVertex_apply {d : ℕ} (c : Site d) (R : ℕ) (j : Fin d × Bool) (k : Fin d) :
    crossVertex c R j k = c k + (if j.2 then (R : ℤ) else -(R : ℤ)) * (if k = j.1 then 1 else 0) := by
  obtain ⟨i, b⟩ := j
  by_cases hk : k = i <;> cases b <;> simp [crossVertex, unit, sub_eq_add_neg, hk]

theorem norm_toE_unit' {d : ℕ} (i : Fin d) : ‖toE (unit i)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [unit, Pi.single_apply, apply_ite]

/-- Every vertex is within `R` of `c`: `‖toE (crossVertex c R j) - toE c‖ = R`. -/
theorem norm_crossVertex_sub {d : ℕ} (c : Site d) (R : ℕ) (j : Fin d × Bool) :
    ‖toE (crossVertex c R j) - toE c‖ = R := by
  obtain ⟨i, b⟩ := j
  have h : toE (crossVertex c R (i, b)) - toE c
      = (if b then (R : ℝ) else -(R : ℝ)) • toE (unit i) := by
    ext k
    simp only [PiLp.sub_apply, toE_apply, PiLp.smul_apply, smul_eq_mul]
    rw [crossVertex_apply]
    cases b <;> simp [unit, Pi.single_apply]
  rw [h, norm_smul, norm_toE_unit']
  cases b <;> simp

/-- A point within `ℓ¹`-distance `R` of the lattice point `c` is a convex combination of the
vertices `c ± R e_i`. -/
theorem exists_crossPolytope_weights {d : ℕ} (hd : 1 ≤ d) (c : Site d) {R : ℕ} (hR : 1 ≤ R)
    (x : Rd d) (hx : ∑ i, |x i - (c i : ℝ)| ≤ R) :
    ∃ lam : Fin d × Bool → ℝ, (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧
      ∑ j, lam j • toE (crossVertex c R j) = x := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set y : Fin d → ℝ := fun i => x i - (c i : ℝ) with hy
  set S : ℝ := ∑ i, |y i| with hS
  set s : ℝ := 1 - S / R with hs
  have hs0 : 0 ≤ s := by
    have : S / R ≤ 1 := by rw [div_le_one hRpos]; exact hx
    linarith
  have hmax : ∀ a : ℝ, max a 0 + max (-a) 0 = |a| := by
    intro a
    rcases le_total 0 a with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  have hmax' : ∀ a : ℝ, max a 0 - max (-a) 0 = a := by
    intro a
    rcases le_total 0 a with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  obtain ⟨lamT, hT⟩ : ∃ f : Fin d → ℝ, ∀ i, f i = max (y i) 0 / R + s / (2 * d) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨lamF, hF⟩ : ∃ f : Fin d → ℝ, ∀ i, f i = max (-y i) 0 / R + s / (2 * d) :=
    ⟨_, fun _ => rfl⟩
  have hT0 : ∀ i, 0 ≤ lamT i := fun i => by
    rw [hT]
    have : 0 ≤ s / (2 * d) := by positivity
    have : 0 ≤ max (y i) 0 / R := div_nonneg (le_max_right _ _) hRpos.le
    linarith
  have hF0 : ∀ i, 0 ≤ lamF i := fun i => by
    rw [hF]
    have : 0 ≤ s / (2 * d) := by positivity
    have : 0 ≤ max (-y i) 0 / R := div_nonneg (le_max_right _ _) hRpos.le
    linarith
  have hpair : ∀ i, lamT i + lamF i = |y i| / R + s / d := by
    intro i
    rw [hT, hF, ← hmax (y i)]
    field_simp
    ring
  have hdiff : ∀ i, (R : ℝ) * (lamT i - lamF i) = y i := by
    intro i
    rw [hT, hF]
    have e : (R : ℝ) * (max (y i) 0 / R + s / (2 * d) - (max (-y i) 0 / R + s / (2 * d)))
        = max (y i) 0 - max (-y i) 0 := by
      field_simp
      ring
    rw [e, hmax']
  have hsum : ∑ i, (lamT i + lamF i) = 1 := by
    simp only [hpair, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_div, ← hS]
    field_simp
    rw [hs]
    field_simp
    ring
  refine ⟨fun j => if j.2 then lamT j.1 else lamF j.1, ?_, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact hT0 _
    · exact hF0 _
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    rw [← hsum]
  · ext k
    simp only [PiLp.smul_apply, toE_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, crossVertex_apply, ite_true, Bool.false_eq_true, ite_false]
    push_cast
    have key : ∀ i : Fin d,
        lamT i * ((c k : ℝ) + (R : ℝ) * (if k = i then 1 else 0)) +
          lamF i * ((c k : ℝ) + -(R : ℝ) * (if k = i then 1 else 0))
        = (lamT i + lamF i) * (c k : ℝ) +
          (if k = i then (R : ℝ) * (lamT i - lamF i) else 0) := by
      intro i
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, ← Finset.sum_mul, hsum,
      Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ k), hdiff]
    simp only [hy]
    ring

end StrictConcavityCross
end RandomSandpile

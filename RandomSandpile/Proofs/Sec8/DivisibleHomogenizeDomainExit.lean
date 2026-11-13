import RandomSandpile.Steps.Sec8.DivisibleHomogenizeDomain
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeRadial

/-!
# Lemma 8.1: exit time, weighted occupation and the boundary layer by the maximum principle

`paper/random_piles-corrected.tex` (Lemma 8.1, no printed proof).
Comparison arguments for the killed Green's function `g_n = greenKilled W_n` of a bounded set
`W_n = ℤ^d ∩ nW`, `W ⊆ B̄_R(0)`, so that `W_n ⊆ {|y| ≤ R n}` and `W̄_n ⊆ {|y| ≤ R n + 1}`:

* `greenDomainExitTime : GreenDomainExitTimeStmt`, (exit_time) on `W_n`, by comparison with the
  quadratic `((R n + 1)² - |y|²) / (2d)` (`greenPotential_le_of_lapR_le`);
* `weightedSum_le`: the weighted occupation bound `∑_{y ≠ x} g_A(x, y) / |y - x| ≤ 3 (ρ + 1)`
  for a finite `A ⊆ {|y| ≤ ρ}`, by comparison with `3 (ρ + 1) - (3/2) |y - x|`, whose Laplacian
  is `≤ -1 / |y - x|` (`lapR_norm_sub_ge`), as for the ball (`greenBallWeightedSum`);
* `greenPotential_indicator_le`: the maximum principle for the occupation density of a set `L`:
  `∑_{y ∈ A ∩ L} g_A(x, y) ≤ max_{z ∈ A ∩ L} ∑_{y ∈ A} g_A(z, y)`, since the left side is
  harmonic in `x` on `A ∖ L`;
* `greenDomainBoundaryLayer_of_exit : GreenDomainBoundaryExitStmt → GreenDomainBoundaryLayerStmt`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

open OdometerLowerBound DivisibleHomogenize

namespace DivisibleHomogenizeDomain

variable {d : ℕ}

/-- A bounded set of `ℝ^d` lies in a closed ball `B̄_R(0)` with `R ≥ 0`. -/
theorem exists_closedBall_of_isBounded {W : Set (Rd d)} (hW : Bornology.IsBounded W) :
    ∃ R : ℝ, 0 ≤ R ∧ W ⊆ Metric.closedBall 0 R := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Rd d)).1 hW
  refine ⟨max R 0, le_max_right _ _, hR.trans (Metric.closedBall_subset_closedBall ?_)⟩
  exact le_max_left _ _

/-- Sites of `W_n` have norm at most `R n` when `W ⊆ B̄_R(0)`. -/
theorem norm_le_of_mem_discretize {W : Set (Rd d)} {R : ℝ} (hW : W ⊆ Metric.closedBall 0 R)
    {n : ℕ} {x : Site d} (hx : x ∈ discretize W n) : ‖toE x‖ ≤ R * n := by
  obtain ⟨w, hw, hxw⟩ := hx
  rw [← hxw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  have h1 : ‖w‖ ≤ R := mem_closedBall_zero_iff.1 (hW hw)
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [norm_nonneg w]

/-- Points of `∂A` are within distance `1` of `A`: if `A ⊆ {|x| ≤ ρ}` then `|y| ≤ ρ + 1` on
`∂A`. -/
theorem norm_le_of_mem_bdry {A : Set (Site d)} {ρ : ℝ} (hA : ∀ x ∈ A, ‖toE x‖ ≤ ρ)
    {y : Site d} (hy : y ∈ bdry A) : ‖toE y‖ ≤ ρ + 1 := by
  obtain ⟨-, x, hx, i, hi | hi⟩ := mem_bdry.1 hy
  · have hy' : y = x - unit i := by rw [hi]; abel
    rw [hy', toE_sub]
    calc ‖toE x - toE (unit i)‖ ≤ ‖toE x‖ + ‖toE (unit i)‖ := norm_sub_le _ _
      _ ≤ ρ + 1 := by rw [norm_toE_unit]; linarith [hA x hx]
  · rw [hi, toE_add]
    calc ‖toE x + toE (unit i)‖ ≤ ‖toE x‖ + ‖toE (unit i)‖ := norm_add_le _ _
      _ ≤ ρ + 1 := by rw [norm_toE_unit]; linarith [hA x hx]

/-- The quadratic `(ρ² - |y|²) / (2d)` has Laplacian `-1`. -/
theorem lapR_quad (hd : 1 ≤ d) (ρ : ℝ) (z : Site d) :
    lapR (fun y : Site d => (ρ ^ 2 - ‖toE y‖ ^ 2) / (2 * d)) z = -1 := by
  have hfun : (fun y : Site d => (ρ ^ 2 - ‖toE y‖ ^ 2) / (2 * d)) =
      fun y => ρ ^ 2 / (2 * d) + qlZ (-1) y := funext fun y => by
    rw [qlZ_eq]; ring
  rw [hfun, lapR_const_add', lapR_qlZ hd]

/-- Monotonicity of the Green potential in the density (`g_A ≥ 0`). -/
theorem greenPotential_mono {A : Set (Site d)} (hA : A.Finite) {f f' : Site d → ℝ}
    (h : ∀ y, f y ≤ f' y) (x : Site d) : greenPotential A f x ≤ greenPotential A f' x := by
  obtain ⟨B, rfl⟩ := hA.exists_finset_coe
  rw [greenPotential_coe_finset, greenPotential_coe_finset]
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (greenKilled_nonneg _ _ _)

/-- The Green potential of a nonnegative density is nonnegative. -/
theorem greenPotential_nonneg {A : Set (Site d)} (hA : A.Finite) {f : Site d → ℝ}
    (h : ∀ y, 0 ≤ f y) (x : Site d) : 0 ≤ greenPotential A f x := by
  obtain ⟨B, rfl⟩ := hA.exists_finset_coe
  rw [greenPotential_coe_finset]
  exact Finset.sum_nonneg fun y _ => mul_nonneg (greenKilled_nonneg _ _ _) (h y)

/-- **Weighted occupation bound** on a finite `A ⊆ {|y| ≤ ρ}`:
`∑_{y ∈ A, y ≠ x} g_A(x, y) / |y - x| ≤ 3 (ρ + 1)` for `x ∈ A` (`d ≥ 2`). -/
theorem weightedSum_le (hd : 2 ≤ d) {A : Set (Site d)} (hA : A.Finite) {ρ : ℝ}
    (hAρ : ∀ x ∈ A, ‖toE x‖ ≤ ρ) {x : Site d} (hx : x ∈ A) :
    greenPotential A (fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹) x ≤ 3 * (ρ + 1) := by
  have hd1 : 1 ≤ d := by omega
  set g : Site d → ℝ := fun y => ‖toE (y - x)‖ with hg_def
  set w : Site d → ℝ := fun y => 3 * (ρ + 1) + (-(3 / 2)) * g y with hw_def
  have hwlap : ∀ z, lapR w z = -(3 / 2) * lapR g z := by
    intro z
    have h1 : lapR w z = lapR (fun y => (-(3 / 2 : ℝ)) * g y) z :=
      lapR_const_add' (3 * (ρ + 1)) (fun y => (-(3 / 2 : ℝ)) * g y) z
    rw [h1]
    simp only [lapR, nbrSum, ← mul_add, ← Finset.mul_sum]
    ring
  have key := greenPotential_le_of_lapR_le hd1 hA
    (fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹) w (fun z _ => ?_) (fun y hy => ?_) x hx
  · have hwx : w x = 3 * (ρ + 1) := by
      simp only [hw_def, hg_def, sub_self, toE_zero, norm_zero]
      ring
    rw [hwx] at key
    exact key
  · rw [hwlap]
    have h := lapR_norm_sub_ge hd x z
    by_cases hzx : z = x
    · subst hzx
      simp only [ite_true] at h ⊢
      simp only [hg_def]
      linarith
    · simp only [ite_eq_right hzx] at h ⊢
      have hr : 1 ≤ ‖toE (z - x)‖ := one_le_norm_toE (sub_ne_zero.2 hzx)
      have : (3 / 2 : ℝ) * (2 / (3 * ‖toE (z - x)‖)) = ‖toE (z - x)‖⁻¹ := by
        field_simp
      simp only [hg_def]
      nlinarith
  · have h1 := norm_le_of_mem_bdry hAρ hy
    have h2 := hAρ x hx
    have h3 : ‖toE (y - x)‖ ≤ ‖toE y‖ + ‖toE x‖ := by
      rw [toE_sub]; exact norm_sub_le _ _
    simp only [hw_def, hg_def]
    linarith

/-- **Maximum principle for an occupation density**: if `∑_{y ∈ A} g_A(z, y) ≤ M` for every
`z ∈ A ∩ L`, then `∑_{y ∈ A ∩ L} g_A(x, y) ≤ M` for every `x`. The left side is harmonic in `x`
on `A ∖ L`, vanishes off `A` and is at most the exit time on `A ∩ L`. -/
theorem greenPotential_indicator_le (hd : 1 ≤ d) {A L : Set (Site d)} (hA : A.Finite) {M : ℝ}
    (hM0 : 0 ≤ M) (hL : ∀ z ∈ A, z ∈ L → greenPotential A (fun _ => 1) z ≤ M) (x : Site d) :
    greenPotential A (L.indicator fun _ => 1) x ≤ M := by
  set u : Site d → ℝ := greenPotential A (L.indicator fun _ => 1) with hu
  have hle : ∀ z, u z ≤ greenPotential A (fun _ => 1) z := fun z =>
    greenPotential_mono hA (fun y => by by_cases hy : y ∈ L <;> simp [hy]) z
  have hbd : ∀ z, z ∉ A ∨ z ∈ L → u z ≤ M := by
    rintro z (hz | hz)
    · rw [hu, greenPotential_eq_zero_of_not_mem _ _ hz]; exact hM0
    · by_cases hzA : z ∈ A
      · exact (hle z).trans (hL z hzA hz)
      · rw [hu, greenPotential_eq_zero_of_not_mem _ _ hzA]; exact hM0
  by_cases hx : x ∉ A ∨ x ∈ L
  · exact hbd x hx
  simp only [not_or, not_not] at hx
  obtain ⟨hxA, hxL⟩ := hx
  have hA' : (A ∩ Lᶜ).Finite := hA.subset Set.inter_subset_left
  have hsuper : ∀ z ∈ A ∩ Lᶜ, lapR (fun y => M - u y) z ≤ 0 := by
    intro z hz
    rw [lapR_sub', lapR_const', hu, lapR_greenPotential hd hA _ hz.1]
    simp [Set.indicator_of_notMem hz.2]
  obtain ⟨y, hy, hyx⟩ := superharmonicMinPrinciple d hd (A ∩ Lᶜ) hA' (fun y => M - u y) hsuper x
    ⟨hxA, hxL⟩
  have hyA' : y ∉ A ∩ Lᶜ := (mem_bdry.1 hy).1
  have hy' : y ∉ A ∨ y ∈ L := by
    by_cases hyA : y ∈ A
    · right
      by_contra hyL
      exact hyA' ⟨hyA, hyL⟩
    · left; exact hyA
  have := hbd y hy'
  linarith

end DivisibleHomogenizeDomain

open DivisibleHomogenizeDomain

/-- **(exit_time) on `W_n`**: `∑_{y ∈ W_n} g_n(x, y) ≤ (R n + 1)² / (2d)` when `W ⊆ B̄_R(0)`. -/
theorem greenDomainExitTime : GreenDomainExitTimeStmt := by
  intro d hd W R hR hW n x
  have hfin : (discretize W n).Finite :=
    DivisibleHomogenizeDomain.discretize_finite (Metric.isBounded_closedBall.subset hW) n
  have hRn : 0 ≤ R * n := mul_nonneg hR (Nat.cast_nonneg n)
  by_cases hx : x ∈ discretize W n
  · have key := greenPotential_le_of_lapR_le hd hfin (fun _ => 1)
      (fun y => ((R * n + 1) ^ 2 - ‖toE y‖ ^ 2) / (2 * d)) (fun z _ => ?_) (fun y hy => ?_) x hx
    · refine key.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      nlinarith [norm_nonneg (toE x)]
    · rw [lapR_quad hd]
    · have h1 := norm_le_of_mem_bdry (fun x hx => norm_le_of_mem_discretize hW hx) hy
      have h2 : ‖toE y‖ ^ 2 ≤ (R * n + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      exact div_nonneg (by linarith) (by positivity)
  · rw [greenPotential_eq_zero_of_not_mem _ _ hx]
    positivity

/-- **Boundary layer from the exit time near the boundary** (maximum principle): the occupation
density of the layer `W_n ∩ {dist(·, ℤ^d ∖ W_n) ≤ γ n}` is at most the maximal expected exit time
from a point of the layer. -/
theorem greenDomainBoundaryLayer_of_exit (h : GreenDomainBoundaryExitStmt) :
    GreenDomainBoundaryLayerStmt := by
  intro d hd W hW δ hδ
  obtain ⟨γ, hγ, n₀, hn₀⟩ := h d hd W hW δ hδ
  refine ⟨γ, hγ, n₀, fun n hn x => ?_⟩
  exact greenPotential_indicator_le (by omega) (DivisibleHomogenizeDomain.discretize_finite hW.1 n)
    (by positivity) (fun z _ hz => hn₀ n hn z hz) x

end RandomSandpile

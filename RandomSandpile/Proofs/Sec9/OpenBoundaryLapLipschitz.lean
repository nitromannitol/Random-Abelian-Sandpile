import RandomSandpile.Proofs.Sec7.CompactnessGradient
import RandomSandpile.Steps.Sec9.OpenBoundary
import LatticeProb.Walk.Shells

/-!
# Theorem 9.1: interior Lipschitz estimate (`LapLipschitzInteriorStmt`)

`lapLipschitzInterior : LapLipschitzInteriorStmt`. The route follows `lapGradientBound_core`
(Proofs/Sec7/CompactnessGradient.lean): the Green representation
`∇_i u(p) = -(2d)⁻¹ ∑_y ∇_i g(y - p) Δu(y)` (after letting the heat term vanish). The charges
are split into
* `y ∈ A`, where `|Δu| ≤ M`: the box sum of `|∇g| ≤ C (1 + |·|)^{1-d}` gives `C M (R + 1)`;
* `y ∉ A`, where `Δu(y) ≥ 0` (`u ≥ 0`, `u(y) = 0`) with total mass `= -∑_A Δu ≤ M |B_R|`
  (`sum_lap_eq_zero`); at distance `≥ ρ` from `p` they contribute `C ρ^{1-d} M (2R + 1)^d`
  (`step_bound`).
A monotone lattice path from `x` to `y` stays in the box spanned by `x` and `y`, hence at distance
`≥ r/2` from `ℤ^d ∖ A` (`chain_bound`); it has `∑ |x_i - y_i| ≤ d |x - y|` steps.
-/

open Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace OpenBoundaryLapLipschitz

open LapGradient

variable {d : ℕ}

theorem toE_zero' : toE (0 : Site d) = 0 := by ext j; simp [toE_apply]

theorem toE_add' (x y : Site d) : toE (x + y) = toE x + toE y := by
  ext j; simp [toE_apply]

theorem toE_sub' (x y : Site d) : toE (x - y) = toE x - toE y := by
  ext j; simp [toE_apply]

theorem norm_toE_unit' (i : Fin d) : ‖toE (unit i)‖ = 1 := by
  have h2 : ‖toE (unit i)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_eq_single i]
    · simp [toE_apply, unit]
    · intro j _ hj; simp [toE_apply, unit, hj]
    · simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2

theorem norm_toE_le_graphNorm (z : Site d) : ‖toE z‖ ≤ (graphNorm z : ℝ) := by
  have hg : (graphNorm z : ℝ) = ∑ i, |(z i : ℝ)| := by
    simp only [graphNorm, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h1 : ‖toE z‖ ^ 2 ≤ (graphNorm z : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, hg]
    calc ∑ i, ‖toE z i‖ ^ 2 = ∑ i, |(z i : ℝ)| ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [toE_apply, Real.norm_eq_abs]
      _ ≤ (∑ i, |(z i : ℝ)|) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Nat.cast_nonneg _) (by norm_num)).1 h1

/-- The discrete Laplacian of a function supported in the open box `{|x|_∞ < R}` sums to `0`
over `[-R, R]^d`. -/
theorem sum_lap_eq_zero (u : Site d → ℤ) (R : ℕ)
    (hu : ∀ x : Site d, (∃ i, (R : ℤ) ≤ |x i|) → u x = 0) :
    ∑ y ∈ boxFinset (0 : Site d) R, (lap u y : ℝ) = 0 := by
  set S := boxFinset (0 : Site d) R with hS
  set U : Site d → ℝ := fun y => (u y : ℝ) with hU
  have hout : ∀ y, y ∉ S → ∃ j, (R : ℤ) + 1 ≤ |y j| := by
    intro y hy
    rw [hS, mem_boxFinset_iff] at hy
    push Not at hy
    obtain ⟨j, hj⟩ := hy
    simp only [Pi.zero_apply, sub_zero] at hj
    exact ⟨j, hj⟩
  have hUS : ∀ y, y ∉ S → U y = 0 := fun y hy => by
    obtain ⟨j, hj⟩ := hout y hy
    simp only [hU]; rw [hu y ⟨j, by linarith⟩]; simp
  have hUp : ∀ (i : Fin d) y, y ∉ S → U (y + unit i) = 0 := fun i y hy => by
    obtain ⟨j, hj⟩ := hout y hy
    simp only [hU]
    rw [hu _ ⟨j, by
      have := (le_abs_add_of_le_abs (abs_unit_le i j) hj).1
      simpa using this⟩]
    simp
  have hUm : ∀ (i : Fin d) y, y ∉ S → U (y - unit i) = 0 := fun i y hy => by
    obtain ⟨j, hj⟩ := hout y hy
    simp only [hU]
    rw [hu _ ⟨j, by
      have := (le_abs_add_of_le_abs (abs_unit_le i j) hj).2
      simpa using this⟩]
    simp
  have e0 : ∑' y, U y = ∑ y ∈ S, U y := tsum_eq_sum (s := S) (fun y hy => hUS y hy)
  have hshp : ∀ i : Fin d, ∑ y ∈ S, U (y + unit i) = ∑ y ∈ S, U y := fun i => by
    have e1 : ∑' y, U (y + unit i) = ∑ y ∈ S, U (y + unit i) :=
      tsum_eq_sum (s := S) (fun y hy => hUp i y hy)
    rw [← e1, ← e0]
    exact (Equiv.addRight (unit i)).tsum_eq U
  have hshm : ∀ i : Fin d, ∑ y ∈ S, U (y - unit i) = ∑ y ∈ S, U y := fun i => by
    have e1 : ∑' y, U (y - unit i) = ∑ y ∈ S, U (y - unit i) :=
      tsum_eq_sum (s := S) (fun y hy => hUm i y hy)
    rw [← e1, ← e0]
    exact (Equiv.subRight (unit i)).tsum_eq U
  have hF : ∀ y, (lap u y : ℝ) = ∑ i : Fin d, (U (y + unit i) + U (y - unit i)) - 2 * d * U y := by
    intro y; simp only [hU, lap_eq, nbrSumZ]; push_cast; ring
  have h1 : ∑ y ∈ S, ∑ i : Fin d, (U (y + unit i) + U (y - unit i)) =
      ∑ i : Fin d, ∑ y ∈ S, (U (y + unit i) + U (y - unit i)) := Finset.sum_comm
  rw [Finset.sum_congr rfl fun y _ => hF y, Finset.sum_sub_distrib, h1, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, hshp, hshm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **One step**: the increment `u(p + e_i) - u(p)` at a point `p` at distance `≥ ρ` from
`ℤ^d ∖ A`. -/
theorem step_bound (hd : 2 ≤ d) : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (u : Site d → ℤ) (A : Set (Site d)) (M : ℝ) (R : ℕ) (ρ : ℝ),
      (∀ x, 0 ≤ u x) → (∀ x, x ∉ A → u x = 0) → (∀ x ∈ A, ∀ i, |x i| < (R : ℤ)) →
      (∀ x ∈ A, |(lap u x : ℝ)| ≤ M) → 0 < ρ →
      ∀ p : Site d, (∀ z, z ∉ A → ρ ≤ ‖toE (z - p)‖) → ∀ i : Fin d,
        |(u (p + unit i) : ℝ) - u p| ≤
          C₁ * M * ((R : ℝ) + 1) + C₂ * M * ((2 * R + 1 : ℕ) : ℝ) ^ d * ρ ^ (1 - (d : ℝ)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨Cg, hCg, hgrad⟩ := exists_srwGreen_gradient d hd
  obtain ⟨Ch, hCh, hheat⟩ := GreenTwoSided.srwHeat_le_mul_rpow_neg_half (d := d) (by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  refine ⟨(2 * d : ℝ)⁻¹ * Cg * (1 + 4 * d * 2 ^ (d - 1)), (2 * d : ℝ)⁻¹ * Cg, by positivity,
    by positivity, ?_⟩
  intro u A M R ρ hu0 huA hAbox hM hρ p hfar i
  classical
  have hpA : p ∈ A := by
    by_contra h
    have := hfar p h
    rw [sub_self, toE_zero', norm_zero] at this
    linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM p hpA)
  have hu : ∀ x : Site d, (∃ j, (R : ℤ) ≤ |x j|) → u x = 0 := by
    rintro x ⟨j, hj⟩
    apply huA
    intro hx
    have := hAbox x hx j
    linarith
  have hx : p ∈ boxFinset (0 : Site d) (R + 1) := by
    rw [mem_boxFinset_iff]
    intro j
    have := hAbox p hpA j
    simp only [Pi.zero_apply, sub_zero]
    push_cast
    linarith
  set S : Finset (Site d) := boxFinset (0 : Site d) R with hS
  set U : Site d → ℝ := fun y => (u y : ℝ) with hUdef
  set F : Site d → ℝ := fun y => (lap u y : ℝ) with hFdef
  have hFeq : ∀ y, F y = nbrSum U y - 2 * d * U y := by
    intro y
    simp only [hFdef, hUdef, lap, nbrSumZ, nbrSum]
    push_cast
    ring
  have hUS : ∀ y, y ∉ S → U y = 0 := by
    intro y hy
    rw [hS, mem_boxFinset_iff] at hy
    push Not at hy
    obtain ⟨j, hj⟩ := hy
    simp only [Pi.zero_apply, sub_zero] at hj
    simp only [hUdef]
    rw [hu y ⟨j, by linarith⟩]
    simp
  have hFS : ∀ y, y ∉ S → F y = 0 := by
    intro y hy
    simp only [hFdef]
    rw [lap_eq_zero_of_not_mem_box u R hu y hy]
    simp
  -- splitting the charges
  set F₁ : Site d → ℝ := fun y => if y ∈ A then F y else 0 with hF₁
  set F₂ : Site d → ℝ := fun y => if y ∈ A then 0 else F y with hF₂
  have hF12 : ∀ y, F y = F₁ y + F₂ y := fun y => by
    by_cases h : y ∈ A <;> simp [hF₁, hF₂, h]
  have hF₁M : ∀ y, |F₁ y| ≤ M := fun y => by
    by_cases h : y ∈ A
    · simp only [hF₁, h, ite_true, hFdef]; exact hM y h
    · simp only [hF₁, h, ite_false, abs_zero]; exact hM0
  have hF₂0 : ∀ y, 0 ≤ F₂ y := fun y => by
    by_cases h : y ∈ A
    · simp [hF₂, h]
    · simp only [hF₂, h, ite_false, hFdef]
      rw [lap_eq, huA y h, nbrSumZ]
      have : (0 : ℤ) ≤ ∑ j : Fin d, (u (y + unit j) + u (y - unit j)) :=
        Finset.sum_nonneg fun j _ => add_nonneg (hu0 _) (hu0 _)
      have : (0 : ℤ) ≤ ∑ j : Fin d, (u (y + unit j) + u (y - unit j)) - 2 * d * 0 := by
        simpa using this
      exact_mod_cast this
  have hsumF : ∑ y ∈ S, F y = 0 := sum_lap_eq_zero u R hu
  have hmass : ∑ y ∈ S, F₂ y ≤ M * (S.card : ℝ) := by
    have h1 : ∑ y ∈ S, F y = ∑ y ∈ S, F₁ y + ∑ y ∈ S, F₂ y := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun y _ => hF12 y
    have h2 : -∑ y ∈ S, F₁ y ≤ ∑ y ∈ S, |F₁ y| := by
      have := Finset.abs_sum_le_sum_abs F₁ S
      linarith [neg_abs_le (∑ y ∈ S, F₁ y)]
    have h3 : ∑ y ∈ S, |F₁ y| ≤ ∑ _y ∈ S, M := Finset.sum_le_sum fun y _ => hF₁M y
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    linarith
  -- the far charges
  have hfarG : ∀ (m : ℕ) (y : Site d), y ∉ A →
      |srwGreen d m (y - (p + unit i)) - srwGreen d m (y - p)| ≤ Cg * ρ ^ (1 - (d : ℝ)) := by
    intro m y hy
    have hmem : y - p ∈ nbrFinset (y - (p + unit i)) := by
      rw [nbrFinset, Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      abel
    refine (hgrad m _ _ hmem).trans (mul_le_mul_of_nonneg_left ?_ hCg.le)
    apply Real.rpow_le_rpow_of_nonpos hρ _ (by linarith)
    have h1 := hfar y hy
    have h2 : ‖toE (y - p)‖ ≤ ‖toE (y - (p + unit i))‖ + 1 := by
      rw [show y - p = (y - (p + unit i)) + unit i by abel, toE_add']
      exact (norm_add_le _ _).trans (by rw [norm_toE_unit'])
    have h3 := norm_toE_le_graphNorm (y - (p + unit i))
    linarith
  have hB2 : ∀ m : ℕ, |∑ y ∈ S, (srwGreen d m (y - (p + unit i)) - srwGreen d m (y - p)) * F₂ y|
      ≤ Cg * ρ ^ (1 - (d : ℝ)) * (M * S.card) := by
    intro m
    calc |∑ y ∈ S, (srwGreen d m (y - (p + unit i)) - srwGreen d m (y - p)) * F₂ y|
        ≤ ∑ y ∈ S, |(srwGreen d m (y - (p + unit i)) - srwGreen d m (y - p)) * F₂ y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ S, Cg * ρ ^ (1 - (d : ℝ)) * F₂ y := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (hF₂0 y)]
          by_cases hyA : y ∈ A
          · simp [hF₂, hyA]
          · exact mul_le_mul_of_nonneg_right (hfarG m y hyA) (hF₂0 y)
      _ = Cg * ρ ^ (1 - (d : ℝ)) * ∑ y ∈ S, F₂ y := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  have hbound : ∀ m : ℕ, 1 ≤ m →
      |U (p + unit i) - U p| ≤ Ch * (m : ℝ) ^ (-(d : ℝ) / 2) * ∑ y ∈ S, |U y|
        + (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))
          + Cg * ρ ^ (1 - (d : ℝ)) * (M * S.card)) := by
    intro m hm
    have e1 := greenRep hd0 S U F hFeq hUS hFS (p + unit i) m
    have e2 := greenRep hd0 S U F hFeq hUS hFS p m
    have hdiff : U (p + unit i) - U p
        = (∑ y ∈ S, (srwHeat d m (y - (p + unit i)) - srwHeat d m (y - p)) * U y)
          - (2 * d : ℝ)⁻¹ * ∑ y ∈ S,
            (srwGreen d m (y - (p + unit i)) - srwGreen d m (y - p)) * F y := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      linarith [e1, e2]
    have hsplit : ∑ y ∈ S, (srwGreen d m (y - (p + unit i)) - srwGreen d m (y - p)) * F y =
        ∑ y ∈ S, (srwGreen d m (y - (p + unit i)) - srwGreen d m (y - p)) * F₁ y +
        ∑ y ∈ S, (srwGreen d m (y - (p + unit i)) - srwGreen d m (y - p)) * F₂ y := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ => by rw [hF12 y, mul_add]
    have hA := heat_diff_sum_le hheat S U p (unit i) m hm
    have hB1 := green_diff_sum_le hCg hgrad (by omega : 1 ≤ d) R p hx i F₁ M hM0 hF₁M m
    rw [hdiff]
    refine (abs_sub _ _).trans ?_
    refine add_le_add hA ?_
    rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity)), hsplit]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hB1 (hB2 m)))
      (by positivity)
  have hlim : Tendsto (fun m : ℕ => Ch * (m : ℝ) ^ (-(d : ℝ) / 2) * ∑ y ∈ S, |U y|
        + (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))
          + Cg * ρ ^ (1 - (d : ℝ)) * (M * S.card)))
      atTop (𝓝 (Ch * 0 * ∑ y ∈ S, |U y|
        + (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))
          + Cg * ρ ^ (1 - (d : ℝ)) * (M * S.card)))) := by
    have hpow : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(d : ℝ) / 2)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := (d : ℝ) / 2) (by positivity)).comp
        tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, neg_div] using h
    exact ((hpow.const_mul Ch).mul_const _).add_const _
  have hfinal := ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun m hm => hbound m hm⟩)
  have hcons : |U (p + unit i) - U p| ≤ (2 * d : ℝ)⁻¹ *
      (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))
        + Cg * ρ ^ (1 - (d : ℝ)) * (M * S.card)) := by
    simpa using hfinal
  have hcard : (S.card : ℝ) = ((2 * R + 1 : ℕ) : ℝ) ^ d := by
    rw [hS, card_boxFinset_zero]; push_cast; ring
  refine hcons.trans ?_
  have hT : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
  have hRn : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hkey : (2 * d : ℝ)⁻¹ * Cg * (1 + 4 * d * 2 ^ (d - 1)) * M * ((R : ℝ) + 1)
      - (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1))))
      = (2 * d : ℝ)⁻¹ * Cg * M * R := by
    push_cast
    ring
  have hpos : 0 ≤ (2 * d : ℝ)⁻¹ * Cg * M * R := by positivity
  rw [hcard]
  show _ ≤ (2 * d : ℝ)⁻¹ * Cg * (1 + 4 * d * 2 ^ (d - 1)) * M * ((R : ℝ) + 1) +
    (2 * d : ℝ)⁻¹ * Cg * M * ((2 * R + 1 : ℕ) : ℝ) ^ d * ρ ^ (1 - (d : ℝ))
  nlinarith

theorem unit_apply' (i j : Fin d) : (unit i : Site d) j = if j = i then 1 else 0 := by
  simp [unit, Pi.single_apply]

/-- **Chaining along a monotone lattice path** from `x` to `y`. -/
theorem chain_bound {f : Site d → ℝ} {K : ℝ} {Good : Site d → Prop}
    (hstep : ∀ p (i : Fin d), Good p → |f (p + unit i) - f p| ≤ K) :
    ∀ (N : ℕ) (x y : Site d), ∑ i, (y i - x i).natAbs = N →
      (∀ p : Site d, (∀ i, min (x i) (y i) ≤ p i ∧ p i ≤ max (x i) (y i)) → Good p) →
      |f x - f y| ≤ N * K := by
  intro N
  induction N with
  | zero =>
    intro x y hN _
    have hxy : x = y := by
      funext i
      have := (Finset.sum_eq_zero_iff.1 hN) i (Finset.mem_univ _)
      omega
    subst hxy; simp
  | succ N ih =>
    intro x y hN hgood
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      have : ∑ i, (y i - x i).natAbs = 0 := Finset.sum_eq_zero fun i _ => by rw [h i]; simp
      omega
    have hsum : ∀ x' : Site d, (∀ j, j ≠ i → x' j = x j) →
        (y i - x' i).natAbs + 1 = (y i - x i).natAbs → ∑ j, (y j - x' j).natAbs = N := by
      intro x' hx' hxi
      have e1 := Finset.add_sum_erase Finset.univ (fun j => (y j - x' j).natAbs) (Finset.mem_univ i)
      have e2 := Finset.add_sum_erase Finset.univ (fun j => (y j - x j).natAbs) (Finset.mem_univ i)
      have e3 : ∑ j ∈ Finset.univ.erase i, (y j - x' j).natAbs =
          ∑ j ∈ Finset.univ.erase i, (y j - x j).natAbs :=
        Finset.sum_congr rfl fun j hj => by rw [hx' j (Finset.ne_of_mem_erase hj)]
      omega
    obtain ⟨x', hx'1, hx'box, hxx'⟩ : ∃ x' : Site d, ∑ j, (y j - x' j).natAbs = N ∧
        (∀ p : Site d, (∀ j, min (x' j) (y j) ≤ p j ∧ p j ≤ max (x' j) (y j)) →
          ∀ j, min (x j) (y j) ≤ p j ∧ p j ≤ max (x j) (y j)) ∧
        |f x - f x'| ≤ K := by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · refine ⟨x + unit i, hsum _ (fun j hj => by simp [unit_apply', hj]) ?_, ?_, ?_⟩
        · simp only [Pi.add_apply, unit_apply', ite_true]; omega
        · intro p hp j
          have h := hp j
          by_cases hj : j = i
          · subst hj; simp only [Pi.add_apply, unit_apply', ite_true] at h; omega
          · simp only [Pi.add_apply, unit_apply', hj, ite_false, add_zero] at h; exact h
        · have := hstep x i (hgood x fun j => ⟨min_le_left _ _, le_max_left _ _⟩)
          rwa [abs_sub_comm]
      · refine ⟨x - unit i, hsum _ (fun j hj => by simp [unit_apply', hj]) ?_, ?_, ?_⟩
        · simp only [Pi.sub_apply, unit_apply', ite_true]; omega
        · intro p hp j
          have h := hp j
          by_cases hj : j = i
          · subst hj; simp only [Pi.sub_apply, unit_apply', ite_true] at h; omega
          · simp only [Pi.sub_apply, unit_apply', hj, ite_false, sub_zero] at h; exact h
        · have hbox : ∀ j, min (x j) (y j) ≤ (x - unit i) j ∧ (x - unit i) j ≤ max (x j) (y j) := by
            intro j
            by_cases hj : j = i
            · subst hj; simp only [Pi.sub_apply, unit_apply', ite_true]; omega
            · simp only [Pi.sub_apply, unit_apply', hj, ite_false, sub_zero]
              exact ⟨min_le_left _ _, le_max_left _ _⟩
          have := hstep (x - unit i) i (hgood _ hbox)
          rwa [sub_add_cancel] at this
    have h2 := ih x' y hx'1 (fun p hp => hgood p (hx'box p hp))
    calc |f x - f y| ≤ |f x - f x'| + |f x' - f y| := abs_sub_le _ _ _
      _ ≤ K + N * K := add_le_add hxx' h2
      _ = ((N + 1 : ℕ) : ℝ) * K := by push_cast; ring

/-- Points of the box spanned by `x` and `y` are closer to `x` than `y` is. -/
theorem box_norm_le {x y p : Site d}
    (hp : ∀ i, min (x i) (y i) ≤ p i ∧ p i ≤ max (x i) (y i)) :
    ‖toE (p - x)‖ ≤ ‖toE (y - x)‖ := by
  have h : ‖toE (p - x)‖ ^ 2 ≤ ‖toE (y - x)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : |p i - x i| ≤ |y i - x i| := by
      have := hp i
      rcases le_total (x i) (y i) with h | h
      · rw [min_eq_left h, max_eq_right h] at this
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
      · rw [min_eq_right h, max_eq_left h] at this
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; omega
    have hz : (p i - x i) ^ 2 ≤ (y i - x i) ^ 2 := sq_le_sq.2 h1
    simp only [toE_apply, Real.norm_eq_abs, sq_abs, Pi.sub_apply]
    push_cast
    exact_mod_cast hz
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h

/-- The number of steps of the path: `∑ |y_i - x_i| ≤ d |x - y|`. -/
theorem natAbs_sum_le (x y : Site d) :
    ((∑ i, (y i - x i).natAbs : ℕ) : ℝ) ≤ d * ‖toE (x - y)‖ := by
  push_cast
  have h : ∀ i, (((y i - x i).natAbs : ℕ) : ℝ) ≤ ‖toE (x - y)‖ := by
    intro i
    have h1 := PiLp.norm_apply_le (toE (x - y)) i
    rw [toE_apply, Real.norm_eq_abs] at h1
    rw [Nat.cast_natAbs, Int.cast_abs]
    calc |((y i - x i : ℤ) : ℝ)| = |(((x - y) i : ℤ) : ℝ)| := by
          rw [← abs_neg]; congr 1; simp
      _ ≤ _ := h1
  calc ∑ i, (((y i - x i).natAbs : ℕ) : ℝ) ≤ ∑ _i : Fin d, ‖toE (x - y)‖ :=
        Finset.sum_le_sum fun i _ => h i
    _ = d * ‖toE (x - y)‖ := by simp

/-- The final constant: `(2R+1)^d (r/2)^{1-d} ≤ 4^d (R+1) ((R+1)/r)^{d-1}`. -/
theorem final_arith (hd1 : 1 ≤ d) (R : ℕ) {r : ℝ} (hr : 0 < r) :
    ((2 * R + 1 : ℕ) : ℝ) ^ d * (r / 2) ^ (1 - (d : ℝ)) ≤
      4 ^ d * ((R : ℝ) + 1) * (((R : ℝ) + 1) / r) ^ (d - 1) := by
  have e : ((1 : ℝ) - d) = -(((d - 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hd1]; push_cast; ring
  rw [e, Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow, inv_div, div_pow, div_pow]
  set Rr : ℝ := (R : ℝ) + 1 with hRr
  have hRr0 : 0 < Rr := by positivity
  have hdd : d = (d - 1) + 1 := by omega
  have h1 : ((2 * R + 1 : ℕ) : ℝ) ^ d ≤ (2 * Rr) ^ d := by
    apply pow_le_pow_left₀ (by positivity); push_cast; rw [hRr]; linarith
  have h2 : (2 * Rr) ^ d = 2 ^ d * (Rr * Rr ^ (d - 1)) := by
    rw [mul_pow]; congr 1; conv_lhs => rw [hdd]
    rw [pow_succ]; ring
  have h4 : (2 : ℝ) ^ d * 2 ^ (d - 1) ≤ 4 ^ d := by
    have : (4 : ℝ) ^ d = 2 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  have hr0 : 0 < r ^ (d - 1) := by positivity
  rw [div_eq_mul_inv (2 ^ (d - 1) : ℝ), div_eq_mul_inv (Rr ^ (d - 1))]
  have hX : 0 ≤ (r ^ (d - 1))⁻¹ := by positivity
  calc ((2 * R + 1 : ℕ) : ℝ) ^ d * (2 ^ (d - 1) * (r ^ (d - 1))⁻¹)
      ≤ (2 * Rr) ^ d * (2 ^ (d - 1) * (r ^ (d - 1))⁻¹) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 ^ d * 2 ^ (d - 1)) * (Rr * (Rr ^ (d - 1) * (r ^ (d - 1))⁻¹)) := by rw [h2]; ring
    _ ≤ 4 ^ d * (Rr * (Rr ^ (d - 1) * (r ^ (d - 1))⁻¹)) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = 4 ^ d * Rr * (Rr ^ (d - 1) * (r ^ (d - 1))⁻¹) := by ring

end OpenBoundaryLapLipschitz

open OpenBoundaryLapLipschitz in
/-- **Theorem 9.1** (`LapLipschitzInteriorStmt`): interior Lipschitz estimate for
nonnegative lattice functions with a bounded Laplacian in `A`. -/
theorem lapLipschitzInterior : LapLipschitzInteriorStmt := by
  intro d hd
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, C₂, hC₁, hC₂, hstep⟩ := step_bound hd
  refine ⟨d * (C₁ + C₂ * 4 ^ d), by positivity, ?_⟩
  intro u A M R r hu0 huA hAbox hM hr x y hx hy hxy
  have hxA : x ∈ A := by
    by_contra h
    have := hx x h
    rw [sub_self, toE_zero', norm_zero] at this
    linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hxA)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C₁ * M * ((R : ℝ) + 1) +
      C₂ * M * ((2 * R + 1 : ℕ) : ℝ) ^ d * (r / 2) ^ (1 - (d : ℝ)) := ⟨_, rfl⟩
  have hstep' : ∀ p (i : Fin d), (∀ z, z ∉ A → r / 2 ≤ ‖toE (z - p)‖) →
      |(u (p + unit i) : ℝ) - u p| ≤ K := fun p i hp => by
    rw [hK]; exact hstep u A M R (r / 2) hu0 huA hAbox hM (by positivity) p hp i
  have hgood : ∀ p : Site d, (∀ i, min (x i) (y i) ≤ p i ∧ p i ≤ max (x i) (y i)) →
      ∀ z, z ∉ A → r / 2 ≤ ‖toE (z - p)‖ := by
    intro p hp z hz
    have h1 := hx z hz
    have h2 := box_norm_le hp
    have h3 : ‖toE (y - x)‖ = ‖toE (x - y)‖ := by rw [toE_sub', toE_sub', norm_sub_rev]
    have h4 : ‖toE (z - x)‖ ≤ ‖toE (z - p)‖ + ‖toE (p - x)‖ := by
      rw [show z - x = (z - p) + (p - x) by abel, toE_add']; exact norm_add_le _ _
    linarith
  have hchain := chain_bound (f := fun q => (u q : ℝ))
    (Good := fun p => ∀ z, z ∉ A → r / 2 ≤ ‖toE (z - p)‖) hstep' _ x y rfl hgood
  have hN := natAbs_sum_le x y
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hQ := final_arith hd1 R hr
  have hX0 : 0 ≤ (((R : ℝ) + 1) / r) ^ (d - 1) := by positivity
  have hKle : K ≤ (C₁ + C₂ * 4 ^ d) * M * ((R : ℝ) + 1) * (1 + (((R : ℝ) + 1) / r) ^ (d - 1)) := by
    rw [hK]
    have h1 : C₂ * M * ((2 * R + 1 : ℕ) : ℝ) ^ d * (r / 2) ^ (1 - (d : ℝ)) ≤
        C₂ * M * (4 ^ d * ((R : ℝ) + 1) * (((R : ℝ) + 1) / r) ^ (d - 1)) := by
      rw [mul_assoc (C₂ * M)]
      exact mul_le_mul_of_nonneg_left hQ (by positivity)
    have h2 : 0 ≤ C₁ * M * ((R : ℝ) + 1) * (((R : ℝ) + 1) / r) ^ (d - 1) := by positivity
    have h3 : 0 ≤ C₂ * 4 ^ d * M * ((R : ℝ) + 1) := by positivity
    nlinarith
  have hxy0 : 0 ≤ ‖toE (x - y)‖ := norm_nonneg _
  calc |(u x : ℝ) - u y| ≤ ((∑ i, (y i - x i).natAbs : ℕ) : ℝ) * K := hchain
    _ ≤ (d * ‖toE (x - y)‖) * K := mul_le_mul_of_nonneg_right hN hK0
    _ ≤ (d * ‖toE (x - y)‖) *
          ((C₁ + C₂ * 4 ^ d) * M * ((R : ℝ) + 1) * (1 + (((R : ℝ) + 1) / r) ^ (d - 1))) :=
        mul_le_mul_of_nonneg_left hKle (by positivity)
    _ = _ := by ring

end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessGreen

/-! # Theorem 9.2: gradient bound for `v_n - n g`

For a finitely supported integer function `u` (vanishing where some coordinate has modulus at
least `R`) whose Laplacian is bounded away from one point charge, `|Δu + a δ_0| ≤ M`, the difference
`u - a g` (`g = ssGreen d`, `Δ g = -δ_0`) has gradient `O(M (R + 1))` on the box of radius `R + 1`
(`ssGradient_core`). This is the argument of `lapGradientBound_core`
(`Proofs/Sec7/CompactnessGradient.lean`) with the charge at the origin split off: in the Green
representation `u(x) = ∑ P^m(y - x) u(y) - (2d)⁻¹ ∑ g_m(y - x) Δu(y)` the term `y = 0` contributes
`(2d)⁻¹ a g_m(x)` (`g_m` is symmetric), whose gradient tends to `a ∇ g(x)` as `m → ∞`
(`tendsto_ssGreen_sub`). Applied to the single-source odometer `u = v_n`, `a = n`, it replaces the
maximum principle and the interior regularity of the decomposition (`SSInteriorLipschitzStmt`): the
gradient of `w_n = v_n - n g` is `O(n^{1/d})` on every ball of radius `O(n^{1/d})`.
-/

noncomputable section

open Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

open LapGradient in
/-- **Gradient bound for `u - a g`.** -/
theorem ssGradient_core (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, 0 < C ∧
    ∀ (u : Site d → ℤ) (M a : ℝ) (R : ℕ),
    (∀ x : Site d, (∃ i, (R : ℤ) ≤ |x i|) → u x = 0) →
    (∀ y, |(lap u y : ℝ) + a * (if y = 0 then 1 else 0)| ≤ M) →
    ∀ x ∈ boxFinset (0 : Site d) (R + 1), ∀ i : Fin d,
      |((u (x + unit i) : ℝ) - u x) - a * (ssGreen d (x + unit i) - ssGreen d x)|
        ≤ C * M * ((R : ℝ) + 1) := by
  have hd0 : 0 < d := by omega
  obtain ⟨Cg, hCg, hgrad⟩ := exists_srwGreen_gradient d hd
  obtain ⟨Ch, hCh, hheat⟩ := GreenTwoSided.srwHeat_le_mul_rpow_neg_half (d := d) (by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  refine ⟨(2 * d : ℝ)⁻¹ * Cg * (1 + 4 * d * 2 ^ (d - 1)), by positivity, ?_⟩
  intro u M a R hu hM x hx i
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set S : Finset (Site d) := boxFinset (0 : Site d) R with hS
  set U : Site d → ℝ := fun y => (u y : ℝ) with hUdef
  set F : Site d → ℝ := fun y => (lap u y : ℝ) with hFdef
  set f : Site d → ℝ := fun y => (lap u y : ℝ) + a * (if y = 0 then 1 else 0) with hfdef
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
  have h0S : (0 : Site d) ∈ S := by
    rw [hS, mem_boxFinset_iff]
    intro j
    simp
  have hfM : ∀ y, |f y| ≤ M := hM
  have hFf : ∀ y, F y = f y - a * (if y = 0 then 1 else 0) := fun y => by
    simp only [hFdef, hfdef]; ring
  have hsplit : ∀ m : ℕ,
      ∑ y ∈ S, (srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) * F y
        = ∑ y ∈ S, (srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) * f y
          - a * (srwGreen d m (x + unit i) - srwGreen d m x) := by
    intro m
    have e1 : ∑ y ∈ S, (srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) * F y
        = ∑ y ∈ S, ((srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) * f y
          - (srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) *
            (a * (if y = 0 then 1 else 0))) :=
      Finset.sum_congr rfl fun y _ => by rw [hFf y]; ring
    have e2 : ∑ y ∈ S, (srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) *
          (a * (if y = 0 then 1 else 0))
        = a * (srwGreen d m (x + unit i) - srwGreen d m x) := by
      rw [Finset.sum_eq_single_of_mem 0 h0S (fun y _ hy => by simp [hy]), if_pos rfl,
        zero_sub, zero_sub, SSGreen.srwGreen_neg, SSGreen.srwGreen_neg]
      ring
    rw [e1, Finset.sum_sub_distrib, e2]
  have hbound : ∀ m : ℕ, 1 ≤ m →
      |U (x + unit i) - U x - a * ((2 * d : ℝ)⁻¹ *
          (srwGreen d m (x + unit i) - srwGreen d m x))|
        ≤ Ch * (m : ℝ) ^ (-(d : ℝ) / 2) * ∑ y ∈ S, |U y|
          + (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))) := by
    intro m hm
    have e1 := greenRep hd0 S U F hFeq hUS hFS (x + unit i) m
    have e2 := greenRep hd0 S U F hFeq hUS hFS x m
    have h3 := hsplit m
    have hdiff : U (x + unit i) - U x - a * ((2 * d : ℝ)⁻¹ *
          (srwGreen d m (x + unit i) - srwGreen d m x))
        = (∑ y ∈ S, (srwHeat d m (y - (x + unit i)) - srwHeat d m (y - x)) * U y)
          - (2 * d : ℝ)⁻¹ * ∑ y ∈ S,
            (srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) * f y := by
      simp only [sub_mul, Finset.sum_sub_distrib] at h3 ⊢
      linear_combination e1 - e2 - (2 * d : ℝ)⁻¹ * h3
    have hA := heat_diff_sum_le hheat S U x (unit i) m hm
    have hB := green_diff_sum_le hCg hgrad (by omega : 1 ≤ d) R x hx i f M hM0 hfM m
    rw [hdiff]
    refine (abs_sub _ _).trans ?_
    refine add_le_add hA ?_
    rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity))]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have hlimL : Tendsto (fun m : ℕ => |U (x + unit i) - U x - a * ((2 * d : ℝ)⁻¹ *
        (srwGreen d m (x + unit i) - srwGreen d m x))|) atTop
      (𝓝 |U (x + unit i) - U x - a * (ssGreen d (x + unit i) - ssGreen d x)|) :=
    (tendsto_const_nhds.sub ((tendsto_ssGreen_sub hd (x + unit i) x).const_mul a)).abs
  have hlimR : Tendsto (fun m : ℕ => Ch * (m : ℝ) ^ (-(d : ℝ) / 2) * ∑ y ∈ S, |U y|
        + (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))))
      atTop (𝓝 (Ch * 0 * ∑ y ∈ S, |U y|
        + (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))))) := by
    have hpow : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(d : ℝ) / 2)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := (d : ℝ) / 2) (by positivity)).comp
        tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, neg_div] using h
    exact ((hpow.const_mul Ch).mul_const _).add_const _
  have hfinal := le_of_tendsto_of_tendsto hlimL hlimR
    (eventually_atTop.2 ⟨1, fun m hm => hbound m hm⟩)
  have hcons : |U (x + unit i) - U x - a * (ssGreen d (x + unit i) - ssGreen d x)|
      ≤ (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))) := by
    simpa using hfinal
  refine hcons.trans ?_
  have hT : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
  have hRn : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hkey : (2 * d : ℝ)⁻¹ * Cg * (1 + 4 * d * 2 ^ (d - 1)) * M * ((R : ℝ) + 1)
      - (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1))))
      = (2 * d : ℝ)⁻¹ * Cg * M * R := by
    push_cast
    ring
  have hpos : 0 ≤ (2 * d : ℝ)⁻¹ * Cg * M * R := by positivity
  linarith

end RandomSandpile

import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeGreen

/-!
# Proof of the weighted occupation bound `GreenBallWeightedSumStmt`

The weighted occupation bound of Lemma 7.3 (`paper/random_piles-corrected.tex`),
`∑_{y ∈ B_n, y ≠ x} g_n(x, y) / |y - x| ≤ C (n + 1)`, by comparison with a multiple of
`2n + 2 - |y - x|` (`greenPotential_le_of_lapR_le`), via the discrete Laplacian of the Euclidean
norm:

* `lapR_norm_ge`: for `z ≠ 0`, `Δ_{ℤ^d} |z| ≥ 4 (d - 1) / (4 |z| + 2)`. Per coordinate `i`, with
  `t = z_i`, `r = |z|`, `a = |z + e_i|`, `b = |z - e_i|`, one has `a² = r² + 2t + 1`,
  `b² = r² - 2t + 1`, hence `(ab)² = (r² + 1)² - 4t² ≥ (r² + 1 - 2t²/r²)²`
  (`coord_ineq`); thus `(a + b)² - 4r² ≥ 4 (1 - t²/r²)`, and `a + b ≤ 2r + 2` gives
  `a + b - 2r ≥ 4 (1 - t²/r²) / (4r + 2)`. Summing over `i` with `∑ t_i² = r²` gives the claim.
* `lapR_norm_shift_ge`: the same at the centre `x`, in the form `Δ |· - x| (y) ≥ 2 / (3 |y - x|)`
  for `y ≠ x` (using `d ≥ 2` and `|y - x| ≥ 1`), and `Δ |· - x| (x) ≥ 0`.
* `greenBallWeightedSum`: `w(y) = (3/2) (2n + 2 - |y - x|)` has `Δ w ≤ -f` on `B_n`, where
  `f(y) = 1_{y ≠ x} / |y - x|`, and `w ≥ 0` on `∂B_n`; so the Green potential of `f` at `x` is at
  most `w(x) = 3 (n + 1)`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

open OdometerLowerBound

variable {d : ℕ}

namespace DivisibleHomogenize

/-- The real inequality behind the per-coordinate estimate (`t = z_i`, `u = t²/r²`,
`a = |z + e_i|`, `b = |z - e_i|`, `r = |z|`):
`4 (1 - u) ≤ (a + b - 2r) (4r + 2)`. -/
theorem coord_ineq {r u t a b : ℝ} (hr : 1 ≤ r) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (ht : t ^ 2 = u * r ^ 2) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha2 : a ^ 2 = r ^ 2 + 2 * t + 1)
    (hb2 : b ^ 2 = r ^ 2 - 2 * t + 1) (hab : a + b ≤ 2 * r + 2) :
    4 * (1 - u) ≤ (a + b - 2 * r) * (4 * r + 2) := by
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hprod : (a * b) ^ 2 = (r ^ 2 + 1) ^ 2 - 4 * (u * r ^ 2) := by
    rw [mul_pow, ha2, hb2, ← ht]; ring
  have hs0 : 0 ≤ r ^ 2 + 1 - 2 * u := by linarith
  have hsq : (r ^ 2 + 1 - 2 * u) ^ 2 ≤ (a * b) ^ 2 := by
    rw [hprod]; nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu1)]
  have hge : r ^ 2 + 1 - 2 * u ≤ a * b :=
    (pow_le_pow_iff_left₀ hs0 (mul_nonneg ha hb) two_ne_zero).1 hsq
  have hexp : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
  have hfac : (a + b - 2 * r) * (a + b + 2 * r) ≥ 4 * (1 - u) := by
    have : (a + b - 2 * r) * (a + b + 2 * r) = (a + b) ^ 2 - 4 * r ^ 2 := by ring
    rw [this, hexp, ha2, hb2]
    linarith
  have hpos : 0 < a + b + 2 * r := by linarith
  have hp : 0 ≤ a + b - 2 * r := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hpos
    linarith
  calc 4 * (1 - u) ≤ (a + b - 2 * r) * (a + b + 2 * r) := hfac
    _ ≤ (a + b - 2 * r) * (4 * r + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hp

/-- `|x_i| ≤ |x|`. -/
theorem coord_abs_le_norm (x : Site d) (i : Fin d) : |(x i : ℝ)| ≤ ‖toE x‖ := by
  have h := PiLp.norm_apply_le (toE x) i
  simpa [Real.norm_eq_abs] using h

/-- `|x|² = ∑_j x_j²`. -/
theorem norm_toE_sq (v : Site d) : ‖toE v‖ ^ 2 = ∑ j, ((v j : ℤ) : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  simp [toE]

/-- `|z + e_i|² = |z|² + 2 z_i + 1`. -/
theorem norm_toE_add_unit_sq (z : Site d) (i : Fin d) :
    ‖toE (z + unit i)‖ ^ 2 = ‖toE z‖ ^ 2 + 2 * (z i : ℝ) + 1 := by
  have hj : ∀ j, ((((z + unit i) j : ℤ)) : ℝ) ^ 2 =
      ((z j : ℤ) : ℝ) ^ 2 + (if j = i then 2 * (z i : ℝ) + 1 else 0) := by
    intro j
    by_cases h : j = i
    · subst h; simp [unit]; ring
    · simp [unit, h]
  rw [norm_toE_sq, norm_toE_sq]
  simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- `|z - e_i|² = |z|² - 2 z_i + 1`. -/
theorem norm_toE_sub_unit_sq (z : Site d) (i : Fin d) :
    ‖toE (z - unit i)‖ ^ 2 = ‖toE z‖ ^ 2 - 2 * (z i : ℝ) + 1 := by
  have hj : ∀ j, ((((z - unit i) j : ℤ)) : ℝ) ^ 2 =
      ((z j : ℤ) : ℝ) ^ 2 + (if j = i then -2 * (z i : ℝ) + 1 else 0) := by
    intro j
    by_cases h : j = i
    · subst h; simp [unit]; ring
    · simp [unit, h]
  rw [norm_toE_sq, norm_toE_sq]
  simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
theorem one_le_norm_toE {z : Site d} (hz : z ≠ 0) : 1 ≤ ‖toE z‖ := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  have h1 : (1 : ℤ) ≤ |z i| := Int.one_le_abs hi
  have h2 : (1 : ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast h1
  exact h2.trans (coord_abs_le_norm z i)

/-- **Laplacian of the Euclidean norm**: for `z ≠ 0`, `Δ_{ℤ^d} |z| ≥ 4 (d - 1) / (4 |z| + 2)`
(the lattice analogue of `Δ |z| = (d - 1) / |z|`). -/
theorem lapR_norm_ge {z : Site d} (hz : z ≠ 0) :
    4 * ((d : ℝ) - 1) / (4 * ‖toE z‖ + 2) ≤ lapR (fun y => ‖toE y‖) z := by
  set r : ℝ := ‖toE z‖ with hr_def
  have hr : 1 ≤ r := one_le_norm_toE hz
  have hr0 : 0 < r ^ 2 := by positivity
  set u : Fin d → ℝ := fun i => ((z i : ℤ) : ℝ) ^ 2 / r ^ 2 with hu_def
  have hu_sum : ∑ i, u i = 1 := by
    rw [hu_def]
    simp only
    rw [← Finset.sum_div, ← norm_toE_sq]
    exact div_self hr0.ne'
  have hcoord : ∀ i, 4 * (1 - u i) ≤
      (‖toE (z + unit i)‖ + ‖toE (z - unit i)‖ - 2 * r) * (4 * r + 2) := by
    intro i
    have hti : ((z i : ℤ) : ℝ) ^ 2 ≤ r ^ 2 := by
      have := coord_abs_le_norm z i
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    refine coord_ineq (t := ((z i : ℤ) : ℝ)) hr (div_nonneg (sq_nonneg _) hr0.le)
      ((div_le_one hr0).2 hti) ?_ (norm_nonneg _) (norm_nonneg _) (norm_toE_add_unit_sq z i)
      (norm_toE_sub_unit_sq z i) ?_
    · simp only [hu_def]
      field_simp
    · have h1 : ‖toE (z + unit i)‖ ≤ r + 1 := by
        rw [toE_add]
        calc ‖toE z + toE (unit i)‖ ≤ ‖toE z‖ + ‖toE (unit i)‖ := norm_add_le _ _
          _ = r + 1 := by rw [norm_toE_unit]
      have h2 : ‖toE (z - unit i)‖ ≤ r + 1 := by
        rw [toE_sub]
        calc ‖toE z - toE (unit i)‖ ≤ ‖toE z‖ + ‖toE (unit i)‖ := norm_sub_le _ _
          _ = r + 1 := by rw [norm_toE_unit]
      linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcoord i
  have hL : ∑ i, 4 * (1 - u i) = 4 * ((d : ℝ) - 1) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hu_sum]
    simp
  have hlap : lapR (fun y => ‖toE y‖) z =
      ∑ i, (‖toE (z + unit i)‖ + ‖toE (z - unit i)‖ - 2 * r) := by
    simp only [lapR, nbrSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hL, ← Finset.sum_mul, ← hlap] at hsum
  rw [div_le_iff₀ (by linarith)]
  exact hsum

/-- The Laplacian of the norm centred at `x` is the Laplacian of the norm at `y - x`. -/
theorem lapR_norm_sub (x y : Site d) :
    lapR (fun w => ‖toE (w - x)‖) y = lapR (fun w => ‖toE w‖) (y - x) := by
  simp only [lapR, nbrSum, add_sub_right_comm, sub_right_comm]

/-- The Laplacian of the norm centred at `x`: `Δ |· - x| (y) ≥ 2 / (3 |y - x|)` for `y ≠ x`
(`d ≥ 2`, `|y - x| ≥ 1`), and `Δ |· - x| (x) ≥ 0`. -/
theorem lapR_norm_sub_ge (hd : 2 ≤ d) (x y : Site d) :
    (if y = x then 0 else 2 / (3 * ‖toE (y - x)‖)) ≤ lapR (fun w => ‖toE (w - x)‖) y := by
  by_cases hyx : y = x
  · subst hyx
    simp only [if_true, lapR, nbrSum, sub_self]
    have h0 : ‖toE (0 : Site d)‖ = 0 := by rw [toE_zero, norm_zero]
    rw [h0]
    have : 0 ≤ ∑ i : Fin d, (‖toE (y + unit i - y)‖ + ‖toE (y - unit i - y)‖) :=
      Finset.sum_nonneg fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith
  · rw [if_neg hyx, lapR_norm_sub]
    have hz : y - x ≠ 0 := sub_ne_zero.2 hyx
    have hr : 1 ≤ ‖toE (y - x)‖ := one_le_norm_toE hz
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    refine le_trans ?_ (lapR_norm_ge hz)
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith

end DivisibleHomogenize

open DivisibleHomogenize

/-- **Weighted occupation bound**. -/
theorem greenBallWeightedSum : GreenBallWeightedSumStmt := by
  intro d hd
  refine ⟨3, by norm_num, fun n x hx => ?_⟩
  have hd1 : 1 ≤ d := by omega
  set g : Site d → ℝ := fun y => ‖toE (y - x)‖ with hg_def
  set w : Site d → ℝ := fun y => 3 * ((n : ℝ) + 1) + (-(3 / 2)) * g y with hw_def
  have hwlap : ∀ z, lapR w z = -(3 / 2) * lapR g z := by
    intro z
    have h1 : lapR w z = lapR (fun y => (-(3 / 2 : ℝ)) * g y) z :=
      lapR_const_add' (3 * ((n : ℝ) + 1)) (fun y => (-(3 / 2 : ℝ)) * g y) z
    rw [h1]
    simp only [lapR, nbrSum, ← mul_add, ← Finset.mul_sum]
    ring
  have key := greenPotential_le_of_lapR_le hd1 (ballZ0_finite (d := d) (n : ℝ))
    (fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹) w (fun z _ => ?_) (fun y hy => ?_) x hx
  · have hwx : w x = 3 * ((n : ℝ) + 1) := by
      simp only [hw_def, hg_def, sub_self, toE_zero, norm_zero]
      ring
    rw [hwx] at key
    exact key
  · rw [hwlap]
    have h := lapR_norm_sub_ge hd x z
    by_cases hzx : z = x
    · subst hzx
      simp only [if_true] at h ⊢
      simp only [hg_def]
      linarith
    · simp only [if_neg hzx] at h ⊢
      have hr : 1 ≤ ‖toE (z - x)‖ := one_le_norm_toE (sub_ne_zero.2 hzx)
      have : (3 / 2 : ℝ) * (2 / (3 * ‖toE (z - x)‖)) = ‖toE (z - x)‖⁻¹ := by
        field_simp
      simp only [hg_def]
      nlinarith
  · have h1 := norm_lt_of_mem_bdry_ballZ0 hy
    have h2 := mem_ballZ0.1 hx
    have h3 : ‖toE (y - x)‖ ≤ ‖toE y‖ + ‖toE x‖ := by
      rw [toE_sub]; exact norm_sub_le _ _
    simp only [hw_def, hg_def]
    linarith

end RandomSandpile

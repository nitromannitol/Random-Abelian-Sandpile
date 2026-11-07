import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeSymm
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeLatticeSum
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeRadial

/-!
# The summed (difference) estimate from the Harnack gradient bound (Lemma 7.3)

Proof of `GreenBallGradientSumStmt` (1166-1185) from
`GreenBallHarnackGradientStmt` (`|∇_y g_n(x, y)| |x - y| ≤ C_δ g_n(x, y)` for `|x - y| ≥ R_δ`,
the Lawler-Limic estimate combined with the Harnack inequality) and `GreenBallWeightedSumStmt`
(`∑_{y ≠ x} g_n(x, y) / |y - x| ≤ C (n + 1)`).

* Far from `x` (`|x - y| ≥ R_δ`): `∑_i |∇_i g_n(x, y)| ≤ d C_δ g_n(x, y) / |x - y|`, summed by the
  weighted occupation bound.
* Near `x` (`|x - y| < R_δ`, at most `(2⌈R_δ⌉ + 1)^d` sites): each `g_n(x, w)` with `w` near `x`
  is `O(n)`: for `w ≠ x` it is one term of the weighted sum times `|w - x|`, and
  `2d g_n(x, x) = 1 + ∑_{w ∼ x} g_n(x, w)` (`lapR_greenKilled_right`).
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

variable {d : ℕ}

namespace DivisibleHomogenize

open OdometerLowerBound

theorem norm_toE_sub_comm (x y : Site d) : ‖toE (x - y)‖ = ‖toE (y - x)‖ := by
  rw [toE_sub, toE_sub, norm_sub_rev]

theorem arith_diag {g S D C m : ℝ} (hD : 1 ≤ D) (hm : 1 ≤ m)
    (hS : S ≤ 2 * D * (C * m)) (h : S - 2 * D * g = -1) : g ≤ (0 + 1) * ((C + 1) * m) := by
  nlinarith

theorem arith_off {g r C m : ℝ} (hr : 0 ≤ r) (hm : 0 ≤ m) (hC : 0 ≤ C)
    (h : g ≤ C * m * r) : g ≤ (r + 1) * ((C + 1) * m) := by
  nlinarith [mul_nonneg hC hm, mul_nonneg hr hm]

/-- **`g_n(x, ·)` near `x` from the weighted occupation bound**:
`g_n(x, w) ≤ (|w - x| + 1)(C + 1)(n + 1)`. -/
theorem greenKilled_le_of_weighted (hd : 1 ≤ d) {n : ℕ} {x : Site d}
    (hx : x ∈ ballZ0 (d := d) (n : ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hW : greenPotential (ballZ0 (n : ℝ)) (fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹) x ≤
      C * ((n : ℝ) + 1)) (w : Site d) :
    greenKilled (ballZ0 (n : ℝ)) x w ≤ (‖toE (w - x)‖ + 1) * ((C + 1) * ((n : ℝ) + 1)) := by
  have hfin := ballZ0_finite (d := d) (n : ℝ)
  have hCn : 0 ≤ C * ((n : ℝ) + 1) := mul_nonneg hC (by positivity)
  have hsingle : ∀ v, v ≠ x →
      greenKilled (ballZ0 (n : ℝ)) x v * ‖toE (v - x)‖⁻¹ ≤ C * ((n : ℝ) + 1) := by
    intro v hv
    by_cases hvB : v ∈ ballZ0 (d := d) (n : ℝ)
    · refine le_trans ?_ hW
      rw [greenPotential, finsum_mem_eq_finite_toFinset_sum _ hfin]
      have := Finset.single_le_sum
        (f := fun y => greenKilled (ballZ0 (n : ℝ)) x y *
          (if y = x then 0 else ‖toE (y - x)‖⁻¹))
        (fun y _ => mul_nonneg (greenKilled_nonneg _ _ _) (by split_ifs <;> positivity))
        (hfin.mem_toFinset.2 hvB)
      simpa [hv] using this
    · rw [greenKilled_eq_zero_of_not_mem_right hd hfin x hvB, zero_mul]
      exact hCn
  by_cases hwx : w = x
  · subst hwx
    have hlap := lapR_greenKilled_right hd hfin w hx
    rw [if_pos rfl, lapR, nbrSum] at hlap
    have hne : ∀ i : Fin d, w + unit i ≠ w ∧ w - unit i ≠ w := fun i => by
      constructor <;> intro h <;> have h2 := congrFun h i <;> simp [unit] at h2
    have hnb : ∀ i : Fin d, greenKilled (ballZ0 (n : ℝ)) w (w + unit i) +
        greenKilled (ballZ0 (n : ℝ)) w (w - unit i) ≤ 2 * (C * ((n : ℝ) + 1)) := by
      intro i
      have h1 := hsingle (w + unit i) (hne i).1
      have h2 := hsingle (w - unit i) (hne i).2
      rw [show w + unit i - w = unit i by abel, norm_toE_unit, inv_one, mul_one] at h1
      rw [show w - unit i - w = 0 - unit i by abel, toE_sub, toE_zero, zero_sub, norm_neg,
        norm_toE_unit, inv_one, mul_one] at h2
      linarith
    have hS : ∑ i : Fin d, (greenKilled (ballZ0 (n : ℝ)) w (w + unit i) +
        greenKilled (ballZ0 (n : ℝ)) w (w - unit i)) ≤ 2 * (d : ℝ) * (C * ((n : ℝ) + 1)) := by
      calc _ ≤ ∑ _i : Fin d, 2 * (C * ((n : ℝ) + 1)) := Finset.sum_le_sum fun i _ => hnb i
        _ = _ := by simp; ring
    rw [sub_self, toE_zero, norm_zero]
    exact arith_diag (by exact_mod_cast hd) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      hS (by linarith)
  · have hr := one_le_norm_toE (sub_ne_zero.2 hwx)
    have h := hsingle w hwx
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)] at h
    exact arith_off (by linarith) (by positivity) hC h

/-- **Near `x`**: `∑_i |∇_i g_n(x, y)| ≤ 2d (ρ + 2)(C + 1)(n + 1)` when `|y - x| ≤ ρ`. -/
theorem sum_abs_grad_le_near (hd : 1 ≤ d) {n : ℕ} {x : Site d}
    (hx : x ∈ ballZ0 (d := d) (n : ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hW : greenPotential (ballZ0 (n : ℝ)) (fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹) x ≤
      C * ((n : ℝ) + 1)) {ρ : ℝ} (y : Site d) (hy : ‖toE (y - x)‖ ≤ ρ) :
    ∑ i : Fin d, |greenKilled (ballZ0 (n : ℝ)) x (y + unit i) -
        greenKilled (ballZ0 (n : ℝ)) x y| ≤ d * (2 * ((ρ + 2) * ((C + 1) * ((n : ℝ) + 1)))) := by
  have hP : 0 ≤ (C + 1) * ((n : ℝ) + 1) := by
    have : 0 ≤ C + 1 := by linarith
    positivity
  calc _ ≤ ∑ _i : Fin d, 2 * ((ρ + 2) * ((C + 1) * ((n : ℝ) + 1))) :=
        Finset.sum_le_sum fun i _ => by
          have h1 := greenKilled_le_of_weighted hd hx hC hW (y + unit i)
          have h2 := greenKilled_le_of_weighted hd hx hC hW y
          have h3 : ‖toE (y + unit i - x)‖ ≤ ρ + 1 := by
            rw [show y + unit i - x = (y - x) + unit i by abel, toE_add]
            exact (norm_add_le _ _).trans (by rw [norm_toE_unit]; linarith)
          have h1' : greenKilled (ballZ0 (n : ℝ)) x (y + unit i) ≤
              (ρ + 2) * ((C + 1) * ((n : ℝ) + 1)) :=
            h1.trans (mul_le_mul_of_nonneg_right (by linarith) hP)
          have h2' : greenKilled (ballZ0 (n : ℝ)) x y ≤ (ρ + 2) * ((C + 1) * ((n : ℝ) + 1)) :=
            h2.trans (mul_le_mul_of_nonneg_right (by linarith) hP)
          have g1 := greenKilled_nonneg (ballZ0 (d := d) (n : ℝ)) x (y + unit i)
          have g2 := greenKilled_nonneg (ballZ0 (d := d) (n : ℝ)) x y
          rw [abs_le]
          constructor <;> linarith
    _ = _ := by simp

end DivisibleHomogenize

open DivisibleHomogenize OdometerLowerBound

/-- **The summed (difference) estimate** from the Harnack gradient bound and the weighted
occupation bound (1166-1185). -/
theorem greenBallGradientSum_of_harnack (hH : GreenBallHarnackGradientStmt)
    (hW : GreenBallWeightedSumStmt) : GreenBallGradientSumStmt := by
  intro d hd δ hδ0 hδ1
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, R₀, hC₁, hH'⟩ := hH d hd δ hδ0 hδ1
  obtain ⟨C₂, hC₂, hW'⟩ := hW d hd
  set R₁ : ℝ := max R₀ 1 with hR₁
  set m : ℕ := ⌈R₁⌉₊ with hm
  set A : ℝ := (((2 * m + 1) ^ d : ℕ) : ℝ) * ((d : ℝ) * (2 * ((R₁ + 2) * (C₂ + 1))))
  set K : ℝ := (d : ℝ) * C₁ * C₂ + A
  have hR₁1 : 1 ≤ R₁ := le_max_right _ _
  have hA : 0 ≤ A := by
    have : 0 ≤ C₂ + 1 := by linarith
    have : 0 ≤ R₁ + 2 := by linarith
    positivity
  have hK : 0 ≤ K := by
    have : 0 ≤ (d : ℝ) * C₁ * C₂ := by positivity
    linarith
  refine ⟨2 * K + 1, by linarith, fun n x hx => ?_⟩
  have hxδ : ‖toE x‖ < (1 - δ) * n := mem_ballZ0.1 hx
  have hnpos : (0 : ℝ) < n := by
    have := norm_nonneg (toE x)
    by_contra h
    have : (1 - δ) * (n : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 h)
    linarith
  have hn1 : (1 : ℝ) ≤ n := by
    have : 0 < n := by exact_mod_cast hnpos
    exact_mod_cast this
  have hxn : x ∈ ballZ0 (d := d) (n : ℝ) := mem_ballZ0.2 (by nlinarith)
  have hWx := hW' n x hxn
  rw [finsum_mem_eq_finite_toFinset_sum _ (ballZ0_finite _)]
  set Sδ := (ballZ0_finite (d := d) ((1 - δ) * (n : ℝ))).toFinset with hSδ
  set g : Site d → ℝ := greenKilled (ballZ0 (n : ℝ)) x with hg
  rw [← Finset.sum_filter_add_sum_filter_not Sδ (fun y => ‖toE (x - y)‖ < R₁)]
  -- near `x`
  have hnear : ∑ y ∈ Sδ.filter (fun y => ‖toE (x - y)‖ < R₁),
      ∑ i : Fin d, |g (y + unit i) - g y| ≤ A * ((n : ℝ) + 1) := by
    have hcard : (Sδ.filter (fun y => ‖toE (x - y)‖ < R₁)).card ≤ (2 * m + 1) ^ d := by
      rw [← card_box d m]
      refine Finset.card_le_card_of_injOn (fun y => y - x) (fun y hy => ?_)
        (fun y _ z _ h => by simpa using h)
      have hy' := (Finset.mem_filter.1 hy).2
      rw [Finset.mem_coe, mem_box]
      intro i
      have h1 := abs_coord_le_norm (y - x) i
      rw [← norm_toE_sub_comm] at h1
      have h2 : R₁ ≤ (m : ℝ) := Nat.le_ceil _
      have h3 : |((y - x) i : ℝ)| < m := by linarith
      exact_mod_cast h3.le
    calc _ ≤ ∑ _y ∈ Sδ.filter (fun y => ‖toE (x - y)‖ < R₁),
          (d : ℝ) * (2 * ((R₁ + 2) * ((C₂ + 1) * ((n : ℝ) + 1)))) :=
          Finset.sum_le_sum fun y hy => sum_abs_grad_le_near hd1 hxn hC₂.le hWx y (by
            rw [← norm_toE_sub_comm]; exact (Finset.mem_filter.1 hy).2.le)
      _ = ((Sδ.filter (fun y => ‖toE (x - y)‖ < R₁)).card : ℝ) *
            ((d : ℝ) * (2 * ((R₁ + 2) * ((C₂ + 1) * ((n : ℝ) + 1))))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((2 * m + 1) ^ d : ℕ) : ℝ) *
            ((d : ℝ) * (2 * ((R₁ + 2) * ((C₂ + 1) * ((n : ℝ) + 1))))) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          have : 0 ≤ C₂ + 1 := by linarith
          have : 0 ≤ R₁ + 2 := by linarith
          positivity
      _ = A * ((n : ℝ) + 1) := by ring
  -- far from `x`
  have hfar : ∑ y ∈ Sδ.filter (fun y => ¬ ‖toE (x - y)‖ < R₁),
      ∑ i : Fin d, |g (y + unit i) - g y| ≤ (d : ℝ) * C₁ * (C₂ * ((n : ℝ) + 1)) := by
    have hterm : ∀ y ∈ Sδ.filter (fun y => ¬ ‖toE (x - y)‖ < R₁),
        ∑ i : Fin d, |g (y + unit i) - g y| ≤
          (d : ℝ) * C₁ * (g y * (if y = x then 0 else ‖toE (y - x)‖⁻¹)) := by
      intro y hy
      obtain ⟨hyS, hyR⟩ := Finset.mem_filter.1 hy
      have hyR' : R₁ ≤ ‖toE (x - y)‖ := not_lt.1 hyR
      have hpos : 0 < ‖toE (x - y)‖ := by linarith
      have hyx : y ≠ x := by
        rintro rfl
        rw [sub_self, toE_zero, norm_zero] at hpos
        exact lt_irrefl _ hpos
      have hyδ : y ∈ ballZ0 (d := d) ((1 - δ) * n) := (Set.Finite.mem_toFinset _).1 hyS
      rw [if_neg hyx, ← norm_toE_sub_comm]
      calc _ ≤ ∑ _i : Fin d, C₁ * (g y * ‖toE (x - y)‖⁻¹) := Finset.sum_le_sum fun i _ => by
            have h := hH' n x y hx hyδ ((le_max_left _ _).trans hyR') i
            rw [← le_div_iff₀ hpos] at h
            rw [mul_div_assoc, div_eq_mul_inv] at h
            exact h
        _ = _ := by simp; ring
    calc _ ≤ ∑ y ∈ Sδ.filter (fun y => ¬ ‖toE (x - y)‖ < R₁),
          (d : ℝ) * C₁ * (g y * (if y = x then 0 else ‖toE (y - x)‖⁻¹)) := Finset.sum_le_sum hterm
      _ = (d : ℝ) * C₁ * ∑ y ∈ Sδ.filter (fun y => ¬ ‖toE (x - y)‖ < R₁),
            g y * (if y = x then 0 else ‖toE (y - x)‖⁻¹) := by rw [Finset.mul_sum]
      _ ≤ (d : ℝ) * C₁ * ∑ y ∈ (ballZ0_finite (d := d) (n : ℝ)).toFinset,
            g y * (if y = x then 0 else ‖toE (y - x)‖⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro y hy
            have hyδ := (Set.Finite.mem_toFinset _).1 (Finset.mem_filter.1 hy).1
            refine (Set.Finite.mem_toFinset _).2 (mem_ballZ0.2 ?_)
            have := mem_ballZ0.1 hyδ
            nlinarith
          · intro y _ _
            exact mul_nonneg (greenKilled_nonneg _ _ _) (by split_ifs <;> positivity)
      _ ≤ (d : ℝ) * C₁ * (C₂ * ((n : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [greenPotential, finsum_mem_eq_finite_toFinset_sum _ (ballZ0_finite _)] at hWx
          exact hWx
  have htot : K * ((n : ℝ) + 1) ≤ (2 * K + 1) * n := by nlinarith
  calc _ ≤ A * ((n : ℝ) + 1) + (d : ℝ) * C₁ * (C₂ * ((n : ℝ) + 1)) := add_le_add hnear hfar
    _ = K * ((n : ℝ) + 1) := by ring
    _ ≤ (2 * K + 1) * n := htot

end RandomSandpile

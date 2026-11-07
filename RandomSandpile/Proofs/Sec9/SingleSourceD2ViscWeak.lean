import RandomSandpile.Proofs.Sec9.SingleSourceD2Approx
import RandomSandpile.Proofs.Sec9.SingleSourceD2WeakLap
import RandomSandpile.Proofs.Sec9.OpenBoundaryComparison

/-!
# Theorem 9.2 in dimension two: viscosity Laplacian bounds in distributions

Tools for `distLaplace_ge` (SIMPLE-PROOF §7.3: a continuous function whose upper tests have
`Δφ ≥ -C` satisfies `Δu ≥ -C` in distributions), with Alexandrov's theorem as the only input:
* second differences `sd t f x = t² Σᵢ (f(x + eᵢ/t) + f(x - eᵢ/t) - 2f(x))`; they are nonnegative for
  convex `f` (`sd_nonneg_of_convexOn`) and converge to `tr X` at a point of Peano expansion `(p, X)`
  (`tendsto_sd_of_taylor`);
* translation invariance moves them from a test function onto `f` (`integral_sd_eq`), and
  `∫ f · t²(second difference of φ) → ∫ f Δφ` for continuous `f` (`tendsto_integral_sd_cont`);
* `sd` of `|x|²/(2δ)` is `2/δ` (`sd_sq_norm`), and subtracting it shifts a Peano expansion
  (`taylor_sub_sq_norm`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric LatticeProb LatticeProb.Sandpile
open scoped ENNReal

namespace RandomSandpile

namespace SingleSourceD2

/-- The second difference `t² Σᵢ (f(x + eᵢ/t) + f(x - eᵢ/t) - 2 f(x))` at scale `1/t`. -/
def sd (t : ℝ) (f : Rd 2 → ℝ) (x : Rd 2) : ℝ :=
  t ^ 2 * ∑ i : Fin 2, (f (x + t⁻¹ • toE (unit i)) + f (x - t⁻¹ • toE (unit i)) - 2 * f x)

/-! ### Second differences -/

/-- Second differences of a convex function are nonnegative. -/
theorem secondDiff_nonneg_of_convexOn {c : Rd 2 → ℝ} (hc : ConvexOn ℝ Set.univ c) (x v : Rd 2) :
    0 ≤ c (x + v) + c (x - v) - 2 * c x := by
  have h := hc.2 (Set.mem_univ (x + v)) (Set.mem_univ (x - v)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • (x + v) + (1 / 2 : ℝ) • (x - v) = x := by
    rw [← smul_add, show x + v + (x - v) = (2 : ℝ) • x by rw [two_smul]; abel, smul_smul]
    norm_num
  rw [e, smul_eq_mul, smul_eq_mul] at h
  linarith

theorem sd_nonneg_of_convexOn {c : Rd 2 → ℝ} (hc : ConvexOn ℝ Set.univ c) (t : ℝ) (x : Rd 2) :
    0 ≤ sd t c x :=
  mul_nonneg (sq_nonneg t) (Finset.sum_nonneg fun _ _ => secondDiff_nonneg_of_convexOn hc x _)

/-- At a point of second-order Peano expansion `(p, X)`, the second differences converge to
`tr X`. -/
theorem tendsto_sd_of_taylor {c : Rd 2 → ℝ} {x p : Rd 2} {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hT : HasSecondOrderTaylorAt c x p X) :
    Tendsto (fun t : ℝ => sd t c x) atTop (𝓝 X.trace) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ρ, hρ, hb⟩ := hT.bound (κ := ε / 8) (by positivity)
  refine ⟨2 / ρ, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have htρ : t⁻¹ < ρ := by
    rw [inv_lt_comm₀ ht0 hρ]
    have : 1 / ρ < 2 / ρ := div_lt_div_of_pos_right (by norm_num) hρ
    rw [one_div] at this
    linarith
  have ht2 : t ^ 2 * t⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ ht0.ne', one_pow]
  have hper : ∀ i : Fin 2, |t ^ 2 * (c (x + t⁻¹ • toE (unit i)) + c (x - t⁻¹ • toE (unit i)) -
      2 * c x) - X i i| ≤ ε / 4 := by
    intro i
    set v : Rd 2 := t⁻¹ • toE (unit i) with hv
    have hvn : ‖v‖ = t⁻¹ := by
      rw [hv, norm_smul, norm_toE_unit', mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0)]
    have h1 := hb (x + v) (by rw [add_sub_cancel_left, hvn]; exact htρ)
    have h2 := hb (x - v) (by rw [sub_sub_cancel_left, norm_neg, hvn]; exact htρ)
    rw [add_sub_cancel_left, hvn] at h1
    rw [sub_sub_cancel_left, norm_neg, hvn, inner_neg_right, qM_neg_right] at h2
    have hq : qM X v = t⁻¹ ^ 2 * qM X (toE (unit i)) := by rw [hv, qM_smul_right]
    have h2q := two_qM_toE_unit X i
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 h2
    rw [hq] at a1 a2
    have e1 : t ^ 2 * (c (x + v) + c (x - v) - 2 * c x) - X i i =
        t ^ 2 * ((c (x + v) - c x - inner ℝ p v - t⁻¹ ^ 2 * qM X (toE (unit i))) +
          (c (x - v) - c x - -inner ℝ p v - t⁻¹ ^ 2 * qM X (toE (unit i)))) := by
      rw [← h2q]
      have : t ^ 2 * (2 * (t⁻¹ ^ 2 * qM X (toE (unit i)))) = 2 * qM X (toE (unit i)) := by
        rw [show t ^ 2 * (2 * (t⁻¹ ^ 2 * qM X (toE (unit i)))) =
          2 * (t ^ 2 * t⁻¹ ^ 2) * qM X (toE (unit i)) by ring, ht2, mul_one]
      linear_combination this
    rw [e1, abs_le]
    have hk : t ^ 2 * (ε / 8 * t⁻¹ ^ 2) = ε / 8 := by
      rw [show t ^ 2 * (ε / 8 * t⁻¹ ^ 2) = ε / 8 * (t ^ 2 * t⁻¹ ^ 2) by ring, ht2, mul_one]
    have ht2' : 0 ≤ t ^ 2 := sq_nonneg t
    have b1 := mul_le_mul_of_nonneg_left a1.1 ht2'
    have b2 := mul_le_mul_of_nonneg_left a2.1 ht2'
    have b3 := mul_le_mul_of_nonneg_left a1.2 ht2'
    have b4 := mul_le_mul_of_nonneg_left a2.2 ht2'
    constructor <;> nlinarith
  rw [Real.dist_eq, sd, Finset.mul_sum, Matrix.trace_fin_two, Fin.sum_univ_two]
  have h0 := abs_le.1 (hper 0)
  have h1 := abs_le.1 (hper 1)
  rw [abs_lt]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- `sd` of `|x|²/(2δ)` is `2/δ`. -/
theorem sd_sq_norm {t δ : ℝ} (ht : t ≠ 0) (x : Rd 2) :
    sd t (fun y => ‖y‖ ^ 2 / (2 * δ)) x = 2 / δ := by
  have hterm : ∀ i : Fin 2, ‖x + t⁻¹ • toE (unit i)‖ ^ 2 / (2 * δ) +
      ‖x - t⁻¹ • toE (unit i)‖ ^ 2 / (2 * δ) - 2 * (‖x‖ ^ 2 / (2 * δ)) = t⁻¹ ^ 2 / δ := by
    intro i
    have hn : ‖t⁻¹ • toE (unit i : Site 2)‖ = |t⁻¹| := by
      rw [norm_smul, norm_toE_unit', mul_one, Real.norm_eq_abs]
    have h1 := norm_add_sq_real x (t⁻¹ • toE (unit i))
    have h2 := norm_sub_sq_real x (t⁻¹ • toE (unit i))
    rw [hn, sq_abs] at h1 h2
    rw [h1, h2]
    by_cases hδ : δ = 0
    · simp [hδ]
    · field_simp
      ring
  simp only [sd, hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hδ : δ = 0
  · simp [hδ]
  · field_simp
    norm_num

/-- Subtracting `|x|²/(2δ)` shifts a Peano expansion. -/
theorem taylor_sub_sq_norm {c : Rd 2 → ℝ} {x p : Rd 2} {X : Matrix (Fin 2) (Fin 2) ℝ} (δ : ℝ)
    (hT : HasSecondOrderTaylorAt c x p X) :
    HasSecondOrderTaylorAt (fun y => c y - ‖y‖ ^ 2 / (2 * δ)) x (p - δ⁻¹ • x)
      (X + (-δ⁻¹) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  unfold HasSecondOrderTaylorAt at hT ⊢
  refine hT.congr_left fun y => ?_
  beta_reduce
  have hn : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
    have := norm_add_sq_real x (y - x)
    rwa [add_sub_cancel] at this
  rw [qM_add_smul_one, inner_sub_left, real_inner_smul_left, hn]
  by_cases hδ : δ = 0
  · simp [hδ]
  · field_simp
    ring

/-! ### Summation by parts in the continuum -/

theorem integral_mul_comp_sub (f φ : Rd 2 → ℝ) (v : Rd 2) :
    ∫ x, f x * φ (x - v) = ∫ x, f (x + v) * φ x := by
  have h := integral_add_right_eq_self (μ := (volume : Measure (Rd 2)))
    (fun x => f x * φ (x - v)) v
  simp only [add_sub_cancel_right] at h
  exact h.symm

theorem integral_mul_comp_add (f φ : Rd 2 → ℝ) (v : Rd 2) :
    ∫ x, f x * φ (x + v) = ∫ x, f (x - v) * φ x := by
  have h := integral_mul_comp_sub f φ (-v)
  simp only [sub_neg_eq_add, ← sub_eq_add_neg] at h
  exact h

/-- One direction of the summation by parts. -/
theorem integral_secondDiff_dir {f φ : Rd 2 → ℝ} (hf : Continuous f) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (v : Rd 2) :
    ∫ x, f x * (-2 * φ x + φ (x - v) + φ (x + v)) =
      ∫ x, (f (x + v) + f (x - v) - 2 * f x) * φ x := by
  have hA : Integrable (fun x => f x * φ (x - v)) :=
    (hf.mul (hφ.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (hφc.comp_homeomorph (Homeomorph.subRight v)).mul_left
  have hB : Integrable (fun x => f x * φ (x + v)) :=
    (hf.mul (hφ.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hφc.comp_homeomorph (Homeomorph.addRight v)).mul_left
  have hC : Integrable (fun x => f (x + v) * φ x) :=
    ((hf.comp (continuous_id.add continuous_const)).mul hφ).integrable_of_hasCompactSupport
      hφc.mul_left
  have hD : Integrable (fun x => f (x - v) * φ x) :=
    ((hf.comp (continuous_id.sub continuous_const)).mul hφ).integrable_of_hasCompactSupport
      hφc.mul_left
  have hE : Integrable (fun x => f x * φ x) :=
    (hf.mul hφ).integrable_of_hasCompactSupport hφc.mul_left
  have e1 : (fun x => f x * (-2 * φ x + φ (x - v) + φ (x + v))) =
      fun x => (f x * φ (x - v) + f x * φ (x + v)) - 2 * (f x * φ x) := by
    funext x; ring
  have e2 : (fun x => (f (x + v) + f (x - v) - 2 * f x) * φ x) =
      fun x => (f (x + v) * φ x + f (x - v) * φ x) - 2 * (f x * φ x) := by
    funext x; ring
  have hAB : Integrable (fun x => f x * φ (x - v) + f x * φ (x + v)) := hA.add hB
  have hCD : Integrable (fun x => f (x + v) * φ x + f (x - v) * φ x) := hC.add hD
  have hE2 : Integrable (fun x => 2 * (f x * φ x)) := hE.const_mul 2
  rw [e1, e2, integral_sub hAB hE2, integral_sub hCD hE2, integral_add hA hB, integral_add hC hD,
    integral_mul_comp_sub, integral_mul_comp_add]

/-- Second differences move from `φ` onto `f`. -/
theorem integral_sd_eq {f φ : Rd 2 → ℝ} (hf : Continuous f) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (t : ℝ) :
    ∫ x, f x * (t ^ 2 * ∑ i : Fin 2,
      (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) + φ (x + t⁻¹ • toE (unit i)))) =
      ∫ x, sd t f x * φ x := by
  have hI1 : ∀ i : Fin 2, Integrable (fun x => f x *
      (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) + φ (x + t⁻¹ • toE (unit i)))) := fun i =>
    (hf.mul (((continuous_const.mul hφ).add (hφ.comp (continuous_id.sub continuous_const))).add
      (hφ.comp (continuous_id.add continuous_const)))).integrable_of_hasCompactSupport
      ((hφc.mul_left.add (hφc.comp_homeomorph (Homeomorph.subRight _))).add
        (hφc.comp_homeomorph (Homeomorph.addRight _))).mul_left
  have hI2 : ∀ i : Fin 2, Integrable (fun x => (f (x + t⁻¹ • toE (unit i)) +
      f (x - t⁻¹ • toE (unit i)) - 2 * f x) * φ x) := fun i =>
    ((((hf.comp (continuous_id.add continuous_const)).add
      (hf.comp (continuous_id.sub continuous_const))).sub (continuous_const.mul hf)).mul
        hφ).integrable_of_hasCompactSupport hφc.mul_left
  have hL : (fun x => f x * (t ^ 2 * ∑ i : Fin 2,
      (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) + φ (x + t⁻¹ • toE (unit i))))) =
      fun x => ∑ i : Fin 2, t ^ 2 * (f x *
        (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) + φ (x + t⁻¹ • toE (unit i)))) := by
    funext x
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : (fun x => sd t f x * φ x) = fun x => ∑ i : Fin 2, t ^ 2 *
      ((f (x + t⁻¹ • toE (unit i)) + f (x - t⁻¹ • toE (unit i)) - 2 * f x) * φ x) := by
    funext x
    simp only [sd]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hL, hR, integral_finsetSum _ fun i _ => (hI1 i).const_mul _,
    integral_finsetSum _ fun i _ => (hI2 i).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_secondDiff_dir hf hφ hφc]

/-- For continuous `f`, `∫ f · t²(second difference of φ) → ∫ f Δφ`. -/
theorem tendsto_integral_sd_cont {f φ : Rd 2 → ℝ} (hf : Continuous f) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    Tendsto (fun t : ℝ => ∫ x, f x * (t ^ 2 * ∑ i : Fin 2,
      (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) + φ (x + t⁻¹ • toE (unit i))))) atTop
      (𝓝 (∫ x, f x * Matrix.trace (hessian φ x))) := by
  set ψ : ℝ → Rd 2 → ℝ := fun t x => t ^ 2 * ∑ i : Fin 2,
      (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) + φ (x + t⁻¹ • toE (unit i))) with hψ_def
  set K := cthickening 1 (tsupport φ) with hK_def
  have hK : IsCompact K := hφc.cthickening
  have hψ : TendstoUniformly ψ (fun x => Matrix.trace (hessian φ x)) atTop :=
    tendsto_secondDiff' (d := 2) hφ hφc
  have hψK : ∀ᶠ t in atTop, ∀ x, x ∉ K → ψ t x = 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht x hx
    have ht0 : 0 < t := by linarith
    have hz : ∀ y, dist x y ≤ 1 → φ y = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport fun hy' =>
        hx (Metric.mem_cthickening_of_dist_le x y 1 _ hy' hy)
    have hn1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
    have hcn : ∀ i : Fin 2, ‖t⁻¹ • toE (unit i : Site 2)‖ ≤ 1 := fun i => by
      rw [norm_smul, norm_toE_unit', mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0)]
      exact hn1
    simp only [hψ_def]
    rw [Finset.sum_eq_zero fun i _ => by
      rw [hz x (by simp), hz (x - _) (by rw [dist_eq_norm, sub_sub_cancel]; exact hcn i),
        hz (x + _) (by rw [dist_eq_norm, sub_add_cancel_left, norm_neg]; exact hcn i)]
      ring, mul_zero]
  obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hΔc := PegdenSmartAdapter.continuous_trace_hessian hφ
  obtain ⟨CΔ, hCΔ⟩ := hK.exists_bound_of_continuousOn hΔc.continuousOn
  set bnd : ℝ := (|Cf| + 1) * (|CΔ| + 1) with hbnd
  have hφcont : Continuous φ := hφ.continuous
  have hmeasF : ∀ t, AEStronglyMeasurable (fun x => f x * ψ t x) volume := by
    intro t
    have h2 : Continuous (ψ t) := by
      simp only [hψ_def]
      fun_prop
    exact (hf.mul h2).aestronglyMeasurable
  refine tendsto_integral_filter_of_dominated_convergence (K.indicator fun _ => bnd)
    (Eventually.of_forall hmeasF) ?_
    ((integrable_indicator_iff hK.measurableSet).2
      (integrableOn_const (C := bnd) hK.measure_lt_top.ne)) (ae_of_all _ fun x => ?_)
  · have hψ1 := Metric.tendstoUniformly_iff.1 hψ 1 one_pos
    filter_upwards [hψ1, hψK] with t hψt hψ0
    refine ae_of_all _ fun x => ?_
    show ‖f x * ψ t x‖ ≤ _
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, abs_mul, hbnd]
      have a1 : |f x| ≤ |Cf| + 1 := by
        have := hCf x hx
        rw [Real.norm_eq_abs] at this
        linarith [le_abs_self Cf]
      have a2 : |ψ t x| ≤ |CΔ| + 1 := by
        have := hψt x
        rw [dist_eq_norm, Real.norm_eq_abs] at this
        have hc := hCΔ x hx
        rw [Real.norm_eq_abs] at hc
        have := abs_sub_abs_le_abs_sub (ψ t x) (Matrix.trace (hessian φ x))
        rw [abs_sub_comm (Matrix.trace (hessian φ x))] at *
        linarith [le_abs_self CΔ]
      exact mul_le_mul a1 a2 (abs_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hx, hψ0 x hx, mul_zero, abs_zero]
  · exact tendsto_const_nhds.mul (hψ.tendsto_at x)

end SingleSourceD2

end RandomSandpile

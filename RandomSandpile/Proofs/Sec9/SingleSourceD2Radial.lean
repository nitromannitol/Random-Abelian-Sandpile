import RandomSandpile.Proofs.Sec9.SingleSourceD2ViscWeakRep

/-!
# Theorem 9.2 in dimension two: a radial test function for dyadic averages

For the equicontinuity step we use, instead of the Poisson kernel, one explicit
radial function. With `b` a bump on `(1/4, 3/4)`, `B(s) = ∫₀ˢ b`, `σ(s) = (B(s) - B(s/4))/4`,
`h(s) = σ(s)/s` (zero for `s ≤ 1/4`) and `H(s) = ∫₄ˢ h`, the function `Ψ(z) = H(|z|²)` is `C²`,
nonpositive, supported in `|z|² ≤ 3`, and `ΔΨ(z) = b(|z|²) - b(|z|²/4)/4`
(`4 (s h)' = b(s) - b(s/4)/4`, `radial_trace_hessian`). Rescaled and translated,
`Ψ(ρ⁻¹(z - x))` has Laplacian `β_ρ - β_{2ρ}`, `β_ρ(z) = ρ⁻² b(|z - x|²/ρ²)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

/-! ### The radial Laplacian -/

/-- The Laplacian of `z ↦ K(|z|²)`: `4 (|y|² K''(|y|²) + K'(|y|²))`. -/
theorem radial_trace_hessian {K K1 K2 : ℝ → ℝ} (hK : ∀ s, HasDerivAt K (K1 s) s)
    (hK1 : ∀ s, HasDerivAt K1 (K2 s) s) (y : Rd 2) :
    (hessian (fun z => K (‖z‖ ^ 2)) y).trace = 4 * (‖y‖ ^ 2 * K2 (‖y‖ ^ 2) + K1 (‖y‖ ^ 2)) := by
  have hq : ∀ z : Rd 2, HasFDerivAt (fun x : Rd 2 => ‖x‖ ^ 2) (2 • innerSL ℝ z) z := fun z =>
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hΨ : ∀ z : Rd 2, HasFDerivAt (fun x => K (‖x‖ ^ 2))
      (K1 (‖z‖ ^ 2) • (2 • innerSL ℝ z)) z := fun z =>
    (hK (‖z‖ ^ 2)).comp_hasFDerivAt z (hq z)
  have hD : fderiv ℝ (fun x => K (‖x‖ ^ 2)) = fun z => K1 (‖z‖ ^ 2) • (2 • innerSL ℝ z) :=
    funext fun z => (hΨ z).fderiv
  have hc : HasFDerivAt (fun z : Rd 2 => K1 (‖z‖ ^ 2)) (K2 (‖y‖ ^ 2) • (2 • innerSL ℝ y)) y :=
    (hK1 (‖y‖ ^ 2)).comp_hasFDerivAt y (hq y)
  have hf : HasFDerivAt (fun z : Rd 2 => 2 • innerSL ℝ z) (2 • innerSL ℝ) y :=
    (2 • innerSL ℝ (E := Rd 2)).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun z => by simp)
  have hDD := hc.smul hf
  have hD2 : fderiv ℝ (fderiv ℝ (fun x => K (‖x‖ ^ 2))) y =
      K1 (‖y‖ ^ 2) • (2 • innerSL ℝ (E := Rd 2)) +
        (K2 (‖y‖ ^ 2) • (2 • innerSL ℝ y)).smulRight (2 • innerSL ℝ y) := by
    rw [hD]
    exact hDD.fderiv
  have h0 : ∀ i : Fin 2, (innerSL ℝ (E := Rd 2)) (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i 1) = 1 := by
    intro i
    change inner ℝ (EuclideanSpace.single i (1 : ℝ) : Rd 2) (EuclideanSpace.single i 1) = 1
    rw [EuclideanSpace.inner_single_left]
    simp
  rw [Matrix.trace_fin_two, hessian_apply, hessian_apply, hD2]
  simp [h0, innerSL_apply_apply, EuclideanSpace.inner_single_right, norm_sq_two y]
  ring

/-- The Laplacian of `z ↦ K(|z - x|²)`. -/
theorem radial_trace_hessian' {K K1 K2 : ℝ → ℝ} (hK : ∀ s, HasDerivAt K (K1 s) s)
    (hK1 : ∀ s, HasDerivAt K1 (K2 s) s) (x y : Rd 2) :
    (hessian (fun z => K (‖z - x‖ ^ 2)) y).trace =
      4 * (‖y - x‖ ^ 2 * K2 (‖y - x‖ ^ 2) + K1 (‖y - x‖ ^ 2)) := by
  rw [hessian_comp_sub_right (fun z => K (‖z‖ ^ 2)) x y]
  exact radial_trace_hessian hK hK1 (y - x)

/-! ### The profile -/

/-- The bump on `(1/4, 3/4)`. -/
def bumpB : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- `b`. -/
def pb (s : ℝ) : ℝ := bumpB s

theorem pb_continuous : Continuous pb := bumpB.continuous

theorem pb_contDiff : ContDiff ℝ (⊤ : ℕ∞) pb := bumpB.contDiff

theorem pb_nonneg (s : ℝ) : 0 ≤ pb s := bumpB.nonneg

theorem pb_le_one (s : ℝ) : pb s ≤ 1 := bumpB.le_one

theorem pb_eq_zero {s : ℝ} (hs : s ≤ 1 / 4 ∨ 3 / 4 ≤ s) : pb s = 0 := by
  refine Function.notMem_support.1 fun h => ?_
  have h' : s ∈ Function.support bumpB := h
  rw [bumpB.support_eq, mem_ball, Real.dist_eq] at h'
  have h'' : |s - 1 / 2| < 1 / 4 := h'
  rw [abs_lt] at h''
  rcases hs with hs | hs <;> linarith [h''.1, h''.2]

theorem pb_half : pb (1 / 2) = 1 :=
  bumpB.one_of_mem_closedBall (mem_closedBall_self (by norm_num [bumpB]))

/-- `B(s) = ∫₀ˢ b`. -/
def pB (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, pb t

theorem hasDerivAt_pB (s : ℝ) : HasDerivAt pB (pb s) s :=
  (pb_continuous.integral_hasStrictDerivAt 0 s).hasDerivAt

theorem pB_eq_zero {s : ℝ} (hs : s ≤ 1 / 4) : pB s = 0 := by
  unfold pB
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
  · simp
  · refine pb_eq_zero (Or.inl ?_)
    rcases Set.mem_uIcc.1 ht with h | h <;> linarith [h.1, h.2]

theorem pB_sub_eq_zero {s : ℝ} (hs : 3 ≤ s) : pB s - pB (s / 4) = 0 := by
  unfold pB
  rw [intervalIntegral.integral_interval_sub_left (pb_continuous.intervalIntegrable _ _)
    (pb_continuous.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
  · simp
  · refine pb_eq_zero (Or.inr ?_)
    rcases Set.mem_uIcc.1 ht with h | h <;> linarith [h.1, h.2]

theorem pB_sub_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pB s - pB (s / 4) := by
  unfold pB
  rw [intervalIntegral.integral_interval_sub_left (pb_continuous.intervalIntegrable _ _)
    (pb_continuous.intervalIntegrable _ _)]
  exact intervalIntegral.integral_nonneg (by linarith) fun t _ => pb_nonneg t

/-- `σ(s) = (B(s) - B(s/4))/4`. -/
def pσ (s : ℝ) : ℝ := (pB s - pB (s / 4)) / 4

theorem hasDerivAt_pσ (s : ℝ) : HasDerivAt pσ ((pb s - pb (s / 4) / 4) / 4) s := by
  have h := ((hasDerivAt_pB s).sub ((hasDerivAt_pB (s / 4)).comp s
    ((hasDerivAt_id' s).div_const 4))).div_const 4
  exact h.congr_deriv (by ring)

theorem pσ_contDiff : ContDiff ℝ 1 pσ := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hasDerivAt_pσ s).differentiableAt, ?_⟩
  have e : deriv pσ = fun s => (pb s - pb (s / 4) / 4) / 4 :=
    funext fun s => (hasDerivAt_pσ s).deriv
  rw [e]
  have hc := pb_continuous
  fun_prop

/-- `h(s) = σ(s)/s`. -/
def ph (s : ℝ) : ℝ := pσ s / s

theorem ph_eq_zero {s : ℝ} (hs : s ≤ 1 / 4) : ph s = 0 := by
  simp [ph, pσ, pB_eq_zero hs, pB_eq_zero (show s / 4 ≤ 1 / 4 by linarith)]

theorem ph_eq_zero_far {s : ℝ} (hs : 3 ≤ s) : ph s = 0 := by
  simp [ph, pσ, pB_sub_eq_zero hs]

theorem ph_nonneg (s : ℝ) : 0 ≤ ph s := by
  by_cases hs : s ≤ 1 / 4
  · rw [ph_eq_zero hs]
  · have hs0 : 0 < s := by linarith
    exact div_nonneg (div_nonneg (pB_sub_nonneg hs0.le) (by norm_num)) hs0.le

theorem mul_ph (s : ℝ) : s * ph s = pσ s := by
  by_cases hs : s = 0
  · subst hs
    simp [ph, pσ]
  · unfold ph
    field_simp

theorem ph_contDiff : ContDiff ℝ 1 ph := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s < 1 / 4
  · have hev : ph =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hs] with t ht
      exact ph_eq_zero (le_of_lt ht)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    exact pσ_contDiff.contDiffAt.div contDiffAt_id hs0

theorem hasDerivAt_ph (s : ℝ) : HasDerivAt ph (deriv ph s) s :=
  ((ph_contDiff.differentiable (by norm_num)) s).hasDerivAt

/-- `h(s) + s h'(s) = (b(s) - b(s/4)/4)/4`. -/
theorem ph_identity (s : ℝ) : ph s + s * deriv ph s = (pb s - pb (s / 4) / 4) / 4 := by
  have h1 : HasDerivAt (fun s => s * ph s) (1 * ph s + s * deriv ph s) s :=
    (hasDerivAt_id' s).mul (hasDerivAt_ph s)
  have h2 : HasDerivAt (fun s => s * ph s) ((pb s - pb (s / 4) / 4) / 4) s := by
    rw [show (fun s => s * ph s) = pσ from funext mul_ph]
    exact hasDerivAt_pσ s
  have := h1.unique h2
  linarith

/-- `H(s) = ∫₄ˢ h`. -/
def pH (s : ℝ) : ℝ := ∫ t in (4 : ℝ)..s, ph t

theorem hasDerivAt_pH (s : ℝ) : HasDerivAt pH (ph s) s :=
  (ph_contDiff.continuous.integral_hasStrictDerivAt 4 s).hasDerivAt

theorem pH_eq_zero {s : ℝ} (hs : 3 ≤ s) : pH s = 0 := by
  unfold pH
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
  · simp
  · refine ph_eq_zero_far ?_
    rcases Set.mem_uIcc.1 ht with h | h <;> linarith [h.1, h.2]

theorem pH_nonpos (s : ℝ) : pH s ≤ 0 := by
  by_cases hs : s ≤ 4
  · unfold pH
    rw [intervalIntegral.integral_symm]
    exact neg_nonpos.2 (intervalIntegral.integral_nonneg hs fun t _ => ph_nonneg t)
  · exact (pH_eq_zero (by linarith)).le

theorem pH_contDiff : ContDiff ℝ 2 pH := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun s => (hasDerivAt_pH s).differentiableAt, by simp, ?_⟩
  rw [show deriv pH = ph from funext fun s => (hasDerivAt_pH s).deriv]
  exact ph_contDiff

/-- **The rescaled radial test function** `Ψ(z) = H(|z - x|²/ρ²)` has Laplacian
`(b(t) - b(t/4)/4)/ρ²`, `t = |z - x|²/ρ²`. -/
theorem trace_hessian_psi {ρ : ℝ} (hρ : 0 < ρ) (x y : Rd 2) :
    (hessian (fun z => pH (‖z - x‖ ^ 2 / ρ ^ 2)) y).trace =
      (pb (‖y - x‖ ^ 2 / ρ ^ 2) - pb (‖y - x‖ ^ 2 / ρ ^ 2 / 4) / 4) / ρ ^ 2 := by
  have hρ2 : ρ ^ 2 ≠ 0 := by positivity
  have hK : ∀ s, HasDerivAt (fun s => pH (s / ρ ^ 2)) (ph (s / ρ ^ 2) / ρ ^ 2) s := by
    intro s
    have h := (hasDerivAt_pH (s / ρ ^ 2)).comp s ((hasDerivAt_id' s).div_const (ρ ^ 2))
    have e : ph (s / ρ ^ 2) * (1 / ρ ^ 2) = ph (s / ρ ^ 2) / ρ ^ 2 := by ring
    rw [e] at h
    exact h
  have hK1 : ∀ s, HasDerivAt (fun s => ph (s / ρ ^ 2) / ρ ^ 2)
      (deriv ph (s / ρ ^ 2) / ρ ^ 2 / ρ ^ 2) s := by
    intro s
    have h := ((hasDerivAt_ph (s / ρ ^ 2)).comp s
      ((hasDerivAt_id' s).div_const (ρ ^ 2))).div_const (ρ ^ 2)
    have e : deriv ph (s / ρ ^ 2) * (1 / ρ ^ 2) / ρ ^ 2 = deriv ph (s / ρ ^ 2) / ρ ^ 2 / ρ ^ 2 := by
      ring
    rw [e] at h
    exact h
  rw [radial_trace_hessian' hK hK1 x y]
  have hid := ph_identity (‖y - x‖ ^ 2 / ρ ^ 2)
  have hid' : pb (‖y - x‖ ^ 2 / ρ ^ 2) - pb (‖y - x‖ ^ 2 / ρ ^ 2 / 4) / 4 =
      4 * (ph (‖y - x‖ ^ 2 / ρ ^ 2) + ‖y - x‖ ^ 2 / ρ ^ 2 * deriv ph (‖y - x‖ ^ 2 / ρ ^ 2)) := by
    linarith [hid]
  rw [hid']
  field_simp
  ring

end SingleSourceD2

end RandomSandpile

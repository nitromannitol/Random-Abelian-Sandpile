import RandomSandpile.Proofs.Sec9.SingleSourceD2Radial

/-!
# Theorem 9.2 in dimension two: equicontinuity from Laplacian bounds

`viscLaplaceEquicont : AlexandrovStmt → ViscLaplaceEquicontStmt`, without the
Poisson kernel or a regularity theorem. For `u` with `|Δu| ≤ C` in distributions (from the viscosity
bounds, `distLaplace_ge`), the weighted averages `I_ρ(x) = ∫ u β_ρ(· - x)` over annuli
(`β_ρ(z) = ρ⁻² b(|z|²/ρ²)`, `∫ β_ρ = m₀`) satisfy `|I_ρ - I_{2ρ}| ≤ C I₀ ρ²` (`dyadic_step`: test the
bounds with the explicit radial `-Ψ ≥ 0`, `ΔΨ = β_ρ - β_{2ρ}`). Telescoping and continuity give
`|m₀ u(x) - I_r(x)| ≤ C I₀ r² / 3` (`center_bound`), while `|I_r(x) - I_r(y)| ≤ |M| ∫ |β_r(· - x) -
β_r(· - y)|` is small for `|x - y|` small, uniformly in `x` (`translate_bound`). Hence the modulus.
-/

noncomputable section

open MeasureTheory Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

/-- The annular weight `β_ρ(z - x) = ρ⁻² b(|z - x|²/ρ²)`. -/
def wt (ρ : ℝ) (x z : Rd 2) : ℝ := pb (‖z - x‖ ^ 2 / ρ ^ 2) / ρ ^ 2

/-- The test function `Ψ(z) = H(|z - x|²/ρ²)`. -/
def psi (ρ : ℝ) (x z : Rd 2) : ℝ := pH (‖z - x‖ ^ 2 / ρ ^ 2)

/-- `m₀ = ∫ b(|z|²)`. -/
def m0 : ℝ := ∫ z : Rd 2, pb (‖z‖ ^ 2)

/-- `I₀ = ∫ -H(|z|²)`. -/
def I0 : ℝ := ∫ z : Rd 2, -pH (‖z‖ ^ 2)

theorem I0_nonneg : 0 ≤ I0 := integral_nonneg fun _ => neg_nonneg.2 (pH_nonpos _)

/-! ### The weights -/

theorem continuous_wt (ρ : ℝ) (x : Rd 2) : Continuous (wt ρ x) := by
  show Continuous fun z => pb (‖z - x‖ ^ 2 / ρ ^ 2) / ρ ^ 2
  have hc := pb_continuous
  fun_prop

theorem wt_nonneg (ρ : ℝ) (x z : Rd 2) : 0 ≤ wt ρ x z :=
  div_nonneg (pb_nonneg _) (sq_nonneg _)

theorem wt_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {x z : Rd 2} (hz : ρ ≤ ‖z - x‖) : wt ρ x z = 0 := by
  have h1 : 1 ≤ ‖z - x‖ ^ 2 / ρ ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ hρ.le hz 2
  rw [wt, pb_eq_zero (Or.inr (by linarith)), zero_div]

theorem hasCompactSupport_wt {ρ : ℝ} (hρ : 0 < ρ) (x : Rd 2) : HasCompactSupport (wt ρ x) :=
  HasCompactSupport.intro (isCompact_closedBall x ρ) fun z hz => by
    rw [mem_closedBall, not_le, dist_eq_norm] at hz
    exact wt_eq_zero hρ hz.le

theorem tsupport_wt {ρ : ℝ} (hρ : 0 < ρ) (x : Rd 2) : tsupport (wt ρ x) ⊆ closedBall x ρ := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra hn
  rw [mem_closedBall, not_le, dist_eq_norm] at hn
  exact hz (wt_eq_zero hρ hn.le)

theorem wt_translate0 (r : ℝ) (x w : Rd 2) : wt r x (x + w) = wt r 0 w := by
  rw [wt, wt, add_sub_cancel_left, sub_zero]

theorem wt_translate (r : ℝ) (x y w : Rd 2) : wt r y (x + w) = wt r 0 (w + (x - y)) := by
  rw [wt, wt, sub_zero, show x + w - y = w + (x - y) by abel]

theorem norm_smul_sq_div {ρ : ℝ} (hρ : 0 < ρ) (y : Rd 2) : ‖ρ • y‖ ^ 2 / ρ ^ 2 = ‖y‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_pow]
  exact mul_div_cancel_left₀ _ (by positivity)

theorem integral_wt {ρ : ℝ} (hρ : 0 < ρ) (x : Rd 2) : ∫ z, wt ρ x z = m0 := by
  have h := integral_comp_affine_two (wt ρ x) x hρ
  have e : ∀ y : Rd 2, wt ρ x (x + ρ • y) = pb (‖y‖ ^ 2) / ρ ^ 2 := fun y => by
    rw [wt, add_sub_cancel_left, norm_smul_sq_div hρ]
  simp only [e] at h
  rw [integral_div] at h
  have hρ2 : ρ ^ 2 ≠ 0 := by positivity
  calc ∫ z, wt ρ x z = ρ ^ 2 * ((ρ ^ 2)⁻¹ * ∫ z, wt ρ x z) := by
        rw [← mul_assoc, mul_inv_cancel₀ hρ2, one_mul]
    _ = ρ ^ 2 * (m0 / ρ ^ 2) := by rw [← h, m0]
    _ = m0 := by rw [mul_comm (ρ ^ 2), div_mul_cancel₀ _ hρ2]

theorem m0_pos : 0 < m0 := by
  have hc : Continuous fun z : Rd 2 => pb (‖z‖ ^ 2) := by
    have := pb_continuous
    fun_prop
  have hcs : HasCompactSupport fun z : Rd 2 => pb (‖z‖ ^ 2) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Rd 2) 1) fun z hz => by
      rw [mem_closedBall, not_le, dist_zero_right] at hz
      exact pb_eq_zero (Or.inr (by nlinarith))
  have h0 : (EuclideanSpace.single (0 : Fin 2) (Real.sqrt (1 / 2)) : Rd 2) 0 =
      Real.sqrt (1 / 2) := by simp
  have h1 : (EuclideanSpace.single (0 : Fin 2) (Real.sqrt (1 / 2)) : Rd 2) 1 = 0 := by simp
  have hz0 : ‖(EuclideanSpace.single (0 : Fin 2) (Real.sqrt (1 / 2)) : Rd 2)‖ ^ 2 = 1 / 2 := by
    rw [norm_sq_two, h0, h1, Real.sq_sqrt (by norm_num)]
    norm_num
  show 0 < ∫ z : Rd 2, pb (‖z‖ ^ 2)
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun z => pb_nonneg _)
    (show pb (‖(EuclideanSpace.single (0 : Fin 2) (Real.sqrt (1 / 2)) : Rd 2)‖ ^ 2) ≠ 0 by
      rw [hz0, pb_half]
      norm_num)

/-! ### The radial test function -/

theorem psi_contDiff (ρ : ℝ) (x : Rd 2) : ContDiff ℝ 2 (psi ρ x) := by
  show ContDiff ℝ 2 fun z => pH (‖z - x‖ ^ 2 / ρ ^ 2)
  exact pH_contDiff.comp (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _)

theorem psi_nonpos (ρ : ℝ) (x z : Rd 2) : psi ρ x z ≤ 0 := pH_nonpos _

theorem psi_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {x z : Rd 2} (hz : 2 * ρ ≤ ‖z - x‖) :
    psi ρ x z = 0 := by
  refine pH_eq_zero ?_
  rw [le_div_iff₀ (by positivity)]
  have := pow_le_pow_left₀ (by positivity) hz 2
  nlinarith

theorem tsupport_neg_psi {ρ : ℝ} (hρ : 0 < ρ) (x : Rd 2) :
    tsupport (fun z => -psi ρ x z) ⊆ closedBall x (2 * ρ) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra hn
  rw [mem_closedBall, not_le, dist_eq_norm] at hn
  exact hz (show -psi ρ x z = 0 by rw [psi_eq_zero hρ hn.le, neg_zero])

theorem integral_neg_psi {ρ : ℝ} (hρ : 0 < ρ) (x : Rd 2) :
    ∫ z, -psi ρ x z = ρ ^ 2 * I0 := by
  have h := integral_comp_affine_two (fun z => -psi ρ x z) x hρ
  have e : ∀ y : Rd 2, -psi ρ x (x + ρ • y) = -pH (‖y‖ ^ 2) := fun y => by
    rw [psi, add_sub_cancel_left, norm_smul_sq_div hρ]
  simp only [e] at h
  have hρ2 : ρ ^ 2 ≠ 0 := by positivity
  rw [I0, h, ← mul_assoc, mul_inv_cancel₀ hρ2, one_mul]

theorem trace_hessian_psi' {ρ : ℝ} (hρ : 0 < ρ) (x z : Rd 2) :
    (hessian (psi ρ x) z).trace = wt ρ x z - wt (2 * ρ) x z := by
  have h := trace_hessian_psi hρ x z
  have e : ‖z - x‖ ^ 2 / (2 * ρ) ^ 2 = ‖z - x‖ ^ 2 / ρ ^ 2 / 4 := by ring
  show (hessian (fun z => pH (‖z - x‖ ^ 2 / ρ ^ 2)) z).trace = _
  rw [h, wt, wt, e]
  ring

/-! ### The dyadic step and telescoping -/

theorem integrable_mul_wt {V : Set (Rd 2)} (hV : IsOpen V) {u : Rd 2 → ℝ}
    (hu : ContinuousOn u V) {ρ : ℝ} (hρ : 0 < ρ) {x : Rd 2} (hx : closedBall x ρ ⊆ V) :
    Integrable (fun z => u z * wt ρ x z) := by
  have hc := continuous_mul_of_tsupport hV hu (continuous_wt ρ x) ((tsupport_wt hρ x).trans hx)
  have hc' : Continuous fun z => u z * wt ρ x z := hc.congr fun z => mul_comm _ _
  refine hc'.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall x ρ) fun z hz => ?_)
  rw [mem_closedBall, not_le, dist_eq_norm] at hz
  show u z * wt ρ x z = 0
  rw [wt_eq_zero hρ hz.le, mul_zero]

/-- **The dyadic step** `|∫ u β_ρ - ∫ u β_{2ρ}| ≤ C ρ² I₀`. -/
theorem dyadic_step {V : Set (Rd 2)} (hV : IsOpen V) {C : ℝ} {u : Rd 2 → ℝ}
    (hu : ContinuousOn u V)
    (hge : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → -C * ∫ x, φ x ≤ ∫ x, u x * Matrix.trace (hessian φ x))
    (hle : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → ∫ x, u x * Matrix.trace (hessian φ x) ≤ C * ∫ x, φ x)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Rd 2} (hx : closedBall x (2 * ρ) ⊆ V) :
    |(∫ z, u z * wt ρ x z) - ∫ z, u z * wt (2 * ρ) x z| ≤ C * (ρ ^ 2 * I0) := by
  have hφ : ContDiff ℝ 2 (fun z => -psi ρ x z) := (psi_contDiff ρ x).neg
  have hφc : HasCompactSupport (fun z => -psi ρ x z) :=
    (isCompact_closedBall x (2 * ρ)).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_neg_psi hρ x)
  have hφV : tsupport (fun z => -psi ρ x z) ⊆ V := (tsupport_neg_psi hρ x).trans hx
  have hφ0 : ∀ z, 0 ≤ -psi ρ x z := fun z => neg_nonneg.2 (psi_nonpos ρ x z)
  have h1 := hge _ hφ hφc hφV hφ0
  have h2 := hle _ hφ hφc hφV hφ0
  have hI1 := integrable_mul_wt hV hu hρ ((closedBall_subset_closedBall (by linarith)).trans hx)
  have hI2 := integrable_mul_wt hV hu (by linarith : (0 : ℝ) < 2 * ρ) hx
  have e : ∫ z, u z * Matrix.trace (hessian (fun z => -psi ρ x z) z) =
      -((∫ z, u z * wt ρ x z) - ∫ z, u z * wt (2 * ρ) x z) := by
    rw [← integral_sub hI1 hI2, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show u z * Matrix.trace (hessian (fun z => -psi ρ x z) z) =
      -(u z * wt ρ x z - u z * wt (2 * ρ) x z)
    rw [hessian_neg', Matrix.trace_neg, trace_hessian_psi' hρ]
    ring
  rw [e, integral_neg_psi hρ x] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **Telescoping** over the scales `r / 2^k`. -/
theorem dyadic_sum {V : Set (Rd 2)} (hV : IsOpen V) {C : ℝ} {u : Rd 2 → ℝ}
    (hu : ContinuousOn u V)
    (hge : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → -C * ∫ x, φ x ≤ ∫ x, u x * Matrix.trace (hessian φ x))
    (hle : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → ∫ x, u x * Matrix.trace (hessian φ x) ≤ C * ∫ x, φ x)
    {r : ℝ} (hr : 0 < r) {x : Rd 2} (hx : closedBall x (2 * r) ⊆ V) (N : ℕ) :
    |(∫ z, u z * wt (r / 2 ^ N) x z) - ∫ z, u z * wt r x z| ≤
      C * I0 * (r ^ 2 - (r / 2 ^ N) ^ 2) / 3 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hρ : 0 < r / 2 ^ (N + 1) := by positivity
    have h2ρ : 2 * (r / 2 ^ (N + 1)) = r / 2 ^ N := by
      rw [pow_succ, ← div_div]
      ring
    have hρr : 2 * (r / 2 ^ (N + 1)) ≤ 2 * r := by
      rw [h2ρ]
      have h1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
      have := div_le_self hr.le h1
      linarith
    have hstep := dyadic_step hV hu hge hle hρ ((closedBall_subset_closedBall hρr).trans hx)
    rw [h2ρ] at hstep
    have htri := abs_sub_le (∫ z, u z * wt (r / 2 ^ (N + 1)) x z)
      (∫ z, u z * wt (r / 2 ^ N) x z) (∫ z, u z * wt r x z)
    have e : (r / 2 ^ N) ^ 2 = 4 * (r / 2 ^ (N + 1)) ^ 2 := by
      rw [← h2ρ]
      ring
    rw [e] at ih
    linarith

/-- The averages at small scales are close to `m₀ u(x)`. -/
theorem avg_close {V : Set (Rd 2)} (hV : IsOpen V) {u : Rd 2 → ℝ} (hu : ContinuousOn u V)
    {x : Rd 2} (hx : x ∈ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < δ → |(∫ z, u z * wt ρ x z) - m0 * u x| < ε := by
  have hm := m0_pos
  obtain ⟨δ, hδ, hδu⟩ :=
    Metric.continuousOn_iff.1 hu x hx (ε / (2 * m0)) (div_pos hε (by linarith))
  obtain ⟨δ', hδ', hδV⟩ := Metric.isOpen_iff.1 hV x hx
  refine ⟨min δ δ', lt_min hδ hδ', fun ρ hρ hρδ => ?_⟩
  have hball : closedBall x ρ ⊆ V :=
    (closedBall_subset_ball (lt_of_lt_of_le hρδ (min_le_right _ _))).trans hδV
  have hI := integrable_mul_wt hV hu hρ hball
  have hIw : Integrable (wt ρ x) :=
    (continuous_wt ρ x).integrable_of_hasCompactSupport (hasCompactSupport_wt hρ x)
  have e : (∫ z, u z * wt ρ x z) - m0 * u x = ∫ z, (u z - u x) * wt ρ x z := by
    rw [← integral_wt hρ x, ← integral_mul_const, ← integral_sub hI (hIw.mul_const _)]
    exact integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [e]
  calc |∫ z, (u z - u x) * wt ρ x z| = ‖∫ z, (u z - u x) * wt ρ x z‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, ε / (2 * m0) * wt ρ x z := by
        refine norm_integral_le_of_norm_le (hIw.const_mul _) (ae_of_all _ fun z => ?_)
        show ‖(u z - u x) * wt ρ x z‖ ≤ ε / (2 * m0) * wt ρ x z
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (wt_nonneg ρ x z)]
        by_cases hz : ‖z - x‖ < ρ
        · have hzV : z ∈ V := hball (by rw [mem_closedBall, dist_eq_norm]; exact hz.le)
          have h := hδu z hzV (by rw [dist_eq_norm]; linarith [min_le_left δ δ'])
          rw [Real.dist_eq] at h
          exact mul_le_mul_of_nonneg_right h.le (wt_nonneg ρ x z)
        · rw [wt_eq_zero hρ (not_lt.1 hz), mul_zero, mul_zero]
    _ = ε / (2 * m0) * m0 := by rw [integral_const_mul, integral_wt hρ x]
    _ = ε / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hm.ne']
    _ < ε := half_lt_self hε

/-- The dyadic averages converge to `m₀ u(x)`. -/
theorem tendsto_avg {V : Set (Rd 2)} (hV : IsOpen V) {u : Rd 2 → ℝ} (hu : ContinuousOn u V)
    {r : ℝ} (hr : 0 < r) {x : Rd 2} (hx : x ∈ V) :
    Tendsto (fun N : ℕ => ∫ z, u z * wt (r / 2 ^ N) x z) atTop (𝓝 (m0 * u x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := avg_close hV hu hx hε
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (r / δ) (by norm_num : (1 : ℝ) < 2)
  rw [div_lt_iff₀ hδ] at hN₀
  refine ⟨N₀, fun N hN => ?_⟩
  have h2N : (2 : ℝ) ^ N₀ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have h2Npos : (0 : ℝ) < 2 ^ N := by positivity
  rw [Real.dist_eq]
  refine hδc _ (div_pos hr h2Npos) ?_
  rw [div_lt_iff₀ h2Npos]
  nlinarith [mul_le_mul_of_nonneg_left h2N hδ.le]

/-- **The centre bound** `|m₀ u(x) - ∫ u β_r(· - x)| ≤ C I₀ r² / 3`. -/
theorem avg_center_bound {V : Set (Rd 2)} (hV : IsOpen V) {C : ℝ} (hC : 0 ≤ C) {u : Rd 2 → ℝ}
    (hu : ContinuousOn u V)
    (hge : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → -C * ∫ x, φ x ≤ ∫ x, u x * Matrix.trace (hessian φ x))
    (hle : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → ∫ x, u x * Matrix.trace (hessian φ x) ≤ C * ∫ x, φ x)
    {r : ℝ} (hr : 0 < r) {x : Rd 2} (hx : closedBall x (2 * r) ⊆ V) :
    |m0 * u x - ∫ z, u z * wt r x z| ≤ C * I0 * r ^ 2 / 3 := by
  have hxV : x ∈ V := hx (mem_closedBall_self (by linarith))
  have hT := ((tendsto_avg hV hu hr hxV).sub_const (∫ z, u z * wt r x z)).abs
  refine le_of_tendsto hT (Eventually.of_forall fun N => ?_)
  show |(∫ z, u z * wt (r / 2 ^ N) x z) - ∫ z, u z * wt r x z| ≤ C * I0 * r ^ 2 / 3
  have h := dyadic_sum hV hu hge hle hr hx N
  have h0 : 0 ≤ C * I0 * (r / 2 ^ N) ^ 2 := mul_nonneg (mul_nonneg hC I0_nonneg) (sq_nonneg _)
  linarith

/-! ### Continuity of the averages in the centre -/

/-- `∫ |β_r(· - x) - β_r(· - y)|` is small for `|x - y|` small, uniformly. -/
theorem translate_bound {r : ℝ} (hr : 0 < r) {ω : ℝ} (hω : 0 < ω) :
    ∃ δ > 0, ∀ x y : Rd 2, dist x y < δ → ∫ z, |wt r x z - wt r y z| ≤ ω := by
  let β : ContDiffBump (0 : Rd 2) := ⟨r + 1, r + 2, by linarith, by linarith⟩
  have hIβ0 : 0 ≤ ∫ z, β z := integral_nonneg fun _ => β.nonneg
  have hW : UniformContinuous (wt r 0) :=
    (hasCompactSupport_wt hr 0).uniformContinuous_of_continuous (continuous_wt r 0)
  obtain ⟨δ1, hδ1, hδ1W⟩ :=
    Metric.uniformContinuous_iff.1 hW (ω / ((∫ z, β z) + 1)) (div_pos hω (by linarith))
  refine ⟨min δ1 1, lt_min hδ1 one_pos, fun x y hxy => ?_⟩
  have hxy1 : ‖x - y‖ < 1 := by
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le hxy (min_le_right _ _)
  have hxyδ : ‖x - y‖ < δ1 := by
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le hxy (min_le_left _ _)
  have e : ∫ z, |wt r x z - wt r y z| = ∫ w, |wt r 0 w - wt r 0 (w + (x - y))| := by
    refine (integral_add_left_eq_self (μ := (volume : Measure (Rd 2)))
      (fun z => |wt r x z - wt r y z|) x).symm.trans ?_
    congr 1
    funext w
    show |wt r x (x + w) - wt r y (x + w)| = |wt r 0 w - wt r 0 (w + (x - y))|
    rw [wt_translate0, wt_translate]
  rw [e]
  have hg : Integrable (fun w => ω / ((∫ z, β z) + 1) * β w) := β.integrable.const_mul _
  calc ∫ w, |wt r 0 w - wt r 0 (w + (x - y))| ≤ ∫ w, ω / ((∫ z, β z) + 1) * β w := by
        refine integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _) hg
          (ae_of_all _ fun w => ?_)
        show |wt r 0 w - wt r 0 (w + (x - y))| ≤ ω / ((∫ z, β z) + 1) * β w
        by_cases hw : ‖w‖ ≤ r + 1
        · have hβ1 : β w = 1 :=
            β.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hw)
          rw [hβ1, mul_one]
          have h := @hδ1W w (w + (x - y))
            (by rw [dist_comm, dist_eq_norm, add_sub_cancel_left]; exact hxyδ)
          rw [Real.dist_eq] at h
          exact h.le
        · have hw' := not_le.1 hw
          have h1 : wt r 0 w = 0 := wt_eq_zero hr (by rw [sub_zero]; linarith)
          have h2 : wt r 0 (w + (x - y)) = 0 := wt_eq_zero hr (by
            have h3 := norm_add_le (w + (x - y)) (-(x - y))
            rw [add_neg_cancel_right, norm_neg] at h3
            rw [sub_zero]
            linarith)
          rw [h1, h2, sub_zero, abs_zero]
          exact mul_nonneg (div_nonneg hω.le (by linarith)) β.nonneg
    _ = ω / ((∫ z, β z) + 1) * ∫ z, β z := integral_const_mul _ _
    _ ≤ ω := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

/-- `|∫ u β_r(· - x) - ∫ u β_r(· - y)| ≤ |M| ∫ |β_r(· - x) - β_r(· - y)|`. -/
theorem avg_diff {V : Set (Rd 2)} (hV : IsOpen V) {u : Rd 2 → ℝ} (hu : ContinuousOn u V)
    {M : ℝ} (hM : ∀ z ∈ V, |u z| ≤ M) {r : ℝ} (hr : 0 < r) {x y : Rd 2}
    (hx : closedBall x r ⊆ V) (hy : closedBall y r ⊆ V) :
    |(∫ z, u z * wt r x z) - ∫ z, u z * wt r y z| ≤ |M| * ∫ z, |wt r x z - wt r y z| := by
  have hIx := integrable_mul_wt hV hu hr hx
  have hIy := integrable_mul_wt hV hu hr hy
  have hIw : Integrable (fun z => |wt r x z - wt r y z|) :=
    (((continuous_wt r x).integrable_of_hasCompactSupport (hasCompactSupport_wt hr x)).sub
      ((continuous_wt r y).integrable_of_hasCompactSupport (hasCompactSupport_wt hr y))).abs
  rw [← integral_sub hIx hIy, ← integral_const_mul]
  calc |∫ z, (u z * wt r x z - u z * wt r y z)| =
        ‖∫ z, (u z * wt r x z - u z * wt r y z)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, |M| * |wt r x z - wt r y z| := by
        refine norm_integral_le_of_norm_le (hIw.const_mul _) (ae_of_all _ fun z => ?_)
        show ‖u z * wt r x z - u z * wt r y z‖ ≤ |M| * |wt r x z - wt r y z|
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
        by_cases hz : z ∈ V
        · exact mul_le_mul_of_nonneg_right ((hM z hz).trans (le_abs_self M)) (abs_nonneg _)
        · have h1 : wt r x z = 0 := wt_eq_zero hr (not_lt.1 fun h =>
            hz (hx (by rw [mem_closedBall, dist_eq_norm]; exact h.le)))
          have h2 : wt r y z = 0 := wt_eq_zero hr (not_lt.1 fun h =>
            hz (hy (by rw [mem_closedBall, dist_eq_norm]; exact h.le)))
          rw [h1, h2, sub_zero, abs_zero, mul_zero, mul_zero]

/-! ### The equicontinuity step -/

/-- The viscosity bounds `-C ≤ Δu ≤ C` give `|Δu| ≤ |C|` in distributions. -/
theorem dist_bounds (hA : AlexandrovStmt) {V : Set (Rd 2)} (hV : IsOpen V) {C : ℝ}
    {u : Rd 2 → ℝ} (hu : ContinuousOn u V) (h1 : ViscFromAboveGE (fun X => X.trace + C) V u)
    (h2 : ViscFromBelowLE (fun X => X.trace - C) V u) :
    (∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → -|C| * ∫ x, φ x ≤ ∫ x, u x * Matrix.trace (hessian φ x)) ∧
    (∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → ∫ x, u x * Matrix.trace (hessian φ x) ≤ |C| * ∫ x, φ x) := by
  refine ⟨fun φ hφ hφc hφV hφ0 => ?_, fun φ hφ hφc hφV hφ0 => ?_⟩
  · have h := distLaplace_ge hA hV hu h1 hφ hφc hφV hφ0
    have hφi : 0 ≤ ∫ x, φ x := integral_nonneg hφ0
    have : -|C| * ∫ x, φ x ≤ -C * ∫ x, φ x :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hφi
    linarith
  · have h2' : ViscFromAboveGE (fun X => X.trace + C) V (fun x => -u x) := by
      intro x hx ψ hψ hmax
      have hmin : IsLocalMin (fun y => u y - (fun y => -ψ y) y) x := by
        filter_upwards [hmax] with y hy
        have hy' : -u y - ψ y ≤ -u x - ψ x := hy
        show u x - -ψ x ≤ u y - -ψ y
        linarith
      have h : (hessian (fun y => -ψ y) x).trace - C ≤ 0 := h2 x hx (fun y => -ψ y) hψ.neg hmin
      rw [hessian_neg', Matrix.trace_neg] at h
      show 0 ≤ (hessian ψ x).trace + C
      linarith
    have h : -C * ∫ x, φ x ≤ ∫ x, -u x * Matrix.trace (hessian φ x) :=
      distLaplace_ge hA hV hu.neg h2' hφ hφc hφV hφ0
    have e : ∫ x, -u x * Matrix.trace (hessian φ x) =
        -∫ x, u x * Matrix.trace (hessian φ x) := by
      rw [← integral_neg]
      exact integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [e] at h
    have hφi : 0 ≤ ∫ x, φ x := integral_nonneg hφ0
    have : C * ∫ x, φ x ≤ |C| * ∫ x, φ x := mul_le_mul_of_nonneg_right (le_abs_self C) hφi
    linarith

/-- **D4.** Viscosity Laplacian bounds give equicontinuity on compact subsets,
from Alexandrov's theorem only. -/
theorem viscLaplaceEquicont (hA : AlexandrovStmt) : ViscLaplaceEquicontStmt := by
  intro V hV C M S hS hSV η hη
  obtain ⟨r0, hr0, hr0V⟩ := IsCompact.exists_cthickening_subset_open hS hV hSV
  have hm := m0_pos
  have hI0 := I0_nonneg
  have hK : 0 ≤ |C| * I0 / 3 := div_nonneg (mul_nonneg (abs_nonneg C) hI0) (by norm_num)
  have hK1 : 0 < |C| * I0 / 3 + 1 := by linarith
  have hM1 : 0 < |M| + 1 := by linarith [abs_nonneg M]
  have hq : 0 < m0 * η / 4 := div_pos (mul_pos hm hη) (by norm_num)
  obtain ⟨r, hr, hr1, hrt, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      r ≤ m0 * η / 4 / (|C| * I0 / 3 + 1) ∧ 2 * r ≤ r0 :=
    ⟨min (r0 / 2) (min 1 (m0 * η / 4 / (|C| * I0 / 3 + 1))),
      lt_min (half_pos hr0) (lt_min one_pos (div_pos hq hK1)),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _),
      by linarith [min_le_left (r0 / 2) (min 1 (m0 * η / 4 / (|C| * I0 / 3 + 1)))]⟩
  obtain ⟨δ, hδ, hδb⟩ := translate_bound hr (div_pos hq hM1)
  refine ⟨δ, hδ, fun u hu hM h1 h2 x hx y hy hxy => ?_⟩
  obtain ⟨hge, hle⟩ := dist_bounds hA hV hu h1 h2
  have hbx : closedBall x (2 * r) ⊆ V :=
    (closedBall_subset_cthickening hx _).trans ((cthickening_mono hr2 S).trans hr0V)
  have hby : closedBall y (2 * r) ⊆ V :=
    (closedBall_subset_cthickening hy _).trans ((cthickening_mono hr2 S).trans hr0V)
  have hrx : closedBall x r ⊆ V := (closedBall_subset_closedBall (by linarith)).trans hbx
  have hry : closedBall y r ⊆ V := (closedBall_subset_closedBall (by linarith)).trans hby
  have hcx := avg_center_bound hV (abs_nonneg C) hu hge hle hr hbx
  have hcy := avg_center_bound hV (abs_nonneg C) hu hge hle hr hby
  have hd := avg_diff hV hu hM hr hrx hry
  have hw := hδb x y hxy
  have hMb : |M| * ∫ z, |wt r x z - wt r y z| ≤ m0 * η / 4 := by
    calc |M| * ∫ z, |wt r x z - wt r y z| ≤ (|M| + 1) * (m0 * η / 4 / (|M| + 1)) :=
          mul_le_mul (by linarith) hw (integral_nonneg fun _ => abs_nonneg _) hM1.le
      _ = m0 * η / 4 := by rw [mul_comm (|M| + 1), div_mul_cancel₀ _ hM1.ne']
  have hKr : |C| * I0 * r ^ 2 / 3 ≤ m0 * η / 4 := by
    have h1' : |C| * I0 / 3 * r ^ 2 ≤ |C| * I0 / 3 * r :=
      mul_le_mul_of_nonneg_left (by nlinarith) hK
    have h2' : |C| * I0 / 3 * r ≤ (|C| * I0 / 3 + 1) * (m0 * η / 4 / (|C| * I0 / 3 + 1)) :=
      mul_le_mul (by linarith) hrt hr.le hK1.le
    rw [mul_comm (|C| * I0 / 3 + 1), div_mul_cancel₀ _ hK1.ne'] at h2'
    linarith
  have e : |m0 * u x - m0 * u y| = m0 * |u x - u y| := by
    rw [← mul_sub, abs_mul, abs_of_pos hm]
  have t1 := abs_sub_le (m0 * u x) (∫ z, u z * wt r x z) (m0 * u y)
  have t2 := abs_sub_le (∫ z, u z * wt r x z) (∫ z, u z * wt r y z) (m0 * u y)
  rw [abs_sub_comm] at hcy
  have hfin : m0 * |u x - u y| < m0 * η := by linarith
  exact lt_of_mul_lt_mul_left hfin hm.le

end SingleSourceD2

end RandomSandpile

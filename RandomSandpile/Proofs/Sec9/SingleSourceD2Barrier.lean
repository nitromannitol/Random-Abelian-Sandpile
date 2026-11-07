import RandomSandpile.Proofs.Sec9.SingleSourceD2Jets

/-!
# Theorem 9.2 in dimension two: the radial lower barrier

For `c, m > 0` and `R² = m/(πc)` (`rad2`), the barrier
`V_m(x) = κ(min(|x|², R²))`, `κ(s) = c/4 (s - R²) - m/(4π) log(s/R²)` (`kap`, `Vbar`)
is `c/4(|x|² - R²) - (m/2π) log(|x|/R)` inside `B_R` and `0` outside. Here:
* `κ ≥ 0` on `(0, ∞)` (`log t ≤ t - 1`) and `κ(R²) = 0`, so `V_m ≥ 0` is continuous off the origin;
* the smooth part `V(x) = κ(|x|²)` has `ΔV = c` off the origin (`trace_hessian_Vsm`, from the radial
  formula `Δ K(|x|²) = 4(|x|² K'' + K')` in a local form, `radial_trace_hessian_loc`);
* `ΔV_m ≥ c` in the viscosity sense (tested from above) where `V_m > 0` (`visc_sub_Vbar`).
-/

noncomputable section

open Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

/-! ### Calculus -/

/-- The Hessian of a difference of functions that are `C²` near `x`. -/
theorem hessian_sub_of_contDiffAt {φ ψ : Rd 2 → ℝ} {x : Rd 2} (hφ : ContDiffAt ℝ 2 φ x)
    (hψ : ContDiffAt ℝ 2 ψ x) :
    hessian (fun y => φ y - ψ y) x = hessian φ x - hessian ψ x := by
  have hevφ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hevψ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ψ y :=
    (hψ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun y => φ y - ψ y) =ᶠ[𝓝 x] fun y => fderiv ℝ φ y - fderiv ℝ ψ y := by
    filter_upwards [hevφ, hevψ] with y h1 h2
    exact (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv
  have hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDψ : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fun y => fderiv ℝ φ y - fderiv ℝ ψ y) x =
      fderiv ℝ (fderiv ℝ φ) x - fderiv ℝ (fderiv ℝ ψ) x :=
    (hDφ.hasFDerivAt.sub hDψ.hasFDerivAt).fderiv
  ext i j
  rw [hessian_apply, h1.fderiv_eq, h2]
  simp only [sub_apply, Matrix.sub_apply, hessian_apply]

/-- The Laplacian of `z ↦ K(|z|²)` where `K` is twice differentiable on `(a, ∞)`,
`a < |y|²`: `4 (|y|² K''(|y|²) + K'(|y|²))`. -/
theorem radial_trace_hessian_loc {K K1 K2 : ℝ → ℝ} {a : ℝ}
    (hK : ∀ s, a < s → HasDerivAt K (K1 s) s) (hK1 : ∀ s, a < s → HasDerivAt K1 (K2 s) s)
    {y : Rd 2} (hy : a < ‖y‖ ^ 2) :
    (hessian (fun z => K (‖z‖ ^ 2)) y).trace = 4 * (‖y‖ ^ 2 * K2 (‖y‖ ^ 2) + K1 (‖y‖ ^ 2)) := by
  have hq : ∀ z : Rd 2, HasFDerivAt (fun x : Rd 2 => ‖x‖ ^ 2) (2 • innerSL ℝ z) z := fun z =>
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hU : ∀ᶠ z in 𝓝 y, a < ‖z‖ ^ 2 :=
    ((continuous_norm.pow 2).tendsto y).eventually (lt_mem_nhds hy)
  have hD : fderiv ℝ (fun x => K (‖x‖ ^ 2)) =ᶠ[𝓝 y]
      fun z => K1 (‖z‖ ^ 2) • (2 • innerSL ℝ z) := by
    filter_upwards [hU] with z hz
    exact ((hK _ hz).comp_hasFDerivAt z (hq z)).fderiv
  have hc : HasFDerivAt (fun z : Rd 2 => K1 (‖z‖ ^ 2)) (K2 (‖y‖ ^ 2) • (2 • innerSL ℝ y)) y :=
    (hK1 _ hy).comp_hasFDerivAt y (hq y)
  have hf : HasFDerivAt (fun z : Rd 2 => 2 • innerSL ℝ z) (2 • innerSL ℝ) y :=
    (2 • innerSL ℝ (E := Rd 2)).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun z => by simp)
  have hDD := hc.smul hf
  have hD2 : fderiv ℝ (fderiv ℝ (fun x => K (‖x‖ ^ 2))) y =
      K1 (‖y‖ ^ 2) • (2 • innerSL ℝ) +
        (K2 (‖y‖ ^ 2) • (2 • innerSL ℝ y)).smulRight (2 • innerSL ℝ y) := by
    rw [hD.fderiv_eq]
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

/-! ### The profile -/

/-- `R² = m / (π c)`. -/
def rad2 (c m : ℝ) : ℝ := m / (Real.pi * c)

theorem rad2_pos {c m : ℝ} (hc : 0 < c) (hm : 0 < m) : 0 < rad2 c m := by
  unfold rad2
  positivity

/-- `κ(s) = c/4 (s - R²) - m/(4π) log(s/R²)`. -/
def kap (c m s : ℝ) : ℝ :=
  c / 4 * (s - rad2 c m) - m / (4 * Real.pi) * Real.log (s / rad2 c m)

/-- The smooth part `κ(|x|²)`. -/
def Vsm (c m : ℝ) (x : Rd 2) : ℝ := kap c m (‖x‖ ^ 2)

/-- The barrier `V_m(x) = κ(min(|x|², R²))`. -/
def Vbar (c m : ℝ) (x : Rd 2) : ℝ := kap c m (min (‖x‖ ^ 2) (rad2 c m))

theorem kap_rad2 {c m : ℝ} (hc : 0 < c) (hm : 0 < m) : kap c m (rad2 c m) = 0 := by
  simp [kap, div_self (rad2_pos hc hm).ne']

theorem kap_nonneg {c m s : ℝ} (hc : 0 < c) (hm : 0 < m) (hs : 0 < s) : 0 ≤ kap c m s := by
  have hR := rad2_pos hc hm
  have hlog := Real.log_le_sub_one_of_pos (div_pos hs hR)
  have hm' : m ≠ 0 := hm.ne'
  have hc' : c ≠ 0 := hc.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hkey : m / (4 * Real.pi) * (s / rad2 c m - 1) = c / 4 * (s - rad2 c m) := by
    unfold rad2
    field_simp
  have h := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ m / (4 * Real.pi))
  unfold kap
  linarith

theorem Vbar_nonneg {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {x : Rd 2} (hx : x ≠ 0) :
    0 ≤ Vbar c m x :=
  kap_nonneg hc hm (lt_min (pow_pos (norm_pos_iff.2 hx) 2) (rad2_pos hc hm))

theorem Vbar_eq_zero {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {x : Rd 2} (hx : rad2 c m ≤ ‖x‖ ^ 2) :
    Vbar c m x = 0 := by
  rw [Vbar, min_eq_right hx, kap_rad2 hc hm]

theorem Vbar_eq_Vsm {c m : ℝ} {x : Rd 2} (hx : ‖x‖ ^ 2 ≤ rad2 c m) : Vbar c m x = Vsm c m x := by
  rw [Vbar, min_eq_left hx, Vsm]

theorem lt_of_Vbar_pos {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {x : Rd 2} (hx : 0 < Vbar c m x) :
    ‖x‖ ^ 2 < rad2 c m := by
  by_contra h
  rw [Vbar_eq_zero hc hm (not_lt.1 h)] at hx
  exact lt_irrefl _ hx

theorem continuousOn_kap {c m : ℝ} (hc : 0 < c) (hm : 0 < m) :
    ContinuousOn (kap c m) (Set.Ioi 0) := by
  have hR := rad2_pos hc hm
  show ContinuousOn (fun s => c / 4 * (s - rad2 c m) - m / (4 * Real.pi) *
    Real.log (s / rad2 c m)) (Set.Ioi 0)
  exact ContinuousOn.sub (by fun_prop)
    (continuousOn_const.mul ((continuousOn_id.div_const _).log fun s hs => (div_pos hs hR).ne'))

theorem continuousOn_Vbar {c m : ℝ} (hc : 0 < c) (hm : 0 < m) :
    ContinuousOn (Vbar c m) {x | x ≠ 0} := by
  have hR := rad2_pos hc hm
  have hg : Continuous fun x : Rd 2 => min (‖x‖ ^ 2) (rad2 c m) := by fun_prop
  exact (continuousOn_kap hc hm).comp hg.continuousOn fun x hx =>
    lt_min (pow_pos (norm_pos_iff.2 hx) 2) hR

theorem contDiffAt_kap {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ 2 (kap c m) s := by
  have hR := rad2_pos hc hm
  have hlog : ContDiffAt ℝ 2 (fun s => Real.log (s / rad2 c m)) s :=
    (Real.contDiffAt_log.2 (div_pos hs hR).ne').comp s (contDiffAt_id.div_const _)
  show ContDiffAt ℝ 2 (fun s => c / 4 * (s - rad2 c m) - m / (4 * Real.pi) *
    Real.log (s / rad2 c m)) s
  exact (contDiffAt_const.mul (contDiffAt_id.sub contDiffAt_const)).sub (contDiffAt_const.mul hlog)

theorem contDiffAt_Vsm {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {x : Rd 2} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (Vsm c m) x :=
  (contDiffAt_kap hc hm (pow_pos (norm_pos_iff.2 hx) 2)).comp x (contDiff_norm_sq ℝ).contDiffAt

theorem hasDerivAt_kap {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (kap c m) (c / 4 - m / (4 * Real.pi) * s⁻¹) s := by
  have hR := rad2_pos hc hm
  have hR' := hR.ne'
  have hs' := hs.ne'
  have h1 : HasDerivAt (fun s => Real.log (s / rad2 c m)) s⁻¹ s :=
    (((hasDerivAt_id' s).div_const (rad2 c m)).log (div_pos hs hR).ne').congr_deriv
      (by field_simp)
  have h2 := ((hasDerivAt_id' s).sub_const (rad2 c m)).const_mul (c / 4)
  exact (h2.sub (h1.const_mul (m / (4 * Real.pi)))).congr_deriv (by ring)

theorem hasDerivAt_kap1 {c m : ℝ} {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => c / 4 - m / (4 * Real.pi) * s⁻¹) (m / (4 * Real.pi) * (s ^ 2)⁻¹) s :=
  ((hasDerivAt_const s (c / 4)).sub ((hasDerivAt_inv hs.ne').const_mul (m / (4 * Real.pi)))).congr_deriv
    (by ring)

/-- **`ΔV = c`** off the origin. -/
theorem trace_hessian_Vsm {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {x : Rd 2} (hx : x ≠ 0) :
    (hessian (Vsm c m) x).trace = c := by
  have hs : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
  have h := radial_trace_hessian_loc (K := kap c m)
    (K1 := fun s => c / 4 - m / (4 * Real.pi) * s⁻¹)
    (K2 := fun s => m / (4 * Real.pi) * (s ^ 2)⁻¹) (a := 0)
    (fun s hs => hasDerivAt_kap hc hm hs) (fun s hs => hasDerivAt_kap1 hs) hs
  show (hessian (fun z => kap c m (‖z‖ ^ 2)) x).trace = c
  rw [h]
  show 4 * (‖x‖ ^ 2 * (m / (4 * Real.pi) * ((‖x‖ ^ 2) ^ 2)⁻¹) +
    (c / 4 - m / (4 * Real.pi) * (‖x‖ ^ 2)⁻¹)) = c
  generalize ‖x‖ ^ 2 = s at hs ⊢
  have e : s * (m / (4 * Real.pi) * (s ^ 2)⁻¹) = m / (4 * Real.pi) * s⁻¹ := by
    rw [mul_left_comm, pow_two, mul_inv, ← mul_assoc s, mul_inv_cancel₀ hs.ne', one_mul]
  rw [e]
  ring

/-- **`ΔV_m ≥ c`** in the viscosity sense where `V_m > 0`. -/
theorem visc_sub_Vbar {c m : ℝ} (hc : 0 < c) (hm : 0 < m) :
    ViscFromAboveLE (fun M => c - M.trace) {x : Rd 2 | x ≠ 0 ∧ ‖x‖ ^ 2 < rad2 c m}
      (Vbar c m) := by
  intro x hx φ hφ hmax
  have hx0 : x ≠ 0 := hx.1
  have hopen : IsOpen {y : Rd 2 | ‖y‖ ^ 2 < rad2 c m} :=
    isOpen_lt (by fun_prop) continuous_const
  have hev : ∀ᶠ y in 𝓝 x, Vbar c m y = Vsm c m y := by
    filter_upwards [hopen.mem_nhds hx.2] with y hy
    exact Vbar_eq_Vsm (le_of_lt hy)
  have hx' : Vbar c m x = Vsm c m x := hev.self_of_nhds
  have hmin : IsLocalMin (fun y => φ y - Vsm c m y) x := by
    filter_upwards [hmax, hev] with y hy hye
    have h1 : Vbar c m y - φ y ≤ Vbar c m x - φ x := hy
    show φ x - Vsm c m x ≤ φ y - Vsm c m y
    linarith
  have hV := contDiffAt_Vsm hc hm hx0
  have h := trace_hessian_nonneg_of_isLocalMin (hφ.sub hV) hmin
  rw [hessian_sub_of_contDiffAt hφ hV, Matrix.trace_sub, trace_hessian_Vsm hc hm hx0] at h
  show c - (hessian φ x).trace ≤ 0
  linarith

end SingleSourceD2

end RandomSandpile

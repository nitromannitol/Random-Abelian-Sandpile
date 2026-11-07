import RandomSandpile.Proofs.Sec9.SingleSourceD2ViscWeak

/-!
# Theorem 9.2 in dimension two: `Δu ≥ -C` in distributions

`distLaplace_ge`: if `u ∈ C(V)` satisfies `Δu ≥ -C` in the viscosity sense on the open set `V`,
then `∫ u Δφ ≥ -C ∫ φ` for every nonnegative `φ ∈ C²_c(V)`, from Alexandrov's
theorem. For the sup-convolution `u^δ` (`distLaplace_ge_supConv`): `c = u^δ + |x|²/(2δ)` is convex,
its second differences are nonnegative and converge at Alexandrov points to `tr D²c ≥ 2/δ - C`;
Fatou's lemma and the summation by parts give `∫ u^δ Δφ + (2/δ) ∫ φ ≥ (2/δ - C) ∫ φ`. Then
`u^δ → u` uniformly on a neighbourhood of the support of `φ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric LatticeProb LatticeProb.Sandpile
open scoped ENNReal

namespace RandomSandpile

namespace SingleSourceD2

theorem continuous_sd {f : Rd 2 → ℝ} (hf : Continuous f) (t : ℝ) : Continuous (sd t f) := by
  unfold sd
  simp only [Fin.sum_univ_two]
  fun_prop

theorem sd_add (t : ℝ) (f g : Rd 2 → ℝ) (x : Rd 2) :
    sd t (fun y => f y + g y) x = sd t f x + sd t g x := by
  simp only [sd, Fin.sum_univ_two]
  ring

/-- The trace bound at an Alexandrov point of the semiconvex `u^δ + |x|²/(2δ)`. -/
theorem trace_ge_of_supConv {S U : Set (Rd 2)} (hS : IsCompact S) (hU : IsOpen U) (hUS : U ⊆ S)
    (hne : S.Nonempty) {δ C : ℝ} {u : Rd 2 → ℝ} (hu : ContinuousOn u S)
    (hvisc : ViscFromAboveGE (fun X => X.trace + C) U u) {x p : Rd 2}
    {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : X.IsSymm)
    (hT : HasSecondOrderTaylorAt (fun y => supConv S δ u y + ‖y‖ ^ 2 / (2 * δ)) x p X)
    (hmax : ∀ y ∈ S, supConv S δ u x = u y - ‖x - y‖ ^ 2 / (2 * δ) → y ∈ U) :
    2 * δ⁻¹ - C ≤ X.trace := by
  have hT' := taylor_sub_sq_norm δ hT
  have e : (fun y => supConv S δ u y + ‖y‖ ^ 2 / (2 * δ) - ‖y‖ ^ 2 / (2 * δ)) =
      supConv S δ u := by
    funext y; ring
  rw [e] at hT'
  obtain ⟨y, hyS, hy⟩ := (supConv_spec hS hne δ hu x).2
  have hyU := hmax y hyS hy
  have hXs : (X + (-δ⁻¹) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm :=
    hX.add (Matrix.isSymm_one.smul _)
  have h := trace_add_nonneg_of_taylor hXs hT' fun φ hφ hmax' =>
    ViscFromAboveGE.supConv_at hS hU hUS hu hvisc hyU hy φ hφ hmax'
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at h
  push_cast at h
  linarith

/-- **`Δu^δ ≥ -C` in distributions** for the sup-convolution. -/
theorem distLaplace_ge_supConv (hA : AlexandrovStmt) {S U : Set (Rd 2)} (hS : IsCompact S)
    (hU : IsOpen U) (hUS : U ⊆ S) (hne : S.Nonempty) {δ C : ℝ} (hδ : 0 < δ) {u : Rd 2 → ℝ}
    (hu : ContinuousOn u S) (hvisc : ViscFromAboveGE (fun X => X.trace + C) U u)
    {φ : Rd 2 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hmax : ∀ x ∈ tsupport φ, ∀ y ∈ S, supConv S δ u x = u y - ‖x - y‖ ^ 2 / (2 * δ) → y ∈ U) :
    -C * ∫ x, φ x ≤ ∫ x, supConv S δ u x * Matrix.trace (hessian φ x) := by
  set uδ := supConv S δ u
  set c : Rd 2 → ℝ := fun y => uδ y + ‖y‖ ^ 2 / (2 * δ)
  have huδc : Continuous uδ := OpenComparison.continuous_supConv hS hu δ
  have hcc : Continuous c := huδc.add (by fun_prop)
  have hconv : ConvexOn ℝ Set.univ c := convexOn_supConv_add hS hne hδ hu
  have hφcont : Continuous φ := hφ.continuous
  set t : ℕ → ℝ := fun n => (n : ℝ) + 1
  have htt : Tendsto t atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  -- `a_n = ∫ sd_{t_n} c · φ`
  set a : ℕ → ℝ := fun n => ∫ x, sd (t n) c x * φ x with ha
  have hsdc : ∀ n x, sd (t n) c x = sd (t n) uδ x + 2 / δ := fun n x => by
    rw [show c = fun y => uδ y + ‖y‖ ^ 2 / (2 * δ) from rfl, sd_add,
      sd_sq_norm (show (n : ℝ) + 1 ≠ 0 by positivity)]
  have hIφ : Integrable φ := hφcont.integrable_of_hasCompactSupport hφc
  have hIsd : ∀ n, Integrable (fun x => sd (t n) uδ x * φ x) := fun n =>
    ((continuous_sd huδc _).mul hφcont).integrable_of_hasCompactSupport hφc.mul_left
  have ha_eq : ∀ n, a n = (∫ x, sd (t n) uδ x * φ x) + 2 / δ * ∫ x, φ x := by
    intro n
    simp only [ha, hsdc, add_mul]
    rw [integral_add (hIsd n) (hIφ.const_mul _), integral_const_mul]
  set L : ℝ := (∫ x, uδ x * Matrix.trace (hessian φ x)) + 2 / δ * ∫ x, φ x with hL
  have hlim : Tendsto a atTop (𝓝 L) := by
    have h := (tendsto_integral_sd_cont huδc hφ hφc).comp htt
    have h2 := h.add_const (2 / δ * ∫ x, φ x)
    refine h2.congr fun n => ?_
    exact (congrArg (· + 2 / δ * ∫ x, φ x) (integral_sd_eq huδc hφcont hφc (t n))).trans
      (ha_eq n).symm
  have ha0 : ∀ n, 0 ≤ a n := fun n =>
    integral_nonneg fun x => mul_nonneg (sd_nonneg_of_convexOn hconv _ x) (hφ0 x)
  have hL0 : 0 ≤ L := ge_of_tendsto' hlim ha0
  -- Fatou
  have hFatou : ENNReal.ofReal ((2 / δ - C) * ∫ x, φ x) ≤ ENNReal.ofReal L := by
    by_cases hlam : 2 / δ - C ≤ 0
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hlam
        (integral_nonneg hφ0))]
      exact zero_le
    have hlam' : 0 ≤ 2 / δ - C := (not_le.mp hlam).le
    set g : ℕ → Rd 2 → ℝ≥0∞ := fun n x => ENNReal.ofReal (sd (t n) c x * φ x) with hg
    have hgm : ∀ n, Measurable (g n) := fun n =>
      ENNReal.measurable_ofReal.comp ((continuous_sd hcc _).mul hφcont).measurable
    have hIc : ∀ n, Integrable (fun x => sd (t n) c x * φ x) := fun n =>
      ((continuous_sd hcc _).mul hφcont).integrable_of_hasCompactSupport hφc.mul_left
    have hgint : ∀ n, ∫⁻ x, g n x = ENNReal.ofReal (a n) := fun n =>
      (ofReal_integral_eq_lintegral_ofReal (hIc n) (ae_of_all _ fun x =>
        mul_nonneg (sd_nonneg_of_convexOn hconv _ x) (hφ0 x))).symm
    have hpt : ∀ᵐ x ∂volume, ENNReal.ofReal ((2 / δ - C) * φ x) ≤
        liminf (fun n => g n x) atTop := by
      filter_upwards [hA 2 c hconv] with x hx
      by_cases hxK : x ∈ tsupport φ
      · obtain ⟨p, X, hXs, hT⟩ := hx
        have htr := trace_ge_of_supConv hS hU hUS hne hu hvisc hXs hT (hmax x hxK)
        have h1 : Tendsto (fun n => g n x) atTop (𝓝 (ENNReal.ofReal (X.trace * φ x))) :=
          ENNReal.tendsto_ofReal (((tendsto_sd_of_taylor hT).comp htt).mul_const (φ x))
        rw [h1.liminf_eq]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (hφ0 x))
        rw [div_eq_mul_inv]
        linarith
      · rw [image_eq_zero_of_notMem_tsupport hxK, mul_zero, ENNReal.ofReal_zero]
        exact zero_le
    calc ENNReal.ofReal ((2 / δ - C) * ∫ x, φ x)
        = ∫⁻ x, ENNReal.ofReal ((2 / δ - C) * φ x) := by
          rw [← integral_const_mul]
          exact ofReal_integral_eq_lintegral_ofReal (hIφ.const_mul _)
            (ae_of_all _ fun x => mul_nonneg hlam' (hφ0 x))
      _ ≤ ∫⁻ x, liminf (fun n => g n x) atTop := lintegral_mono_ae hpt
      _ ≤ liminf (fun n => ∫⁻ x, g n x) atTop := lintegral_liminf_le hgm
      _ = liminf (fun n => ENNReal.ofReal (a n)) atTop := by simp only [hgint]
      _ = ENNReal.ofReal L := (ENNReal.tendsto_ofReal hlim).liminf_eq
  have hφint : 0 ≤ ∫ x, φ x := integral_nonneg hφ0
  by_cases hlam : 2 / δ - C ≤ 0
  · have : (2 / δ) * ∫ x, φ x ≤ C * ∫ x, φ x := mul_le_mul_of_nonneg_right (by linarith) hφint
    show -C * ∫ x, φ x ≤ ∫ x, uδ x * Matrix.trace (hessian φ x)
    linarith
  · have h := (ENNReal.ofReal_le_ofReal_iff hL0).1 hFatou
    show -C * ∫ x, φ x ≤ ∫ x, uδ x * Matrix.trace (hessian φ x)
    nlinarith

/-- **`Δu ≥ -C` in distributions** from the viscosity inequality. -/
theorem distLaplace_ge (hA : AlexandrovStmt) {V : Set (Rd 2)} (hV : IsOpen V) {C : ℝ}
    {u : Rd 2 → ℝ} (hu : ContinuousOn u V) (hvisc : ViscFromAboveGE (fun X => X.trace + C) V u)
    {φ : Rd 2 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφV : tsupport φ ⊆ V)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    -C * ∫ x, φ x ≤ ∫ x, u x * Matrix.trace (hessian φ x) := by
  by_cases hK : (tsupport φ).Nonempty
  swap
  · have h0 : ∀ x, φ x = 0 := fun x =>
      image_eq_zero_of_notMem_tsupport (fun hx => hK ⟨x, hx⟩)
    have hΔ0 : ∀ x, Matrix.trace (hessian φ x) = 0 := fun x => by
      rw [PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport (fun hx => hK ⟨x, hx⟩),
        Matrix.trace_zero]
    simp [h0, hΔ0]
  obtain ⟨ρ, hρ, hρV⟩ := IsCompact.exists_cthickening_subset_open hφc hV hφV
  set S := cthickening ρ (tsupport φ)
  set U := thickening ρ (tsupport φ)
  have hS : IsCompact S := hφc.cthickening
  have hU : IsOpen U := isOpen_thickening
  have hUS : U ⊆ S := thickening_subset_cthickening _ _
  have hKS : tsupport φ ⊆ S := self_subset_cthickening _
  have hne : S.Nonempty := hK.mono hKS
  have huS : ContinuousOn u S := hu.mono hρV
  have hviscU : ViscFromAboveGE (fun X => X.trace + C) U u := fun x hx =>
    hvisc x (hρV (hUS hx))
  have hIu : Integrable (fun x => u x * Matrix.trace (hessian φ x)) :=
    PegdenSmartAdapter.integrable_mul_trace_hessian hV hu hφ hφc hφV
  have hItr : Integrable (fun x => Matrix.trace (hessian φ x)) := by
    simpa using PegdenSmartAdapter.integrable_mul_trace_hessian isOpen_univ
      (continuousOn_const (c := (1 : ℝ))) hφ hφc (Set.subset_univ _)
  have key : ∀ θ : ℝ, 0 < θ → -C * (∫ x, φ x) - θ * ∫ x, |Matrix.trace (hessian φ x)| ≤
      ∫ x, u x * Matrix.trace (hessian φ x) := by
    intro θ hθ
    obtain ⟨δ₀, hδ₀, hδu⟩ := OpenComparison.supConv_uniform hS huS hθ hρ
    have hmax : ∀ x ∈ tsupport φ, ∀ y ∈ S,
        supConv S δ₀ u x = u y - ‖x - y‖ ^ 2 / (2 * δ₀) → y ∈ U := by
      intro x hx y hy hxy
      have h := (hδu δ₀ hδ₀ le_rfl x (hKS hx) y hy hxy).1
      exact Metric.mem_thickening_iff.2 ⟨x, hx, by rw [dist_comm, dist_eq_norm]; exact h⟩
    have hge := distLaplace_ge_supConv hA hS hU hUS hne hδ₀ huS hviscU hφ hφc hφ0 hmax
    have hclose : ∀ x ∈ S, supConv S δ₀ u x - u x ≤ θ := by
      intro x hx
      obtain ⟨y, hyS, hy⟩ := (supConv_spec hS hne δ₀ huS x).2
      have h := (hδu δ₀ hδ₀ le_rfl x hx y hyS hy).2
      have hsq : 0 ≤ ‖x - y‖ ^ 2 / (2 * δ₀) := by positivity
      rw [hy]
      linarith
    have hge0 : ∀ x ∈ S, u x ≤ supConv S δ₀ u x := fun x hx => le_supConv hS huS hx
    have huδc : Continuous (supConv S δ₀ u) := OpenComparison.continuous_supConv hS huS δ₀
    have hIuδ : Integrable (fun x => supConv S δ₀ u x * Matrix.trace (hessian φ x)) :=
      PegdenSmartAdapter.integrable_mul_trace_hessian isOpen_univ huδc.continuousOn hφ hφc
        (Set.subset_univ _)
    have hdiff : (∫ x, supConv S δ₀ u x * Matrix.trace (hessian φ x)) -
        ∫ x, u x * Matrix.trace (hessian φ x) ≤ θ * ∫ x, |Matrix.trace (hessian φ x)| := by
      rw [← integral_sub hIuδ hIu, ← integral_const_mul]
      refine integral_mono (hIuδ.sub hIu) (hItr.abs.const_mul θ) fun x => ?_
      show supConv S δ₀ u x * Matrix.trace (hessian φ x) - u x * Matrix.trace (hessian φ x) ≤
        θ * |Matrix.trace (hessian φ x)|
      by_cases hx : x ∈ S
      · have h1 := hclose x hx
        have h2 := hge0 x hx
        have h3 := le_abs_self (Matrix.trace (hessian φ x))
        have h4 := abs_nonneg (Matrix.trace (hessian φ x))
        have e : supConv S δ₀ u x * Matrix.trace (hessian φ x) -
            u x * Matrix.trace (hessian φ x) =
            (supConv S δ₀ u x - u x) * Matrix.trace (hessian φ x) := by ring
        rw [e]
        calc (supConv S δ₀ u x - u x) * Matrix.trace (hessian φ x)
            ≤ (supConv S δ₀ u x - u x) * |Matrix.trace (hessian φ x)| :=
              mul_le_mul_of_nonneg_left h3 (by linarith)
          _ ≤ θ * |Matrix.trace (hessian φ x)| := mul_le_mul_of_nonneg_right h1 h4
      · have hxK : x ∉ tsupport φ := fun h => hx (hKS h)
        rw [PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport hxK]
        simp
    linarith
  by_contra hlt
  have hlt' : ∫ x, u x * Matrix.trace (hessian φ x) < -C * ∫ x, φ x := not_le.mp hlt
  have hA0 : 0 ≤ ∫ x, |Matrix.trace (hessian φ x)| := integral_nonneg fun x => abs_nonneg _
  set g := -C * (∫ x, φ x) - ∫ x, u x * Matrix.trace (hessian φ x) with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  have hA1 : (0 : ℝ) < 2 * ((∫ x, |Matrix.trace (hessian φ x)|) + 1) := by linarith
  have h := key (g / (2 * ((∫ x, |Matrix.trace (hessian φ x)|) + 1))) (div_pos hg0 hA1)
  have h2 : g / (2 * ((∫ x, |Matrix.trace (hessian φ x)|) + 1)) *
      ∫ x, |Matrix.trace (hessian φ x)| ≤ g / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hA1 (by norm_num)]
    nlinarith
  linarith

end SingleSourceD2

end RandomSandpile

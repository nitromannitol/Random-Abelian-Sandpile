import RandomSandpile.Proofs.Sec9.SingleSourceD2ViscWeakGe

/-!
# Theorem 9.2 in dimension two: from distributional Laplacian bounds to a weak Laplacian (part 3)

`viscLaplaceWeak : AlexandrovStmt → ViscLaplaceWeakStmt`. By `distLaplace_ge` (for `u` and `-u`),
viscosity bounds `-C ≤ Δu ≤ C` give `-C ∫ φ ≤ ∫ u Δφ ≤ C ∫ φ` for nonnegative test functions.
Near `a ∈ V`, with `ũ = χ' u` a continuous extension and normalized bumps `ρ_n` of radius `→ 0`,
the functions `m_n(x) = ∫ ũ(y) Δρ_n(y - x) dy` (the functional evaluated at the translated bump
`ρ_n(· - x)`) are bounded by `C` near `a`, and `∫ m_n ψ → ∫ ũ Δψ` (Fubini, Green's identity, and
uniform convergence of the mollified `Δψ`). The weak-* representation in `L^∞`
(`weakStarRepresentation`) then produces the bounded weak Laplacian, as in
`Proofs/Sec9/SingleSourceD2WeakLap.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace SingleSourceD2

/-! ### Calculus -/

/-- The Hessian of a reflection `z ↦ φ(c - z)`. -/
theorem hessian_comp_sub_left {φ : Rd 2 → ℝ} (hφ : ContDiff ℝ 2 φ) (c y : Rd 2) :
    hessian (fun z => φ (c - z)) y = hessian φ (c - y) := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hD1 : Differentiable ℝ (fderiv ℝ φ) := hD.differentiable (by norm_num)
  have hsub : ∀ z : Rd 2, HasFDerivAt (fun z : Rd 2 => c - z)
      (-ContinuousLinearMap.id ℝ (Rd 2)) z := fun z => (hasFDerivAt_id z).const_sub c
  have h1 : fderiv ℝ (fun z => φ (c - z)) = fun z => -fderiv ℝ φ (c - z) := by
    funext z
    exact (((hφ1 (c - z)).hasFDerivAt.comp z (hsub z)).fderiv).trans (by ext v; simp)
  have h2 : fderiv ℝ (fun z => -fderiv ℝ φ (c - z)) y = fderiv ℝ (fderiv ℝ φ) (c - y) :=
    ((((hD1 (c - y)).hasFDerivAt.comp y (hsub y)).neg).fderiv).trans (by ext v w; simp)
  ext i j
  rw [hessian_apply, hessian_apply, h1, h2]

theorem hessian_comp_sub_right (φ : Rd 2 → ℝ) (x y : Rd 2) :
    hessian (fun z => φ (z - x)) y = hessian φ (y - x) := by
  simp only [sub_eq_add_neg]
  exact hessian_comp_add_right φ (-x) y

/-- A function continuous on `V` times a continuous cutoff supported in `V` is continuous. -/
theorem continuous_mul_of_tsupport {V : Set (Rd 2)} (hV : IsOpen V) {u χ : Rd 2 → ℝ}
    (hu : ContinuousOn u V) (hχ : Continuous χ) (hχV : tsupport χ ⊆ V) :
    Continuous (fun x => χ x * u x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ V
  · exact hχ.continuousAt.mul (hu.continuousAt (hV.mem_nhds hx))
  · have hxs : x ∉ tsupport χ := fun h => hx (hχV h)
    have hev : (fun x => χ x * u x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxs] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact continuousAt_const.congr hev.symm

/-! ### Mollified Laplacians -/

theorem bump_contDiff (β : ContDiffBump (0 : Rd 2)) : ContDiff ℝ 2 (β.normed volume) :=
  (β.contDiff_normed (n := ⊤)).of_le (WithTop.coe_le_coe.2 le_top)

/-- The translated normalized bump. -/
theorem translate_bump_props (β : ContDiffBump (0 : Rd 2)) (x : Rd 2) :
    ContDiff ℝ 2 (fun y => β.normed volume (y - x)) ∧
      HasCompactSupport (fun y => β.normed volume (y - x)) ∧
      tsupport (fun y => β.normed volume (y - x)) ⊆ closedBall x β.rOut ∧
      (∀ y, 0 ≤ β.normed volume (y - x)) ∧ ∫ y, β.normed volume (y - x) = 1 := by
  refine ⟨(bump_contDiff β).comp (contDiff_id.sub contDiff_const),
    β.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subRight x), ?_,
    fun y => β.nonneg_normed _, ?_⟩
  · refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    have h : y - x ∈ Function.support (β.normed volume) := hy
    rw [β.support_normed_eq, mem_ball, dist_zero_right] at h
    rw [mem_closedBall, dist_eq_norm]
    exact h.le
  · rw [integral_sub_right_eq_self (μ := volume) (fun y => β.normed volume y) x]
    exact β.integral_normed

/-- `m(x) = ∫ ũ(y) Δρ(y - x) dy` is the functional at the translated bump. -/
theorem mollified_eq (β : ContDiffBump (0 : Rd 2)) (f : Rd 2 → ℝ) (x : Rd 2) :
    ∫ y, f y * Matrix.trace (hessian (β.normed volume) (y - x)) =
      ∫ y, f y * Matrix.trace (hessian (fun z => β.normed volume (z - x)) y) := by
  simp only [hessian_comp_sub_right]

theorem measurable_mollified (β : ContDiffBump (0 : Rd 2)) {f : Rd 2 → ℝ} (hf : Continuous f) :
    Measurable (fun x => ∫ y, f y * Matrix.trace (hessian (β.normed volume) (y - x))) := by
  have hg := PegdenSmartAdapter.continuous_trace_hessian (bump_contDiff β)
  have hF : Continuous (fun p : Rd 2 × Rd 2 =>
      f p.2 * Matrix.trace (hessian (β.normed volume) (p.2 - p.1))) :=
    (hf.comp continuous_snd).mul (hg.comp (continuous_snd.sub continuous_fst))
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- Fubini and Green's identity: `∫ m(x) ψ(x) dx = ∫ ũ(y) (ρ * Δψ)(y) dy`. -/
theorem integral_mollified_mul (β : ContDiffBump (0 : Rd 2)) {f : Rd 2 → ℝ} (hf : Continuous f)
    {ψ : Rd 2 → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, (∫ y, f y * Matrix.trace (hessian (β.normed volume) (y - x))) * ψ x =
      ∫ y, f y * ∫ x, β.normed volume (y - x) * Matrix.trace (hessian ψ x) := by
  set ρ := β.normed volume with hρdef
  have hρ : ContDiff ℝ 2 ρ := bump_contDiff β
  have hg := PegdenSmartAdapter.continuous_trace_hessian hρ
  have hψcont : Continuous ψ := hψ.continuous
  set K := tsupport ψ
  have hK : IsCompact K := hψc
  set K' := cthickening β.rOut K
  have hK' : IsCompact K' := hψc.cthickening
  have hρK : ∀ z, Matrix.trace (hessian ρ z) ≠ 0 → ‖z‖ ≤ β.rOut := by
    intro z hz
    by_contra hlt
    have hz' : z ∉ tsupport ρ := by
      rw [hρdef, β.tsupport_normed_eq, mem_closedBall, dist_zero_right]
      exact hlt
    exact hz (by rw [PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport hz',
      Matrix.trace_zero])
  have hint : ∀ x, (∫ y, f y * Matrix.trace (hessian ρ (y - x))) * ψ x =
      ∫ y, f y * Matrix.trace (hessian ρ (y - x)) * ψ x := fun x =>
    (integral_mul_const (ψ x) _).symm
  simp only [hint]
  rw [integral_integral_swap_of_hasCompactSupport]
  · refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show ∫ x, f y * Matrix.trace (hessian ρ (y - x)) * ψ x =
      f y * ∫ x, ρ (y - x) * Matrix.trace (hessian ψ x)
    have hgreen := integral_mul_trace_hessian_eq (f := fun z => ρ (y - z))
      (hρ.comp (contDiff_const.sub contDiff_id)) hψ hψc
    simp only [hessian_comp_sub_left hρ] at hgreen
    rw [hgreen, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  · exact ((hf.comp continuous_snd).mul (hg.comp (continuous_snd.sub continuous_fst))).mul
      (hψcont.comp continuous_fst)
  · refine HasCompactSupport.intro (hK.prod hK') fun p hp => ?_
    by_contra hne
    apply hp
    have h1 : ψ p.1 ≠ 0 := fun h => hne (by simp [Function.uncurry, h])
    have h2 : Matrix.trace (hessian ρ (p.2 - p.1)) ≠ 0 := fun h => hne (by
      simp [Function.uncurry, h])
    have hp1 : p.1 ∈ K := subset_tsupport ψ h1
    refine ⟨hp1, Metric.mem_cthickening_of_dist_le p.2 p.1 β.rOut K hp1 ?_⟩
    rw [dist_eq_norm]
    exact hρK _ h2

/-- The mollifications of `Δψ` converge pointwise as the radius tends to `0`. -/
theorem tendsto_mollify_at {ψ : Rd 2 → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    {β : ℕ → ContDiffBump (0 : Rd 2)} (hβ : Tendsto (fun n => (β n).rOut) atTop (𝓝 0)) (y : Rd 2) :
    Tendsto (fun n => ∫ x, (β n).normed volume (y - x) * Matrix.trace (hessian ψ x)) atTop
      (𝓝 (Matrix.trace (hessian ψ y))) := by
  have hΔc := PegdenSmartAdapter.continuous_trace_hessian hψ
  have hΔcs : HasCompactSupport fun x => Matrix.trace (hessian ψ x) :=
    HasCompactSupport.intro' hψc (isClosed_tsupport ψ) fun x hx => by
      rw [PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport hx, Matrix.trace_zero]
  have hUC := hΔcs.uniformContinuous_of_continuous hΔc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1 hUC (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hβ δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hrn : (β n).rOut < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (β n).rOut_pos] at this
    exact this
  have hρc : Continuous fun x => (β n).normed volume (y - x) :=
    (β n).continuous_normed.comp (continuous_const.sub continuous_id)
  have hρcs : HasCompactSupport fun x => (β n).normed volume (y - x) :=
    (β n).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft y)
  have hρ1 : ∫ x, (β n).normed volume (y - x) = 1 := by
    rw [integral_sub_left_eq_self (μ := volume) (fun z => (β n).normed volume z) y]
    exact (β n).integral_normed
  have hIρ : Integrable (fun x => (β n).normed volume (y - x)) :=
    hρc.integrable_of_hasCompactSupport hρcs
  have hI1 : Integrable (fun x => (β n).normed volume (y - x) * Matrix.trace (hessian ψ x)) :=
    (hρc.mul hΔc).integrable_of_hasCompactSupport hΔcs.mul_left
  have hI2 : Integrable (fun x => (β n).normed volume (y - x) * Matrix.trace (hessian ψ y)) :=
    hIρ.mul_const _
  have hI3 : Integrable (fun x => |(β n).normed volume (y - x) *
      (Matrix.trace (hessian ψ x) - Matrix.trace (hessian ψ y))|) :=
    ((hρc.mul (hΔc.sub continuous_const)).abs).integrable_of_hasCompactSupport
      (hρcs.mul_right.comp_left (g := fun t : ℝ => |t|) abs_zero)
  have e : ∫ x, (β n).normed volume (y - x) *
      (Matrix.trace (hessian ψ x) - Matrix.trace (hessian ψ y)) =
      (∫ x, (β n).normed volume (y - x) * Matrix.trace (hessian ψ x)) -
        Matrix.trace (hessian ψ y) := by
    have h := integral_sub hI1 hI2
    rw [integral_mul_const, hρ1, one_mul] at h
    rw [← h]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [Real.dist_eq, ← e]
  calc |∫ x, (β n).normed volume (y - x) *
        (Matrix.trace (hessian ψ x) - Matrix.trace (hessian ψ y))|
      ≤ ∫ x, |(β n).normed volume (y - x) *
          (Matrix.trace (hessian ψ x) - Matrix.trace (hessian ψ y))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, (β n).normed volume (y - x) * (ε / 2) := by
        refine integral_mono hI3 (hIρ.mul_const _) fun x => ?_
        show |(β n).normed volume (y - x) *
          (Matrix.trace (hessian ψ x) - Matrix.trace (hessian ψ y))| ≤
          (β n).normed volume (y - x) * (ε / 2)
        rw [abs_mul, abs_of_nonneg ((β n).nonneg_normed _)]
        by_cases hx : (β n).normed volume (y - x) = 0
        · rw [hx, zero_mul, zero_mul]
        · have hmem : y - x ∈ Function.support ((β n).normed volume) := hx
          rw [(β n).support_normed_eq, mem_ball, dist_zero_right] at hmem
          have hd : dist x y < δ := by
            rw [dist_eq_norm, ← norm_neg, neg_sub]
            linarith
          have h := hδu hd
          rw [Real.dist_eq] at h
          exact mul_le_mul_of_nonneg_left h.le ((β n).nonneg_normed _)
    _ = ε / 2 := by rw [integral_mul_const, hρ1, one_mul]
    _ < ε := half_lt_self hε

/-- `∫ m_n ψ → ∫ ũ Δψ` as the bump radius tends to `0`. -/
theorem tendsto_integral_mollified {f : Rd 2 → ℝ} (hf : Continuous f) {ψ : Rd 2 → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) {β : ℕ → ContDiffBump (0 : Rd 2)}
    (hβ : Tendsto (fun n => (β n).rOut) atTop (𝓝 0)) (hβ1 : ∀ n, (β n).rOut ≤ 1) :
    Tendsto (fun n => ∫ x, (∫ y, f y * Matrix.trace (hessian ((β n).normed volume) (y - x))) *
      ψ x) atTop (𝓝 (∫ y, f y * Matrix.trace (hessian ψ y))) := by
  refine Tendsto.congr (fun n => (integral_mollified_mul (β n) hf hψ hψc).symm) ?_
  have hΔc := PegdenSmartAdapter.continuous_trace_hessian hψ
  have hΔcs : HasCompactSupport fun x => Matrix.trace (hessian ψ x) :=
    HasCompactSupport.intro' hψc (isClosed_tsupport ψ) fun x hx => by
      rw [PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport hx, Matrix.trace_zero]
  obtain ⟨MΔ, hMΔ⟩ := hΔc.bounded_above_of_compact_support hΔcs
  set K' := cthickening 1 (tsupport ψ)
  have hK' : IsCompact K' := hψc.cthickening
  obtain ⟨Mf, hMf⟩ := hK'.exists_bound_of_continuousOn hf.continuousOn
  have hA0 : ∀ n, ∀ y, y ∉ K' →
      ∫ x, (β n).normed volume (y - x) * Matrix.trace (hessian ψ x) = 0 := by
    intro n y hy
    refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ tsupport ψ
    · have hne : (β n).normed volume (y - x) = 0 := by
        by_contra hne
        have hmem : y - x ∈ Function.support ((β n).normed volume) := hne
        rw [(β n).support_normed_eq, mem_ball, dist_zero_right] at hmem
        exact hy (Metric.mem_cthickening_of_dist_le y x 1 _ hx
          (by rw [dist_eq_norm]; linarith [hβ1 n]))
      show (β n).normed volume (y - x) * Matrix.trace (hessian ψ x) = 0
      rw [hne, zero_mul]
    · show (β n).normed volume (y - x) * Matrix.trace (hessian ψ x) = 0
      rw [PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport hx, Matrix.trace_zero, mul_zero]
  have hAb : ∀ n, ∀ y, |∫ x, (β n).normed volume (y - x) * Matrix.trace (hessian ψ x)| ≤ MΔ := by
    intro n y
    have hρc : Continuous fun x => (β n).normed volume (y - x) :=
      (β n).continuous_normed.comp (continuous_const.sub continuous_id)
    have hρcs : HasCompactSupport fun x => (β n).normed volume (y - x) :=
      (β n).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft y)
    have hρ1 : ∫ x, (β n).normed volume (y - x) = 1 := by
      rw [integral_sub_left_eq_self (μ := volume) (fun z => (β n).normed volume z) y]
      exact (β n).integral_normed
    have hI3 : Integrable (fun x => |(β n).normed volume (y - x) *
        Matrix.trace (hessian ψ x)|) :=
      ((hρc.mul hΔc).abs).integrable_of_hasCompactSupport
        (hρcs.mul_right.comp_left (g := fun t : ℝ => |t|) abs_zero)
    calc |∫ x, (β n).normed volume (y - x) * Matrix.trace (hessian ψ x)|
        ≤ ∫ x, |(β n).normed volume (y - x) * Matrix.trace (hessian ψ x)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, (β n).normed volume (y - x) * MΔ := by
          refine integral_mono hI3 ((hρc.integrable_of_hasCompactSupport hρcs).mul_const _)
            fun x => ?_
          show |(β n).normed volume (y - x) * Matrix.trace (hessian ψ x)| ≤
            (β n).normed volume (y - x) * MΔ
          rw [abs_mul, abs_of_nonneg ((β n).nonneg_normed _)]
          have := hMΔ x
          rw [Real.norm_eq_abs] at this
          exact mul_le_mul_of_nonneg_left this ((β n).nonneg_normed _)
      _ = MΔ := by rw [integral_mul_const, hρ1, one_mul]
  have hmeas : ∀ n, AEStronglyMeasurable (fun y => f y *
      ∫ x, (β n).normed volume (y - x) * Matrix.trace (hessian ψ x)) volume := by
    intro n
    have hF : Continuous (fun p : Rd 2 × Rd 2 =>
        (β n).normed volume (p.1 - p.2) * Matrix.trace (hessian ψ p.2)) :=
      ((β n).continuous_normed.comp (continuous_fst.sub continuous_snd)).mul
        (hΔc.comp continuous_snd)
    exact hf.aestronglyMeasurable.mul
      (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
  refine tendsto_integral_of_dominated_convergence (K'.indicator fun _ => |Mf| * |MΔ|) hmeas
    ((integrable_indicator_iff hK'.measurableSet).2
      (integrableOn_const (C := |Mf| * |MΔ|) hK'.measure_lt_top.ne)) (fun n => ?_)
    (ae_of_all _ fun y => tendsto_const_nhds.mul (tendsto_mollify_at hψ hψc hβ y))
  refine ae_of_all _ fun y => ?_
  show ‖f y * ∫ x, (β n).normed volume (y - x) * Matrix.trace (hessian ψ x)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hy : y ∈ K'
  · rw [Set.indicator_of_mem hy]
    have h1 := hMf y hy
    rw [Real.norm_eq_abs] at h1
    exact mul_le_mul (h1.trans (le_abs_self _)) ((hAb n y).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  · rw [Set.indicator_of_notMem hy, hA0 n y hy, abs_zero, mul_zero]

/-- The weak Laplacian near one point, from two-sided distributional bounds. -/
theorem weak_near_of_dist {V : Set (Rd 2)} (hV : IsOpen V) {C : ℝ} (hC : 0 ≤ C)
    {u : Rd 2 → ℝ} (hu : ContinuousOn u V)
    (hge : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → -C * ∫ x, φ x ≤ ∫ x, u x * Matrix.trace (hessian φ x))
    (hle : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → ∫ x, u x * Matrix.trace (hessian φ x) ≤ C * ∫ x, φ x)
    {a : Rd 2} (ha : a ∈ V) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ V ∧ ∃ (s : Rd 2 → ℝ) (C' : ℝ), Measurable s ∧
      (∀ x, |s x| ≤ C') ∧ IsWeakSolutionLaplace (ball a r) u s := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV a ha
  set r := min (ε / 8) 1
  have hr : 0 < r := lt_min (by linarith) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hrε : r ≤ ε / 8 := min_le_left _ _
  -- the continuous extension
  let χ' : ContDiffBump a := ⟨3 * r, 4 * r, by linarith, by linarith⟩
  have hχ'V : tsupport χ' ⊆ V := by
    rw [χ'.tsupport_eq]
    exact (closedBall_subset_ball (show χ'.rOut < ε by show 4 * r < ε; linarith)).trans hball
  set ũ : Rd 2 → ℝ := fun x => χ' x * u x
  have hũc : Continuous ũ := continuous_mul_of_tsupport hV hu χ'.continuous hχ'V
  have hint_eq : ∀ φ : Rd 2 → ℝ, tsupport φ ⊆ closedBall a (3 * r) →
      ∫ x, ũ x * Matrix.trace (hessian φ x) = ∫ x, u x * Matrix.trace (hessian φ x) := by
    intro φ hφ
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · show χ' x * u x * _ = u x * _
      rw [χ'.one_of_mem_closedBall (hφ hx), one_mul]
    · show χ' x * u x * _ = u x * _
      rw [PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport hx]
      simp
  -- the mollifiers
  have hpos : ∀ n : ℕ, 0 < r * (1 / ((n : ℝ) + 1)) := fun n => mul_pos hr (by positivity)
  let β : ℕ → ContDiffBump (0 : Rd 2) := fun n =>
    ⟨r * (1 / ((n : ℝ) + 1)) / 2, r * (1 / ((n : ℝ) + 1)), half_pos (hpos n),
      half_lt_self (hpos n)⟩
  have hβr : ∀ n, (β n).rOut ≤ r := fun n => by
    show r * (1 / ((n : ℝ) + 1)) ≤ r
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  have hβ : Tendsto (fun n => (β n).rOut) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r
    rw [mul_zero] at h
    exact h
  set m : ℕ → Rd 2 → ℝ := fun n x =>
    ∫ y, ũ y * Matrix.trace (hessian ((β n).normed volume) (y - x))
  have hmb : ∀ n, ∀ x ∈ closedBall a (2 * r), |m n x| ≤ C := by
    intro n x hx
    obtain ⟨hψ, hψc, hψts, hψ0, hψ1⟩ := translate_bump_props (β n) x
    have hts : tsupport (fun y => (β n).normed volume (y - x)) ⊆ closedBall a (3 * r) := by
      refine hψts.trans fun y hy => ?_
      rw [mem_closedBall] at hy hx ⊢
      linarith [dist_triangle y x a, hβr n]
    have hV' : tsupport (fun y => (β n).normed volume (y - x)) ⊆ V :=
      hts.trans ((closedBall_subset_ball (by linarith)).trans hball)
    have e : m n x = ∫ y, u y * Matrix.trace (hessian (fun z => (β n).normed volume (z - x)) y) :=
      (mollified_eq (β n) ũ x).trans (hint_eq _ hts)
    have h1 := hge _ hψ hψc hV' hψ0
    have h2 := hle _ hψ hψc hV' hψ0
    rw [hψ1] at h1 h2
    rw [e, abs_le]
    constructor <;> linarith
  -- the localized sequence
  let χ : ContDiffBump a := ⟨r, 2 * r, hr, by linarith⟩
  have hχ0 : ∀ x, x ∉ ball a (2 * r) → χ x = 0 := fun x hx =>
    Function.notMem_support.1 (by rw [χ.support_eq]; exact hx)
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [χ.nonneg (x := x)], χ.le_one⟩
  set f : ℕ → Rd 2 → ℝ := fun n x => χ x * m n x
  have hfm : ∀ n, Measurable (f n) := fun n =>
    χ.continuous.measurable.mul (measurable_mollified (β n) hũc)
  have hfb : ∀ n x, |f n x| ≤ C := by
    intro n x
    show |χ x * m n x| ≤ C
    by_cases hx : x ∈ ball a (2 * r)
    · rw [abs_mul]
      calc |χ x| * |m n x| ≤ 1 * C :=
            mul_le_mul (hχb x) (hmb n x (ball_subset_closedBall hx)) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    · rw [hχ0 x hx, zero_mul, abs_zero]; exact hC
  have hloc : ∀ φ : Rd 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      Tendsto (fun n => ∫ x, f n x * φ x) atTop
        (𝓝 (∫ y, ũ y * Matrix.trace (hessian (fun z => χ z * φ z) y))) := by
    intro φ hφ
    have hg : ContDiff ℝ 2 (fun y => χ y * φ y) :=
      (χ.contDiff.mul hφ).of_le (WithTop.coe_le_coe.2 le_top)
    have hgc : HasCompactSupport (fun y => χ y * φ y) := χ.hasCompactSupport.mul_right
    refine (tendsto_integral_mollified hũc hg hgc hβ fun n => (hβr n).trans hr1).congr
      fun n => ?_
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show m n x * (χ x * φ x) = χ x * m n x * φ x
    ring
  obtain ⟨s, hsLp, hweak⟩ := weakStarRepresentation 2 f C (ball a (2 * r)) isBounded_ball hfm hfb
    (Eventually.of_forall fun n x hx => by
      show χ x * m n x = 0
      rw [hχ0 x hx, zero_mul])
    (fun φ hφ _ => ⟨_, hloc φ hφ⟩)
  have hle' : ∀ᵐ x ∂volume, s x ≤ C :=
    hweak.ae_le hsLp hfm hfb (Eventually.of_forall fun n x => (abs_le.1 (hfb n x)).2)
  have hweak' : WeakStarTendsto (fun n x => -f n x) (fun x => -s x) := fun g hg => by
    have := (hweak g hg).neg
    simpa only [neg_mul, integral_neg] using this
  have hge' : ∀ᵐ x ∂volume, -s x ≤ C :=
    hweak'.ae_le hsLp.neg (fun n => (hfm n).neg)
      (fun n x => (abs_neg _).trans_le (hfb n x))
      (Eventually.of_forall fun n x => neg_le.2 (abs_le.1 (hfb n x)).1)
  obtain ⟨s', hs'm, hs'b, hs'e⟩ := exists_bounded_rep hsLp.aestronglyMeasurable hC hle' hge'
  refine ⟨r, hr, (ball_subset_ball (by linarith)).trans hball, s', C, hs'm, hs'b,
    fun φ hφ hφc hφs => ?_⟩
  have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hχφ : (fun y => χ y * φ y) = φ := by
    funext y
    by_cases hy : y ∈ tsupport φ
    · rw [χ.one_of_mem_closedBall (ball_subset_closedBall (hφs hy)), one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  have h1 := hloc φ hφ
  rw [hχφ, hint_eq φ (hφs.trans ((ball_subset_ball (by linarith)).trans
    ball_subset_closedBall))] at h1
  have h2 := hweak φ hφi
  rw [tendsto_nhds_unique h1 h2]
  exact integral_congr_ae (hs'e.mono fun x hx => by
    show s x * φ x = s' x * φ x
    rw [hx])

theorem hessian_neg' (φ : Rd 2 → ℝ) (x : Rd 2) :
    hessian (fun y => -φ y) x = -hessian φ x := by
  have h1 : fderiv ℝ (fun y => -φ y) = fun z => -fderiv ℝ φ z := funext fun z => fderiv_neg
  have h2 : fderiv ℝ (fun z => -fderiv ℝ φ z) x = -fderiv ℝ (fderiv ℝ φ) x := fderiv_neg
  ext i j
  rw [hessian_apply, h1, h2]
  simp [hessian_apply]

/-- ** Viscosity Laplacian bounds give a locally bounded weak Laplacian**, from Alexandrov's
theorem. -/
theorem viscLaplaceWeak (hA : AlexandrovStmt) : ViscLaplaceWeakStmt := by
  intro V hV C u hu h1 h2
  have hge : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → -|C| * ∫ x, φ x ≤ ∫ x, u x * Matrix.trace (hessian φ x) := by
    intro φ hφ hφc hφV hφ0
    have h := distLaplace_ge hA hV hu h1 hφ hφc hφV hφ0
    have hφi : 0 ≤ ∫ x, φ x := integral_nonneg hφ0
    have : -|C| * ∫ x, φ x ≤ -C * ∫ x, φ x :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hφi
    linarith
  have hle : ∀ φ : Rd 2 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) → ∫ x, u x * Matrix.trace (hessian φ x) ≤ |C| * ∫ x, φ x := by
    intro φ hφ hφc hφV hφ0
    have h2' : ViscFromAboveGE (fun X => X.trace + C) V (fun x => -u x) := by
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
  intro a ha
  exact weak_near_of_dist hV (abs_nonneg C) hu hge hle ha

end SingleSourceD2

end RandomSandpile

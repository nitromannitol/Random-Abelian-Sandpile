import RandomSandpile.Proofs.Sec7.PegdenSmartAdapterWeak
import RandomSandpile.Proofs.Sec7.PegdenSmartAdapterVisc
import RandomSandpile.Inputs.Proposed

/-!
# `PegdenSmartTouchingStmt` from Pegden-Smart's Propositions 2.4 and 2.5

`pegdenSmartTouching_of_ps13 : PegdenSmartProp25Stmt → PegdenSmartProp24Stmt →
ViscosityWeakLaplaceStmt → PegdenSmartTouchingStmt` (inputs in `Inputs/PegdenSmartProp25.lean`).
No ABP estimate on general domains is needed: the argument localizes to a ball.

Route. Let `w = u - v`, `x₀ ∈ U` with `w(x₀) > m`, and `ε > 0` so small that `ε|x - x₀|² < (w(x₀) -
m)/2` on `Ū`. A maximum point `x₁` of `w + ε|x - x₀|²` on the compact `Ū` lies in `U` (on `∂U` the
function is below `w(x₀)`) and has `w(x₁) > m`. Take `ρ > 0` with `B̄_ρ(x₁) ⊆ U ∩ {w > m}` and
`ũ(y) = u'(x₁ + ρ y)`, `vt(y) = v(x₁ + ρ y)`, `u' = u + ε|x - x₀|² - (ε/2)|x - x₁|²`. Both satisfy
`|Δ| ≤ ρ²(K + dε)` in the viscosity sense on `B_1` (`Proofs/Sec7/PegdenSmartAdapterVisc.lean`), hence
are weak solutions with bounded right sides (`ViscosityWeakLaplaceStmt`), and so is `f = ũ - vt`
(`isWeakSolutionLaplace_sub`). `f(0) = max_{Ū}(w + ε|x - x₀|²)` exceeds `f` on `∂B_1` by `ερ²/2`, so
Proposition 2.5 gives a set of positive measure where `f` has a Peano expansion with `D²f < 0`;
Proposition 2.4 adds expansions of `ũ` and `vt` almost everywhere. At such a point, by uniqueness of
the quadratic form (`qM_eq_of_taylor`), `D²u - D²v = ρ⁻²(D²ũ - D²vt) - εI ≤ -εI` at `x₁ + ρ y`, and
`y ↦ x₁ + ρ y` maps sets of positive measure to sets of positive measure.
-/

noncomputable section

open MeasureTheory Filter Topology Metric

namespace RandomSandpile

variable {d : ℕ}

namespace PegdenSmartAdapter

theorem qM_nonpos_of_neg_posDef {Y : Matrix (Fin d) (Fin d) ℝ} (hY : (-Y).PosDef) (h : Rd d) :
    qM Y h ≤ 0 := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hY
  by_cases h0 : WithLp.ofLp h = 0
  · simp [qM, h0]
  · have := hY.2 h0
    simp only [star_trivial, Matrix.neg_mulVec, dotProduct_neg] at this
    simp only [qM]
    linarith

theorem isSymm_smul_one (c : ℝ) : (c • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
  unfold Matrix.IsSymm
  simp

/-- A set whose preimage under `y ↦ x₁ + ρ y` contains almost all of a set of positive measure has
positive measure. -/
theorem volume_pos_of_preimage {A S : Set (Rd d)} {x₁ : Rd d} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : 0 < volume S) (hSA : ∀ᵐ y, y ∈ S → x₁ + ρ • y ∈ A) : 0 < volume A := by
  have h1 : volume S ≤ volume ((fun y : Rd d => x₁ + ρ • y) ⁻¹' A) := measure_mono_ae hSA
  refine pos_iff_ne_zero.2 fun hA0 => ?_
  have h2 : volume ((fun y : Rd d => x₁ + ρ • y) ⁻¹' A) = 0 := by
    have e : (fun y : Rd d => x₁ + ρ • y) ⁻¹' A =
        (fun y : Rd d => ρ • y) ⁻¹' ((fun z : Rd d => x₁ + z) ⁻¹' A) := rfl
    rw [e, Measure.addHaar_preimage_smul volume hρ.ne', measure_preimage_add, hA0, mul_zero]
  exact hS.ne' (nonpos_iff_eq_zero.1 (h1.trans h2.le))

end PegdenSmartAdapter

open PegdenSmartAdapter in
/-- **`PegdenSmartTouchingStmt` from Pegden-Smart's Propositions 2.4 and 2.5** and the
viscosity/weak equivalence for `|Δu| ≤ K` (see the module docstring). -/
theorem pegdenSmartTouching_of_ps13 (h25 : PegdenSmartProp25Stmt) (h24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) : PegdenSmartTouchingStmt := by
  intro d hd U hU hUb K u v hu hv hu1 hu2 hv1 hv2 m hm hex
  obtain ⟨x₀, hx₀U, hx₀⟩ := hex
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hK : IsCompact (closure U) := hUb.isCompact_closure
  have hx₀c : x₀ ∈ closure U := subset_closure hx₀U
  -- `ε` with `ε |x - x₀|² < (w(x₀) - m)/2` on `Ū`
  have hcf : ContinuousOn (fun x : Rd d => x - x₀) (closure U) :=
    (continuous_id.sub continuous_const).continuousOn
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hcf
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR x₀ hx₀c)
  have hgap0 : 0 < u x₀ - v x₀ - m := by linarith
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = (u x₀ - v x₀ - m) / (2 * (R ^ 2 + 1)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hε_def]; positivity
  have hεR : ∀ x ∈ closure U, ε * ‖x - x₀‖ ^ 2 < (u x₀ - v x₀ - m) / 2 := fun x hx => by
    have h1 : ‖x - x₀‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hR x hx) 2
    have h2 : ε * (R ^ 2 + 1) = (u x₀ - v x₀ - m) / 2 := by
      rw [hε_def, div_mul_eq_mul_div, mul_div_mul_right _ _ (by positivity : R ^ 2 + 1 ≠ 0)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hε.le]
  -- the maximum point `x₁` of `w + ε|x - x₀|²` on `Ū`
  have hwc : ContinuousOn (fun x => u x - v x + ε * ‖x - x₀‖ ^ 2) (closure U) :=
    (hu.sub hv).add
      (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)).continuousOn
  obtain ⟨x₁, hx₁c, hmax⟩ := hK.exists_isMaxOn ⟨x₀, hx₀c⟩ hwc
  have hmax' : ∀ x ∈ closure U, u x - v x + ε * ‖x - x₀‖ ^ 2 ≤
      u x₁ - v x₁ + ε * ‖x₁ - x₀‖ ^ 2 := fun x hx => isMaxOn_iff.1 hmax x hx
  have h30 := hmax' x₀ hx₀c
  rw [sub_self, norm_zero] at h30
  have hx₁ : x₁ ∈ U := by
    by_contra hx₁U
    have hfr : x₁ ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hx₁c, hx₁U⟩
    have h1 := hm x₁ hfr
    have h2 := hεR x₁ hx₁c
    nlinarith
  have hw₁ : m < u x₁ - v x₁ := by
    have h2 := hεR x₁ hx₁c
    nlinarith
  -- a closed ball `B̄_ρ(x₁) ⊆ U ∩ {w > m}`
  have hO : IsOpen (U ∩ (fun x => u x - v x) ⁻¹' Set.Ioi m) :=
    ((hu.mono subset_closure).sub (hv.mono subset_closure)).isOpen_inter_preimage hU isOpen_Ioi
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO x₁ ⟨hx₁, hw₁⟩
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = r / 2 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; positivity
  have hcb : closedBall x₁ ρ ⊆ U ∩ (fun x => u x - v x) ⁻¹' Set.Ioi m :=
    (closedBall_subset_ball (by rw [hρ_def]; linarith)).trans hball
  have hΦ : ∀ y : Rd d, ‖y‖ ≤ 1 → x₁ + ρ • y ∈ closedBall x₁ ρ := fun y hy => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ]
    nlinarith [norm_nonneg y]
  -- the modified function `u' = u + ε|x - x₀|² - (ε/2)|x - x₁|²`
  obtain ⟨u', hu'⟩ : ∃ u' : Rd d → ℝ,
      u' = fun x => u x + ε * ‖x - x₀‖ ^ 2 + (-(ε / 2)) * ‖x - x₁‖ ^ 2 := ⟨_, rfl⟩
  have hu'x : ∀ x, u' x = u x + ε * ‖x - x₀‖ ^ 2 + (-(ε / 2)) * ‖x - x₁‖ ^ 2 := fun x => by
    rw [hu']
  have hdε : 0 ≤ (d : ℝ) * ε := mul_nonneg hdR hε.le
  have hu'1 : ViscFromAboveGE (fun X => X.trace + (K + d * ε)) U u' := by
    rw [hu']
    exact viscAboveGE_mono (viscAboveGE_add_sq (viscAboveGE_add_sq hu1 ε x₀) (-(ε / 2)) x₁)
      (by linarith)
  have hu'2 : ViscFromBelowLE (fun X => X.trace - (K + d * ε)) U u' := by
    rw [hu']
    exact viscBelowLE_mono (viscBelowLE_add_sq (viscBelowLE_add_sq hu2 ε x₀) (-(ε / 2)) x₁)
      (by linarith)
  have hv'1 : ViscFromAboveGE (fun X => X.trace + (K + d * ε)) U v :=
    viscAboveGE_mono hv1 (by linarith)
  have hv'2 : ViscFromBelowLE (fun X => X.trace - (K + d * ε)) U v :=
    viscBelowLE_mono hv2 (by linarith)
  -- the rescaled functions on `B_1`
  have hsubB : ball (0 : Rd d) 1 ⊆ {y | x₁ + ρ • y ∈ U} := fun y hy => by
    rw [mem_ball, dist_zero_right] at hy
    exact (hcb (hΦ y hy.le)).1
  have hũ1 : ViscFromAboveGE (fun X => X.trace + ρ ^ 2 * (K + d * ε)) (ball 0 1)
      (fun y => u' (x₁ + ρ • y)) :=
    fun y hy => viscAboveGE_comp_affine hu'1 x₁ hρ y (hsubB hy)
  have hũ2 : ViscFromBelowLE (fun X => X.trace - ρ ^ 2 * (K + d * ε)) (ball 0 1)
      (fun y => u' (x₁ + ρ • y)) :=
    fun y hy => viscBelowLE_comp_affine hu'2 x₁ hρ y (hsubB hy)
  have hvt1 : ViscFromAboveGE (fun X => X.trace + ρ ^ 2 * (K + d * ε)) (ball 0 1)
      (fun y => v (x₁ + ρ • y)) :=
    fun y hy => viscAboveGE_comp_affine hv'1 x₁ hρ y (hsubB hy)
  have hvt2 : ViscFromBelowLE (fun X => X.trace - ρ ^ 2 * (K + d * ε)) (ball 0 1)
      (fun y => v (x₁ + ρ • y)) :=
    fun y hy => viscBelowLE_comp_affine hv'2 x₁ hρ y (hsubB hy)
  have hu'c : ContinuousOn u' (closure U) := by
    rw [hu']
    exact (hu.add (continuous_const.mul
      ((continuous_id.sub continuous_const).norm.pow 2)).continuousOn).add
      (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)).continuousOn
  have hΦc : Continuous fun y : Rd d => x₁ + ρ • y := continuous_const.add (continuous_const_smul ρ)
  have hmaps : Set.MapsTo (fun y : Rd d => x₁ + ρ • y) (closedBall 0 1) (closure U) :=
    fun y hy => by
      rw [mem_closedBall, dist_zero_right] at hy
      exact subset_closure (hcb (hΦ y hy)).1
  have hũc : ContinuousOn (fun y => u' (x₁ + ρ • y)) (closedBall 0 1) :=
    hu'c.comp hΦc.continuousOn hmaps
  have hvtc : ContinuousOn (fun y => v (x₁ + ρ • y)) (closedBall 0 1) :=
    hv.comp hΦc.continuousOn hmaps
  -- weak solutions (viscosity/weak equivalence) and their difference
  obtain ⟨s₁, hs₁m, hs₁b, hs₁w⟩ := hVW d hd (ball 0 1) isOpen_ball ⟨0, mem_ball_self one_pos⟩ (ρ ^ 2 * (K + d * ε)) _
    (hũc.mono ball_subset_closedBall) hũ1 hũ2
  obtain ⟨s₂, hs₂m, hs₂b, hs₂w⟩ := hVW d hd (ball 0 1) isOpen_ball ⟨0, mem_ball_self one_pos⟩ (ρ ^ 2 * (K + d * ε)) _
    (hvtc.mono ball_subset_closedBall) hvt1 hvt2
  have hfw := isWeakSolutionLaplace_sub isOpen_ball (hũc.mono ball_subset_closedBall)
    (hvtc.mono ball_subset_closedBall) hs₁m hs₂m hs₁b hs₂b hs₁w hs₂w
  have hmem : ∀ s : Rd d → ℝ, Measurable s → ∀ C : ℝ, (∀ x, |s x| ≤ C) →
      MemLp s ⊤ (volume.restrict (ball (0 : Rd d) 1)) := fun s hs C hC =>
    memLp_top_of_bound hs.aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hdiffb : ∀ x, |s₁ x - s₂ x| ≤ 2 * (ρ ^ 2 * (K + d * ε)) := fun x => by
    have h1 := abs_le.1 (hs₁b x)
    have h2 := abs_le.1 (hs₂b x)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  -- the strict interior maximum of `f = ũ - vt` on `B̄_1`
  have hfval : ∀ y : Rd d, ‖y‖ ≤ 1 → u' (x₁ + ρ • y) - v (x₁ + ρ • y) ≤
      (u x₁ - v x₁ + ε * ‖x₁ - x₀‖ ^ 2) - ε / 2 * ρ ^ 2 * ‖y‖ ^ 2 := fun y hy => by
    have h1 := hmax' (x₁ + ρ • y) (subset_closure (hcb (hΦ y hy)).1)
    have h2 : ‖x₁ + ρ • y - x₁‖ ^ 2 = ρ ^ 2 * ‖y‖ ^ 2 := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_pow]
    rw [hu'x, h2]
    linarith
  have hf0 : u' (x₁ + ρ • (0 : Rd d)) - v (x₁ + ρ • (0 : Rd d)) =
      u x₁ - v x₁ + ε * ‖x₁ - x₀‖ ^ 2 := by
    rw [smul_zero, add_zero, hu'x, sub_self, norm_zero]
    ring
  obtain ⟨e, he⟩ : ∃ e : Rd d, ‖e‖ = 1 :=
    ⟨EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ), by simp⟩
  have hsph : sSup ((fun y => u' (x₁ + ρ • y) - v (x₁ + ρ • y)) '' sphere 0 1) ≤
      (u x₁ - v x₁ + ε * ‖x₁ - x₀‖ ^ 2) - ε / 2 * ρ ^ 2 := by
    refine csSup_le ⟨_, e, by rw [mem_sphere, dist_zero_right, he], rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_sphere, dist_zero_right] at hy
    have := hfval y hy.le
    rw [hy, one_pow, mul_one] at this
    exact this
  have hballsup : u x₁ - v x₁ + ε * ‖x₁ - x₀‖ ^ 2 ≤
      sSup ((fun y => u' (x₁ + ρ • y) - v (x₁ + ρ • y)) '' ball 0 1) := by
    refine le_csSup ⟨u x₁ - v x₁ + ε * ‖x₁ - x₀‖ ^ 2, ?_⟩ ⟨0, mem_ball_self one_pos, hf0⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_ball, dist_zero_right] at hy
    have h1 := hfval y hy.le
    have h2 : 0 ≤ ε / 2 * ρ ^ 2 * ‖y‖ ^ 2 := by positivity
    show u' (x₁ + ρ • y) - v (x₁ + ρ • y) ≤ u x₁ - v x₁ + ε * ‖x₁ - x₀‖ ^ 2
    linarith
  have hstrict : sSup ((fun y => u' (x₁ + ρ • y) - v (x₁ + ρ • y)) '' sphere 0 1) <
      sSup ((fun y => u' (x₁ + ρ • y) - v (x₁ + ρ • y)) '' ball 0 1) := by
    have : 0 < ε / 2 * ρ ^ 2 := by positivity
    linarith
  -- Propositions 2.5 and 2.4
  have hP := h25 d hd (fun x => s₁ x - s₂ x) (fun y => u' (x₁ + ρ • y) - v (x₁ + ρ • y))
    (hmem _ (hs₁m.sub hs₂m) _ hdiffb) (hũc.sub hvtc) hfw hstrict
  have hP24u := h24 d hd s₁ (fun y => u' (x₁ + ρ • y)) (hmem s₁ hs₁m _ hs₁b)
    (hũc.mono ball_subset_closedBall) hs₁w
  have hP24v := h24 d hd s₂ (fun y => v (x₁ + ρ • y)) (hmem s₂ hs₂m _ hs₂b)
    (hvtc.mono ball_subset_closedBall) hs₂w
  rw [ae_restrict_iff' measurableSet_ball] at hP24u hP24v
  -- back to `U`
  refine volume_pos_of_preimage (x₁ := x₁) hρ hP ?_
  filter_upwards [hP24u, hP24v] with y hyu hyv
  rintro ⟨hyB, -, q, Y, -, hYT, hYneg⟩
  obtain ⟨pũ, Xũ, hXũs, hũT⟩ := hyu hyB
  obtain ⟨pvt, Xvt, hXvts, hvtT⟩ := hyv hyB
  have hy1 : ‖y‖ ≤ 1 := by rw [mem_ball, dist_zero_right] at hyB; exact hyB.le
  have ha := hcb (hΦ y hy1)
  have hpt : -(ρ⁻¹ • x₁) + ρ⁻¹ • (x₁ + ρ • y) = y := by
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    abel
  have hback : ∀ z : Rd d, x₁ + ρ • (-(ρ⁻¹ • x₁) + ρ⁻¹ • z) = z := fun z => by
    simp only [smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
    abel
  have hTu' : HasSecondOrderTaylorAt u' (x₁ + ρ • y) (ρ⁻¹ • pũ) (ρ⁻¹ ^ 2 • Xũ) := by
    have h := taylor_comp_affine (u := fun y => u' (x₁ + ρ • y)) (c := -(ρ⁻¹ • x₁)) (ρ := ρ⁻¹)
      (y := x₁ + ρ • y) (p := pũ) (X := Xũ) (by rw [hpt]; exact hũT)
    simp only [hback] at h
    exact h
  have hTv : HasSecondOrderTaylorAt v (x₁ + ρ • y) (ρ⁻¹ • pvt) (ρ⁻¹ ^ 2 • Xvt) := by
    have h := taylor_comp_affine (u := fun y => v (x₁ + ρ • y)) (c := -(ρ⁻¹ • x₁)) (ρ := ρ⁻¹)
      (y := x₁ + ρ • y) (p := pvt) (X := Xvt) (by rw [hpt]; exact hvtT)
    simp only [hback] at h
    exact h
  have hTu : HasSecondOrderTaylorAt u (x₁ + ρ • y)
      (ρ⁻¹ • pũ + (2 * -ε) • (x₁ + ρ • y - x₀) + (2 * (ε / 2)) • (x₁ + ρ • y - x₁))
      (ρ⁻¹ ^ 2 • Xũ + (2 * -ε) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (2 * (ε / 2)) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    have h := taylor_add_sq_norm (taylor_add_sq_norm hTu' (-ε) x₀) (ε / 2) x₁
    have hfun : (fun x => u' x + -ε * ‖x - x₀‖ ^ 2 + ε / 2 * ‖x - x₁‖ ^ 2) = u := by
      funext x
      rw [hu'x]
      ring
    rw [hfun] at h
    exact h
  have hXs : (ρ⁻¹ ^ 2 • Xũ + (2 * -ε) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (2 * (ε / 2)) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    ((hXũs.smul _).add (isSymm_smul_one _)).add (isSymm_smul_one _)
  refine ⟨ha.1, ha.2, _, _, _, _, hXs, hXvts.smul _, hTu, hTv, ε / 2, by positivity,
    posDef_of_qM_sub_le hXs (hXvts.smul _) (by positivity) fun h => ?_⟩
  have hq := qM_eq_of_taylor hYT (taylor_sub hũT hvtT) h
  have hYn := qM_nonpos_of_neg_posDef hYneg h
  rw [qM_sub_mat] at hq
  have hq1 : qM (1 : Matrix (Fin d) (Fin d) ℝ) h = ‖h‖ ^ 2 / 2 := by
    have := qM_smul_one (d := d) 1 h
    rwa [one_smul, one_mul] at this
  simp only [qM_add_mat, qM_smul_mat, hq1]
  have hρi : 0 ≤ ρ⁻¹ ^ 2 := by positivity
  nlinarith [mul_nonneg hρi (by linarith : (0 : ℝ) ≤ -(qM Xũ h - qM Xvt h))]

end RandomSandpile

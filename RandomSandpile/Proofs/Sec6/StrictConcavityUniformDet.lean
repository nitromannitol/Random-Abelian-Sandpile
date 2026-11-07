import RandomSandpile.Defs.Lattice

/-! # Step L2-C, part 3: the Jacobian of a Lipschitz map with large images of balls

Let `g : ℝ^d → ℝ^d` be Lipschitz on `B_δ`, with `|g(K)| ≥ α |K|` for closed balls `K ⊆ B_δ` and
`|det Dg| ≤ B` at differentiability points. Then `|det Dg| ≥ α` a.e. in `B_δ`
(`ae_le_abs_det`). Ingredients:
* Rademacher (`LipschitzOnWith.ae_differentiableWithinAt_of_mem`);
* Lipschitz images of null sets are null (`volume_image_eq_zero_of_lipschitzOnWith`, through
  `μHE[d] = volume` and `LipschitzOnWith.hausdorffMeasure_image_le`);
* the area inequality `addHaar_image_le_lintegral_abs_det_fderiv`;
* Lebesgue differentiation along closed balls (`VitaliFamily.ae_tendsto_lintegral_div` for the
  Besicovitch family). -/

open MeasureTheory Filter Metric Set
open scoped Topology NNReal ENNReal

namespace RandomSandpile

namespace UniformConcavity

variable {d : ℕ}

/-- The image of a null set under a map that is Lipschitz on it is null. -/
theorem volume_image_eq_zero_of_lipschitzOnWith {g : Rd d → Rd d} {K : ℝ≥0} {s : Set (Rd d)}
    (hg : LipschitzOnWith K g s) (hs : volume s = 0) : volume (g '' s) = 0 := by
  have hV : (volume : Measure (Rd d)) = μHE[d] :=
    (EuclideanSpace.euclideanHausdorffMeasure_eq_volume d).symm
  rw [hV, Measure.euclideanHausdorffMeasure_def] at hs ⊢
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hs ⊢
  have hc := Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  have hs' : μH[(d : ℝ)] s = 0 := by
    rcases mul_eq_zero.1 hs with h | h
    · exact absurd (ENNReal.coe_eq_zero.1 h) hc
    · exact h
  have := hg.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d)
  rw [hs', mul_zero] at this
  rw [le_zero_iff.1 this, mul_zero]

/-- `|det Dg| ≥ α` a.e. on `B_δ` when `g` blows up the volume of closed balls by `α`. -/
theorem ae_le_abs_det {g : Rd d → Rd d} {K : ℝ≥0} {δ α B : ℝ} (hα : 0 < α)
    (hlip : LipschitzOnWith K g (ball (0 : Rd d) δ))
    (hmass : ∀ (c : Rd d) (r : ℝ), 0 < r → closedBall c r ⊆ ball (0 : Rd d) δ →
      ENNReal.ofReal α * volume (closedBall c r) ≤ volume (g '' closedBall c r))
    (hB : ∀ x ∈ ball (0 : Rd d) δ, DifferentiableAt ℝ g x → |(fderiv ℝ g x).det| ≤ B) :
    ∀ᵐ x, x ∈ ball (0 : Rd d) δ → DifferentiableAt ℝ g x ∧ α ≤ |(fderiv ℝ g x).det| := by
  set Ω := ball (0 : Rd d) δ with hΩ
  set D := {x | DifferentiableAt ℝ g x} with hD
  have hDm : MeasurableSet D := measurableSet_of_differentiableAt ℝ g
  have hΩm : MeasurableSet Ω := measurableSet_ball
  have hrad : ∀ᵐ x, x ∈ Ω → x ∈ D := by
    filter_upwards [hlip.ae_differentiableWithinAt_of_mem] with x hx hxΩ
    exact (hx hxΩ).differentiableAt (isOpen_ball.mem_nhds hxΩ)
  have hnull : volume (Ω \ D) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hrad)
    show ¬(x ∈ Ω → x ∈ D)
    exact fun h => hx.2 (h hx.1)
  set h : Rd d → ℝ≥0∞ := fun x => ENNReal.ofReal |(fderiv ℝ g x).det| with hh
  have hhm : Measurable h :=
    ((ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ g)).abs).ennreal_ofReal
  set f := (Ω ∩ D).indicator h with hf
  have hfm : Measurable f := hhm.indicator (hΩm.inter hDm)
  have hfle : ∀ x, f x ≤ Ω.indicator (fun _ => ENNReal.ofReal B) x := by
    intro x
    by_cases hx : x ∈ Ω ∩ D
    · rw [hf, indicator_of_mem hx, indicator_of_mem hx.1]
      exact ENNReal.ofReal_le_ofReal (hB x hx.1 hx.2)
    · rw [hf, indicator_of_notMem hx]; exact zero_le
  have hfin : ∫⁻ x, f x ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hfle)
    rw [lintegral_indicator hΩm, setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hint : ∀ (c : Rd d) (r : ℝ), 0 < r → closedBall c r ⊆ Ω →
      ENNReal.ofReal α * volume (closedBall c r) ≤ ∫⁻ x in closedBall c r, f x := by
    intro c r hr hsub
    set Kb := closedBall c r
    have himg : volume (g '' Kb) ≤ volume (g '' (Kb ∩ D)) + volume (g '' (Kb \ D)) := by
      calc volume (g '' Kb) = volume (g '' (Kb ∩ D) ∪ g '' (Kb \ D)) := by
            rw [← image_union, inter_union_sdiff]
        _ ≤ _ := measure_union_le _ _
    have h2 : volume (g '' (Kb \ D)) = 0 :=
      volume_image_eq_zero_of_lipschitzOnWith (hlip.mono (fun x hx => hsub hx.1))
        (measure_mono_null (fun x (hx : x ∈ Kb \ D) => (⟨hsub hx.1, hx.2⟩ : x ∈ Ω \ D)) hnull)
    have h1 : volume (g '' (Kb ∩ D)) ≤ ∫⁻ x in Kb ∩ D, h x :=
      addHaar_image_le_lintegral_abs_det_fderiv volume (isClosed_closedBall.measurableSet.inter hDm)
        (fun x hx => (hx.2 : DifferentiableAt ℝ g x).hasFDerivAt.hasFDerivWithinAt)
    have h3 : ∫⁻ x in Kb, f x = ∫⁻ x in Kb ∩ D, h x := by
      rw [hf, lintegral_indicator (hΩm.inter hDm), Measure.restrict_restrict (hΩm.inter hDm)]
      congr 2
      exact Set.ext fun x => ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hsub hx.1, hx.2⟩, hx.1⟩⟩
    calc ENNReal.ofReal α * volume Kb ≤ volume (g '' Kb) := hmass c r hr hsub
      _ ≤ _ := himg
      _ ≤ (∫⁻ x in Kb ∩ D, h x) + 0 := add_le_add h1 h2.le
      _ = _ := by rw [add_zero, h3]
  have hlim := (Besicovitch.vitaliFamily (volume : Measure (Rd d))).ae_tendsto_lintegral_div
    hfm.aemeasurable hfin
  filter_upwards [hlim] with x hx hxΩ
  have hT := hx.comp (Besicovitch.tendsto_filterAt volume x)
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 isOpen_ball x hxΩ
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal α ≤ ((fun a => (∫⁻ y in a, f y) / volume a) ∘ fun r => closedBall x r) r := by
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    have hsub : closedBall x r ⊆ Ω := (closedBall_subset_ball hr.2).trans hεs
    simp only [Function.comp_apply]
    rw [ENNReal.le_div_iff_mul_le (Or.inl (measure_closedBall_pos volume x hr.1).ne')
      (Or.inl measure_closedBall_lt_top.ne)]
    exact hint x r hr.1 hsub
  have hfx : ENNReal.ofReal α ≤ f x := ge_of_tendsto hT hev
  by_cases hxD : x ∈ D
  · have hmem : x ∈ Ω ∩ D := ⟨hxΩ, hxD⟩
    rw [hf, indicator_of_mem hmem] at hfx
    exact ⟨hxD, (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).1 hfx⟩
  · have hmem : x ∉ Ω ∩ D := fun h' => hxD h'.2
    rw [hf, indicator_of_notMem hmem] at hfx
    exact absurd (ENNReal.ofReal_eq_zero.1 (le_zero_iff.1 hfx)) (not_le.2 hα)

end UniformConcavity

end RandomSandpile

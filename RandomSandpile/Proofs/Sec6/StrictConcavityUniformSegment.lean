import RandomSandpile.Defs.Lattice

/-! # Step L2-C, part 4: strong monotonicity from an a.e. bound on the derivative

Let `g : ℝ^d → ℝ^d` be Lipschitz on `B̄_δ`, differentiable a.e. in `B_δ` with
`⟪Dg(x) w, w⟫ ≤ -c |w|²`. Then `⟪g(Y) - g(X), Y - X⟫ ≤ -c |Y - X|²` for `X, Y ∈ B_δ`
(`inner_sub_le_of_ae`). By Fubini, almost every translate `[X + h, Y + h]` of the segment meets the
bad null set in a null set of times; along such a translate `t ↦ ⟪v, g(X + h + t v)⟫` is Lipschitz,
hence absolutely continuous, and the fundamental theorem of calculus applies
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`). Continuity of `g` lets `h → 0`. -/

open MeasureTheory Filter Metric Set
open scoped Topology NNReal ENNReal

namespace RandomSandpile

namespace UniformConcavity

variable {d : ℕ}

theorem inner_sub_le_of_ae {g : Rd d → Rd d} {δ c : ℝ} {K : ℝ≥0}
    (hlip : LipschitzOnWith K g (closedBall (0 : Rd d) δ))
    (hgood : ∀ᵐ x, x ∈ ball (0 : Rd d) δ → DifferentiableAt ℝ g x ∧
      ∀ w, inner ℝ (fderiv ℝ g x w) w ≤ -c * ‖w‖ ^ 2)
    {X Y : Rd d} (hX : X ∈ ball (0 : Rd d) δ) (hY : Y ∈ ball (0 : Rd d) δ) :
    inner ℝ (g Y - g X) (Y - X) ≤ -c * ‖Y - X‖ ^ 2 := by
  set v := Y - X with hv
  set m := max ‖X‖ ‖Y‖ with hmdef
  have hm : m < δ := max_lt (mem_ball_zero_iff.1 hX) (mem_ball_zero_iff.1 hY)
  set ρ := (δ - m) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hseg : ∀ h : Rd d, ‖h‖ < ρ → ∀ t ∈ Icc (0 : ℝ) 1, X + h + t • v ∈ ball (0 : Rd d) δ := by
    intro h hh t ht
    have hXt : X + t • v ∈ closedBall (0 : Rd d) m :=
      (convex_closedBall (0 : Rd d) m).add_smul_sub_mem
        (mem_closedBall_zero_iff.2 (le_max_left _ _)) (mem_closedBall_zero_iff.2 (le_max_right _ _)) ht
    rw [mem_ball_zero_iff]
    calc ‖X + h + t • v‖ = ‖(X + t • v) + h‖ := by congr 1; abel
      _ ≤ ‖X + t • v‖ + ‖h‖ := norm_add_le _ _
      _ < δ := by have := mem_closedBall_zero_iff.1 hXt; rw [hρ] at hh; linarith
  -- the bad set
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodN : ∀ x ∈ ball (0 : Rd d) δ, x ∉ N → DifferentiableAt ℝ g x ∧
      ∀ w, inner ℝ (fderiv ℝ g x w) w ≤ -c * ‖w‖ ^ 2 := by
    intro x hx hxN
    by_contra hcon
    exact hxN (hNsub (show ¬(x ∈ ball (0 : Rd d) δ → _) from fun h => hcon (h hx)))
  -- Fubini: almost every translate meets `N` in a null set of times
  have hprod : ∀ᵐ h : Rd d, ∀ᵐ t : ℝ, X + h + t • v ∉ N := by
    have hS : MeasurableSet {z : Rd d × ℝ | X + z.1 + z.2 • v ∈ N} :=
      hNm.preimage (by fun_prop)
    refine Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume)
      (p := fun z : Rd d × ℝ => X + z.1 + z.2 • v ∉ N) ?_
    rw [ae_iff]
    simp only [not_not]
    rw [Measure.prod_apply_symm hS]
    have hslice : ∀ t : ℝ, volume ((fun x : Rd d => (x, t)) ⁻¹'
        {z : Rd d × ℝ | X + z.1 + z.2 • v ∈ N}) = 0 := by
      intro t
      have : (fun x : Rd d => (x, t)) ⁻¹' {z : Rd d × ℝ | X + z.1 + z.2 • v ∈ N} =
          (fun x => x + (X + t • v)) ⁻¹' N := by
        ext x
        simp only [mem_preimage, mem_setOf_eq]
        rw [show X + x + t • v = x + (X + t • v) by abel]
      rw [this, measure_preimage_add_right]
      exact hN0
    simp only [hslice, lintegral_zero]
  have hex : ∀ ε > 0, ∃ h : Rd d, ‖h‖ < ε ∧ ∀ᵐ t : ℝ, X + h + t • v ∉ N := by
    intro ε hε
    have hne : volume.restrict (ball (0 : Rd d) ε) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]; exact (measure_ball_pos volume 0 hε).ne'
    haveI : (ae (volume.restrict (ball (0 : Rd d) ε))).NeBot := ae_neBot.2 hne
    have h1 : ∀ᵐ h ∂(volume.restrict (ball (0 : Rd d) ε)), ∀ᵐ t : ℝ, X + h + t • v ∉ N :=
      ae_restrict_of_ae hprod
    have h2 : ∀ᵐ h ∂(volume.restrict (ball (0 : Rd d) ε)), h ∈ ball (0 : Rd d) ε :=
      ae_restrict_mem measurableSet_ball
    obtain ⟨h, hh1, hh2⟩ := (h1.and h2).exists
    exact ⟨h, mem_ball_zero_iff.1 hh2, hh1⟩
  -- along a good translate
  have hK : ∀ h : Rd d, ‖h‖ < ρ → (∀ᵐ t : ℝ, X + h + t • v ∉ N) →
      inner ℝ v (g (X + h + (1 : ℝ) • v)) - inner ℝ v (g (X + h + (0 : ℝ) • v)) ≤
        -c * ‖v‖ ^ 2 := by
    intro h hh hgh
    set ψ : ℝ → ℝ := fun t => inner ℝ v (g (X + h + t • v)) with hψ
    have hlipψ : LipschitzOnWith (K * ‖v‖₊ * ‖v‖₊) ψ (uIcc 0 1) := by
      refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
      rw [uIcc_of_le zero_le_one] at hs ht
      have hs' := hseg h hh s hs
      have ht' := hseg h hh t ht
      rw [Real.dist_eq, hψ]
      simp only
      rw [← inner_sub_right]
      have hdiff : X + h + s • v - (X + h + t • v) = (s - t) • v := by rw [sub_smul]; abel
      calc |inner ℝ v (g (X + h + s • v) - g (X + h + t • v))|
          ≤ ‖v‖ * ‖g (X + h + s • v) - g (X + h + t • v)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖v‖ * (K * ‖X + h + s • v - (X + h + t • v)‖) := by
            gcongr
            exact hlip.norm_sub_le (ball_subset_closedBall hs') (ball_subset_closedBall ht')
        _ = ((K * ‖v‖₊ * ‖v‖₊ : ℝ≥0) : ℝ) * dist s t := by
            rw [hdiff, norm_smul, Real.norm_eq_abs, Real.dist_eq]
            push_cast [coe_nnnorm]
            ring
    have hac := hlipψ.absolutelyContinuousOnInterval
    have hftc := hac.integral_deriv_eq_sub
    have hderiv : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), deriv ψ t ≤ -c * ‖v‖ ^ 2 := by
      filter_upwards [ae_restrict_of_ae hgh, ae_restrict_mem measurableSet_Icc] with t ht1 ht2
      have hxt := hseg h hh t ht2
      obtain ⟨hdiff, hq⟩ := hgoodN _ hxt ht1
      have hline : HasDerivAt (fun s : ℝ => X + h + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add (X + h)
      have hgd : HasDerivAt (fun s => g (X + h + s • v)) (fderiv ℝ g (X + h + t • v) v) t :=
        hdiff.hasFDerivAt.comp_hasDerivAt t hline
      have hψd : HasDerivAt ψ (inner ℝ v (fderiv ℝ g (X + h + t • v) v)) t := by
        have := (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t hgd
        simp only [Function.comp_def, innerSL_apply_apply] at this
        exact this
      rw [hψd.deriv, real_inner_comm]
      exact hq v
    have hint : ∫ t in (0 : ℝ)..1, deriv ψ t ≤ ∫ _t in (0 : ℝ)..1, -c * ‖v‖ ^ 2 :=
      intervalIntegral.integral_mono_ae_restrict zero_le_one hac.intervalIntegrable_deriv
        intervalIntegrable_const hderiv
    rw [hftc, intervalIntegral.integral_const, sub_zero, one_smul] at hint
    exact hint
  -- let the translate tend to `0`
  set F : Rd d → ℝ := fun h => inner ℝ v (g (Y + h)) - inner ℝ v (g (X + h)) with hFdef
  have hF : ∀ h : Rd d, ‖h‖ < ρ → (∀ᵐ t : ℝ, X + h + t • v ∉ N) → F h ≤ -c * ‖v‖ ^ 2 := by
    intro h hh hgh
    have := hK h hh hgh
    have hXv : X + h + (1 : ℝ) • v = Y + h := by rw [one_smul, hv]; abel
    rw [hXv, zero_smul, add_zero] at this
    exact this
  have hgc : ∀ Z ∈ ball (0 : Rd d) δ, ContinuousAt g Z := fun Z hZ =>
    hlip.continuousOn.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hZ) ball_subset_closedBall)
  have hFc : ContinuousAt F 0 := by
    have h1 : ContinuousAt (fun h : Rd d => g (Y + h)) 0 :=
      (hgc Y hY).comp_of_eq (continuous_const.add continuous_id).continuousAt (by simp)
    have h2 : ContinuousAt (fun h : Rd d => g (X + h)) 0 :=
      (hgc X hX).comp_of_eq (continuous_const.add continuous_id).continuousAt (by simp)
    exact (continuousAt_const.inner h1).sub (continuousAt_const.inner h2)
  set S := {h : Rd d | ‖h‖ < ρ ∧ ∀ᵐ t : ℝ, X + h + t • v ∉ N} with hSdef
  have hcl : (0 : Rd d) ∈ closure S := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨h, hh, hgh⟩ := hex (min ε ρ) (lt_min hε hρ0)
    exact ⟨h, ⟨hh.trans_le (min_le_right _ _), hgh⟩, by
      rw [dist_zero_left]; exact hh.trans_le (min_le_left _ _)⟩
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hlim : Tendsto F (𝓝[S] 0) (𝓝 (F 0)) := hFc.tendsto.mono_left nhdsWithin_le_nhds
  have hle : F 0 ≤ -c * ‖v‖ ^ 2 :=
    le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun h hh => hF h hh.1 hh.2)
  simp only [F, add_zero] at hle
  rw [inner_sub_left, real_inner_comm v (g Y), real_inner_comm v (g X)]
  exact hle

end UniformConcavity

end RandomSandpile

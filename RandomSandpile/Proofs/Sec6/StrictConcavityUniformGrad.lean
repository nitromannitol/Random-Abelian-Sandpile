import RandomSandpile.Steps.Sec6.StrictConcavity

/-! # Step L2-C, part 1: the limit is `C^{1,1}`

Setting of `ConcaveUniformConcavityStmt`: `V` is concave on `B_1`, touched from below by paraboloids
of opening `Λ` at every point of `B̄_δ` with every touching slope (`Semiconvex`), and its slope image
has mass `≥ α |K|` on closed sub-balls `K` (`SlopeMass`). Then:
* `exists_touch`: every `X ∈ B_1` carries a touching slope (limit of slopes over shrinking balls,
  which are nonempty by the mass bound);
* `hasFDerivAt_of_touch`: `V` is differentiable at `X` with derivative `⟪q, ·⟫` for every touching
  slope `q`; hence the touching slope is unique and equals `gradient V X` (`touch_gradient`);
* `lipschitzOnWith_gradient`: `∇V` is `2Λ`-Lipschitz on every `B̄_δ`, `δ < 1`;
* `inner_fderiv_gradient_nonpos`, `neg_le_inner_fderiv_gradient`, `inner_fderiv_gradient_comm`: at
  differentiability points of `∇V` in `B_1`, its derivative is symmetric, with quadratic form in
  `[-2Λ|v|², 0]`. -/

open MeasureTheory Filter Metric Set
open scoped Topology NNReal ENNReal

namespace RandomSandpile

namespace UniformConcavity

variable {d : ℕ}

/-- `q` touches `V` from above at `X`, on `B_1`. -/
def Touch (V : Rd d → ℝ) (X q : Rd d) : Prop :=
  ∀ Y ∈ ball (0 : Rd d) 1, V Y ≤ V X + inner ℝ q (Y - X)

/-- The paraboloid lower bound at touching slopes (hypothesis L2-A of `ConcaveUniformConcavityStmt`). -/
def Semiconvex (V : Rd d → ℝ) (Λ : ℝ) : Prop :=
  ∀ δ : ℝ, δ < 1 → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ X ∈ closedBall (0 : Rd d) δ, ∀ q : Rd d, Touch V X q →
      ∀ Y ∈ ball X r₀, V X + inner ℝ q (Y - X) - Λ * ‖Y - X‖ ^ 2 ≤ V Y

/-- The slope mass bound on closed sub-balls (hypothesis L2-B of `ConcaveUniformConcavityStmt`). -/
def SlopeMass (V : Rd d → ℝ) (α : ℝ) : Prop :=
  ∀ (c : Rd d) (r : ℝ), 0 < r → closedBall c r ⊆ ball (0 : Rd d) 1 →
    ENNReal.ofReal α * volume (closedBall c r) ≤ volume (slopeSet V (closedBall c r))

theorem closedBall_subset_ball_one {X : Rd d} {ρ : ℝ} (h : ‖X‖ + ρ < 1) :
    closedBall X ρ ⊆ ball (0 : Rd d) 1 := by
  intro Y hY
  rw [mem_closedBall, dist_eq_norm] at hY
  rw [mem_ball_zero_iff]
  calc ‖Y‖ = ‖(Y - X) + X‖ := by rw [sub_add_cancel]
    _ ≤ ‖Y - X‖ + ‖X‖ := norm_add_le _ _
    _ < 1 := by linarith

/-- Touching slopes are bounded by the oscillation of `V`. -/
theorem norm_le_of_touch {V : Rd d → ℝ} {X q : Rd d} {ρ M : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall X ρ ⊆ ball (0 : Rd d) 1) (hM : ∀ Y ∈ closedBall X ρ, |V Y| ≤ M)
    (hq : Touch V X q) : ρ * ‖q‖ ≤ 2 * M := by
  have hXX : X ∈ closedBall X ρ := mem_closedBall_self hρ.le
  have h1 := hM X hXX
  rcases eq_or_ne q 0 with rfl | hq0
  · simp only [norm_zero, mul_zero]; linarith [abs_nonneg (V X)]
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq0
  set Y := X - (ρ / ‖q‖) • q with hYdef
  have hYX : Y - X = -((ρ / ‖q‖) • q) := by rw [hYdef]; abel
  have hY : Y ∈ closedBall X ρ := by
    rw [mem_closedBall, dist_eq_norm, hYX, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hρ hqn), div_mul_cancel₀ _ hqn.ne']
  have h := hq Y (hsub hY)
  rw [hYX, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have h2 := hM Y hY
  rw [abs_le] at h1 h2
  have : ρ / ‖q‖ * ‖q‖ ^ 2 = ρ * ‖q‖ := by field_simp
  nlinarith

/-- Every point of `B_1` carries a touching slope. -/
theorem exists_touch {V : Rd d → ℝ} {α : ℝ} (hα : 0 < α)
    (hconc : ConcaveOn ℝ (ball (0 : Rd d) 1) V) (hB : SlopeMass V α) :
    ∀ X ∈ ball (0 : Rd d) 1, ∃ q, Touch V X q := by
  intro X hX
  have hX1 : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
  set ρ := (1 - ‖X‖) / 4 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hcont : ContinuousOn V (ball (0 : Rd d) 1) := hconc.continuousOn isOpen_ball
  have hsub2 : closedBall X (2 * ρ) ⊆ ball (0 : Rd d) 1 :=
    closedBall_subset_ball_one (by rw [hρ]; linarith)
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall X (2 * ρ)).exists_bound_of_continuousOn (hcont.mono hsub2)
  have hpt : ∀ j : ℕ, ∃ Xj ∈ closedBall X (ρ / (j + 1)), ∃ qj, Touch V Xj qj := by
    intro j
    have hr : 0 < ρ / (j + 1) := by positivity
    have hle : ρ / (j + 1) ≤ 2 * ρ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hsub : closedBall X (ρ / (j + 1)) ⊆ ball (0 : Rd d) 1 :=
      (closedBall_subset_closedBall hle).trans hsub2
    have hmass := hB X _ hr hsub
    have hpos : 0 < volume (slopeSet V (closedBall X (ρ / (j + 1)))) :=
      lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.2 hα).ne'
        (measure_closedBall_pos volume X hr).ne') hmass
    obtain ⟨q, Xj, hXj, hq⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ⟨Xj, hXj, q, hq⟩
  choose Xs hXs qs hqs using hpt
  have hqb : ∀ j, qs j ∈ closedBall (0 : Rd d) (2 * M / ρ) := by
    intro j
    rw [mem_closedBall_zero_iff, le_div_iff₀ hρ0, mul_comm]
    have hXj := hXs j
    rw [mem_closedBall] at hXj
    have hdj : ρ / (j + 1) ≤ ρ := div_le_self hρ0.le (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
    have hsubj : closedBall (Xs j) ρ ⊆ closedBall X (2 * ρ) := by
      intro Y hY
      rw [mem_closedBall] at hY ⊢
      linarith [dist_triangle Y (Xs j) X]
    refine norm_le_of_touch hρ0 (hsubj.trans hsub2) (fun Y hY => ?_) (hqs j)
    have := hM Y (hsubj hY)
    rwa [Real.norm_eq_abs] at this
  obtain ⟨q, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Rd d) (2 * M / ρ)).tendsto_subseq hqb
  have hXlim0 : Tendsto Xs atTop (𝓝 X) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Tendsto (fun j : ℕ => ρ * (1 / ((j : ℝ) + 1))) atTop (𝓝 (ρ * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
    rw [mul_zero] at h0
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) h0
    have := hXs j
    rw [mem_closedBall] at this
    calc dist (Xs j) X ≤ ρ / (j + 1) := this
      _ = ρ * (1 / ((j : ℝ) + 1)) := by ring
  have hXlim : Tendsto (fun j => Xs (φ j)) atTop (𝓝 X) := hXlim0.comp hφ.tendsto_atTop
  refine ⟨q, fun Y hY => ?_⟩
  have hVc : ContinuousAt V X := hcont.continuousAt (isOpen_ball.mem_nhds hX)
  have h1 : Tendsto (fun j => V (Xs (φ j)) + inner ℝ (qs (φ j)) (Y - Xs (φ j))) atTop
      (𝓝 (V X + inner ℝ q (Y - X))) :=
    (hVc.tendsto.comp hXlim).add (hlim.inner (tendsto_const_nhds.sub hXlim))
  exact ge_of_tendsto h1 (Eventually.of_forall fun j => hqs (φ j) Y hY)

/-- A touching slope is the derivative. -/
theorem hasFDerivAt_of_touch {V : Rd d → ℝ} {Λ : ℝ} (hA : Semiconvex V Λ) {X q : Rd d}
    (hX : X ∈ ball (0 : Rd d) 1) (hq : Touch V X q) : HasFDerivAt V (innerSL ℝ q) X := by
  have hX1 : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
  obtain ⟨r₀, hr₀, hr⟩ := hA ‖X‖ hX1
  have hXc : X ∈ closedBall (0 : Rd d) ‖X‖ := mem_closedBall_zero_iff.2 le_rfl
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun h : Rd d => V (X + h) - V X - innerSL ℝ q h) =O[𝓝 0]
      (fun h : Rd d => ‖h‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound Λ ?_
    have hε : 0 < min r₀ (1 - ‖X‖) := lt_min hr₀ (by linarith)
    filter_upwards [ball_mem_nhds (0 : Rd d) hε] with h hh
    rw [mem_ball_zero_iff, lt_min_iff] at hh
    have hY1 : X + h ∈ ball (0 : Rd d) 1 := by
      rw [mem_ball_zero_iff]
      calc ‖X + h‖ ≤ ‖X‖ + ‖h‖ := norm_add_le _ _
        _ < 1 := by linarith [hh.2]
    have hY2 : X + h ∈ ball X r₀ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hh.1
    have hup := hq _ hY1
    have hlo := hr X hXc q hq _ hY2
    rw [add_sub_cancel_left] at hup hlo
    rw [innerSL_apply_apply, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖h‖ ^ 2), abs_le]
    constructor <;> linarith
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

/-- The touching slope at `X ∈ B_1` exists, is unique, and is `gradient V X`. -/
theorem touch_gradient {V : Rd d → ℝ} {Λ α : ℝ} (hα : 0 < α)
    (hconc : ConcaveOn ℝ (ball (0 : Rd d) 1) V) (hA : Semiconvex V Λ) (hB : SlopeMass V α)
    {X : Rd d} (hX : X ∈ ball (0 : Rd d) 1) :
    Touch V X (gradient V X) ∧ HasFDerivAt V (innerSL ℝ (gradient V X)) X ∧
      ∀ q, Touch V X q → q = gradient V X := by
  have key : ∀ q, Touch V X q → gradient V X = q := by
    intro q hq
    have h := hasFDerivAt_of_touch hA hX hq
    have hdual : (InnerProductSpace.toDual ℝ (Rd d)) q = innerSL ℝ q :=
      ContinuousLinearMap.ext fun y => by
        simp only [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    have hg : HasGradientAt V q X := by
      rw [hasGradientAt_iff_hasFDerivAt, hdual]; exact h
    exact hg.gradient
  obtain ⟨q, hq⟩ := exists_touch hα hconc hB X hX
  have hgq := key q hq
  refine ⟨hgq ▸ hq, hgq ▸ hasFDerivAt_of_touch hA hX hq, fun q' hq' => (key q' hq').symm⟩

/-- A uniform local Lipschitz bound on a convex set is a global one. -/
theorem lipschitzOnWith_of_local {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace F] {s : Set E} (hs : Convex ℝ s) {f : E → F} {L : ℝ≥0} {ρ : ℝ}
    (hρ : 0 < ρ) (h : ∀ x ∈ s, ∀ y ∈ s, dist x y < ρ → dist (f x) (f y) ≤ L * dist x y) :
    LipschitzOnWith L f s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (dist x y / ρ)
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set z : ℕ → E := fun i => x + ((i : ℝ) / ((N : ℝ) + 1)) • (y - x) with hz
  have hzs : ∀ i, i ≤ N + 1 → z i ∈ s := by
    intro i hi
    refine hs.add_smul_sub_mem hx hy ⟨by positivity, ?_⟩
    rw [div_le_one hN0]; exact_mod_cast hi
  have hstep : ∀ i, dist (z i) (z (i + 1)) = dist x y / ((N : ℝ) + 1) := by
    intro i
    rw [dist_eq_norm, hz]
    simp only
    have : x + ((i : ℝ) / ((N : ℝ) + 1)) • (y - x) - (x + (((i + 1 : ℕ) : ℝ) / ((N : ℝ) + 1)) • (y - x))
        = -((1 / ((N : ℝ) + 1)) • (y - x)) := by
      rw [← sub_eq_zero]; push_cast
      rw [← sub_eq_zero]
      simp only [add_div, add_smul]
      abel_nf
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← dist_eq_norm,
      dist_comm]
    ring
  have hlt : dist x y / ((N : ℝ) + 1) < ρ := by
    rw [div_lt_iff₀ hN0]
    rw [div_lt_iff₀ hρ] at hN
    nlinarith
  have hz0 : z 0 = x := by simp [hz]
  have hzN : z (N + 1) = y := by
    simp only [hz]; push_cast; rw [div_self hN0.ne', one_smul]; abel
  calc dist (f x) (f y) = dist (f (z 0)) (f (z (N + 1))) := by rw [hz0, hzN]
    _ ≤ ∑ i ∈ Finset.range (N + 1), dist (f (z i)) (f (z (i + 1))) :=
        dist_le_range_sum_dist (fun i => f (z i)) (N + 1)
    _ ≤ ∑ i ∈ Finset.range (N + 1), (L : ℝ) * (dist x y / ((N : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [← hstep i]
        exact h _ (hzs i hi.le) _ (hzs (i + 1) hi) (by rw [hstep i]; exact hlt)
    _ = L * dist x y := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp

section Gradient

variable {V : Rd d → ℝ} {Λ α : ℝ}

/-- Local Lipschitz bound for the gradient. -/
theorem gradient_dist_le (hΛ : 0 ≤ Λ) {δ r₀ : ℝ} (hδ : δ < 1)
    (hT : ∀ X ∈ ball (0 : Rd d) 1, Touch V X (gradient V X))
    (hr : ∀ X ∈ closedBall (0 : Rd d) δ, ∀ q : Rd d, Touch V X q →
      ∀ Y ∈ ball X r₀, V X + inner ℝ q (Y - X) - Λ * ‖Y - X‖ ^ 2 ≤ V Y)
    {X Y : Rd d} (hX : X ∈ closedBall (0 : Rd d) δ) (hY : Y ∈ closedBall (0 : Rd d) δ)
    (hXY : ‖X - Y‖ < min r₀ (1 - δ)) :
    ‖gradient V X - gradient V Y‖ ≤ 2 * Λ * ‖X - Y‖ := by
  set p := gradient V X
  set p' := gradient V Y
  set t := ‖X - Y‖ with ht
  rw [lt_min_iff] at hXY
  have hX1 : X ∈ ball (0 : Rd d) 1 := closedBall_subset_ball hδ hX
  have hY1 : Y ∈ ball (0 : Rd d) 1 := closedBall_subset_ball hδ hY
  rcases eq_or_ne p p' with hpp | hpp
  · rw [hpp, sub_self, norm_zero]; positivity
  have hn : 0 < ‖p - p'‖ := norm_pos_iff.2 (sub_ne_zero.2 hpp)
  set u := (t / ‖p - p'‖) • (p - p') with hu
  have hun : ‖u‖ = t := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hn.le),
      div_mul_cancel₀ _ hn.ne']
  have hZ1 : X + u ∈ ball (0 : Rd d) 1 := by
    rw [mem_ball_zero_iff]
    have := mem_closedBall_zero_iff.1 hX
    calc ‖X + u‖ ≤ ‖X‖ + ‖u‖ := norm_add_le _ _
      _ < 1 := by rw [hun]; linarith
  have hZ2 : X + u ∈ ball X r₀ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hun]; exact hXY.1
  have hXr : X ∈ ball Y r₀ := by rw [mem_ball, dist_eq_norm]; exact hXY.1
  have h1 := hr X hX p (hT X hX1) _ hZ2
  have h2 := hT Y hY1 _ hZ1
  have h3 := hr Y hY p' (hT Y hY1) _ hXr
  rw [add_sub_cancel_left, hun] at h1
  have hZY : X + u - Y = u + (X - Y) := by abel
  rw [hZY, inner_add_right] at h2
  have hXYn : ‖X - Y‖ = t := rfl
  rw [hXYn] at h3
  have hin : inner ℝ (p - p') u = t * ‖p - p'‖ := by
    rw [hu, inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  have hin2 : inner ℝ (p - p') u = inner ℝ p u - inner ℝ p' u := inner_sub_left _ _ _
  have key : t * ‖p - p'‖ ≤ 2 * Λ * t ^ 2 := by nlinarith
  rcases eq_or_lt_of_le (norm_nonneg (X - Y)) with h0 | hpos
  · have : X = Y := by rw [← sub_eq_zero, ← norm_eq_zero]; exact h0.symm
    exact absurd (show gradient V X = gradient V Y by rw [this]) hpp
  · have : ‖p - p'‖ ≤ 2 * Λ * t := by
      nlinarith
    exact this

/-- `∇V` is `2Λ`-Lipschitz on `B̄_δ`. -/
theorem lipschitzOnWith_gradient (hΛ : 0 ≤ Λ) (hA : Semiconvex V Λ)
    (hT : ∀ X ∈ ball (0 : Rd d) 1, Touch V X (gradient V X)) {δ : ℝ} (hδ : δ < 1) :
    LipschitzOnWith (2 * Λ).toNNReal (gradient V) (closedBall (0 : Rd d) δ) := by
  obtain ⟨r₀, hr₀, hr⟩ := hA δ hδ
  refine lipschitzOnWith_of_local (convex_closedBall 0 δ) (ρ := min r₀ (1 - δ))
    (lt_min hr₀ (by linarith))
    fun x hx y hy hxy => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  rw [dist_eq_norm] at hxy
  exact gradient_dist_le hΛ hδ hT hr hx hy hxy

/-- Monotonicity of the gradient of a concave function. -/
theorem inner_gradient_sub_nonpos (hT : ∀ X ∈ ball (0 : Rd d) 1, Touch V X (gradient V X))
    {X Y : Rd d} (hX : X ∈ ball (0 : Rd d) 1) (hY : Y ∈ ball (0 : Rd d) 1) :
    inner ℝ (gradient V Y - gradient V X) (Y - X) ≤ 0 := by
  have h1 := hT X hX Y hY
  have h2 := hT Y hY X hX
  have : X - Y = -(Y - X) := by abel
  rw [this, inner_neg_right] at h2
  rw [inner_sub_left]
  linarith

/-- At a differentiability point of `∇V` in `B_1`, the quadratic form of the derivative is `≤ 0`. -/
theorem inner_fderiv_gradient_nonpos (hT : ∀ X ∈ ball (0 : Rd d) 1, Touch V X (gradient V X))
    {x : Rd d} (hx : x ∈ ball (0 : Rd d) 1) {A : Rd d →L[ℝ] Rd d}
    (hAx : HasFDerivAt (gradient V) A x) (v : Rd d) : inner ℝ (A v) v ≤ 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hg : HasDerivAt (fun t : ℝ => gradient V (x + t • v)) (A v) 0 :=
    hAx.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hφ : HasDerivAt (fun t : ℝ => inner ℝ v (gradient V (x + t • v))) (inner ℝ v (A v)) 0 := by
    have := (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
    simp only [Function.comp_def, innerSL_apply_apply] at this
    exact this
  have hsl := hφ.tendsto_slope_zero_right
  have hε : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • v ∈ ball (0 : Rd d) 1 := by
    have hc : ContinuousAt (fun t : ℝ => x + t • v) 0 := hline.continuousAt
    have : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ ball (0 : Rd d) 1 :=
      hc.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hx)
    exact nhdsWithin_le_nhds this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • (inner ℝ v (gradient V (x + (0 + t) • v)) - inner ℝ v (gradient V (x + (0 : ℝ) • v)))
        ≤ 0 := by
    filter_upwards [hε, self_mem_nhdsWithin] with t ht ht0
    rw [zero_add, zero_smul, add_zero, smul_eq_mul]
    have hmono := inner_gradient_sub_nonpos hT hx ht
    rw [add_sub_cancel_left, inner_smul_right, real_inner_comm] at hmono
    have ht0' : (0 : ℝ) < t := ht0
    have : inner ℝ v (gradient V (x + t • v)) - inner ℝ v (gradient V x) ≤ 0 := by
      rw [← inner_sub_right]
      by_contra hcon
      have := mul_pos ht0' (not_le.1 hcon)
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht0'.le) this
  have := le_of_tendsto hsl hev
  rwa [real_inner_comm] at this

/-- At a differentiability point of `∇V` in `B_δ`, `‖D∇V‖ ≤ 2Λ`, so the quadratic form is
`≥ -2Λ |v|²`. -/
theorem neg_le_inner_fderiv_gradient (hΛ : 0 ≤ Λ) {δ : ℝ}
    (hlip : LipschitzOnWith (2 * Λ).toNNReal (gradient V) (closedBall (0 : Rd d) δ))
    {x : Rd d} (hx : x ∈ ball (0 : Rd d) δ) {A : Rd d →L[ℝ] Rd d}
    (hAx : HasFDerivAt (gradient V) A x) (v : Rd d) :
    -(2 * Λ) * ‖v‖ ^ 2 ≤ inner ℝ (A v) v := by
  have hnorm : ‖A‖ ≤ 2 * Λ := by
    have := hAx.le_of_lipschitzOn (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
      hlip
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  have h1 : |inner ℝ (A v) v| ≤ ‖A v‖ * ‖v‖ := abs_real_inner_le_norm _ _
  have h2 : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  have h3 : ‖A v‖ * ‖v‖ ≤ 2 * Λ * ‖v‖ ^ 2 := by
    calc ‖A v‖ * ‖v‖ ≤ ‖A‖ * ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ 2 * Λ * ‖v‖ * ‖v‖ := by gcongr
      _ = 2 * Λ * ‖v‖ ^ 2 := by ring
  rw [abs_le] at h1
  linarith [h1.1]

/-- Symmetry of the derivative of `∇V` at differentiability points in `B_1`. -/
theorem inner_fderiv_gradient_comm
    (hD : ∀ X ∈ ball (0 : Rd d) 1, HasFDerivAt V (innerSL ℝ (gradient V X)) X)
    {x : Rd d} (hx : x ∈ ball (0 : Rd d) 1) {A : Rd d →L[ℝ] Rd d}
    (hAx : HasFDerivAt (gradient V) A x) (v w : Rd d) :
    inner ℝ (A v) w = inner ℝ v (A w) := by
  have hf : ∀ᶠ y in 𝓝 x, HasFDerivAt V (innerSL ℝ (gradient V y)) y :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) hD
  have hx' : HasFDerivAt (fun y => innerSL ℝ (gradient V y)) ((innerSL ℝ).comp A) x :=
    (innerSL ℝ).hasFDerivAt.comp x hAx
  have := second_derivative_symmetric_of_eventually hf hx' v w
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at this
  rw [this, real_inner_comm]

end Gradient

end UniformConcavity

end RandomSandpile

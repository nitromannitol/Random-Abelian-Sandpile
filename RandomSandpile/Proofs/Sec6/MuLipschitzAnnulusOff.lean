import RandomSandpile.Proofs.Sec6.MuLipschitzAnnulus

/-!
# An off-centre annulus is a bounded Lipschitz domain

For `d ≥ 2`, the unit ball minus a closed sub-ball, `B_1 \ B̄_r(c)` with `B̄_r(c) ⊆ B_1`, `r > 0`,
is a bounded Lipschitz domain. This is the translated analogue of
`MuLipschitzAnnulus.annulus_isLipschitzDomain` (the centred case `c = 0`).

Put `m = 1 - ‖c‖ - r > 0`. Bounded and open are immediate. Connected: the centred shell
`B_1 \ B̄_{1 - m/2}` is a connected subset, and every point of the domain is joined to it by a
segment moving radially away from `c`. At an outer boundary point `‖x₀‖ = 1` we reuse
`unitBallLipschitz` on a smaller ball, and at an inner boundary point `‖x₀ - c‖ = r` we use the
direction `e = (x₀ - c)/r` and `γ(v) = √(r² - min(|v|, r/2)²) - r`, which is `1`-Lipschitz.
-/

open MeasureTheory LatticeProb Metric
namespace RandomSandpile
namespace MuLipschitzAnnulusOff

/-- Pythagoras for the splitting of `y - c e` along a unit vector `e`.
Copy of the private `annulus_geom` of `RandomSandpile/Proofs/Sec6/MuLipschitzAnnulus.lean`. -/
private lemma offAnnulus_geom {d : ℕ} {e : Rd d} (he : ‖e‖ = 1) (c : ℝ) (y : Rd d) :
    ‖y‖ ^ 2 = (c + inner ℝ (y - c • e) e) ^ 2 +
        ‖(y - c • e) - inner ℝ (y - c • e) e • e‖ ^ 2 ∧
    ‖y - c • e‖ ^ 2 = (inner ℝ (y - c • e) e) ^ 2 +
        ‖(y - c • e) - inner ℝ (y - c • e) e • e‖ ^ 2 := by
  obtain ⟨t, ht⟩ : ∃ t, t = inner ℝ (y - c • e) e := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z', z' = (y - c • e) - t • e := ⟨_, rfl⟩
  rw [← ht, ← hz']
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have h0 : inner ℝ e z' = 0 := by
    rw [hz', inner_sub_right, inner_smul_right, hee, real_inner_comm, ← ht]
    ring
  have hy : y = (c + t) • e + z' := by
    rw [hz', add_smul]
    abel
  have hz : y - c • e = t • e + z' := by
    rw [hz']; abel
  have h1 : inner ℝ ((c + t) • e) z' = 0 := by rw [inner_smul_left, h0]; simp
  have h2 : inner ℝ (t • e) z' = 0 := by rw [inner_smul_left, h0]; simp
  constructor
  · conv_lhs => rw [hy]
    rw [norm_add_sq_real, h1, norm_smul, mul_pow, he]
    simp
  · conv_lhs => rw [hz]
    rw [norm_add_sq_real, h2, norm_smul, mul_pow, he]
    simp

/-- `a ↦ √(ρ² - a²)` is `1`-Lipschitz on `[0, ρ/2]`.
Copy of the private `sqrt_sub_sq_dist` of `RandomSandpile/Proofs/Sec6/MuLipschitzAnnulus.lean`. -/
private lemma offSqrt_sub_sq_dist {ρ a b : ℝ} (hρ : 0 < ρ) (ha : 0 ≤ a) (ha' : a ≤ ρ / 2)
    (hb : 0 ≤ b) (hb' : b ≤ ρ / 2) : |√(ρ ^ 2 - a ^ 2) - √(ρ ^ 2 - b ^ 2)| ≤ |a - b| := by
  have hp2 : √(ρ ^ 2 - a ^ 2) ^ 2 = ρ ^ 2 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have hq2 : √(ρ ^ 2 - b ^ 2) ^ 2 = ρ ^ 2 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have hp : ρ / 2 ≤ √(ρ ^ 2 - a ^ 2) := (Real.le_sqrt' (by linarith)).2 (by nlinarith)
  have hq : ρ / 2 ≤ √(ρ ^ 2 - b ^ 2) := (Real.le_sqrt' (by linarith)).2 (by nlinarith)
  have key : (√(ρ ^ 2 - a ^ 2) - √(ρ ^ 2 - b ^ 2)) * (√(ρ ^ 2 - a ^ 2) + √(ρ ^ 2 - b ^ 2)) =
      (b - a) * (b + a) := by
    linear_combination hp2 - hq2
  have key' := congrArg abs key
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ √(ρ ^ 2 - a ^ 2) + √(ρ ^ 2 - b ^ 2)),
    abs_of_nonneg (by linarith : 0 ≤ b + a)] at key'
  have hmain : |√(ρ ^ 2 - a ^ 2) - √(ρ ^ 2 - b ^ 2)| * ρ ≤ |a - b| * ρ := by
    calc |√(ρ ^ 2 - a ^ 2) - √(ρ ^ 2 - b ^ 2)| * ρ
        ≤ |√(ρ ^ 2 - a ^ 2) - √(ρ ^ 2 - b ^ 2)| *
            (√(ρ ^ 2 - a ^ 2) + √(ρ ^ 2 - b ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |b - a| * (b + a) := key'
      _ ≤ |b - a| * ρ := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |a - b| * ρ := by rw [abs_sub_comm]
  exact le_of_mul_le_mul_right hmain hρ

/-- Copy of the private `annulusGamma_lipschitz` of
`RandomSandpile/Proofs/Sec6/MuLipschitzAnnulus.lean`. -/
private lemma offAnnulusGamma_lipschitz (d : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzWith 1 (fun v : Rd d => √(ρ ^ 2 - (min ‖v‖ (ρ / 2)) ^ 2) - ρ) := by
  refine LipschitzWith.mk_one fun v w => ?_
  have hm := (lipschitzWith_one_norm.min_const (ρ / 2)).dist_le_mul v w
  rw [Real.dist_eq, NNReal.coe_one, one_mul] at hm
  have hv0 : 0 ≤ min ‖v‖ (ρ / 2) := le_min (norm_nonneg _) (by linarith)
  have hw0 : 0 ≤ min ‖w‖ (ρ / 2) := le_min (norm_nonneg _) (by linarith)
  rw [Real.dist_eq]
  calc |(√(ρ ^ 2 - (min ‖v‖ (ρ / 2)) ^ 2) - ρ) - (√(ρ ^ 2 - (min ‖w‖ (ρ / 2)) ^ 2) - ρ)|
      = |√(ρ ^ 2 - (min ‖v‖ (ρ / 2)) ^ 2) - √(ρ ^ 2 - (min ‖w‖ (ρ / 2)) ^ 2)| := by
        congr 1; ring
    _ ≤ |min ‖v‖ (ρ / 2) - min ‖w‖ (ρ / 2)| :=
        offSqrt_sub_sq_dist hρ hv0 (min_le_right _ _) hw0 (min_le_right _ _)
    _ ≤ dist v w := hm

/-- A closed sub-ball of the unit ball has `‖c‖ + r < 1`. -/
private lemma offNorm_add_radius_lt {d : ℕ} (hd : 2 ≤ d) (c : Rd d) {r : ℝ} (hr : 0 < r)
    (hcr : closedBall c r ⊆ ball (0 : Rd d) 1) : ‖c‖ + r < 1 := by
  obtain ⟨u, hu, hcu⟩ : ∃ u : Rd d, ‖u‖ = 1 ∧ ‖c + r • u‖ = ‖c‖ + r := by
    by_cases hc : c = 0
    · subst hc
      have : Nontrivial (Rd d) := by
        have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
        infer_instance
      obtain ⟨u, hu⟩ := exists_norm_eq (Rd d) zero_le_one
      refine ⟨u, hu, ?_⟩
      rw [zero_add, norm_smul, hu, Real.norm_of_nonneg hr.le, norm_zero]
      ring
    · have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
      refine ⟨‖c‖⁻¹ • c, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc'.ne']
      · have h1 : c + r • (‖c‖⁻¹ • c) = (1 + r * ‖c‖⁻¹) • c := by
          rw [smul_smul, add_smul, one_smul]
        rw [h1, norm_smul, Real.norm_of_nonneg (by positivity)]
        field_simp
  have hmem : c + r • u ∈ closedBall c r := by
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul, hu, Real.norm_of_nonneg hr.le,
      mul_one]
  have := hcr hmem
  rw [mem_ball_zero_iff, hcu] at this
  exact this

/-- The off-centre annulus is connected, for `d ≥ 2`. `m = 1 - ‖c‖ - r > 0`. -/
private lemma offAnnulus_connected {d : ℕ} (hd : 2 ≤ d) (c : Rd d) {r m : ℝ} (hr : 0 < r)
    (hm : ‖c‖ + r + m = 1) (hm0 : 0 < m) :
    IsConnected (ball (0 : Rd d) 1 \ closedBall c r) := by
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
  have hS := (MuLipschitzAnnulus.annulus_isLipschitzDomain hd (ρ := 1 - m / 2)
    (by linarith) (by linarith)).2.2.1
  have hSW : ball (0 : Rd d) 1 \ closedBall (0 : Rd d) (1 - m / 2) ⊆
      ball (0 : Rd d) 1 \ closedBall c r := by
    intro x hx
    rw [Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le] at hx
    refine ⟨mem_ball_zero_iff.2 hx.1, fun h => ?_⟩
    rw [mem_closedBall_iff_norm] at h
    have := norm_sub_norm_le x c
    linarith [hx.2]
  obtain ⟨x₁, hx₁⟩ := hS.nonempty
  refine ⟨⟨x₁, hSW hx₁⟩, ?_⟩
  refine isPreconnected_of_forall x₁ fun x hx => ?_
  by_cases hxS : x ∈ ball (0 : Rd d) 1 \ closedBall (0 : Rd d) (1 - m / 2)
  · exact ⟨_, hSW, hx₁, hxS, hS.isPreconnected⟩
  · -- radial path away from `c`
    have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.1 hx.1
    have hxc : r < ‖x - c‖ := by
      have := hx.2
      rw [mem_closedBall_iff_norm, not_le] at this
      exact this
    have hxle : ‖x‖ ≤ 1 - m / 2 := by
      by_contra h
      rw [not_le] at h
      exact hxS ⟨mem_ball_zero_iff.2 hx1, by rw [mem_closedBall_zero_iff, not_le]; exact h⟩
    have ha0 : 0 < ‖x - c‖ := hr.trans hxc
    obtain ⟨u, hu, hxu⟩ : ∃ u : Rd d, ‖u‖ = 1 ∧ x - c = ‖x - c‖ • u := by
      refine ⟨‖x - c‖⁻¹ • (x - c), ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ha0.ne']
      · rw [smul_inv_smul₀ ha0.ne']
    have hf : Continuous fun t : ℝ => ‖x + t • u‖ := by fun_prop
    have h0 : (1 - m / 4) ∈ Set.Icc ((fun t : ℝ => ‖x + t • u‖) 0)
        ((fun t : ℝ => ‖x + t • u‖) 2) := by
      refine ⟨?_, ?_⟩
      · simp only [zero_smul, add_zero]
        linarith
      · have h3 := norm_sub_le (x + (2 : ℝ) • u) x
        rw [add_sub_cancel_left, norm_smul, hu] at h3
        simp only
        norm_num at h3
        linarith
    obtain ⟨t, ⟨ht0, -⟩, hft⟩ :=
      intermediate_value_Icc (zero_le_two) hf.continuousOn h0
    simp only at hft
    set y' : Rd d := x + t • u with hy'
    have hy'S : y' ∈ ball (0 : Rd d) 1 \ closedBall (0 : Rd d) (1 - m / 2) := by
      rw [Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le, hft]
      exact ⟨by linarith, by linarith⟩
    have hy'W := hSW hy'S
    have hseg : segment ℝ x y' ⊆ ball (0 : Rd d) 1 \ closedBall c r := by
      intro z hz
      refine ⟨(convex_ball (0 : Rd d) 1).segment_subset hx.1 hy'W.1 hz, fun hzc => ?_⟩
      rw [segment_eq_image'] at hz
      obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
      rw [mem_closedBall_iff_norm] at hzc
      have hz1 : x + θ • (y' - x) - c = (‖x - c‖ + θ * t) • u := by
        have : y' - x = t • u := by rw [hy']; abel
        rw [this, add_smul, smul_smul, ← hxu]
        abel
      rw [hz1, norm_smul, hu, mul_one, Real.norm_of_nonneg (by positivity)] at hzc
      nlinarith [mul_nonneg hθ0 ht0]
    exact ⟨_, Set.union_subset hSW hseg, Or.inl hx₁, Or.inr (left_mem_segment ℝ x y'),
      hS.isPreconnected.union y' hy'S (right_mem_segment ℝ x y')
        (convex_segment x y').isPreconnected⟩

/-- For `d ≥ 2`, the unit ball minus a closed sub-ball, `B_1 \ B̄_r(c)` with `B̄_r(c) ⊆ B_1`, `r > 0`,
is a bounded Lipschitz domain. -/
theorem isLipschitzDomain_ball_sdiff_closedBall {d : ℕ} (hd : 2 ≤ d) (c : Rd d) {r : ℝ}
    (hr : 0 < r) (hcr : closedBall c r ⊆ ball (0 : Rd d) 1) :
    IsLipschitzDomain (ball (0 : Rd d) 1 \ closedBall c r) := by
  have hcr1 : ‖c‖ + r < 1 := offNorm_add_radius_lt hd c hr hcr
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
  obtain ⟨m, hm⟩ : ∃ m, m = 1 - ‖c‖ - r := ⟨_, rfl⟩
  have hm0 : 0 < m := by linarith
  have hopen : IsOpen (ball (0 : Rd d) 1 \ closedBall c r) :=
    isOpen_ball.sdiff isClosed_closedBall
  refine ⟨(isBounded_ball (x := (0 : Rd d)) (r := 1)).subset Set.sdiff_subset, hopen,
    offAnnulus_connected hd c hr (m := m) (by linarith) hm0, ?_⟩
  intro x₀ hx₀
  -- location of the frontier point
  have hcl : closure (ball (0 : Rd d) 1 \ closedBall c r) ⊆
      closedBall (0 : Rd d) 1 ∩ (ball c r)ᶜ := by
    refine closure_minimal ?_ (isClosed_closedBall.inter isOpen_ball.isClosed_compl)
    intro y hy
    exact ⟨ball_subset_closedBall hy.1, fun h => hy.2 (ball_subset_closedBall h)⟩
  rw [frontier, hopen.interior_eq] at hx₀
  obtain ⟨hx1, hx2⟩ := hcl hx₀.1
  rw [mem_closedBall_zero_iff] at hx1
  rw [Set.mem_compl_iff, mem_ball_iff_norm, not_lt] at hx2
  have hxW : ¬ (‖x₀‖ < 1 ∧ ¬ ‖x₀ - c‖ ≤ r) := by
    intro h
    exact hx₀.2 ⟨mem_ball_zero_iff.2 h.1, fun h' => h.2 (mem_closedBall_iff_norm.1 h')⟩
  have hcase : ‖x₀‖ = 1 ∨ ‖x₀ - c‖ = r := by
    by_cases h : ‖x₀‖ < 1
    · right
      have : ‖x₀ - c‖ ≤ r := by
        by_contra h'
        exact hxW ⟨h, h'⟩
      exact le_antisymm this hx2
    · left
      exact le_antisymm hx1 (not_lt.1 h)
  rcases hcase with hn | hn
  · -- outer boundary point: reuse the unit ball
    have : Nontrivial (Rd d) := by
      have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      infer_instance
    have hfr : x₀ ∈ frontier (ball (0 : Rd d) 1) := by
      rw [frontier_ball (0 : Rd d) one_ne_zero, mem_sphere_zero_iff_norm]
      exact hn
    obtain ⟨ρ, hρ, e, he, L, γ, hγ, hiff⟩ := (unitBallLipschitz d).2.2.2 x₀ hfr
    refine ⟨min ρ m, lt_min hρ hm0, e, he, L, γ, hγ, ?_⟩
    intro y hy
    have hyr : y ∈ ball x₀ ρ := ball_subset_ball (min_le_left _ _) hy
    rw [← hiff y hyr]
    have hy' : ‖y - x₀‖ < m := by
      have := (mem_ball_iff_norm.1 hy).trans_le (min_le_right _ _)
      exact this
    have hyc : r < ‖y - c‖ := by
      have h3 := norm_sub_norm_le x₀ y
      rw [norm_sub_rev x₀ y] at h3
      have h4 := norm_sub_norm_le y c
      linarith
    constructor
    · intro h
      exact h.1
    · intro h
      refine ⟨h, fun h' => ?_⟩
      rw [mem_closedBall_iff_norm] at h'
      linarith
  · -- inner boundary point
    obtain ⟨e, he, rfl⟩ : ∃ e : Rd d, ‖e‖ = 1 ∧ x₀ = c + r • e := by
      refine ⟨r⁻¹ • (x₀ - c), ?_, ?_⟩
      · rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, hn, inv_mul_cancel₀ hr.ne']
      · rw [smul_inv_smul₀ hr.ne']
        abel
    refine ⟨min (r / 2) (m / 2), lt_min (by linarith) (by linarith), e, he, 1,
      fun v => √(r ^ 2 - (min ‖v‖ (r / 2)) ^ 2) - r, offAnnulusGamma_lipschitz d hr, ?_⟩
    intro y hy
    rw [mem_ball_iff_norm] at hy
    have hyx : y - (c + r • e) = (y - c) - r • e := by abel
    rw [hyx] at hy ⊢
    obtain ⟨h1, h2⟩ := offAnnulus_geom he r (y - c)
    obtain ⟨t, ht⟩ : ∃ t, t = inner ℝ ((y - c) - r • e) e := ⟨_, rfl⟩
    obtain ⟨z', hz'⟩ : ∃ z', z' = ((y - c) - r • e) - t • e := ⟨_, rfl⟩
    rw [← ht, ← hz'] at h1 h2 ⊢
    have hyr : ‖(y - c) - r • e‖ < r / 2 := hy.trans_le (min_le_left _ _)
    have hyr' : ‖(y - c) - r • e‖ < m / 2 := hy.trans_le (min_le_right _ _)
    have hz : ‖(y - c) - r • e‖ ^ 2 < r ^ 2 / 4 := by
      nlinarith [norm_nonneg ((y - c) - r • e)]
    have hb0 : 0 ≤ ‖z'‖ := norm_nonneg _
    have hb : ‖z'‖ < r / 2 := by nlinarith
    have ht2 : |t| < r / 2 := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
    have ht3 : 0 < r + t := by linarith [(abs_lt.mp ht2).1]
    have hy1 : ‖y‖ < 1 := by
      have h5 : ‖y‖ ≤ ‖c + r • e‖ + ‖y - (c + r • e)‖ :=
        norm_le_norm_add_norm_sub' y (c + r • e)
      rw [hyx] at h5
      have h6 : ‖c + r • e‖ ≤ ‖c‖ + ‖r • e‖ := norm_add_le _ _
      rw [norm_smul, he, Real.norm_of_nonneg hr.le, mul_one] at h6
      linarith
    beta_reduce
    rw [Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_iff_norm, min_eq_left hb.le, not_le]
    constructor
    · rintro ⟨-, h⟩
      have h' : r ^ 2 < ‖y - c‖ ^ 2 := by nlinarith [norm_nonneg (y - c)]
      have : √(r ^ 2 - ‖z'‖ ^ 2) < r + t := (Real.sqrt_lt' ht3).2 (by nlinarith)
      linarith
    · intro h
      refine ⟨hy1, ?_⟩
      by_contra hcon
      rw [not_lt] at hcon
      have h3 : √(r ^ 2 - ‖z'‖ ^ 2) < r + t := by linarith
      have h4 := (Real.sqrt_lt' ht3).1 h3
      nlinarith [norm_nonneg (y - c)]

end MuLipschitzAnnulusOff
end RandomSandpile

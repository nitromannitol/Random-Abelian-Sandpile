import RandomSandpile.Proofs.Sec5.MuConvergenceBall

/-!
# An open annulus is a bounded Lipschitz domain

For `d ≥ 2` and `0 < ρ < 1` the open annulus `B_1 \ B̄_ρ` is a bounded Lipschitz domain.
Bounded and open are immediate; connected because it is the image of `(ρ, 1) × S^{d-1}` under
`(s, u) ↦ s • u` (this needs `d ≥ 2`); at an outer boundary point `‖x₀‖ = 1` we reuse
`unitBallLipschitz` on a smaller ball, and at an inner boundary point `‖x₀‖ = ρ` we use the
direction `e = x₀/ρ` and `γ(v) = √(ρ² - min(|v|, ρ/2)²) - ρ`, which is `1`-Lipschitz.
-/

open MeasureTheory LatticeProb Metric
namespace RandomSandpile
namespace MuLipschitzAnnulus

/-- Pythagoras for the splitting of `y - c e` along a unit vector `e`. -/
private lemma annulus_geom {d : ℕ} {e : Rd d} (he : ‖e‖ = 1) (c : ℝ) (y : Rd d) :
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

/-- `a ↦ √(ρ² - a²)` is `1`-Lipschitz on `[0, ρ/2]`. -/
private lemma sqrt_sub_sq_dist {ρ a b : ℝ} (hρ : 0 < ρ) (ha : 0 ≤ a) (ha' : a ≤ ρ / 2)
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

private lemma annulusGamma_lipschitz (d : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
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
        sqrt_sub_sq_dist hρ hv0 (min_le_right _ _) hw0 (min_le_right _ _)
    _ ≤ dist v w := hm

/-- The open annulus is connected, for `d ≥ 2`: image of `(ρ, 1) × S^{d-1}`. -/
private lemma annulus_connected {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    IsConnected (ball (0 : Rd d) 1 \ closedBall (0 : Rd d) ρ) := by
  have hrank : 1 < Module.rank ℝ (Rd d) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast hd
  have hP := (isConnected_Ioo hρ1).prod (isConnected_sphere hrank (0 : Rd d) zero_le_one)
  have himg := hP.image (fun p : ℝ × Rd d => p.1 • p.2)
    (continuous_fst.smul continuous_snd).continuousOn
  convert himg using 1
  ext x
  simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, Set.mem_image,
    Set.mem_prod, Set.mem_Ioo, mem_sphere_zero_iff_norm, Prod.exists]
  constructor
  · rintro ⟨h1, h2⟩
    rw [not_le] at h2
    have hx0 : ‖x‖ ≠ 0 := (hρ0.trans h2).ne'
    refine ⟨‖x‖, ‖x‖⁻¹ • x, ⟨⟨h2, h1⟩, ?_⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0]
    · rw [smul_inv_smul₀ hx0]
  · rintro ⟨a, v, ⟨⟨ha1, ha2⟩, hv⟩, rfl⟩
    rw [norm_smul, hv, Real.norm_of_nonneg (by linarith), mul_one]
    exact ⟨ha2, not_le.2 ha1⟩

/-- The open annulus `B_1 \ B̄_ρ` of `ℝ^d`, `d ≥ 2`, `0 < ρ < 1`, is a bounded Lipschitz domain. -/
theorem annulus_isLipschitzDomain {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    IsLipschitzDomain (ball (0 : Rd d) 1 \ closedBall (0 : Rd d) ρ) := by
  have hopen : IsOpen (ball (0 : Rd d) 1 \ closedBall (0 : Rd d) ρ) :=
    isOpen_ball.sdiff isClosed_closedBall
  refine ⟨(isBounded_ball (x := (0 : Rd d)) (r := 1)).subset Set.sdiff_subset, hopen,
    annulus_connected hd hρ0 hρ1, ?_⟩
  intro x₀ hx₀
  -- location of the frontier point
  have hcl : closure (ball (0 : Rd d) 1 \ closedBall (0 : Rd d) ρ) ⊆
      closedBall (0 : Rd d) 1 ∩ (ball (0 : Rd d) ρ)ᶜ := by
    refine closure_minimal ?_ (isClosed_closedBall.inter isOpen_ball.isClosed_compl)
    intro y hy
    exact ⟨ball_subset_closedBall hy.1, fun h => hy.2 (ball_subset_closedBall h)⟩
  rw [frontier, hopen.interior_eq] at hx₀
  obtain ⟨hx1, hx2⟩ := hcl hx₀.1
  rw [mem_closedBall_zero_iff] at hx1
  rw [Set.mem_compl_iff, mem_ball_zero_iff, not_lt] at hx2
  have hxW : ¬ (‖x₀‖ < 1 ∧ ¬ ‖x₀‖ ≤ ρ) := by
    intro h
    exact hx₀.2 ⟨mem_ball_zero_iff.2 h.1, fun h' => h.2 (mem_closedBall_zero_iff.1 h')⟩
  have hcase : ‖x₀‖ = 1 ∨ ‖x₀‖ = ρ := by
    by_cases h : ‖x₀‖ < 1
    · right
      have : ‖x₀‖ ≤ ρ := by
        by_contra h'
        exact hxW ⟨h, h'⟩
      exact le_antisymm this hx2
    · left
      exact le_antisymm hx1 (not_lt.1 h)
  rcases hcase with hn | hn
  · -- outer boundary point: reuse the unit ball
    haveI : Nontrivial (Rd d) := by
      haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      infer_instance
    have hfr : x₀ ∈ frontier (ball (0 : Rd d) 1) := by
      rw [frontier_ball (0 : Rd d) one_ne_zero, mem_sphere_zero_iff_norm]
      exact hn
    obtain ⟨r, hr, e, he, L, γ, hγ, hiff⟩ := (unitBallLipschitz d).2.2.2 x₀ hfr
    refine ⟨min r (1 - ρ), lt_min hr (by linarith), e, he, L, γ, hγ, ?_⟩
    intro y hy
    have hyr : y ∈ ball x₀ r := ball_subset_ball (min_le_left _ _) hy
    rw [← hiff y hyr]
    have hy' : ‖y - x₀‖ < 1 - ρ := by
      have := (mem_ball_iff_norm.1 hy).trans_le (min_le_right _ _)
      exact this
    have hyρ : ρ < ‖y‖ := by
      have h3 := norm_sub_norm_le x₀ y
      rw [norm_sub_rev x₀ y] at h3
      linarith
    constructor
    · intro h
      exact h.1
    · intro h
      refine ⟨h, fun h' => ?_⟩
      rw [mem_closedBall_zero_iff] at h'
      linarith
  · -- inner boundary point
    obtain ⟨e, he, rfl⟩ : ∃ e : Rd d, ‖e‖ = 1 ∧ x₀ = ρ • e := by
      refine ⟨ρ⁻¹ • x₀, ?_, ?_⟩
      · rw [norm_smul, norm_inv, Real.norm_of_nonneg hρ0.le, hn, inv_mul_cancel₀ hρ0.ne']
      · rw [smul_inv_smul₀ hρ0.ne']
    refine ⟨min (ρ / 2) (1 - ρ), lt_min (by linarith) (by linarith), e, he, 1,
      fun v => √(ρ ^ 2 - (min ‖v‖ (ρ / 2)) ^ 2) - ρ, annulusGamma_lipschitz d hρ0, ?_⟩
    intro y hy
    rw [mem_ball_iff_norm] at hy
    obtain ⟨h1, h2⟩ := annulus_geom he ρ y
    obtain ⟨t, ht⟩ : ∃ t, t = inner ℝ (y - ρ • e) e := ⟨_, rfl⟩
    obtain ⟨z', hz'⟩ : ∃ z', z' = (y - ρ • e) - t • e := ⟨_, rfl⟩
    rw [← ht, ← hz'] at h1 h2 ⊢
    have hyr : ‖y - ρ • e‖ < ρ / 2 := hy.trans_le (min_le_left _ _)
    have hyr' : ‖y - ρ • e‖ < 1 - ρ := hy.trans_le (min_le_right _ _)
    have hz : ‖y - ρ • e‖ ^ 2 < ρ ^ 2 / 4 := by
      nlinarith [norm_nonneg (y - ρ • e)]
    have hb0 : 0 ≤ ‖z'‖ := norm_nonneg _
    have hb : ‖z'‖ < ρ / 2 := by nlinarith
    have ht2 : |t| < ρ / 2 := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
    have ht3 : 0 < ρ + t := by linarith [(abs_lt.mp ht2).1]
    have hy1 : ‖y‖ < 1 := by
      have h5 : ‖y‖ ≤ ‖ρ • e‖ + ‖y - ρ • e‖ := norm_le_norm_add_norm_sub' y (ρ • e)
      rw [norm_smul, he, Real.norm_of_nonneg hρ0.le, mul_one] at h5
      linarith
    beta_reduce
    rw [Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, min_eq_left hb.le, not_le]
    constructor
    · rintro ⟨-, h⟩
      have h' : ρ ^ 2 < ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
      have : √(ρ ^ 2 - ‖z'‖ ^ 2) < ρ + t := (Real.sqrt_lt' ht3).2 (by nlinarith)
      linarith
    · intro h
      refine ⟨hy1, ?_⟩
      by_contra hcon
      rw [not_lt] at hcon
      have h3 : √(ρ ^ 2 - ‖z'‖ ^ 2) < ρ + t := by linarith
      have h4 := (Real.sqrt_lt' ht3).1 h3
      nlinarith [norm_nonneg y]

end MuLipschitzAnnulus
end RandomSandpile

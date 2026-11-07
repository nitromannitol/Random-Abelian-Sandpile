import RandomSandpile.Steps.Sec5.MuConvergence

/-!
# Lemma 5.5, Steps 4-5: the unit ball is a Lipschitz domain; `nW ∩ ℤ^d` is finite

* `unitBallLipschitz`: at a boundary point `x₀` (`‖x₀‖ = 1`) take `r = 1/2`, the inner normal
  `e = -x₀` and `γ(v) = 1 - √(1 - min(|v|, 1/2)²)`, which is `1`-Lipschitz; writing
  `y - x₀ = z' + t e` with `z' ⊥ e`, `|y|² = (1 - t)² + |z'|²`, so `|y| < 1` iff `γ(z') < t`
  inside `B_{1/2}(x₀)`. The frontier is located without `frontier_ball`, so every `d` is covered.
* `discretizeFinite`: `nW` lies in a Euclidean ball, whose lattice points lie in a finite box.
-/

open MeasureTheory LatticeProb
noncomputable section
namespace RandomSandpile

/-- Pythagoras for the splitting of `y - x₀` along `e = -x₀` (with `‖x₀‖ = 1`). -/
private lemma ball_geom {d : ℕ} {x₀ : Rd d} (hx : ‖x₀‖ = 1) (y : Rd d) :
    ‖y‖ ^ 2 = (1 - inner ℝ (y - x₀) (-x₀)) ^ 2 +
        ‖(y - x₀) - inner ℝ (y - x₀) (-x₀) • (-x₀)‖ ^ 2 ∧
    ‖y - x₀‖ ^ 2 = (inner ℝ (y - x₀) (-x₀)) ^ 2 +
        ‖(y - x₀) - inner ℝ (y - x₀) (-x₀) • (-x₀)‖ ^ 2 := by
  obtain ⟨t, ht⟩ : ∃ t, t = inner ℝ (y - x₀) (-x₀) := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z', z' = (y - x₀) - t • (-x₀) := ⟨_, rfl⟩
  rw [← ht, ← hz']
  have hxx : inner ℝ x₀ x₀ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have ht' : t = -inner ℝ (y - x₀) x₀ := by rw [ht, inner_neg_right]
  have h0 : inner ℝ x₀ z' = 0 := by
    rw [hz', inner_sub_right, inner_smul_right, inner_neg_right, hxx, real_inner_comm, ht']
    ring
  have hy : y = (1 - t) • x₀ + z' := by
    rw [hz', sub_smul, one_smul, smul_neg]
    abel
  have hz : y - x₀ = t • (-x₀) + z' := by
    rw [hz']; abel
  have h1 : inner ℝ ((1 - t) • x₀) z' = 0 := by rw [inner_smul_left, h0]; simp
  have h2 : inner ℝ (t • (-x₀)) z' = 0 := by rw [inner_smul_left, inner_neg_left, h0]; simp
  constructor
  · conv_lhs => rw [hy]
    rw [norm_add_sq_real, h1, norm_smul, mul_pow, hx]
    simp
  · conv_lhs => rw [hz]
    rw [norm_add_sq_real, h2, norm_smul, mul_pow, norm_neg, hx]
    simp

/-- `a ↦ √(1 - a²)` is `1`-Lipschitz on `[0, 1/2]`. -/
private lemma sqrt_one_sub_sq_dist {a b : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) (hb : 0 ≤ b)
    (hb' : b ≤ 1 / 2) : |√(1 - a ^ 2) - √(1 - b ^ 2)| ≤ |a - b| := by
  have hp2 : √(1 - a ^ 2) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have hq2 : √(1 - b ^ 2) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have hp : 1 / 2 ≤ √(1 - a ^ 2) := (Real.le_sqrt' (by norm_num)).2 (by nlinarith)
  have hq : 1 / 2 ≤ √(1 - b ^ 2) := (Real.le_sqrt' (by norm_num)).2 (by nlinarith)
  have key : (√(1 - a ^ 2) - √(1 - b ^ 2)) * (√(1 - a ^ 2) + √(1 - b ^ 2)) = (b - a) * (b + a) := by
    linear_combination hp2 - hq2
  have key' := congrArg abs key
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ √(1 - a ^ 2) + √(1 - b ^ 2)),
    abs_of_nonneg (by linarith : 0 ≤ b + a)] at key'
  calc |√(1 - a ^ 2) - √(1 - b ^ 2)|
      ≤ |√(1 - a ^ 2) - √(1 - b ^ 2)| * (√(1 - a ^ 2) + √(1 - b ^ 2)) :=
        le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |b - a| * (b + a) := key'
    _ ≤ |b - a| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |a - b| := by rw [mul_one, abs_sub_comm]

private lemma ballGamma_lipschitz (d : ℕ) :
    LipschitzWith 1 (fun v : Rd d => 1 - √(1 - (min ‖v‖ (1 / 2 : ℝ)) ^ 2)) := by
  refine LipschitzWith.mk_one fun v w => ?_
  have hm := (lipschitzWith_one_norm.min_const (1 / 2 : ℝ)).dist_le_mul v w
  rw [Real.dist_eq, NNReal.coe_one, one_mul] at hm
  have h := sqrt_one_sub_sq_dist (a := min ‖v‖ (1 / 2)) (b := min ‖w‖ (1 / 2))
    (le_min (norm_nonneg _) (by norm_num)) (min_le_right _ _)
    (le_min (norm_nonneg _) (by norm_num)) (min_le_right _ _)
  rw [Real.dist_eq]
  calc |(1 - √(1 - (min ‖v‖ (1 / 2 : ℝ)) ^ 2)) - (1 - √(1 - (min ‖w‖ (1 / 2 : ℝ)) ^ 2))|
      = |√(1 - (min ‖w‖ (1 / 2 : ℝ)) ^ 2) - √(1 - (min ‖v‖ (1 / 2 : ℝ)) ^ 2)| := by
        congr 1; ring
    _ ≤ |min ‖w‖ (1 / 2 : ℝ) - min ‖v‖ (1 / 2 : ℝ)| := sqrt_one_sub_sq_dist
        (le_min (norm_nonneg _) (by norm_num)) (min_le_right _ _)
        (le_min (norm_nonneg _) (by norm_num)) (min_le_right _ _)
    _ = |min ‖v‖ (1 / 2 : ℝ) - min ‖w‖ (1 / 2 : ℝ)| := abs_sub_comm _ _
    _ ≤ dist v w := hm

/-- Step 4. The open unit ball of `ℝ^d` is a bounded Lipschitz domain. -/
theorem unitBallLipschitz : UnitBallLipschitzStmt := by
  intro d
  refine ⟨Metric.isBounded_ball, Metric.isOpen_ball,
    (convex_ball (0 : Rd d) 1).isConnected ⟨0, Metric.mem_ball_self one_pos⟩, ?_⟩
  intro x₀ hx₀
  have hn : ‖x₀‖ = 1 := by
    rw [Metric.isOpen_ball.frontier_eq] at hx₀
    have h1 : x₀ ∈ Metric.closedBall (0 : Rd d) 1 := Metric.closure_ball_subset_closedBall hx₀.1
    have h2 : x₀ ∉ Metric.ball (0 : Rd d) 1 := hx₀.2
    rw [mem_closedBall_zero_iff] at h1
    rw [mem_ball_zero_iff, not_lt] at h2
    exact le_antisymm h1 h2
  refine ⟨1 / 2, by norm_num, -x₀, by rw [norm_neg, hn], 1,
    fun v => 1 - √(1 - (min ‖v‖ (1 / 2 : ℝ)) ^ 2), ballGamma_lipschitz d, ?_⟩
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  obtain ⟨h1, h2⟩ := ball_geom hn y
  obtain ⟨t, ht⟩ : ∃ t, t = inner ℝ (y - x₀) (-x₀) := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z', z' = (y - x₀) - t • (-x₀) := ⟨_, rfl⟩
  rw [← ht, ← hz'] at h1 h2 ⊢
  have hz : ‖y - x₀‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg (y - x₀)]
  have hb0 : 0 ≤ ‖z'‖ := norm_nonneg _
  have hb : ‖z'‖ < 1 / 2 := by nlinarith
  have ht2 : |t| < 1 / 2 := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  have ht3 : 0 < 1 - t := by linarith [(abs_lt.mp ht2).2]
  beta_reduce
  rw [mem_ball_zero_iff, min_eq_left hb.le]
  constructor
  · intro h
    have h' : ‖y‖ ^ 2 < 1 := by nlinarith [norm_nonneg y]
    have : 1 - t < √(1 - ‖z'‖ ^ 2) := (Real.lt_sqrt ht3.le).2 (by nlinarith)
    linarith
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    have h3 : 1 - t < √(1 - ‖z'‖ ^ 2) := by linarith
    have h4 := (Real.lt_sqrt ht3.le).1 h3
    nlinarith [norm_nonneg y]

/-- Step 5. For bounded `W ⊆ ℝ^d`, `nW ∩ ℤ^d` is finite. -/
theorem discretizeFinite : DiscretizeFiniteStmt := by
  intro d W hW n
  obtain ⟨R, hR⟩ := (hW.smul₀ (n : ℝ)).exists_norm_le
  refine (Set.finite_Icc (fun _ : Fin d => -⌈R⌉) (fun _ => ⌈R⌉)).subset ?_
  intro x hx
  have hx' : ‖toE x‖ ≤ R := hR _ hx
  have hi : ∀ i, |(x i : ℝ)| ≤ R := fun i => by
    have := PiLp.norm_apply_le (toE x) i
    simpa using this.trans hx'
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.mp (hi i)).1
    have h2 : (-(⌈R⌉ : ℤ) : ℝ) ≤ x i := by
      linarith [Int.le_ceil R]
    exact_mod_cast h2
  · have := (abs_le.mp (hi i)).2
    have h2 : (x i : ℝ) ≤ (⌈R⌉ : ℤ) := by linarith [Int.le_ceil R]
    exact_mod_cast h2

end RandomSandpile

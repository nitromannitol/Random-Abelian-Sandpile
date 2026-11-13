import RandomSandpile.Proofs.Sec7.MainTheoremEnv

/-!
# Theorem 1.1, step: `EnvWeakStarStmt`

Almost surely the rescaled restricted environment `x ↦ η([nx]) 𝟙_{W_n}([nx])` converges weakly-*
in `L^∞(ℝ^d)` to `E η(0) 𝟙_W` (`envWeakStar`).

* Fix `η` with `|η| ≤ K` whose dyadic cube averages converge (`cubeErgodic`). Then
  `∫ η([nx]) 𝟙_{D_{j,k}}(x) dx → m |D_{j,k}|` for every dyadic cell (`tendsto_integral_env_dyadicCell`),
  hence `∫ η([nx]) G(x) dx → m ∫ G` for dyadic step functions `G = F([2^j ·])`
  (`tendsto_env_dyadicStep`).
* Continuous compactly supported `g` are `L¹` limits of the step functions `g(2^{-j} [2^j ·])`
  (`exists_dyadicStep_approx`, dominated convergence), and these are dense in `L¹`
  (`Integrable.exists_hasCompactSupport_integral_sub_le`); since `|η| ≤ K` the convergence passes to
  `L¹` limits (`tendsto_env_of_approx`), so `∫ η([nx]) g(x) dx → m ∫ g` for every integrable `g`
  (`tendsto_env_integrable`).
* The cut-off `𝟙_{W_n}([nx]) = 𝟙_W(n⁻¹ [nx])` converges to `𝟙_W(x)` off `∂W`, which is null for a
  Lipschitz domain (`volume_frontier_of_isLipschitzDomain`); dominated convergence handles the error
  (`weakStarTendsto_env_of_cube`).
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-! ### `n⁻¹ [n x] → x` -/

/-- `|[x] - x| ≤ d + 1` for the coordinatewise floor. The squared bound is copied from
`norm_toE_latticeRound_sub_sq_le` (RandomSandpile/Proofs/Sec7/PegdenSmartRegularityTranslates.lean). -/
theorem norm_toE_latticeRound_sub_le (x : Rd d) : ‖toE (latticeRound x) - x‖ ≤ d + 1 := by
  have hsq : ‖toE (latticeRound x) - x‖ ^ 2 ≤ d := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(toE (latticeRound x) - x) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp only [toE, latticeRound, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
          have h1 := Int.floor_le (x i)
          have h2 := Int.lt_floor_add_one (x i)
          nlinarith
      _ = d := by simp
  nlinarith [norm_nonneg (toE (latticeRound x) - x), sq_nonneg (‖toE (latticeRound x) - x‖ - 1)]

theorem norm_inv_smul_latticeRound_sub_le {n : ℕ} (hn : n ≠ 0) (x : Rd d) :
    ‖(n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x)) - x‖ ≤ (d + 1) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e : (n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x)) - x =
      (n : ℝ)⁻¹ • (toE (latticeRound ((n : ℝ) • x)) - (n : ℝ) • x) := by
    rw [smul_sub, inv_smul_smul₀ hn'.ne']
  rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn', div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_toE_latticeRound_sub_le _) (inv_nonneg.2 hn'.le)

theorem tendsto_inv_smul_latticeRound (x : Rd d) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun n : ℕ => ((d : ℝ) + 1) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact norm_inv_smul_latticeRound_sub_le hn x

/-! ### Passing to `L¹` limits -/

/-- Since `|η| ≤ K`, the convergence `∫ η([nx]) g(x) dx → m ∫ g` passes to `L¹` limits. -/
theorem tendsto_env_of_approx {η : Site d → ℤ} {K m : ℝ} (hK : ∀ y, |(η y : ℝ)| ≤ K)
    {g : Rd d → ℝ} (hg : Integrable g volume)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ h : Rd d → ℝ, Integrable h volume ∧ ∫ x, |g x - h x| ≤ ε ∧
      Tendsto (fun n : ℕ => ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * h x) atTop
        (𝓝 (m * ∫ x, h x))) :
    Tendsto (fun n : ℕ => ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * g x) atTop
      (𝓝 (m * ∫ x, g x)) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (2 * (K + |m| + 1)) with hδ
  have hpos : 0 < 2 * (K + |m| + 1) := by positivity
  have hδ0 : 0 < δ := div_pos hε hpos
  have hδε : δ * (2 * (K + |m| + 1)) = ε := by rw [hδ]; field_simp
  obtain ⟨h, hh, hgh, hlim⟩ := happrox δ hδ0
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hmeas : Measurable fun x : Rd d => (η (latticeRound ((n : ℝ) • x)) : ℝ) :=
    measurable_latticeRound_comp n fun y => (η y : ℝ)
  have hi1 : Integrable (fun x => (η (latticeRound ((n : ℝ) • x)) : ℝ) * (g x - h x)) volume :=
    integrable_mul_of_abs_le hmeas (fun x => hK _) (hg.sub hh)
  have hi2 : Integrable (fun x => (η (latticeRound ((n : ℝ) • x)) : ℝ) * h x) volume :=
    integrable_mul_of_abs_le hmeas (fun x => hK _) hh
  have e1 : |∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * (g x - h x)| ≤ K * ∫ x, |g x - h x| :=
    abs_integral_mul_le_of_abs_le hmeas (fun x => hK _) (hg.sub hh)
  have e2 : (∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * g x) =
      (∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * (g x - h x)) +
        ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * h x := by
    rw [← integral_add hi1 hi2]
    congr 1; funext x; ring
  have e3 : |(∫ x, g x) - ∫ x, h x| ≤ ∫ x, |g x - h x| := by
    rw [← integral_sub hg hh]; exact abs_integral_le_integral_abs
  have hNn := hN n hn
  rw [Real.dist_eq] at hNn ⊢
  rw [e2]
  have hKd : K * ∫ x, |g x - h x| ≤ K * δ := mul_le_mul_of_nonneg_left hgh hK0
  have hmd : |m| * |(∫ x, g x) - ∫ x, h x| ≤ |m| * δ :=
    mul_le_mul_of_nonneg_left (e3.trans hgh) (abs_nonneg m)
  set A := ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * (g x - h x)
  set B := ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * h x
  set G := ∫ x, g x
  set H := ∫ x, h x
  have key : |A + B - m * G| ≤ |A| + |B - m * H| + |m| * |G - H| := by
    have : A + B - m * G = A + (B - m * H) + -(m * (G - H)) := by ring
    rw [this]
    refine (abs_add_three _ _ _).trans (le_of_eq ?_)
    rw [abs_neg, abs_mul]
  have hm0 := abs_nonneg m
  nlinarith

/-! ### Dyadic step functions -/

/-- `∫ η([nx]) G(x) dx → m ∫ G` for a dyadic step function `G(x) = F([2^j x])`, `F` finitely
supported. -/
theorem tendsto_env_dyadicStep {η : Site d → ℤ} {K m : ℝ} (hK : ∀ y, |(η y : ℝ)| ≤ K)
    (hcube : ∀ (j : ℕ) (k : Site d), Tendsto (fun N : ℕ =>
      (∑ y ∈ dyadicCube j k N, ((η y : ℝ) - m)) / (N : ℝ) ^ d) atTop (𝓝 0))
    (j : ℕ) (F : Site d → ℝ) (S : Finset (Site d)) (hS : ∀ y, y ∉ S → F y = 0) :
    Tendsto (fun n : ℕ => ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) *
      F (latticeRound (((2 ^ j : ℕ) : ℝ) • x))) atTop
      (𝓝 (m * ∫ x, F (latticeRound (((2 ^ j : ℕ) : ℝ) • x)))) := by
  have hrep : ∀ x : Rd d, F (latticeRound (((2 ^ j : ℕ) : ℝ) • x)) =
      ∑ k ∈ S, F k * (dyadicCell j k).indicator (fun _ => (1 : ℝ)) x :=
    latticeRound_finsum_eq (2 ^ j) F S hS
  have hDi : ∀ k : Site d, Integrable ((dyadicCell j k).indicator fun _ => (1 : ℝ)) volume := fun k =>
    integrable_indicator_one (measurableSet_dyadicCell j k) (volume_dyadicCell_lt_top j k)
  have hmeas : ∀ n : ℕ, Measurable fun x : Rd d => (η (latticeRound ((n : ℝ) • x)) : ℝ) :=
    fun n => measurable_latticeRound_comp n fun y => (η y : ℝ)
  have hcell : ∀ n : ℕ, ∑ k ∈ S, F k * ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) *
      (dyadicCell j k).indicator (fun _ => (1 : ℝ)) x =
      ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * F (latticeRound (((2 ^ j : ℕ) : ℝ) • x)) := by
    intro n
    have e : (fun x => (η (latticeRound ((n : ℝ) • x)) : ℝ) *
        F (latticeRound (((2 ^ j : ℕ) : ℝ) • x))) = fun x => ∑ k ∈ S, F k *
          ((η (latticeRound ((n : ℝ) • x)) : ℝ) * (dyadicCell j k).indicator (fun _ => (1 : ℝ)) x) := by
      funext x
      rw [hrep x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, integral_finsetSum _ fun k _ =>
      (integrable_mul_of_abs_le (hmeas n) (fun x => hK _) (hDi k)).const_mul (F k)]
    exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
  have hG : ∫ x, F (latticeRound (((2 ^ j : ℕ) : ℝ) • x)) =
      ∑ k ∈ S, F k * volume.real (dyadicCell j k) := by
    rw [show (fun x => F (latticeRound (((2 ^ j : ℕ) : ℝ) • x))) = fun x =>
      ∑ k ∈ S, F k * (dyadicCell j k).indicator (fun _ => (1 : ℝ)) x from funext hrep,
      integral_finsetSum _ fun k _ => (hDi k).const_mul (F k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    exact integral_indicator_one (measurableSet_dyadicCell j k)
  refine Tendsto.congr hcell ?_
  rw [hG, Finset.mul_sum]
  refine tendsto_finsetSum _ fun k _ => ?_
  rw [show m * (F k * volume.real (dyadicCell j k)) = F k * (m * volume.real (dyadicCell j k)) by
    ring]
  exact (tendsto_integral_env_dyadicCell hK hcube j k).const_mul (F k)

/-- A continuous compactly supported `g` is an `L¹` limit of the dyadic step functions
`g(2^{-j} [2^j ·])`. -/
theorem exists_dyadicStep_approx {g : Rd d → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (j : ℕ) (S : Finset (Site d)), (∀ k, k ∉ S → g (((2 ^ j : ℕ) : ℝ)⁻¹ • toE k) = 0) ∧
      ∫ x, |g x - g (((2 ^ j : ℕ) : ℝ)⁻¹ • toE (latticeRound (((2 ^ j : ℕ) : ℝ) • x)))| ≤ ε := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Rd d)).1 hgs.isCompact.isBounded
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  have hzero : ∀ y : Rd d, R < ‖y‖ → g y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
  set p : ℕ → Rd d → Rd d := fun j x =>
    ((2 ^ j : ℕ) : ℝ)⁻¹ • toE (latticeRound (((2 ^ j : ℕ) : ℝ) • x)) with hp
  have hpx : ∀ j x, ‖p j x - x‖ ≤ d + 1 := fun j x => by
    refine (norm_inv_smul_latticeRound_sub_le (pow_ne_zero _ two_ne_zero) x).trans ?_
    have h1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    exact div_le_self (by positivity) h1
  set B : Set (Rd d) := Metric.closedBall 0 (R + d + 1) with hB
  have hBi : Integrable (B.indicator fun _ => (2 * C)) volume :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (measure_closedBall_lt_top (x := (0 : Rd d))).ne)
  have hlim : Tendsto (fun j : ℕ => ∫ x, |g x - g (p j x)|) atTop (𝓝 (∫ _x : Rd d, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => B.indicator (fun _ => 2 * C) x)
      (fun j => ?_) hBi (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · exact (hgc.measurable.sub (measurable_latticeRound_comp (2 ^ j)
        fun y => g (((2 ^ j : ℕ) : ℝ)⁻¹ • toE y))).abs.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_abs]
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx]
        have h1 := hC x
        have h2 := hC (p j x)
        rw [Real.norm_eq_abs] at h1 h2
        exact (abs_sub _ _).trans (by linarith)
      · rw [Set.indicator_of_notMem hx]
        rw [hB, Metric.mem_closedBall, dist_zero_right, not_le] at hx
        have h1 : g x = 0 := hzero x (by linarith)
        have h2 : g (p j x) = 0 := by
          refine hzero _ ?_
          have := norm_sub_norm_le x (p j x)
          rw [norm_sub_rev] at this
          linarith [hpx j x]
        rw [h1, h2, sub_zero, abs_zero]
    · have hpj : Tendsto (fun j => p j x) atTop (𝓝 x) :=
        (tendsto_inv_smul_latticeRound x).comp
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
      have := ((hgc.tendsto x).comp hpj).const_sub (g x)
      rw [sub_self] at this
      have h' := this.abs
      rw [abs_zero] at h'
      exact h'
  rw [integral_zero] at hlim
  obtain ⟨j, hj⟩ := (hlim.eventually (Iic_mem_nhds hε)).exists
  have hfin := finite_norm_toE_le (d := d) (((2 ^ j : ℕ) : ℝ) * R)
  refine ⟨j, hfin.toFinset, fun k hk => hzero _ ?_, hj⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hk
  have h2 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h2, inv_mul_eq_div, lt_div_iff₀ h2]
  linarith

/-- `∫ η([nx]) g(x) dx → m ∫ g` for every integrable `g`. -/
theorem tendsto_env_integrable {η : Site d → ℤ} {K m : ℝ} (hK : ∀ y, |(η y : ℝ)| ≤ K)
    (hcube : ∀ (j : ℕ) (k : Site d), Tendsto (fun N : ℕ =>
      (∑ y ∈ dyadicCube j k N, ((η y : ℝ) - m)) / (N : ℝ) ^ d) atTop (𝓝 0))
    {g : Rd d → ℝ} (hg : Integrable g volume) :
    Tendsto (fun n : ℕ => ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * g x) atTop
      (𝓝 (m * ∫ x, g x)) := by
  refine tendsto_env_of_approx hK hg fun ε hε => ?_
  obtain ⟨g', hg's, hgg', hg'c, hg'i⟩ := hg.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  obtain ⟨j, S, hS, hj⟩ := exists_dyadicStep_approx hg'c hg's (half_pos hε)
  have hGi := integrable_latticeRound_finsum (pow_ne_zero j two_ne_zero)
    (fun k => g' (((2 ^ j : ℕ) : ℝ)⁻¹ • toE k)) S hS
  refine ⟨fun x => g' (((2 ^ j : ℕ) : ℝ)⁻¹ • toE (latticeRound (((2 ^ j : ℕ) : ℝ) • x))), hGi,
    ?_, tendsto_env_dyadicStep hK hcube j (fun k => g' (((2 ^ j : ℕ) : ℝ)⁻¹ • toE k)) S hS⟩
  have hgg'' : ∫ x, |g x - g' x| ≤ ε / 2 := by simpa only [Real.norm_eq_abs] using hgg'
  calc ∫ x, |g x - g' (((2 ^ j : ℕ) : ℝ)⁻¹ • toE (latticeRound (((2 ^ j : ℕ) : ℝ) • x)))|
      ≤ ∫ x, (|g x - g' x| +
          |g' x - g' (((2 ^ j : ℕ) : ℝ)⁻¹ • toE (latticeRound (((2 ^ j : ℕ) : ℝ) • x)))|) :=
        integral_mono (hg.sub hGi).abs ((hg.sub hg'i).abs.add (hg'i.sub hGi).abs)
          fun x => abs_sub_le _ _ _
    _ = (∫ x, |g x - g' x|) + ∫ x,
          |g' x - g' (((2 ^ j : ℕ) : ℝ)⁻¹ • toE (latticeRound (((2 ^ j : ℕ) : ℝ) • x)))| :=
        integral_add (hg.sub hg'i).abs (hg'i.sub hGi).abs
    _ ≤ ε / 2 + ε / 2 := add_le_add hgg'' hj
    _ = ε := by ring

/-! ### The cut-off by `W_n` -/

theorem rescaleSandpile_indicator_eq {η : Site d → ℤ} (W : Set (Rd d)) {n : ℕ} (hn : n ≠ 0)
    (x : Rd d) :
    rescaleSandpile ((discretize W n).indicator η) n x =
      (η (latticeRound ((n : ℝ) • x)) : ℝ) *
        W.indicator (fun _ => (1 : ℝ)) ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [rescaleSandpile]
  by_cases h : (n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x)) ∈ W
  · have h' : latticeRound ((n : ℝ) • x) ∈ discretize W n :=
      (Set.mem_smul_set_iff_inv_smul_mem₀ hn' _ _).2 h
    rw [Set.indicator_of_mem h', Set.indicator_of_mem h, mul_one]
  · have h' : latticeRound ((n : ℝ) • x) ∉ discretize W n := fun h' =>
      h ((Set.mem_smul_set_iff_inv_smul_mem₀ hn' _ _).1 h')
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h, mul_zero, Int.cast_zero]

theorem abs_indicator_one_sub_le (W : Set (Rd d)) (p x : Rd d) :
    |W.indicator (fun _ => (1 : ℝ)) p - W.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
  by_cases hp : p ∈ W <;> by_cases hx : x ∈ W <;> simp [hp, hx]

theorem abs_indicator_one_le (W : Set (Rd d)) (p : Rd d) :
    |W.indicator (fun _ => (1 : ℝ)) p| ≤ 1 := by
  by_cases hp : p ∈ W <;> simp [hp]

/-- Off `∂W`, `𝟙_W(n⁻¹ [nx]) → 𝟙_W(x)`. -/
theorem tendsto_indicator_inv_smul_latticeRound {W : Set (Rd d)} {x : Rd d}
    (hx : x ∉ frontier W) :
    Tendsto (fun n : ℕ => W.indicator (fun _ => (1 : ℝ))
      ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x)))) atTop
      (𝓝 (W.indicator (fun _ => (1 : ℝ)) x)) := by
  have hp := tendsto_inv_smul_latticeRound x
  rw [frontier, Set.mem_sdiff, not_and_or, not_not] at hx
  rcases hx with hx | hx
  · have hev : ∀ᶠ n : ℕ in atTop,
        (n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x)) ∈ (closure W)ᶜ :=
      hp (isClosed_closure.isOpen_compl.mem_nhds hx)
    have hxW : x ∉ W := fun h => hx (subset_closure h)
    rw [Set.indicator_of_notMem hxW]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    rw [Set.indicator_of_notMem fun h => hn (subset_closure h)]
  · have hev : ∀ᶠ n : ℕ in atTop,
        (n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x)) ∈ interior W :=
      hp (isOpen_interior.mem_nhds hx)
    rw [Set.indicator_of_mem (interior_subset hx)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    rw [Set.indicator_of_mem (interior_subset hn)]

/-- The deterministic core of step: for `|η| ≤ K` with convergent dyadic cube averages, and a
measurable `W` with null boundary, `η([nx]) 𝟙_{W_n}([nx]) → m 𝟙_W` weakly-*. -/
theorem weakStarTendsto_env_of_cube {η : Site d → ℤ} {K m : ℝ} (hK : ∀ y, |(η y : ℝ)| ≤ K)
    (hcube : ∀ (j : ℕ) (k : Site d), Tendsto (fun N : ℕ =>
      (∑ y ∈ dyadicCube j k N, ((η y : ℝ) - m)) / (N : ℝ) ^ d) atTop (𝓝 0))
    {W : Set (Rd d)} (hWm : MeasurableSet W) (hW : volume (frontier W) = 0) :
    WeakStarTendsto (fun n : ℕ => rescaleSandpile ((discretize W n).indicator η) n)
      (W.indicator fun _ => m) := by
  intro g hg
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hmeas : ∀ n : ℕ, Measurable fun x : Rd d => (η (latticeRound ((n : ℝ) • x)) : ℝ) :=
    fun n => measurable_latticeRound_comp n fun y => (η y : ℝ)
  have hιm : ∀ n : ℕ, Measurable fun x : Rd d => W.indicator (fun _ => (1 : ℝ))
      ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) :=
    fun n => measurable_latticeRound_comp n fun y =>
      W.indicator (fun _ => (1 : ℝ)) ((n : ℝ)⁻¹ • toE y)
  have hWi : Measurable (W.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hWm
  have hgW : Integrable (W.indicator g) volume := hg.indicator hWm
  have h1 := tendsto_env_integrable hK hcube hgW
  have hval : ∫ x, W.indicator (fun _ => m) x * g x = m * ∫ x, W.indicator g x := by
    rw [← integral_const_mul]
    congr 1; funext x
    by_cases hx : x ∈ W <;> simp [hx]
  -- the error of the cut-off, by dominated convergence
  have h2 : Tendsto (fun n : ℕ => ∫ x, |W.indicator (fun _ => (1 : ℝ))
      ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) - W.indicator (fun _ => (1 : ℝ)) x| *
        |g x|) atTop (𝓝 0) := by
    have hlim := tendsto_integral_of_dominated_convergence (μ := volume) (fun x => |g x|)
      (F := fun (n : ℕ) x => |W.indicator (fun _ => (1 : ℝ))
        ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) - W.indicator (fun _ => (1 : ℝ)) x| *
          |g x|) (f := fun _ => (0 : ℝ))
      (fun n => (((hιm n).sub hWi).abs.aestronglyMeasurable).mul hg.abs.aestronglyMeasurable)
      hg.abs
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_indicator_one_sub_le W _ x))
      (by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hW] with x hx
        have := (((tendsto_indicator_inv_smul_latticeRound hx).sub_const
          (W.indicator (fun _ => (1 : ℝ)) x)).abs).mul_const |g x|
        simpa using this)
    simpa using hlim
  have h3 : Tendsto (fun n : ℕ => (∫ x, rescaleSandpile ((discretize W n).indicator η) n x * g x) -
      ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * W.indicator g x) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using h2.const_mul K)
    filter_upwards [eventually_ne_atTop 0] with n hn
    have e : (fun x => rescaleSandpile ((discretize W n).indicator η) n x * g x) =
        fun x => (η (latticeRound ((n : ℝ) • x)) : ℝ) * (W.indicator (fun _ => (1 : ℝ))
          ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) * g x) := by
      funext x; rw [rescaleSandpile_indicator_eq W hn x]; ring
    have hi1 : Integrable (fun x => W.indicator (fun _ => (1 : ℝ))
        ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) * g x) volume :=
      integrable_mul_of_abs_le (hιm n) (fun x => abs_indicator_one_le W _) hg
    have hi2 : Integrable (fun x => (W.indicator (fun _ => (1 : ℝ))
        ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) - W.indicator (fun _ => (1 : ℝ)) x) *
          g x) volume :=
      integrable_mul_of_abs_le ((hιm n).sub hWi) (fun x => abs_indicator_one_sub_le W _ x) hg
    rw [e, Real.norm_eq_abs, ← integral_sub (integrable_mul_of_abs_le (hmeas n) (fun x => hK _) hi1)
      (integrable_mul_of_abs_le (hmeas n) (fun x => hK _) hgW)]
    have e2 : (fun x => (η (latticeRound ((n : ℝ) • x)) : ℝ) * (W.indicator (fun _ => (1 : ℝ))
          ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) * g x) -
          (η (latticeRound ((n : ℝ) • x)) : ℝ) * W.indicator g x) =
        fun x => (η (latticeRound ((n : ℝ) • x)) : ℝ) * ((W.indicator (fun _ => (1 : ℝ))
          ((n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x))) - W.indicator (fun _ => (1 : ℝ)) x) *
            g x) := by
      funext x
      by_cases hx : x ∈ W
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
    rw [e2]
    refine (abs_integral_mul_le_of_abs_le (hmeas n) (fun x => hK _) hi2).trans (le_of_eq ?_)
    congr 1; congr 1; funext x; rw [abs_mul]
  rw [hval]
  have h4 := h3.add h1
  rw [zero_add] at h4
  exact h4.congr fun n => sub_add_cancel _ _

/-- **Step** (`EnvWeakStarStmt`): almost surely `η([nx]) 𝟙_{W_n}([nx]) → E η(0) 𝟙_W` weakly-*
in `L^∞(ℝ^d)`, from the dyadic cube ergodic theorem `cubeErgodic` and `|∂W| = 0`. -/
theorem envWeakStar : EnvWeakStarStmt := by
  intro d hd E W hW
  have hb : ∀ᵐ η ∂E.P, ∀ y : Site d, E.ηmin ≤ η y ∧ η y ≤ E.ηmax := ae_all_iff.2 E.bounded
  filter_upwards [hb, cubeErgodic d hd E] with η hη hc
  refine weakStarTendsto_env_of_cube (K := max |(E.ηmin : ℝ)| |(E.ηmax : ℝ)|) (fun y => ?_) hc
    hW.2.1.measurableSet (volume_frontier_of_isLipschitzDomain hW)
  have h1 : (E.ηmin : ℝ) ≤ η y := by exact_mod_cast (hη y).1
  have h2 : (η y : ℝ) ≤ E.ηmax := by exact_mod_cast (hη y).2
  have h3 := neg_abs_le (E.ηmin : ℝ)
  have h4 := le_abs_self (E.ηmax : ℝ)
  have h5 := le_max_left |(E.ηmin : ℝ)| |(E.ηmax : ℝ)|
  have h6 := le_max_right |(E.ηmin : ℝ)| |(E.ηmax : ℝ)|
  rw [abs_le]
  constructor <;> linarith

end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceFstarPeano
import RandomSandpile.Proofs.Sec9.SingleSourceFstarDilation
import RandomSandpile.Proofs.Sec7.LimitTraceInterior
import RandomSandpile.Proofs.Sec7.SplitTouchingJensen
import RandomSandpile.Proofs.Sec5.SubadditiveErgodicFinal
import RandomSandpile.Proofs.Sec9.OpenBoundaryComparison

/-!
# Theorem 9.2, `F*`-variant: the subsolution step and the theorem

 §4.4 and §7.

* `neg_le_lap_ssOdometer`: the final configuration of the single-source pile is `≥ min(σ, 0)`
  (leastness: otherwise `v_n - 1_x` is a smaller stabilizing toppling), so
  `|Δ_{ℤ^d} v_n| ≤ 2d + |η_min|` off the origin (`abs_lap_ssOdometer_le`).
* `viscFromAboveGE_of_lap_ge_on`, `viscFromBelowLE_of_lap_le_on`: the consistency of the discrete
  Laplacian (`Proofs/Sec7/FreeOdometerLimitRegular.lean`), localized to an open set with the local
  ABP principle `SingleSourceMin.principle_generic_on`: the limits satisfy `|Δu| ≤ K` off the
  origin in the viscosity sense (Crandall-Ishii-Lions), `K = 2d + |η_min|`.
* `ssLimitSubStar : SSLimitSubStarStmt` (step): if `φ` touches a limit `u` from above at
  `x ∈ {u > 0} ∖ {0}` with `F*(D²φ(x)) > 0`, the quadratic `ψ` of `D²φ(x) + 4εI` touches `u`
  strictly from above; Pegden-Smart's Proposition 2.5 (`PegdenSmartTouchingStmt`, with
  its two-sided bounded Laplacian hypotheses) gives a Peano point `a` of `u` with
  `D²u(a) ≤ D²φ(x) + 4εI`, and `F*(D²u(a)) ≥ F*(D²φ(x)) - 4dε > 0` contradicts `ssPeanoStar`.
* `singleSourceTheoremFstar : SingleSourceTheoremStarStmt` (Theorem 9.2 with `F*`) from compactness
  `SSCompactnessStmt` (step), outer bound `SSOuterBoundStmt`, and the admitted inputs
  `PegdenSmartTouchingStmt` and `AlexandrovStmt`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric
open scoped ENNReal Matrix

namespace RandomSandpile

namespace SingleSourceFstar

variable {d : ℕ}

/-! ### The lattice Laplacian of the single-source odometer -/

/-- **The final configuration is `≥ min(σ, 0)`**: where `v_n ≥ 1` the site toppled and keeps at
least `0` chips (else `v_n - 1_x` is a smaller stabilizing toppling), where `v_n = 0` it only
received chips. -/
theorem neg_le_lap_ssOdometer {η : Site d → ℤ} {n : ℕ}
    (hne : (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty) (x : Site d) :
    min (η x + (n : ℤ) * dirac 0 x) 0 ≤
      η x + (n : ℤ) * dirac 0 x + lap (singleSourceOdometer η n) x := by
  classical
  have hVs := (isLeast_singleSourceOdometer hne).1
  simp only [mem_stabilizing_univ] at hVs
  by_cases hV0 : singleSourceOdometer η n x = 0
  · have h : 0 ≤ lap (singleSourceOdometer η n) x := by
      simp only [lap, nbrSumZ, hV0]
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
        add_nonneg (singleSourceOdometer_nonneg η n (x + unit i))
          (singleSourceOdometer_nonneg η n (x - unit i))
      linarith
    have := min_le_left (η x + (n : ℤ) * dirac 0 x) 0
    linarith
  · by_contra hlt
    have hlt' := not_le.1 hlt
    have hmin := min_le_right (η x + (n : ℤ) * dirac 0 x) 0
    have hV1 : 1 ≤ singleSourceOdometer η n x := by
      have := singleSourceOdometer_nonneg η n x
      omega
    have hne_add : ∀ i, x + unit i ≠ x := fun i h => by
      have := congrFun h i
      simp [unit] at this
    have hne_sub : ∀ i, x - unit i ≠ x := fun i h => by
      have := congrFun h i
      simp [unit] at this
    set V' : Site d → ℤ := fun y => singleSourceOdometer η n y - if y = x then 1 else 0 with hV'
    have hV'x : V' x = singleSourceOdometer η n x - 1 := by simp [hV']
    have hV'a : ∀ i, V' (x + unit i) = singleSourceOdometer η n (x + unit i) := fun i => by
      simp [hV', hne_add i]
    have hV's : ∀ i, V' (x - unit i) = singleSourceOdometer η n (x - unit i) := fun i => by
      simp [hV', hne_sub i]
    have hV'le : ∀ y, V' y ≤ singleSourceOdometer η n y := fun y => by
      simp only [hV']
      split_ifs <;> omega
    have hlapx : lap V' x = lap (singleSourceOdometer η n) x + 2 * d := by
      simp only [lap, nbrSumZ, hV'x, hV'a, hV's]
      ring
    have hV'stab : V' ∈ stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ := by
      simp only [mem_stabilizing_univ]
      refine ⟨fun y => ?_, fun y => ?_⟩
      · simp only [hV']
        split_ifs with hy
        · subst hy; omega
        · have := hVs.1 y; omega
      · by_cases hy : y = x
        · subst hy
          rw [hlapx]
          omega
        · have hVy : V' y = singleSourceOdometer η n y := by simp [hV', hy]
          have hl := lap_le_lap_of_nbr' hVy fun i => ⟨hV'le _, hV'le _⟩
          have := hVs.2 y
          linarith
    have hle : singleSourceOdometer η n x ≤ V' x := singleSourceOdometer_le hV'stab x
    rw [hV'x] at hle
    omega

/-- `|Δ_{ℤ^d} v_n| ≤ 2d + |η_min|` off the origin. -/
theorem abs_lap_ssOdometer_le (hd : 1 ≤ d) {η : Site d → ℤ} {ηmin : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2) {n : ℕ}
    (hne : (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty)
    {z : Site d} (hz : z ≠ 0) :
    -(2 * (d : ℝ) + |(ηmin : ℝ)|) ≤ (lap (singleSourceOdometer η n) z : ℝ) ∧
      (lap (singleSourceOdometer η n) z : ℝ) ≤ 2 * (d : ℝ) + |(ηmin : ℝ)| := by
  have hδ : dirac (0 : Site d) z = 0 := by simp [dirac, hz]
  have hVs := (isLeast_singleSourceOdometer hne).1
  simp only [mem_stabilizing_univ] at hVs
  have h1 := neg_le_lap_ssOdometer hne z
  have h2 := hVs.2 z
  rw [hδ, mul_zero, add_zero] at h1 h2
  have h3 := min_le_right (η z) 0
  have hlo : -(2 * (d : ℤ) - 2) ≤ lap (singleSourceOdometer η n) z := by
    rcases le_total (η z) 0 with h | h
    · rw [min_eq_left h] at h1; omega
    · rw [min_eq_right h] at h1; have := (hη z).2; omega
  have hup : lap (singleSourceOdometer η n) z ≤ 2 * (d : ℤ) - 1 - ηmin := by
    have := (hη z).1; omega
  have hlo' : -(2 * (d : ℝ) - 2) ≤ (lap (singleSourceOdometer η n) z : ℝ) := by exact_mod_cast hlo
  have hup' : (lap (singleSourceOdometer η n) z : ℝ) ≤ 2 * (d : ℝ) - 1 - (ηmin : ℝ) := by
    exact_mod_cast hup
  have ha := neg_abs_le (ηmin : ℝ)
  have hb := abs_nonneg (ηmin : ℝ)
  constructor <;> linarith

/-! ### Viscosity Laplacian bounds of the limits, localized -/

/-- Localized from `Proofs/Sec7/FreeOdometerLimitRegular.lean`
(`FreeLimitRegular.viscFromAboveGE_of_lap_ge`): uniform convergence and the lattice bound are needed
only on closed balls in the open set `U`. -/
theorem viscFromAboveGE_of_lap_ge_on (hd : 1 ≤ d) {nk : ℕ → ℕ} (hnk : Tendsto nk atTop atTop)
    {vk : ℕ → Site d → ℤ} {v : Rd d → ℝ} {U : Set (Rd d)} (hU : IsOpen U) (hv : ContinuousOn v U)
    (hconv : ∀ (a : Rd d) (r : ℝ), closedBall a r ⊆ U →
      TendstoUniformlyOn (fun k => rescaleOdo (vk k) (nk k)) v atTop (closedBall a r))
    {K : ℝ} (hK : ∀ k z, (nk k : ℝ)⁻¹ • toE z ∈ U → -K ≤ (lap (vk k) z : ℝ)) :
    ViscFromAboveGE (fun X => X.trace + K) U v := by
  intro x hx φ hφ hmax
  simp only
  by_contra hneg
  have hneg' := not_le.1 hneg
  set H := hessian φ x with hHdef
  have hH : H.IsSymm := hessian_isSymm_of_contDiffAt hφ
  set δ : ℝ := -(H.trace + K) with hδ
  have hδ0 : 0 < δ := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set κ : ℝ := δ / (8 * d) with hκ
  have hκ0 : 0 < κ := by positivity
  set l : ℝ := δ / 2 with hl
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ hκ0
  obtain ⟨ρ₂, hρ₂, hm⟩ := Metric.eventually_nhds_iff.1 hmax
  obtain ⟨ρ₃, hρ₃, hball⟩ := Metric.isOpen_iff.1 hU x hx
  set r : ℝ := min (min ρ₁ ρ₂) ρ₃ / 4 with hr
  have hr0 : 0 < r := by positivity
  have hm1 : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₃ := min_le_right _ _
  have hcl : closedBall x (2 * r) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  set p : Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x) with hp
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (1 : ℝ) *
      ((vk k z : ℝ) - (nk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - x) + qM H (X - x) + ql l (X - x))
          ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball x r) (nk k))) ≤ 0 ∧
      (0 : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards [hnk.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : nk k ≠ 0 := by omega
    refine ⟨?_, ENNReal.zero_ne_top⟩
    rw [FreeLimitRegular.supGradSet_eq_empty fun z hz => ?_]
    · simp
    · rw [FreeLimitRegular.lapR_rescaled hd 1 (vk k) hH p x l hn0 z]
      have hzU : (nk k : ℝ)⁻¹ • toE z ∈ U := by
        have h := (OpenMaxPrinciple.mem_discretize_iff' hn0).1 hz
        exact hcl (ball_subset_closedBall (ball_subset_ball (by linarith) h))
      linarith [hK k z hzU]
  have hV : Tendsto (fun k => ((0 : ℝ≥0∞)).toReal / (nk k : ℝ) ^ d) atTop (𝓝 0) := by simp
  obtain ⟨y, hy, h⟩ := SingleSourceMin.principle_generic_on hd (σ := 1) (V := fun _ => 0)
    (OpenMaxPrinciple.continuous_quadratic p x H l) hr0 (by linarith : r < 2 * r)
    (hv.mono hcl) hnk (hconv x (2 * r) hcl) hvol hV (mem_ball_self hr0)
  rw [mem_sphere, dist_eq_norm] at hy
  have hy1 : ‖y - x‖ < ρ₁ := by rw [hy]; linarith
  have hy2 : dist y x < ρ₂ := by rw [dist_eq_norm, hy]; linarith
  have hTy := abs_le.1 (hT y hy1)
  have hmy : v y - φ y ≤ v x - φ x := hm hy2
  simp only [one_mul, sub_self, inner_zero_right, qM_zero_right, ql_zero_right, add_zero,
    sub_zero] at h
  have hql : ql l (y - x) = l * r ^ 2 / (2 * d) := by rw [ql, hy]
  have hfd : inner ℝ p (y - x) = fderiv ℝ φ x (y - x) := by
    rw [hp, InnerProductSpace.toDual_symm_apply]
  rw [hy] at hTy
  have hkey : l * r ^ 2 / (2 * d) = 2 * (κ * r ^ 2) := by
    rw [hl, hκ]; field_simp; ring
  have hr2 : 0 < κ * r ^ 2 := by positivity
  rw [hql, hfd] at h
  linarith [hTy.2]

/-- Localized from `Proofs/Sec7/FreeOdometerLimitRegular.lean`
(`FreeLimitRegular.viscFromBelowLE_of_lap_le`). -/
theorem viscFromBelowLE_of_lap_le_on (hd : 1 ≤ d) {nk : ℕ → ℕ} (hnk : Tendsto nk atTop atTop)
    {vk : ℕ → Site d → ℤ} {v : Rd d → ℝ} {U : Set (Rd d)} (hU : IsOpen U) (hv : ContinuousOn v U)
    (hconv : ∀ (a : Rd d) (r : ℝ), closedBall a r ⊆ U →
      TendstoUniformlyOn (fun k => rescaleOdo (vk k) (nk k)) v atTop (closedBall a r))
    {K : ℝ} (hK : ∀ k z, (nk k : ℝ)⁻¹ • toE z ∈ U → (lap (vk k) z : ℝ) ≤ K) :
    ViscFromBelowLE (fun X => X.trace - K) U v := by
  intro x hx φ hφ hmin
  simp only
  by_contra hneg
  have hneg' := not_le.1 hneg
  set H := hessian φ x with hHdef
  have hH : H.IsSymm := hessian_isSymm_of_contDiffAt hφ
  set δ : ℝ := H.trace - K with hδ
  have hδ0 : 0 < δ := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set κ : ℝ := δ / (8 * d) with hκ
  have hκ0 : 0 < κ := by positivity
  set l : ℝ := δ / 2 with hl
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ hκ0
  obtain ⟨ρ₂, hρ₂, hm⟩ := Metric.eventually_nhds_iff.1 hmin
  obtain ⟨ρ₃, hρ₃, hball⟩ := Metric.isOpen_iff.1 hU x hx
  set r : ℝ := min (min ρ₁ ρ₂) ρ₃ / 4 with hr
  have hr0 : 0 < r := by positivity
  have hm1 : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₃ := min_le_right _ _
  have hcl : closedBall x (2 * r) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  set p : Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x) with hp
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (-1 : ℝ) *
      ((vk k z : ℝ) - (nk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - x) + qM H (X - x) + ql (-l) (X - x))
          ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball x r) (nk k))) ≤ 0 ∧
      (0 : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards [hnk.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : nk k ≠ 0 := by omega
    refine ⟨?_, ENNReal.zero_ne_top⟩
    rw [FreeLimitRegular.supGradSet_eq_empty fun z hz => ?_]
    · simp
    · rw [FreeLimitRegular.lapR_rescaled hd (-1) (vk k) hH p x (-l) hn0 z]
      have hzU : (nk k : ℝ)⁻¹ • toE z ∈ U := by
        have h := (OpenMaxPrinciple.mem_discretize_iff' hn0).1 hz
        exact hcl (ball_subset_closedBall (ball_subset_ball (by linarith) h))
      linarith [hK k z hzU]
  have hV : Tendsto (fun k => ((0 : ℝ≥0∞)).toReal / (nk k : ℝ) ^ d) atTop (𝓝 0) := by simp
  obtain ⟨y, hy, h⟩ := SingleSourceMin.principle_generic_on hd (σ := -1) (V := fun _ => 0)
    (OpenMaxPrinciple.continuous_quadratic p x H (-l)) hr0 (by linarith : r < 2 * r)
    (hv.mono hcl) hnk (hconv x (2 * r) hcl) hvol hV (mem_ball_self hr0)
  rw [mem_sphere, dist_eq_norm] at hy
  have hy1 : ‖y - x‖ < ρ₁ := by rw [hy]; linarith
  have hy2 : dist y x < ρ₂ := by rw [dist_eq_norm, hy]; linarith
  have hTy := abs_le.1 (hT y hy1)
  have hmy : v x - φ x ≤ v y - φ y := hm hy2
  simp only [sub_self, inner_zero_right, qM_zero_right, ql_zero_right, add_zero,
    sub_zero] at h
  have hql : ql (-l) (y - x) = -(l * r ^ 2 / (2 * d)) := by rw [ql, hy]; ring
  have hfd : inner ℝ p (y - x) = fderiv ℝ φ x (y - x) := by
    rw [hp, InnerProductSpace.toDual_symm_apply]
  rw [hy] at hTy
  have hkey : l * r ^ 2 / (2 * d) = 2 * (κ * r ^ 2) := by
    rw [hl, hκ]; field_simp; ring
  have hr2 : 0 < κ * r ^ 2 := by positivity
  rw [hql, hfd] at h
  linarith [hTy.1]

/-! ### The exact second-order expansion of a quadratic -/

theorem hasSecondOrderTaylorAt_quad {c : ℝ} {g x : Rd d} {Q : Matrix (Fin d) (Fin d) ℝ}
    (hQ : Q.IsSymm) (a : Rd d) :
    HasSecondOrderTaylorAt (fun y => c + inner ℝ g (y - x) + qM Q (y - x)) a
      (g + WithLp.toLp 2 (Q *ᵥ WithLp.ofLp (a - x))) Q := by
  have h : ∀ y : Rd d, (fun y => c + inner ℝ g (y - x) + qM Q (y - x)) y -
      (fun y => c + inner ℝ g (y - x) + qM Q (y - x)) a -
      inner ℝ (g + WithLp.toLp 2 (Q *ᵥ WithLp.ofLp (a - x))) (y - a) - qM Q (y - a) = 0 := by
    intro y
    have e : y - x = (a - x) + (y - a) := by abel
    simp only
    rw [e, SplitJensen.qM_add_sym hQ (y - a) (a - x), inner_add_right, inner_add_left]
    ring
  unfold HasSecondOrderTaylorAt
  exact (Asymptotics.isLittleO_zero _ _).congr_left fun y => (h y).symm

/-! ### Step -/

/-- **Step**: the limits are viscosity subsolutions of `F*(D²u) ≤ 0` where
they are positive, off the origin. -/
theorem ssLimitSubStar (hconv : MuConvergenceStmt) (hComp : SSCompactnessStmt)
    (hPS : PegdenSmartTouchingStmt) : SSLimitSubStarStmt := by
  intro d hd E hmax
  have hd1 : 1 ≤ d := by omega
  have hE : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hmax]; omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  filter_upwards [ssPeanoStar hconv hComp d hd E hmax, ae_all_iff.2 E.bounded] with η hpeano hbd
  intro u hu
  have hbd' : ∀ z, E.ηmin ≤ η z ∧ η z ≤ 2 * (d : ℤ) - 2 := fun z =>
    ⟨(hbd z).1, (hbd z).2.trans hmax.le⟩
  obtain ⟨nk, hnk, hconvu⟩ := hu
  -- continuity of `u` off the origin (step)
  obtain ⟨φ₀, hφ₀, v, hvc, hconvφ⟩ := hComp d hd E.ηmin η hbd' nk hnk
  have hopen : IsOpen {x : Rd d | x ≠ 0} := isOpen_ne
  have huv : Set.EqOn u (fun y => v y + fundamentalSolution d y) {x : Rd d | x ≠ 0} :=
    fun y hy => tendsto_nhds_unique ((hconvu.tendsto_at hy).comp hφ₀.tendsto_atTop)
      (hconvφ.tendsto_at hy)
  have hucont : ContinuousOn u {x : Rd d | x ≠ 0} :=
    (hvc.continuousOn.add (SingleSourceMin.continuousOn_fundamentalSolution d)).congr huv
  -- integer scales and uniform convergence on closed balls off the origin
  have hdpos' : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  set hk : ℕ → ℝ := fun k => (nk k : ℝ) ^ (1 / (d : ℝ)) with hhk_def
  set mk : ℕ → ℕ := fun k => ⌊hk k⌋₊ with hmk_def
  have hhk : Tendsto hk atTop atTop :=
    (tendsto_rpow_atTop hdpos').comp (tendsto_natCast_atTop_atTop.comp hnk.tendsto_atTop)
  have hmk : Tendsto mk atTop atTop := tendsto_nat_floor_atTop.comp hhk
  have ht : Tendsto (fun k => (mk k : ℝ) / hk k) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hhk
  have hcs : Tendsto (fun k => (hk k / mk k) ^ 2) atTop (𝓝 1) := by
    have h := (ht.inv₀ one_ne_zero).pow 2
    simp only [inv_one, one_pow] at h
    exact h.congr fun k => by rw [inv_div]
  have hballs : ∀ (a : Rd d) (r : ℝ), closedBall a r ⊆ {x : Rd d | x ≠ 0} →
      TendstoUniformlyOn (fun k => rescaleOdo (singleSourceOdometer η (nk k)) (mk k)) u atTop
        (closedBall a r) := by
    intro a r har
    have hra : r < ‖a‖ := by
      by_contra hle
      have h0 : (0 : Rd d) ∈ closedBall a r := by
        rw [mem_closedBall, dist_zero_left]
        exact not_lt.1 hle
      exact har h0 rfl
    have hball₂ : closedBall a ((r + ‖a‖) / 2) ⊆ {x : Rd d | x ≠ 0} := by
      intro y hy hy0
      rw [hy0, mem_closedBall, dist_zero_left] at hy
      linarith
    have hFunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).1 hconvu _ hball₂
      (isCompact_closedBall a _)
    have h := SingleSourceMin.tendstoUniformlyOn_rescale (by linarith : r < (r + ‖a‖) / 2)
      (hucont.mono hball₂) hFunif hcs ht
    refine h.congr ?_
    filter_upwards [hmk.eventually (eventually_ge_atTop 1),
      hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk1 hn1 y _
    exact (SingleSourceMin.rescaleOdo_eq _ (by omega) (by omega) y).symm
  -- `|Δu| ≤ K₀` off the origin in the viscosity sense
  set K₀ : ℝ := 2 * (d : ℝ) + |(E.ηmin : ℝ)| with hK₀
  have hz0 : ∀ (k : ℕ) (z : Site d), (mk k : ℝ)⁻¹ • toE z ∈ {x : Rd d | x ≠ 0} → z ≠ 0 := by
    intro k z hz h0
    rw [h0, toE_zero', smul_zero] at hz
    exact hz rfl
  have hAu : ViscFromAboveGE (fun X => X.trace + K₀) {x : Rd d | x ≠ 0} u :=
    viscFromAboveGE_of_lap_ge_on hd1 hmk hopen hucont hballs fun k z hz =>
      (abs_lap_ssOdometer_le hd1 hbd' (ssNonempty d hd1 η (fun x => (hbd' x).2) (nk k))
        (hz0 k z hz)).1
  have hBu : ViscFromBelowLE (fun X => X.trace - K₀) {x : Rd d | x ≠ 0} u :=
    viscFromBelowLE_of_lap_le_on hd1 hmk hopen hucont hballs fun k z hz =>
      (abs_lap_ssOdometer_le hd1 hbd' (ssNonempty d hd1 η (fun x => (hbd' x).2) (nk k))
        (hz0 k z hz)).2
  -- the subsolution property
  intro x hx φ hφ hmx
  by_contra hneg
  have hpos : 0 < effOpStar E (hessian φ x) := not_le.1 hneg
  set H := hessian φ x with hHdef
  have hH : H.IsSymm := hessian_isSymm_of_contDiffAt hφ
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = effOpStar E H / (8 * d) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact div_pos hpos (by positivity)
  have h8 : 8 * (d : ℝ) * ε = effOpStar E H := by
    rw [hε, mul_div_assoc', mul_div_cancel_left₀ _ (by positivity : (8 * (d : ℝ)) ≠ 0)]
  have hH's : (H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    hH.add (Matrix.isSymm_one.smul _)
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ hε0
  obtain ⟨ρ₂, hρ₂, hm⟩ := Metric.eventually_nhds_iff.1 hmx
  have hUopen : IsOpen {y : Rd d | y ≠ 0 ∧ 0 < u y} :=
    hucont.isOpen_inter_preimage hopen (isOpen_Ioi (a := (0 : ℝ)))
  obtain ⟨ρ₃, hρ₃, hball3⟩ := Metric.isOpen_iff.1 hUopen x hx
  obtain ⟨ρ, hρ0, hρ1, hρ2, hρ3⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ₁ ∧ ρ < ρ₂ ∧ ρ < ρ₃ :=
    ⟨min (min ρ₁ ρ₂) ρ₃ / 2, by positivity,
      by linarith [(min_le_left (min ρ₁ ρ₂) ρ₃).trans (min_le_left ρ₁ ρ₂),
        (lt_min (lt_min hρ₁ hρ₂) hρ₃ : 0 < min (min ρ₁ ρ₂) ρ₃)],
      by linarith [(min_le_left (min ρ₁ ρ₂) ρ₃).trans (min_le_right ρ₁ ρ₂),
        (lt_min (lt_min hρ₁ hρ₂) hρ₃ : 0 < min (min ρ₁ ρ₂) ρ₃)],
      by linarith [min_le_right (min ρ₁ ρ₂) ρ₃,
        (lt_min (lt_min hρ₁ hρ₂) hρ₃ : 0 < min (min ρ₁ ρ₂) ρ₃)]⟩
  have hsubU : closedBall x ρ ⊆ {y : Rd d | y ≠ 0 ∧ 0 < u y} :=
    (closedBall_subset_ball hρ3).trans hball3
  set g : Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x) with hg
  -- `u ≤ ψ - ε|· - x|²` on `B̄_ρ(x)`, `ψ` the quadratic of `D²φ(x) + 4εI`
  have hle : ∀ y, ‖y - x‖ ≤ ρ → u y - (u x + inner ℝ g (y - x) +
      qM (H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - x)) ≤ -(ε * ‖y - x‖ ^ 2) := by
    intro y hy
    have h1 := abs_le.1 (hT y (by linarith))
    have h2 : u y - φ y ≤ u x - φ x := hm (by rw [dist_eq_norm]; linarith)
    have hfd : inner ℝ g (y - x) = fderiv ℝ φ x (y - x) := by
      rw [hg, InnerProductSpace.toDual_symm_apply]
    rw [qM_add_mat, qM_smul_one, hfd]
    linarith [h1.1, h1.2]
  -- Pegden-Smart's Proposition 2.5 on `B_ρ(x)`
  set K' : ℝ := max K₀ (|(H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ)).trace| + d) with hK'
  have hballne : ball x ρ ⊆ {y : Rd d | y ≠ 0} := fun y hy =>
    (hsubU (ball_subset_closedBall hy)).1
  have hcu : ContinuousOn u (closure (ball x ρ)) := by
    rw [closure_ball x hρ0.ne']
    exact hucont.mono fun y hy => (hsubU hy).1
  have hfront : ∀ y ∈ frontier (ball x ρ), u y - (u x + inner ℝ g (y - x) +
      qM (H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - x)) ≤ -(ε * ρ ^ 2 / 2) := by
    intro y hy
    rw [frontier_ball x hρ0.ne', mem_sphere, dist_eq_norm] at hy
    have h1 := hle y hy.le
    rw [hy] at h1
    have : 0 < ε * ρ ^ 2 := by positivity
    linarith
  have hposx : ∃ y ∈ ball x ρ, -(ε * ρ ^ 2 / 2) < u y - (u x + inner ℝ g (y - x) +
      qM (H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - x)) :=
    ⟨x, mem_ball_self hρ0, by
      simp only [sub_self, inner_zero_right, qM_zero_right, add_zero]
      have : 0 < ε * ρ ^ 2 / 2 := by positivity
      linarith⟩
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hvol := hPS d hd (ball x ρ) isOpen_ball isBounded_ball K' u
    (fun y => u x + inner ℝ g (y - x) + qM (H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - x))
    hcu (LimitTrace.continuous_quad _ _ _ _).continuousOn
    (fun y hy φ' hφ' hm' => (hAu.trace_mono (le_max_left K₀ _)) y (hballne hy) φ' hφ' hm')
    (fun y hy φ' hφ' hm' => (hBu.trace_mono (le_max_left K₀ _)) y (hballne hy) φ' hφ' hm')
    (LimitTrace.quad_viscAbove (le_max_of_le_right (by
      have := neg_abs_le (H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ)).trace
      linarith)))
    (LimitTrace.quad_viscBelow hH's (le_max_of_le_right (by
      linarith [le_abs_self (H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ)).trace])))
    _ hfront hposx
  obtain ⟨a, ⟨haB, -, p₁, p₂, X, X', hX, hX', hTu, hTψ, δ, hδ, hpd⟩⟩ :=
    nonempty_of_measure_ne_zero hvol.ne'
  -- the Peano Hessian of the quadratic is its matrix (one inequality suffices)
  have hexact := hasSecondOrderTaylorAt_quad (c := u x) (g := g) (x := x) hH's a
  have hX'le : ∀ h : Rd d, qM X' h ≤ qM (H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ)) h := by
    intro h
    have := qM_sub_le_of_touching isOpen_univ (Set.mem_univ a) hTψ hexact (p₀ := 0) (δ := 0)
      (fun y _ => by simp) h
    linarith
  have hpsdX : (X' - X - δ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
    have e : -(δ • (1 : Matrix (Fin d) (Fin d) ℝ)) - (X - X') =
        X' - X - δ • (1 : Matrix (Fin d) (Fin d) ℝ) := by abel
    rw [e] at hpd
    exact hpd.posSemidef
  have hXle : (H + (4 * ε) • (1 : Matrix (Fin d) (Fin d) ℝ) - X).PosSemidef := by
    refine posSemidef_of_qM_nonneg (hH's.sub hX) fun h => ?_
    have h1 := qM_sub_ge_of_psd hpsdX h
    have h2 := hX'le h
    have h3 : 0 ≤ δ / 2 * ‖h‖ ^ 2 := by positivity
    rw [qM_sub_mat]
    linarith
  -- `F*(D²u(a)) ≥ F*(D²φ(x) + 4εI) = F*(D²φ(x)) - 4dε > 0`, against `ssPeanoStar`
  have hF1 := degenerateElliptic_effOpStar hd1 E hE X _ hX hH's hXle
  have hF2 := effOpStar_add_smul_one hd1 E hE hH (4 * ε)
  have hF3 := hpeano _ ⟨nk, hnk, hconvu⟩ a p₁ X (hsubU (ball_subset_closedBall haB)).1
    (hsubU (ball_subset_closedBall haB)).2 hX hTu
  rw [hF2] at hF1
  linarith

/-! ### Theorem 9.2 with `F*` -/

/-- **Theorem 9.2, `F*`-variant**: the obstacle problem with
`F*(M) = sup {l : μ*(l, M) > 0}`, from compactness (`SSCompactnessStmt`, step), the outer
bound `SSOuterBoundStmt`, Pegden-Smart's Proposition 2.5 (`PegdenSmartTouchingStmt`) and
Alexandrov's theorem (`AlexandrovStmt`, through the Crandall-Ishii-Lions comparison
`shiftComparison_of_alexandrov`); Lemma 5.5 is `muConvergence_unconditional`. No flatness, no
density assumption, no origin step. -/
theorem singleSourceTheoremFstar (hComp : SSCompactnessStmt) (hOB : SSOuterBoundStmt)
    (hPS : PegdenSmartTouchingStmt) (hA : AlexandrovStmt) : SingleSourceTheoremStarStmt :=
  singleSourceTheoremStar_of_sub hComp hOB
    (ssLimitSubStar muConvergence_unconditional hComp hPS) (shiftComparison_of_alexandrov hA)

end SingleSourceFstar

end RandomSandpile

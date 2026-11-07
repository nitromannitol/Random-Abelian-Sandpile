import LatticeProb.External.PotentialKernelAsymptoticsProved
import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessSteps
import RandomSandpile.Proofs.Sec7.CompactnessGradient
import RandomSandpile.Steps.Sec5.ABP

/-! # Theorem 9.2: the lattice fundamental solution (`SSLatticeGreenStmt`)

The lattice fundamental solution used in step is
`ssGreen d x = lim_m (2d)⁻¹ (g_m(x) - g_m(0))`, `g_m = srwGreen d m = ∑_{j < m} P^j` the truncated
Green function of simple random walk. The limit exists for every `d ≥ 2`: for `d ≥ 3` it is
`(2d)⁻¹ (G_∞(x) - G_∞(0))` (`summable_srwHeat`), for `d = 2` it is `-a(x)/4`, `a` the potential
kernel. Since `Δ g_m = 2d (P^m - δ_0)` and `P^m → 0`, `Δ ssGreen = -δ_0` (`lapR_ssGreen`). The
asymptotics `ssGreen = G + κ + O(|x|^{-d})` (`ssGreen_asymp`, `G = fundamentalSolution d`) are the
Lawler-Limic Theorems 4.3.1 and 4.4.4, proved in Lattice-Probability
(`LatticeProb.External.potentialKernelAsymptotics_holds`, the former input). Consequence:
`ssLatticeGreen : SSLatticeGreenStmt`.
-/

noncomputable section

open Filter Topology LatticeProb

namespace RandomSandpile

variable {d : ℕ}

namespace SSGreen

/-- The heat kernel of simple random walk is symmetric. -/
theorem srwHeat_neg (j : ℕ) (x : Site d) : srwHeat d j (-x) = srwHeat d j x := by
  induction j generalizing x with
  | zero => simp [srwHeat_zero]
  | succ j ih =>
    rw [srwHeat_succ, srwHeat_succ, walkOp, walkOp, nbrSum, nbrSum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show -x + unit i = -(x - unit i) by abel, show -x - unit i = -(x + unit i) by abel, ih, ih]
    ring

/-- The truncated Green function is symmetric. -/
theorem srwGreen_neg (m : ℕ) (x : Site d) : srwGreen d m (-x) = srwGreen d m x := by
  simp only [srwGreen, srwHeat_neg]

/-- `Δ (c (u - k)) = c Δ u`. -/
theorem lapR_mul_sub_const (c k : ℝ) (u : Site d → ℝ) (x : Site d) :
    lapR (fun y => c * (u y - k)) x = c * lapR u x := by
  have h : ∀ i : Fin d, c * (u (x + unit i) - k) + c * (u (x - unit i) - k)
      = c * (u (x + unit i) + u (x - unit i)) - 2 * c * k := fun i => by ring
  simp only [lapR, nbrSum, h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- One step of the heat equation: `Δ P^j = 2d (P^{j+1} - P^j)`. -/
theorem lapR_srwHeat (hd : 0 < d) (j : ℕ) (x : Site d) :
    lapR (srwHeat d j) x = 2 * d * (srwHeat d (j + 1) x - srwHeat d j x) := by
  have hd' : (2 * d : ℝ) ≠ 0 := by positivity
  have h2d : (2 * d : ℝ) * (2 * d : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hd'
  rw [lapR, srwHeat_succ, walkOp, div_eq_mul_inv]
  linear_combination (-(nbrSum (srwHeat d j) x)) * h2d

/-- `Δ g_m = 2d (P^m - δ_0)`. -/
theorem lapR_srwGreen (hd : 0 < d) (m : ℕ) (x : Site d) :
    lapR (srwGreen d m) x = 2 * d * (srwHeat d m x - if x = 0 then 1 else 0) := by
  induction m with
  | zero =>
    have h0 : srwGreen d 0 = fun _ => 0 := funext fun y => srwGreen_zero y
    rw [h0, srwHeat_zero]
    simp [lapR, nbrSum]
  | succ m ih =>
    have h1 : srwGreen d (m + 1) = fun y => srwGreen d m y + srwHeat d m y :=
      funext fun y => srwGreen_succ m y
    have hadd : lapR (fun y => srwGreen d m y + srwHeat d m y) x
        = lapR (srwGreen d m) x + lapR (srwHeat d m) x := by
      simp only [lapR, nbrSum, Finset.sum_add_distrib]
      ring
    rw [h1, hadd, ih, lapR_srwHeat hd]
    ring

/-- `P^m(x) → 0` (on-diagonal bound `P^m ≤ C m^{-d/2}`). -/
theorem tendsto_srwHeat_zero (hd : 1 ≤ d) (x : Site d) :
    Tendsto (fun m : ℕ => srwHeat d m x) atTop (𝓝 0) := by
  obtain ⟨C, -, hheat⟩ := GreenTwoSided.srwHeat_le_mul_rpow_neg_half (d := d) hd
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  have hpow : Tendsto (fun m : ℕ => C * (m : ℝ) ^ (-(d : ℝ) / 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (d : ℝ) / 2) (div_pos hd0 two_pos)).comp
      tendsto_natCast_atTop_atTop
    have h' : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(d : ℝ) / 2)) atTop (𝓝 0) := by
      simpa [Function.comp_def, neg_div] using h
    simpa using h'.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow
    (Eventually.of_forall fun m => srwHeat_nonneg m x) ?_
  exact eventually_atTop.2 ⟨1, fun m hm => hheat m hm x⟩

theorem euclidNorm_eq (z : Site d) : euclidNorm z = ‖toE z‖ := by
  simp [euclidNorm, EuclideanSpace.norm_eq, toE]

end SSGreen

open SSGreen

/-- The lattice fundamental solution `lim_m (2d)⁻¹ (g_m(x) - g_m(0))` (`Δ ssGreen = -δ_0`). -/
def ssGreen (d : ℕ) (x : Site d) : ℝ :=
  limUnder atTop fun m : ℕ => (2 * d : ℝ)⁻¹ * (srwGreen d m x - srwGreen d m 0)

theorem exists_tendsto_ssGreenApprox (hd : 2 ≤ d) (x : Site d) :
    ∃ a, Tendsto (fun m : ℕ => (2 * d : ℝ)⁻¹ * (srwGreen d m x - srwGreen d m 0)) atTop
      (𝓝 a) := by
  rcases Nat.lt_or_ge d 3 with h | h
  · have hd2 : d = 2 := by omega
    subst hd2
    obtain ⟨b, hb, -⟩ := (External.potentialKernelAsymptotics_holds 2).1 rfl
    have := ((hb x).neg).const_mul ((2 * 2 : ℝ)⁻¹)
    exact ⟨_, this.congr fun m => by push_cast; ring⟩
  · have hs := fun y => (summable_srwHeat h y).hasSum.tendsto_sum_nat
    exact ⟨_, ((hs x).sub (hs 0)).const_mul ((2 * d : ℝ)⁻¹)⟩

theorem tendsto_ssGreen (hd : 2 ≤ d) (x : Site d) :
    Tendsto (fun m : ℕ => (2 * d : ℝ)⁻¹ * (srwGreen d m x - srwGreen d m 0)) atTop
      (𝓝 (ssGreen d x)) :=
  tendsto_nhds_limUnder (exists_tendsto_ssGreenApprox hd x)

/-- Gradient of `ssGreen` as a limit of gradients of `(2d)⁻¹ g_m`. -/
theorem tendsto_ssGreen_sub (hd : 2 ≤ d) (x y : Site d) :
    Tendsto (fun m : ℕ => (2 * d : ℝ)⁻¹ * (srwGreen d m x - srwGreen d m y)) atTop
      (𝓝 (ssGreen d x - ssGreen d y)) :=
  ((tendsto_ssGreen hd x).sub (tendsto_ssGreen hd y)).congr fun m => by ring

/-- **`Δ ssGreen = -δ_0`.** -/
theorem lapR_ssGreen (hd : 2 ≤ d) (x : Site d) :
    lapR (ssGreen d) x = -(if x = 0 then 1 else 0) := by
  have hd0 : 0 < d := by omega
  have h2d : (2 * d : ℝ) ≠ 0 := by positivity
  set f : ℕ → Site d → ℝ := fun m y => (2 * d : ℝ)⁻¹ * (srwGreen d m y - srwGreen d m 0)
    with hf
  have hlap : ∀ m, lapR (f m) x = srwHeat d m x - if x = 0 then 1 else 0 := by
    intro m
    rw [hf, lapR_mul_sub_const, lapR_srwGreen hd0, ← mul_assoc, inv_mul_cancel₀ h2d, one_mul]
  have hT : Tendsto (fun m => lapR (f m) x) atTop (𝓝 (lapR (ssGreen d) x)) := by
    simp only [lapR, nbrSum]
    exact (tendsto_finsetSum _ fun i _ =>
      ((tendsto_ssGreen hd _).add (tendsto_ssGreen hd _))).sub
        ((tendsto_ssGreen hd x).const_mul _)
  have h2 : Tendsto (fun m => lapR (f m) x) atTop (𝓝 (0 - if x = 0 then (1 : ℝ) else 0)) :=
    ((tendsto_srwHeat_zero (by omega) x).sub_const _).congr fun m => (hlap m).symm
  rw [tendsto_nhds_unique hT h2, zero_sub]

theorem ssGreen_eq_of_three_le (h : 3 ≤ d) (x : Site d) :
    ssGreen d x = (2 * d : ℝ)⁻¹ * (srwGreenInf d x - srwGreenInf d 0) := by
  have hs := fun y => (summable_srwHeat h y).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique (tendsto_ssGreen (by omega) x)
    (((hs x).sub (hs 0)).const_mul ((2 * d : ℝ)⁻¹))

/-- **Asymptotics of the lattice fundamental solution**: `ssGreen = G + κ + O(|x|^{-d})` with
`G = fundamentalSolution d` (Lawler-Limic Thms 4.3.1, 4.4.4, proved in Lattice-Probability). -/
theorem ssGreen_asymp (hd : 2 ≤ d) : ∃ κ C R : ℝ, 1 ≤ R ∧ ∀ z : Site d, R ≤ ‖toE z‖ →
    |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ)) := by
  rcases Nat.lt_or_ge d 3 with h | h
  · have hd2 : d = 2 := by omega
    subst hd2
    obtain ⟨b, hb, κ, C, R, hR, hbd⟩ := (External.potentialKernelAsymptotics_holds 2).1 rfl
    refine ⟨-κ / 4, C / 4, R, hR, fun z hz => ?_⟩
    have hval : ssGreen 2 z = (2 * 2 : ℝ)⁻¹ * -b z :=
      tendsto_nhds_unique (tendsto_ssGreen le_rfl z)
        ((((hb z).neg).const_mul ((2 * 2 : ℝ)⁻¹)).congr fun m => by push_cast; ring)
    have hb' := hbd z (by rwa [euclidNorm_eq])
    rw [euclidNorm_eq] at hb'
    have e : ssGreen 2 z - fundamentalSolution 2 (toE z) - -κ / 4
        = -(1 / 4) * (b z - (2 / Real.pi * Real.log ‖toE z‖ + κ)) := by
      rw [hval, fundamentalSolution, if_pos rfl]
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    rw [e, abs_mul]
    have h4 : |(-(1 / 4) : ℝ)| = 1 / 4 := by norm_num [abs_of_pos]
    rw [h4]
    have h5 : ‖toE z‖ ^ (-((2 : ℕ) : ℝ)) = ‖toE z‖ ^ (-2 : ℝ) := by norm_num
    rw [h5]
    linarith
  · obtain ⟨C, R, hR, hbd⟩ := (External.potentialKernelAsymptotics_holds d).2 h
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast h
    have hω : unitBallVolume d ≠ 0 := (unitBallVolume_pos (by omega)).ne'
    have hdm : (d : ℝ) - 2 ≠ 0 := by linarith
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    refine ⟨-(2 * d : ℝ)⁻¹ * srwGreenInf d 0, (2 * d : ℝ)⁻¹ * C, R, hR, fun z hz => ?_⟩
    have hb' : |srwGreenInf d z - 2 / ((d - 2) * unitBallVolume d) * ‖toE z‖ ^ (2 - (d : ℝ))|
        ≤ C * ‖toE z‖ ^ (-(d : ℝ)) := by
      have := hbd z (by rwa [euclidNorm_eq])
      rw [euclidNorm_eq] at this
      exact this
    have e : ssGreen d z - fundamentalSolution d (toE z) - -(2 * d : ℝ)⁻¹ * srwGreenInf d 0
        = (2 * d : ℝ)⁻¹ *
          (srwGreenInf d z - 2 / ((d - 2) * unitBallVolume d) * ‖toE z‖ ^ (2 - (d : ℝ))) := by
      rw [ssGreen_eq_of_three_le h, fundamentalSolution, if_neg (by omega)]
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity), mul_assoc]
    exact mul_le_mul_of_nonneg_left hb' (by positivity)

/-- **`SSLatticeGreenStmt`** (step 2 of the decomposition), from `ssGreen`. -/
theorem ssLatticeGreen : SSLatticeGreenStmt := by
  intro d hd
  obtain ⟨κ, C, R, hR, hasymp⟩ := ssGreen_asymp hd
  refine ⟨ssGreen d, lapR_ssGreen hd, κ, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  set M : ℝ := max R (Real.sqrt (|C| / ε) + 1) with hM
  refine (ABP.ballZ0_finite (d := d) (M + 1)).subset fun z hz => ?_
  rw [ABP.mem_ballZ0]
  by_contra hzM
  push Not at hzM
  apply hz
  set t : ℝ := ‖toE z‖ with ht
  have hMR : R ≤ M := le_max_left _ _
  have hMs : Real.sqrt (|C| / ε) + 1 ≤ M := le_max_right _ _
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hX := hasymp z (by linarith)
  have hpow : t ^ (-(d : ℝ)) = (t ^ d)⁻¹ := by rw [Real.rpow_neg ht0.le, Real.rpow_natCast]
  have hsplit : t ^ d = t ^ (d - 2) * t ^ 2 := by rw [← pow_add]; congr 1; omega
  have hX' : |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * (t ^ d)⁻¹ := hpow ▸ hX
  have key : t ^ (d - 2) * |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ |C| / t ^ 2 := by
    calc t ^ (d - 2) * |ssGreen d z - fundamentalSolution d (toE z) - κ|
        ≤ t ^ (d - 2) * (C * (t ^ d)⁻¹) := mul_le_mul_of_nonneg_left hX' (by positivity)
      _ = C / t ^ 2 := by rw [hsplit]; field_simp
      _ ≤ |C| / t ^ 2 := div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
  have hsq : |C| / ε < t ^ 2 := by
    have h1 : Real.sqrt (|C| / ε) < t := by linarith
    exact (Real.sqrt_lt' ht0).1 h1
  have hfin : |C| / t ^ 2 < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hsq
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  linarith

end RandomSandpile

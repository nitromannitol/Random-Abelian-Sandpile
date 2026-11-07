import RandomSandpile.Draft.Section1Partial
import RandomSandpile.Proofs.Sec7.MainTheorem

/-!
# Theorem 1.1 with the support radius chosen after the law

* `sandpileSupportLaw : SandpileSupportLawStmt`: for every environment there is `R` with the
  rescaled sandpiles eventually vanishing off `B_R(W)`, from Lemma 7.2's box
  (`FreeOdometerUpperBoundStmt`: `v_n = 0` off `{|x|_∞ < R₀ (n + 1)}`, `R₀ = R₀(W, η_max)`): off
  `W_n` and off the box enlarged by one site, `s_n = Δ v_n = 0`.
* `sandpileLimitLaw : SandpileLimitLawStmt`: step with that radius (all sub-steps proved).
* `mainTheorem_lawRadius_of_steps`, `mainTheorem_lawRadius_of_remainingSteps`:
  `MainTheoremLawRadiusStmt` (Draft/Section1Partial.lean) from the steps of Theorem 1.1, without
  `SandpileSupportStmt`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- Step from Lemma 7.2's box. -/
theorem sandpileSupportLaw_of_upperBound (hUB : FreeOdometerUpperBoundStmt) :
    SandpileSupportLawStmt := by
  intro d hd W hW E
  obtain ⟨C, R₀, hUB'⟩ := hUB d hd W hW.1 E.ηmax
  obtain ⟨w₀, hw₀⟩ := hW.2.2.1.nonempty
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set R : ℝ := ‖w₀‖ + d * (2 * ((R₀ + 1 : ℕ) : ℝ) + 1) + d + 2 with hR
  refine ⟨R, by positivity, ?_⟩
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  filter_upwards [hbdd] with η hη
  filter_upwards [eventually_ge_atTop 1] with n hn x hx
  have hn0 : n ≠ 0 := by omega
  obtain ⟨-, -, hsupp⟩ := hUB' η (fun x => (hη x).2) n
  set y := latticeRound ((n : ℝ) • x) with hy
  have hxw : R ≤ dist x w₀ := by
    by_contra h
    push Not at h
    exact hx (Metric.mem_thickening_iff.2 ⟨w₀, hw₀, h⟩)
  have hxn : (d : ℝ) * (2 * ((R₀ + 1 : ℕ) : ℝ) + 1) < ‖x‖ := by
    have := dist_le_norm_add_norm x w₀
    linarith
  obtain ⟨i, hi⟩ := exists_le_abs_latticeRound hn (R₀ + 1) hxn
  have hyW : y ∉ discretize W n := by
    intro hyW
    have hmem : (n : ℝ)⁻¹ • toE y ∈ W :=
      (Set.mem_smul_set_iff_inv_smul_mem₀ (by exact_mod_cast hn0) _ _).1 hyW
    have h1 := norm_inv_smul_latticeRound_sub_le hn0 x
    have h2 : ((d : ℝ) + 1) / n ≤ d + 1 := div_le_self (by positivity) (by exact_mod_cast hn)
    have h3 := norm_nonneg w₀
    have h4 : 0 ≤ (d : ℝ) * (2 * ((R₀ + 1 : ℕ) : ℝ) + 1) := by positivity
    exact hx (Metric.mem_thickening_iff.2 ⟨_, hmem, by
      rw [dist_comm, dist_eq_norm]; linarith⟩)
  have hn0' : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hv : ∀ z : Site d, |y i| - 1 ≤ |z i| → freeOdometer η (discretize W n) z = 0 := by
    intro z hz
    refine hsupp z ⟨i, ?_⟩
    push_cast at hi
    nlinarith
  have hunit : ∀ j : Fin d, |(unit j : Site d) i| ≤ 1 := fun j => by
    simp only [unit, Pi.single_apply]
    split_ifs <;> simp
  have hnb : nbrSumZ (freeOdometer η (discretize W n)) y = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have hp : |y i| - 1 ≤ |(y + unit j) i| := by
      have := abs_add_le (y i + (unit j : Site d) i) (-(unit j : Site d) i)
      rw [add_neg_cancel_right, abs_neg] at this
      rw [Pi.add_apply]
      linarith [hunit j]
    have hm : |y i| - 1 ≤ |(y - unit j) i| := by
      have := abs_add_le (y i - (unit j : Site d) i) ((unit j : Site d) i)
      rw [sub_add_cancel] at this
      rw [Pi.sub_apply]
      linarith [hunit j]
    rw [hv _ hp, hv _ hm, add_zero]
  simp only [rescaleSandpile, freeSandpile]
  rw [Set.indicator_of_notMem hyW, lap_eq, hv y (by linarith), hnb]
  simp

/-- **Step** (`SandpileSupportLawStmt`), from Lemma 7.2's box. -/
theorem sandpileSupportLaw : SandpileSupportLawStmt :=
  sandpileSupportLaw_of_upperBound (freeOdometerUpperBound_of_oneDim oneDimToppling)

/-- Step with the radius chosen after the law, from its sub-steps. -/
theorem sandpileLimitLaw_of_steps (hUB : FreeOdometerUpperBoundStmt)
    (hLap : FreeOdometerLapBoundStmt) (hEnv : EnvWeakStarStmt) (hRL : RescaledLapWeakStmt)
    (hRep : WeakStarRepresentationStmt) (hSupp : SandpileSupportLawStmt) :
    SandpileLimitLawStmt := by
  intro d hd W hW E _
  obtain ⟨R, hR, hSR⟩ := hSupp d hd W hW E
  exact ⟨R, hR, fun vbar hvc hae =>
    sandpileLimit_core hUB hLap hEnv hRL hRep hd hW E hR hSR vbar hvc hae⟩

/-- **Step with the radius chosen after the law**, unconditionally. -/
theorem sandpileLimitLaw : SandpileLimitLawStmt :=
  sandpileLimitLaw_of_steps (freeOdometerUpperBound_of_oneDim oneDimToppling)
    freeOdometerLapBound envWeakStar rescaledLapWeak weakStarRepresentation sandpileSupportLaw

/-- **Theorem 1.1 with the radius chosen after the law** from its steps. -/
theorem mainTheorem_lawRadius_of_steps (hComp : CompactnessStmt)
    (h64 : EffectiveOperatorBasicStmt) (hU : LimitComparisonStmt) (hEff : LimitViscEffStmt)
    (hZero : LimitViscZeroStmt) (hMin : LimitMinimalStmt) (hS : SandpileLimitLawStmt) :
    MainTheoremLawRadiusStmt := by
  intro d hd W hW E hHD
  obtain ⟨R, hR, hSR⟩ := hS d hd W hW E hHD
  exact ⟨R, hR, mainTheorem_core hComp h64 hU hEff hZero hMin hd hW E hHD hSR⟩

/-- **Theorem 1.1 with the radius chosen after the law** from the steps of
`mainTheorem_of_remainingSteps` except `SandpileSupportStmt`. -/
theorem mainTheorem_lawRadius_of_remainingSteps (h64 : EffectiveOperatorBasicStmt)
    (hT : PegdenSmartTouchingStmt) (hReg : FreeOdometerLimitRegularStmt) (hVan : MuVanishStmt)
    (hExtSup : ExteriorSupersolutionStmt) (hExtSub : ExteriorSubsolutionStmt)
    (hMax : InteriorMaxPrincipleStmt) (hMin : InteriorMinPrincipleStmt)
    (hTr : LimitTraceInteriorStmt) (hSplit : SplitTouchingStmt) : MainTheoremLawRadiusStmt :=
  mainTheorem_lawRadius_of_steps compactness h64
    (limitComparison_of_steps
      (pegdenSmartRegularity_of_touching_regular hT hReg lipschitzDomainFrontierNull)
      hVan hExtSup hExtSub hMax hMin)
    (limitViscEff_of_steps h64 hVan hMin)
    (limitViscZero_of_steps hExtSup hTr hReg lipschitzDomainFrontierNull hSplit)
    (limitMinimal_of_steps h64 hVan hMax hExtSub hReg lipschitzDomainFrontierNull hSplit)
    sandpileLimitLaw

end RandomSandpile

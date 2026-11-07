import RandomSandpile.Proofs.Sec7.MainTheoremUAssembly

/-!
# Theorem 1.1 with the corrected support radius [C12]

The paper prints "for some constant `R > 0` depending on `W` and `E(η(0))`". The corrected
reading is "depending on `W`, `d` and `η_max`" (correction [C12]): the radius comes from the box of Lemma 7.2 (`FreeOdometerUpperBoundStmt`: the
free odometer `v_n` vanishes off `{|x|_∞ < R₀ (n + 1)}`, `R₀ = R₀(d, W, η_max)`), which the proof
of Lemma 7.2 obtains from Lemma 7.1. The statement `MainTheoremStmt` chooses `R` after `d`, `W` and
`η_max`, before the law.

* `SandpileSupportEtaMaxStmt`: step with `R` chosen after `d`, `W` and `η_max`;
* `sandpileSupportEtaMax_of_upperBound`, `sandpileSupportEtaMax`: proof from Lemma 7.2's box. This
  is the argument of `sandpileSupportLaw_of_upperBound`, with the box chosen before the law;
* `mainTheorem_of_steps_etaMaxRadius`: `MainTheoremStmt` from the steps of Theorem 1.1, through
  the per-environment cores `mainTheorem_core` and `sandpileLimit_core`;
* `mainTheorem_etaMaxRadius_of_remainingSteps`, `mainTheorem_etaMaxRadius_of_inputs`,
  `mainTheorem_etaMaxRadius`: `MainTheoremStmt` from the literature inputs Lawler-Limic,
  Pegden-Smart (Proposition 2.5) and Alexandrov. The route is that of
  `mainTheorem_lawRadius`;
* `mainTheoremLawRadius_of_mainTheorem`: the corrected statement implies
  `MainTheoremLawRadiusStmt`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

/-- **Step with the corrected radius** ([C12]). There is `R > 0`, depending only on `d`, `W`
and `η_max`, such that for every environment bounded above by `η_max`, almost surely the rescaled
sandpiles eventually vanish off `B_R(W)`. -/
def SandpileSupportEtaMaxStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ ηmax : ℤ, ∃ R : ℝ, 0 < R ∧
    ∀ E : RandomEnvironment d, E.ηmax = ηmax →
      ∀ᵐ η ∂E.P, ∀ᶠ n : ℕ in atTop, ∀ x : Rd d, x ∉ Metric.thickening R W →
        rescaleSandpile (freeSandpile η (discretize W n)) n x = 0

/-- Step with the corrected radius from Lemma 7.2's box: off `W_n` and off the box enlarged
by one site, `s_n = Δ v_n = 0`. The box `R₀` is chosen from `d`, `W` and `η_max` only. -/
theorem sandpileSupportEtaMax_of_upperBound (hUB : FreeOdometerUpperBoundStmt) :
    SandpileSupportEtaMaxStmt := by
  intro d hd W hW ηmax
  obtain ⟨C, R₀, hUB'⟩ := hUB d hd W hW.1 ηmax
  obtain ⟨w₀, hw₀⟩ := hW.2.2.1.nonempty
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set R : ℝ := ‖w₀‖ + d * (2 * ((R₀ + 1 : ℕ) : ℝ) + 1) + d + 2 with hR
  refine ⟨R, by positivity, fun E hE => ?_⟩
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  filter_upwards [hbdd] with η hη
  filter_upwards [eventually_ge_atTop 1] with n hn x hx
  have hn0 : n ≠ 0 := by omega
  obtain ⟨-, -, hsupp⟩ := hUB' η (fun x => (hη x).2.trans_eq hE) n
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

/-- **Step with the corrected radius** (`SandpileSupportEtaMaxStmt`), from Lemma 7.2's box
(Lemma 7.1, `oneDimToppling`). -/
theorem sandpileSupportEtaMax : SandpileSupportEtaMaxStmt :=
  sandpileSupportEtaMax_of_upperBound (freeOdometerUpperBound_of_oneDim oneDimToppling)

/-- **Theorem 1.1** (`MainTheoremStmt`, with [C3] and [C12]) from its steps: compactness
(Lemma 7.2), Lemma 6.4(1), the comparison of subsequential limits, the identification steps
-, the sandpile sub-steps- and the support radius with `R = R(d, W, η_max)`. -/
theorem mainTheorem_of_steps_etaMaxRadius (hComp : CompactnessStmt)
    (h64 : EffectiveOperatorBasicStmt) (hU : LimitComparisonStmt) (hEff : LimitViscEffStmt)
    (hZero : LimitViscZeroStmt) (hMin : LimitMinimalStmt) (hUB : FreeOdometerUpperBoundStmt)
    (hLap : FreeOdometerLapBoundStmt) (hEnv : EnvWeakStarStmt) (hRL : RescaledLapWeakStmt)
    (hRep : WeakStarRepresentationStmt) (hSupp : SandpileSupportEtaMaxStmt) :
    MainTheoremStmt := by
  intro d hd W hW ηmax
  obtain ⟨R, hR, hSR⟩ := hSupp d hd W hW ηmax
  exact ⟨R, hR, fun E hE hHD => mainTheorem_core hComp h64 hU hEff hZero hMin hd hW E hHD
    (fun vbar hvc hae =>
      sandpileLimit_core hUB hLap hEnv hRL hRep hd hW E hR (hSR E hE) vbar hvc hae)⟩

/-- **Theorem 1.1** (`MainTheoremStmt`) from the steps of `mainTheorem_of_remainingSteps`,
without the printed-radius step `SandpileSupportStmt`. -/
theorem mainTheorem_etaMaxRadius_of_remainingSteps (h64 : EffectiveOperatorBasicStmt)
    (hT : PegdenSmartTouchingStmt) (hReg : FreeOdometerLimitRegularStmt) (hVan : MuVanishStmt)
    (hExtSup : ExteriorSupersolutionStmt) (hExtSub : ExteriorSubsolutionStmt)
    (hMax : InteriorMaxPrincipleStmt) (hMin : InteriorMinPrincipleStmt)
    (hTr : LimitTraceInteriorStmt) (hSplit : SplitTouchingStmt) : MainTheoremStmt :=
  mainTheorem_of_steps_etaMaxRadius compactness h64
    (limitComparison_of_steps
      (pegdenSmartRegularity_of_touching_regular hT hReg lipschitzDomainFrontierNull)
      hVan hExtSup hExtSub hMax hMin)
    (limitViscEff_of_steps h64 hVan hMin)
    (limitViscZero_of_steps hExtSup hTr hReg lipschitzDomainFrontierNull hSplit)
    (limitMinimal_of_steps h64 hVan hMax hExtSub hReg lipschitzDomainFrontierNull hSplit)
    (freeOdometerUpperBound_of_oneDim oneDimToppling) freeOdometerLapBound envWeakStar
    rescaledLapWeak weakStarRepresentation sandpileSupportEtaMax

/-- **Theorem 1.1** (`MainTheoremStmt`) from the inputs Lawler-Limic and Pegden-Smart (Proposition 2.5)
and the step `SplitTouchingStmt`. -/
theorem mainTheorem_etaMaxRadius_of_inputs (hLL : LawlerLimicHarmonicDifferenceStmt)
    (hT : PegdenSmartTouchingStmt) (hSplit : SplitTouchingStmt) : MainTheoremStmt :=
  mainTheorem_etaMaxRadius_of_remainingSteps
    (effectiveOperatorBasic_of_muConvergence muConvergence_unconditional) hT
    freeOdometerLimitRegular (muVanish_of_muConvergence muConvergence_unconditional hLL)
    (exteriorSupersolution_of_touching hT) exteriorSubsolution
    (interiorMaxPrinciple_of_muConvergence muConvergence_unconditional)
    (interiorMinPrinciple_of_muConvergence muConvergence_unconditional)
    (limitTraceInterior_of_touching hT) hSplit

/-- **Theorem 1.1** (`MainTheoremStmt`, with [C3] and [C12]) from the literature inputs Lawler-Limic
(Lawler-Limic), Pegden-Smart (Proposition 2.5) and Alexandrov only. -/
theorem mainTheorem_etaMaxRadius (hLL : LawlerLimicHarmonicDifferenceStmt)
    (hT : PegdenSmartTouchingStmt) (hAlex : AlexandrovStmt) : MainTheoremStmt :=
  mainTheorem_etaMaxRadius_of_inputs hLL hT (splitTouching_of_alexandrov hAlex)

/-- The corrected Theorem 1.1 implies its variant with the radius chosen after the law: take
`η_max = E.ηmax`. -/
theorem mainTheoremLawRadius_of_mainTheorem (h : MainTheoremStmt) : MainTheoremLawRadiusStmt := by
  intro d hd W hW E hHD
  obtain ⟨R, hR, hE⟩ := h d hd W hW E.ηmax
  exact ⟨R, hR, hE E rfl hHD⟩

end RandomSandpile

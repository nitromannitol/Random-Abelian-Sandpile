import RandomSandpile.Proofs.Sec9.OpenBoundaryVisc
import RandomSandpile.Proofs.Sec7.MainTheoremEnvLimit

/-!
# Theorem 9.1 (open boundary) from its steps

* `frontier_subset_closure_compl_closure`: every boundary point of a Lipschitz domain is a limit
  of points off `W̄` (move from `x₀ ∈ ∂W` in the direction `-e` of the local Lipschitz graph).
* `IsOpenOdoSubseqLimit.eq_zero_of_not_mem`: a continuous subsequential limit of the rescaled
  open odometers vanishes off `W` (the `v̄_n` vanish off `n⁻¹ W_n`; on `∂W` by continuity).
* `openBoundaryTheorem_of_steps`: `OpenBoundaryTheoremStmt` from Lemma 6.4(1), compactness,
  the viscosity properties, and the comparison principle: a continuous limit
  exists by compactness; it is a viscosity solution vanishing on `∂W`; solutions are unique on `W̄` by uniqueness;
  every subsequence has a further subsequence converging to it, so the whole sequence converges.
* `openBoundaryTheorem_of_remainingSteps`: the same with, (U) reduced to the interior
  principles, `MuVanishStmt`, the shift identity and the abstract comparison principle.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- Every boundary point of a Lipschitz domain is a limit of points off its closure. -/
theorem frontier_subset_closure_compl_closure {W : Set (Rd d)} (hW : IsLipschitzDomain W) :
    frontier W ⊆ closure (closure W)ᶜ := by
  intro x₀ hx₀
  obtain ⟨r, hr, e, he, L, γ, hγ, hloc⟩ := hW.2.2.2 x₀ hx₀
  have hx₀W : x₀ ∉ W := by
    rw [hW.2.1.frontier_eq] at hx₀; exact hx₀.2
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hγ0 : 0 ≤ γ 0 := by
    have h := hloc x₀ (Metric.mem_ball_self hr)
    simp only [sub_self, inner_zero_left, zero_smul] at h
    exact not_lt.1 fun h' => hx₀W (h.2 h')
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hm : 0 < min ε r := lt_min hε hr
  set s := min ε r / 2 with hs
  have hs0 : 0 < s := half_pos hm
  have hsε : s < ε := (half_lt_self hm).trans_le (min_le_left _ _)
  have hsr : 2 * s ≤ r := by rw [hs]; linarith [min_le_right ε r]
  refine ⟨x₀ - s • e, ?_, ?_⟩
  · set y := x₀ - s • e with hy
    set ρ := s / (2 * (L : ℝ) + 2) with hρ
    have hpos : (0 : ℝ) < 2 * L + 2 := by positivity
    have hρ0 : 0 < ρ := div_pos hs0 hpos
    have hρe : ρ * (2 * (L : ℝ) + 2) = s := by rw [hρ]; field_simp
    have hρs : (2 * (L : ℝ) + 1) * ρ < s := by nlinarith
    have hρs' : ρ ≤ s / 2 := by nlinarith
    intro hyc
    rw [Metric.mem_closure_iff] at hyc
    obtain ⟨z, hzW, hyz⟩ := hyc ρ hρ0
    have hzy : ‖z - y‖ < ρ := by rw [← dist_eq_norm, dist_comm]; exact hyz
    have hyx : ‖y - x₀‖ = s := by
      rw [hy, sub_sub_cancel_left, norm_neg, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_pos hs0]
    have hzx : z ∈ Metric.ball x₀ r := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖z - x₀‖ = ‖(z - y) + (y - x₀)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z - y‖ + ‖y - x₀‖ := norm_add_le _ _
        _ < r := by rw [hyx]; linarith
    have hmem := (hloc z hzx).1 hzW
    have hw : z - x₀ = (z - y) + (-s) • e := by rw [hy, neg_smul]; abel
    rw [hw, proj_add_smul he] at hmem
    rw [inner_add_left, inner_smul_left, hee] at hmem
    simp only [conj_trivial, mul_one] at hmem
    have hin : |inner ℝ (z - y) e| ≤ ‖z - y‖ := by
      have := abs_real_inner_le_norm (z - y) e
      rwa [he, mul_one] at this
    have hP : ‖(z - y) - inner ℝ (z - y) e • e‖ ≤ 2 * ‖z - y‖ := by
      calc ‖(z - y) - inner ℝ (z - y) e • e‖ ≤ ‖z - y‖ + ‖inner ℝ (z - y) e • e‖ :=
            norm_sub_le _ _
        _ = ‖z - y‖ + |inner ℝ (z - y) e| := by rw [norm_smul, he, mul_one, Real.norm_eq_abs]
        _ ≤ 2 * ‖z - y‖ := by linarith
    have hlip := hγ.dist_le_mul ((z - y) - inner ℝ (z - y) e • e) 0
    rw [Real.dist_eq, dist_zero_right] at hlip
    have h1 := (abs_le.1 hlip).1
    have h2 := (abs_le.1 hin).2
    have h3 := mul_le_mul_of_nonneg_left hP hL0
    have h4 : (2 * (L : ℝ) + 1) * ‖z - y‖ < (2 * (L : ℝ) + 1) * ρ :=
      mul_lt_mul_of_pos_left hzy (by positivity)
    nlinarith
  · rw [dist_eq_norm, sub_sub_cancel, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hs0]
    exact hsε

/-- The rescaled open odometer vanishes at `x` once `n⁻¹ [n x] ∉ W`. -/
theorem rescaleOdo_openOdometer_eq_zero {η : Site d → ℤ} {W : Set (Rd d)} {n : ℕ} (hn : n ≠ 0)
    {x : Rd d} (hx : (n : ℝ)⁻¹ • toE (latticeRound ((n : ℝ) • x)) ∉ W) :
    rescaleOdo (openOdometer η (discretize W n)) n x = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h : latticeRound ((n : ℝ) • x) ∉ discretize W n := fun h =>
    hx ((Set.mem_smul_set_iff_inv_smul_mem₀ hn' _ _).1 h)
  simp only [rescaleOdo, openOdometer_eq_zero_of_not_mem h, Int.cast_zero, zero_div]

/-- Subsequential limits of the rescaled open odometers vanish off `W̄`. -/
theorem IsOpenOdoSubseqLimit.eq_zero_of_not_mem_closure {η : Site d → ℤ} {W : Set (Rd d)}
    {v : Rd d → ℝ} (hv : IsOpenOdoSubseqLimit η W v) {x : Rd d} (hx : x ∉ closure W) :
    v x = 0 := by
  obtain ⟨nk, hnk, hconv⟩ := hv
  have hlim := hconv.tendsto_at x
  have hev : ∀ᶠ k in atTop,
      (nk k : ℝ)⁻¹ • toE (latticeRound ((nk k : ℝ) • x)) ∈ (closure W)ᶜ :=
    ((tendsto_inv_smul_latticeRound x).comp hnk.tendsto_atTop)
      (isClosed_closure.isOpen_compl.mem_nhds hx)
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  filter_upwards [hev, hnk.tendsto_atTop.eventually (eventually_ne_atTop 0)] with k hk hk0
  exact (rescaleOdo_openOdometer_eq_zero hk0 fun h => hk (subset_closure h)).symm

/-- Continuous subsequential limits of the rescaled open odometers vanish off `W`, in particular
on `∂W`. -/
theorem IsOpenOdoSubseqLimit.eq_zero_of_not_mem {η : Site d → ℤ} {W : Set (Rd d)}
    (hW : IsLipschitzDomain W) {v : Rd d → ℝ} (hv : IsOpenOdoSubseqLimit η W v)
    (hvc : Continuous v) {x : Rd d} (hx : x ∉ W) : v x = 0 := by
  by_cases hxc : x ∈ closure W
  · have hxf : x ∈ frontier W := by rw [hW.2.1.frontier_eq]; exact ⟨hxc, hx⟩
    have hsub : (closure W)ᶜ ⊆ {y | v y = 0} := fun y hy => hv.eq_zero_of_not_mem_closure hy
    exact closure_minimal hsub (isClosed_eq hvc continuous_const)
      (frontier_subset_closure_compl_closure hW hxf)
  · exact hv.eq_zero_of_not_mem_closure hxc

/-- **Theorem 9.1** (`OpenBoundaryTheoremStmt`) from Lemma 6.4(1), compactness, the viscosity
properties, of subsequential limits and the comparison principle. -/
theorem openBoundaryTheorem_of_steps (h64 : EffectiveOperatorBasicStmt)
    (hComp : OpenCompactnessStmt) (hSub : OpenLimitSubsolutionStmt)
    (hSup : OpenLimitSupersolutionStmt) (hCmp : EffComparisonStmt) : OpenBoundaryTheoremStmt := by
  intro d hd W hW E hHD
  have hDE : DegenerateElliptic (effOp E) := by
    obtain ⟨C, -, hC⟩ := h64 d hd E.ηmin E.ηmax
    intro X Y hX hY hXY
    exact (hC E rfl rfl X Y hX hY).1 hXY
  have hWo : IsOpen W := hW.2.1
  have hWb : Bornology.IsBounded W := hW.1
  have hfr : ∀ x ∈ frontier W, x ∉ W := fun x hx => by
    rw [hWo.frontier_eq] at hx; exact hx.2
  -- uniqueness of continuous solutions with zero boundary values
  have huniq : ∀ u w : Rd d → ℝ, Continuous u → Continuous w →
      ViscositySolution (effOp E) W u → ViscositySolution (effOp E) W w →
      (∀ x ∈ frontier W, u x = 0) → (∀ x ∈ frontier W, w x = 0) →
      Set.EqOn u w (closure W) := by
    intro u w hu hw hsu hsw hbu hbw x hx
    rw [viscositySolution_iff] at hsu hsw
    exact le_antisymm
      (hCmp d hd E hHD W hWo hWb u w hu.continuousOn hw.continuousOn hsu.1 hsw.2
        (fun y hy => by rw [hbu y hy, hbw y hy]) x hx)
      (hCmp d hd E hHD W hWo hWb w u hw.continuousOn hu.continuousOn hsw.1 hsu.2
        (fun y hy => by rw [hbu y hy, hbw y hy]) x hx)
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  have hG : ∀ᵐ η ∂E.P, (∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax) ∧
      ∀ v, IsOpenOdoSubseqLimit η W v → ViscositySolution (effOp E) W v := by
    filter_upwards [hbdd, hSub d hd E hHD W hW, hSup d hd E hHD W hW] with η h1 h2 h3
    exact ⟨h1, fun v hv => (viscositySolution_iff _ _ _).2 ⟨h2 v hv, h3 v hv⟩⟩
  obtain ⟨η₀, hη₀b, hη₀V⟩ := hG.exists
  obtain ⟨φ, hφ, vbar, hvc, hvconv⟩ :=
    hComp d hd W hW E.ηmin E.ηmax η₀ hη₀b id strictMono_id
  have hvbar : IsOpenOdoSubseqLimit η₀ W vbar := ⟨φ, hφ, hvconv⟩
  have hvsol := hη₀V vbar hvbar
  have hvb : ∀ x ∈ frontier W, vbar x = 0 := fun x hx =>
    hvbar.eq_zero_of_not_mem hW hvc (hfr x hx)
  -- every continuous subsequential limit of a good `η` is `vbar`
  have hlim : ∀ η : Site d → ℤ,
      (∀ v, IsOpenOdoSubseqLimit η W v → ViscositySolution (effOp E) W v) →
      ∀ v, Continuous v → IsOpenOdoSubseqLimit η W v → v = vbar := by
    intro η hηV v hvc' hv
    funext x
    by_cases hx : x ∈ closure W
    · exact huniq v vbar hvc' hvc (hηV v hv) hvsol
        (fun y hy => hv.eq_zero_of_not_mem hW hvc' (hfr y hy)) hvb hx
    · rw [hv.eq_zero_of_not_mem_closure hx, hvbar.eq_zero_of_not_mem_closure hx]
  refine ⟨hDE, vbar, hvc, hvsol, hvb,
    fun w hwc hws hwb => huniq w vbar hwc hvc hws hvsol hwb hvb, ?_⟩
  filter_upwards [hG] with η hη
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨nk, hnk, hbad⟩ := extraction_of_frequently_atTop hcon
  obtain ⟨ψ, hψ, v', hv'c, hv'⟩ := hComp d hd W hW E.ηmin E.ηmax η hη.1 nk hnk
  have hv'eq : v' = vbar := hlim η hη.2 v' hv'c ⟨nk ∘ ψ, hnk.comp hψ, hv'⟩
  rw [hv'eq, Metric.tendstoUniformly_iff] at hv'
  obtain ⟨j, hj⟩ := (hv' ε hε).exists
  exact hbad (ψ j) hj

/-- **Theorem 9.1** from the finest steps: Lemma 6.4(1), compactness, the open-boundary
interior maximum and minimum principles, `MuVanishStmt`, the shift identity and
the Crandall-Ishii-Lions comparison principle. -/
theorem openBoundaryTheorem_of_remainingSteps (h64 : EffectiveOperatorBasicStmt)
    (hComp : OpenCompactnessStmt) (hVan : MuVanishStmt) (hMax : OpenInteriorMaxPrincipleStmt)
    (hMin : OpenInteriorMinPrincipleStmt) (hShift : EffShiftStmt)
    (hCIL : ShiftComparisonStmt) : OpenBoundaryTheoremStmt :=
  openBoundaryTheorem_of_steps h64 hComp (openLimitSubsolution_of_steps h64 hVan hMax)
    (openLimitSupersolution_of_steps h64 hVan hMin) (effComparison_of_shift h64 hShift hCIL)

end RandomSandpile

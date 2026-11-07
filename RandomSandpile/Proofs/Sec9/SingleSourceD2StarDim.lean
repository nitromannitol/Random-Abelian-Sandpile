import RandomSandpile.Proofs.Sec9.SingleSourceFstarDilation

/-!
# Theorem 9.2, `F*`-variant, at one dimension

The starred reduction of (`Proofs/Sec9/SingleSourceFstarDilation.lean`,
`Proofs/Sec9/SingleSourceFlatness.lean`) takes the subsolution step `SSLimitSubStarStmt` in
every dimension `d ≥ 2`. The proofs use it only at the dimension and environment at hand, so they
are restated here for one environment `E` (the proofs are those of r4, with the hypotheses at `E`):

* `ssLimitMinimalStar_at`: the minimality step at `E`, from subsolution at `E`
  (copy of `SingleSourceFstar.ssLimitMinimalStar_of_sub`);
* `singleSourceTheoremStar_at`: the starred theorem at `E`, from compactness, and minimality at `E`
  (copy of `singleSourceTheoremStar_of_steps`).

In dimension two: the statements `SSLimitSubStarD2Stmt` and `SingleSourceTheoremStarD2Stmt` (the
`d = 2` instances of `SSLimitSubStarStmt` and `SingleSourceTheoremStarStmt`) and
`singleSourceTheoremStarD2_of_sub : → →_{d=2} → CIL → SingleSourceTheoremStarD2Stmt`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric

namespace RandomSandpile

open EffectiveOperatorBasic

namespace SingleSourceD2

open SingleSourceFstar

/-! ### Dimension two statements -/

/-- **(S*) in dimension two**: almost surely every subsequential limit `u` of the rescaled
single-source odometers is a viscosity subsolution of `F*(D²u) ≤ 0` on `{u > 0} ∖ {0}` (the
`d = 2` instance of `SSLimitSubStarStmt`). -/
def SSLimitSubStarD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    ∀ᵐ η ∂E.P, ∀ u : Rd 2 → ℝ, IsSSSubseqLimit η u →
      ViscFromAboveLE (effOpStar E) {x : Rd 2 | x ≠ 0 ∧ 0 < u x} u

/-- **Theorem 9.2, `F*`-variant, in dimension two** (the `d = 2` instance of
`SingleSourceTheoremStarStmt`). -/
def SingleSourceTheoremStarD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    IsLeast (singleSourceObstacleSetStar E) (singleSourceObstacleSolutionStar E) ∧
    ∀ᵐ η ∂E.P,
      (∀ n : ℕ, (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty) ∧
        TendstoLocallyUniformlyOn
          (fun n : ℕ => rescaleSingleSource (singleSourceOdometer η n) n)
          (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x) atTop
          {x : Rd 2 | x ≠ 0}

theorem ssLimitSubStarD2_of_all (hS : SSLimitSubStarStmt) : SSLimitSubStarD2Stmt :=
  fun E hE => hS 2 le_rfl E hE

theorem singleSourceTheoremStarD2_of_all (h : SingleSourceTheoremStarStmt) :
    SingleSourceTheoremStarD2Stmt :=
  fun E hE => h 2 le_rfl E hE

/-! ### The starred reduction at one environment -/

variable {d : ℕ}

/-- **Step at one environment** from subsolution at that environment, the support of the limits and
the comparison principle (the proof of `SingleSourceFstar.ssLimitMinimalStar_of_sub`). -/
theorem ssLimitMinimalStar_at (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hmax : E.ηmax = 2 * (d : ℤ) - 2)
    (hS : ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
      ViscFromAboveLE (effOpStar E) {x : Rd d | x ≠ 0 ∧ 0 < u x} u)
    (hB : SSLimitSupportStmt) (hCIL : ShiftComparisonStmt) :
    ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, Continuous v →
      IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
        ∀ w ∈ singleSourceObstacleSetStar E, ∀ x, v x ≤ w x := by
  have hd1 : 1 ≤ d := by omega
  have hE : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hmax]; omega
  filter_upwards [hS, hB d hd E hmax] with η hSη hBη
  intro v hvc hv w hw
  set U : Rd d → ℝ := fun x => v x + fundamentalSolution d x with hU
  have hwc : Continuous w := hw.1
  have hwG : ∀ x, x ≠ 0 → -fundamentalSolution d x ≤ w x := hw.2.1
  have hWsup : ViscFromBelowGE (effOpStar E) {x | x ≠ 0}
      (fun x => w x + fundamentalSolution d x) :=
    (viscFromBelowMuStar_iff hd1 E hE _ _).1 hw.2.2
  have hGc : ContinuousOn (fundamentalSolution d) {x : Rd d | x ≠ 0} :=
    SingleSourceMin.continuousOn_fundamentalSolution d
  have hopen : IsOpen {x : Rd d | x ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hUc : ContinuousOn U {x : Rd d | x ≠ 0} := hvc.continuousOn.add hGc
  obtain ⟨R₀, hR₀⟩ := hBη U hv
  -- the dilated comparison: `U ≤ W_t` off the origin, `t > 1`
  have hdil : ∀ t : ℝ, 1 < t → ∀ x : Rd d, x ≠ 0 →
      U x ≤ t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x)) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    set Wt : Rd d → ℝ := fun x => t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x))
      with hWt
    have hWt0 : ∀ x : Rd d, x ≠ 0 → 0 ≤ Wt x := fun x hx => by
      have h := hwG (t⁻¹ • x) (smul_ne_zero (inv_ne_zero ht0.ne') hx)
      show 0 ≤ t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x))
      exact mul_nonneg (sq_nonneg t) (by linarith)
    -- near the origin `W_t ≥ U`
    obtain ⟨ρ, hρ, hnear⟩ : ∃ ρ > 0, ∀ x : Rd d, x ≠ 0 → ‖x‖ ≤ ρ → U x ≤ Wt x := by
      obtain ⟨Mv, hMv⟩ :=
        (isCompact_closedBall (0 : Rd d) 1).exists_bound_of_continuousOn hvc.continuousOn
      obtain ⟨Mw, hMw⟩ :=
        (isCompact_closedBall (0 : Rd d) 1).exists_bound_of_continuousOn hwc.continuousOn
      have htd : 0 < t ^ d - 1 := by
        have := one_lt_pow₀ ht (by omega : d ≠ 0)
        linarith
      obtain ⟨ρ₁, hρ₁, hGl⟩ := fundamentalSolution_large hd ((t ^ 2 * Mw + Mv) / (t ^ d - 1))
      refine ⟨min ρ₁ 1, lt_min hρ₁ one_pos, fun x hx hxρ => ?_⟩
      have hx1 : ‖x‖ ≤ 1 := hxρ.trans (min_le_right _ _)
      have hxt : t⁻¹ • x ∈ closedBall (0 : Rd d) 1 := by
        rw [mem_closedBall, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]
        calc t⁻¹ * ‖x‖ ≤ 1 * 1 :=
              mul_le_mul (inv_le_one_of_one_le₀ ht.le) hx1 (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hv1 := hMv x (by rw [mem_closedBall, dist_zero_right]; exact hx1)
      have hw1 := hMw _ hxt
      rw [Real.norm_eq_abs] at hv1 hw1
      have hGx := (div_le_iff₀ htd).1 (hGl x hx (hxρ.trans (min_le_left _ _)))
      have hscale := pow_mul_fundamentalSolution_le ht.le hx
      have h3 : t ^ 2 * (-Mw) ≤ t ^ 2 * w (t⁻¹ • x) :=
        mul_le_mul_of_nonneg_left (abs_le.1 hw1).1 (sq_nonneg t)
      have h4 := (abs_le.1 hv1).2
      have e1 : fundamentalSolution d x * (t ^ d - 1) =
          t ^ d * fundamentalSolution d x - fundamentalSolution d x := by ring
      have e2 : t ^ 2 * (-Mw) = -(t ^ 2 * Mw) := by ring
      rw [e1] at hGx
      rw [e2] at h3
      show v x + fundamentalSolution d x ≤
        t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x))
      rw [mul_add]
      linarith
    -- the comparison domain `D = {U > 0} ∩ (B_{R'} ∖ B̄_ρ)`
    set R' : ℝ := max R₀ ρ + 1 with hR'
    set D : Set (Rd d) := {x | x ≠ 0 ∧ 0 < U x} ∩ (ball 0 R' ∩ (closedBall 0 ρ)ᶜ) with hD
    have hDo : IsOpen D := by
      refine IsOpen.inter ?_ (isOpen_ball.inter isClosed_closedBall.isOpen_compl)
      exact hUc.isOpen_inter_preimage hopen isOpen_Ioi
    have hDb : Bornology.IsBounded D := isBounded_ball.subset fun x hx => hx.2.1
    have hcl : closure D ⊆ {x | ρ ≤ ‖x‖} := by
      refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const continuous_norm)
      have h := hx.2.2
      simp only [Set.mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at h
      exact h.le
    have hcl0 : ∀ x ∈ closure D, x ≠ 0 := fun x hx h => by
      have h' : ρ ≤ ‖x‖ := hcl hx
      rw [h, norm_zero] at h'
      linarith
    have hWtc : ContinuousOn Wt (closure D) := by
      have hsm : Continuous (fun x : Rd d => t⁻¹ • x) := continuous_const_smul _
      refine continuousOn_const.mul ((hwc.comp hsm).continuousOn.add ?_)
      exact hGc.comp hsm.continuousOn
        (fun x hx => smul_ne_zero (inv_ne_zero ht0.ne') (hcl0 x hx))
    have hUcl : ContinuousOn U (closure D) := hUc.mono fun x hx => hcl0 x hx
    have hsub : ViscFromAboveLE (effOpStar E) D U := fun x hx φ hφ hloc =>
      hSη U hv x hx.1 φ hφ hloc
    have hsup : ViscFromBelowGE (effOpStar E) D Wt := fun x hx =>
      viscFromBelowGE_dilate hd1 E hE hWsup ht0 x hx.1.1
    -- off `D` (and off the origin) `U ≤ W_t`
    have hout : ∀ x : Rd d, x ≠ 0 → x ∉ D → U x ≤ Wt x := by
      intro x hx hxD
      by_cases h1 : ‖x‖ ≤ ρ
      · exact hnear x hx h1
      by_cases h2 : R' ≤ ‖x‖
      · have hlt : R₀ < ‖x‖ := by
          have := le_max_left R₀ ρ
          linarith
        rw [hR₀ x hlt]
        exact hWt0 x hx
      · have hU0 : ¬ 0 < U x := fun h => hxD ⟨⟨hx, h⟩,
          by simpa [mem_ball, dist_zero_right, not_le] using h2,
          by simpa [mem_closedBall, dist_zero_right] using h1⟩
        exact (not_lt.1 hU0).trans (hWt0 x hx)
    have hbd : ∀ x ∈ frontier D, U x ≤ Wt x := fun x hx =>
      hout x (hcl0 x (frontier_subset_closure hx)) fun h => (hDo.frontier_eq ▸ hx).2 h
    have hcmp := hCIL d hd1 (effOpStar E) (degenerateElliptic_effOpStar hd1 E hE)
      (fun M hM s => effOpStar_add_smul_one hd1 E hE hM s) D hDo hDb U Wt hUcl hWtc hsub
      hsup hbd
    intro x hx
    by_cases hxD : x ∈ D
    · exact hcmp x (subset_closure hxD)
    · exact hout x hx hxD
  -- `t ↓ 1`: `v ≤ w` off the origin
  have hoff : ∀ x : Rd d, x ≠ 0 → v x ≤ w x := by
    intro x hx
    have hc : ContinuousAt
        (fun t : ℝ => t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x))) 1 := by
      have h1 : ContinuousAt (fun t : ℝ => t⁻¹ • x) 1 :=
        (continuousAt_inv₀ one_ne_zero).smul continuousAt_const
      have h2 : ContinuousAt (fundamentalSolution d) x := hGc.continuousAt (hopen.mem_nhds hx)
      exact (continuousAt_id.pow 2).mul
        ((hwc.continuousAt.comp h1).add (h2.comp_of_eq h1 (by simp)))
    have hlim : Tendsto (fun t : ℝ => t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x)))
        (𝓝[>] 1) (𝓝 (w x + fundamentalSolution d x)) := by
      have h := hc.tendsto
      simp only [one_pow, inv_one, one_smul, one_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    have hev : ∀ᶠ t in 𝓝[>] (1 : ℝ),
        U x ≤ t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x)) :=
      eventually_nhdsWithin_of_forall fun t ht => hdil t ht x hx
    have h := ge_of_tendsto hlim hev
    have h' : v x + fundamentalSolution d x ≤ w x + fundamentalSolution d x := h
    linarith
  -- the origin, by continuity
  intro x
  by_cases hx : x = 0
  · subst hx
    obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    have he : EuclideanSpace.single i (1 : ℝ) ≠ 0 := fun h => by
      simpa using congrArg (fun z : Rd d => z i) h
    have hlim : Tendsto (fun s : ℝ => s • EuclideanSpace.single i (1 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ => s • EuclideanSpace.single i (1 : ℝ)) (𝓝 0)
          (𝓝 ((0 : ℝ) • EuclideanSpace.single i (1 : ℝ))) :=
        (continuous_id.smul continuous_const).tendsto (0 : ℝ)
      rw [zero_smul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    refine le_of_tendsto_of_tendsto ((hvc.tendsto 0).comp hlim) ((hwc.tendsto 0).comp hlim) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hoff _ (smul_ne_zero (ne_of_gt hs) he)
  · exact hoff x hx

/-- **Theorem 9.2, `F*`-variant, at one environment** from compactness, and minimality at that
environment (the proof of `singleSourceTheoremStar_of_steps`). -/
theorem singleSourceTheoremStar_at (hComp : SSCompactnessStmt) (hSup : SSLimitSuperStarStmt)
    (hd : 2 ≤ d) (E : RandomEnvironment d) (hmax : E.ηmax = 2 * (d : ℤ) - 2)
    (hMin : ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, Continuous v →
      IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
        ∀ w ∈ singleSourceObstacleSetStar E, ∀ x, v x ≤ w x) :
    IsLeast (singleSourceObstacleSetStar E) (singleSourceObstacleSolutionStar E) ∧
    ∀ᵐ η ∂E.P,
      (∀ n : ℕ, (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty) ∧
        TendstoLocallyUniformlyOn
          (fun n : ℕ => rescaleSingleSource (singleSourceOdometer η n) n)
          (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution d x) atTop
          {x : Rd d | x ≠ 0} := by
  have hd1 : 1 ≤ d := by omega
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  have hG : ∀ᵐ η ∂E.P, (∀ x, E.ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2) ∧
      (∀ u, IsSSSubseqLimit η u → ViscFromBelowMuStar E {x : Rd d | x ≠ 0} u) ∧
      (∀ v : Rd d → ℝ, Continuous v →
        IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
          ∀ w ∈ singleSourceObstacleSetStar E, ∀ x, v x ≤ w x) := by
    filter_upwards [hbdd, hSup d hd E hmax, hMin] with η h1 h2 h3
    exact ⟨fun x => ⟨(h1 x).1, hmax ▸ (h1 x).2⟩, h2, h3⟩
  have hmem : ∀ η : Site d → ℤ,
      (∀ u, IsSSSubseqLimit η u → ViscFromBelowMuStar E {x : Rd d | x ≠ 0} u) →
      ∀ v : Rd d → ℝ, Continuous v →
        IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
          v ∈ singleSourceObstacleSetStar E := fun η hηV v hvc hv =>
    ⟨hvc, fun x hx => by have := hv.nonneg hx; linarith, hηV _ hv⟩
  obtain ⟨η₀, hη₀b, hη₀V, hη₀M⟩ := hG.exists
  obtain ⟨φ, hφ, v₀, hv₀c, hv₀⟩ := hComp d hd E.ηmin η₀ hη₀b id strictMono_id
  have hv₀L : IsSSSubseqLimit η₀ (fun x => v₀ x + fundamentalSolution d x) := ⟨φ, hφ, hv₀⟩
  have hLeast : IsLeast (singleSourceObstacleSetStar E) v₀ :=
    ⟨hmem η₀ hη₀V v₀ hv₀c hv₀L, fun w hw x => hη₀M v₀ hv₀c hv₀L w hw x⟩
  rw [singleSourceObstacleSolutionStar_eq_of_isLeast hLeast]
  refine ⟨hLeast, ?_⟩
  filter_upwards [hG] with η hη
  refine ⟨ssNonempty d hd1 η (fun x => (hη.1 x).2), ?_⟩
  refine tendstoLocallyUniformlyOn_of_subseq isOpen_ne fun nk hnk => ?_
  obtain ⟨ψ, hψ, v', hv'c, hv'⟩ := hComp d hd E.ηmin η hη.1 nk hnk
  have hv'L : IsSSSubseqLimit η (fun x => v' x + fundamentalSolution d x) :=
    ⟨nk ∘ ψ, hnk.comp hψ, hv'⟩
  have heq : v' = v₀ := funext fun x =>
    le_antisymm (hη.2.2 v' hv'c hv'L v₀ hLeast.1 x) (hLeast.2 (hmem η hη.2.1 v' hv'c hv'L) x)
  rw [heq] at hv'
  exact ⟨ψ, hψ, hv'⟩

/-! ### Dimension two -/

/-- **Theorem 9.2, `F*`-variant, in dimension two** from compactness, the outer bound, in
dimension two and the comparison principle. -/
theorem singleSourceTheoremStarD2_of_sub (hComp : SSCompactnessStmt) (hOB : SSOuterBoundStmt)
    (hS : SSLimitSubStarD2Stmt) (hCIL : ShiftComparisonStmt) : SingleSourceTheoremStarD2Stmt :=
  fun E hE => singleSourceTheoremStar_at hComp
    (ssLimitSuperStar_of_minPrinciple
      (ssInteriorMinPrinciple_of_compactness muConvergence_unconditional hComp)) le_rfl E hE
    (ssLimitMinimalStar_at le_rfl E hE (hS E hE) (ssLimitSupport_of_outerBound hOB) hCIL)

end SingleSourceD2

end RandomSandpile

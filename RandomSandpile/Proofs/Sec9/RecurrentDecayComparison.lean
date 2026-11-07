import RandomSandpile.Proofs.Sec9.RecurrentLimitDecay
import RandomSandpile.Proofs.Sec9.RecurrentOperatorBasic
import RandomSandpile.Proofs.Sec9.SingleSourceLimitMinimal

/-! # Punctured-domain comparison under vanishing tails

The dilation argument below is adapted from `SingleSourceLimitMinimal.lean`, replacing
compact support by decay at infinity.
-/

noncomputable section
open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric
namespace RandomSandpile
open SingleSourceLimitMinimal
variable {d : ℕ}

theorem scaled_comparison_of_decay (hd : 2 ≤ d) {F : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hDE : DegenerateElliptic F)
    (hshift : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ t : ℝ,
      F (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) = F M - d * t)
    (hCIL : ShiftComparisonStmt) {v w : Rd d → ℝ} (hvc : Continuous v) (hwc : Continuous w)
    (hsub : ViscFromAboveLE F {x | x ≠ 0 ∧ 0 < v x + fundamentalSolution d x}
      (fun x => v x + fundamentalSolution d x))
    (hR : VanishesAboveAtInfinity (fun x : Rd d => v x + fundamentalSolution d x))
    (hwG : ∀ x : Rd d, x ≠ 0 → -fundamentalSolution d x ≤ w x)
    (hsup : ViscFromBelowGE F {x | x ≠ 0} (fun x => w x + fundamentalSolution d x))
    {s : ℝ} (hs : 1 < s) :
    ∀ x : Rd d, x ≠ 0 → v x + fundamentalSolution d x ≤
      s ^ 2 * (w (s⁻¹ • x) + fundamentalSolution d (s⁻¹ • x)) := by
  have hs0 : 0 < s := by linarith
  have hs2 : 1 < s ^ 2 := by nlinarith
  have hsx : ∀ y : Rd d, y ≠ 0 → s⁻¹ • y ≠ 0 := fun y hy =>
    smul_ne_zero (inv_ne_zero hs0.ne') hy
  have hnorm : ∀ y : Rd d, ‖s⁻¹ • y‖ ≤ ‖y‖ := fun y => by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0, inv_mul_eq_div]
    exact div_le_self (norm_nonneg _) hs.le
  have hGc : ContinuousOn (fundamentalSolution d) {y : Rd d | y ≠ 0} :=
    SingleSourceMin.continuousOn_fundamentalSolution d
  have hWc : ContinuousOn
      (fun y : Rd d => s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)))
      {y : Rd d | y ≠ 0} := by
    have hsm : Continuous (fun y : Rd d => s⁻¹ • y) := continuous_const_smul _
    refine continuousOn_const.mul (((hwc.comp hsm).continuousOn).add ?_)
    exact hGc.comp hsm.continuousOn fun y hy => hsx y hy
  have hUc : ContinuousOn (fun y : Rd d => v y + fundamentalSolution d y) {y : Rd d | y ≠ 0} :=
    hvc.continuousOn.add hGc
  have hW0 : ∀ y : Rd d, y ≠ 0 →
      0 ≤ s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)) := fun y hy => by
    have h1 := hwG _ (hsx y hy)
    have h2 : 0 ≤ w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y) := by linarith
    exact mul_nonneg (by positivity) h2
  -- bounds for `v` and `w` on the unit ball
  obtain ⟨Av, hAv⟩ := (isCompact_closedBall (0 : Rd d) 1).exists_bound_of_continuousOn
    hvc.continuousOn
  obtain ⟨Aw, hAw⟩ := (isCompact_closedBall (0 : Rd d) 1).exists_bound_of_continuousOn
    hwc.continuousOn
  have hvA : ∀ y : Rd d, ‖y‖ < 1 → v y ≤ max Av Aw := fun y hy => by
    have h := hAv y (by rw [mem_closedBall, dist_zero_right]; exact hy.le)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_max_left _ _))
  have hwA : ∀ y : Rd d, ‖y‖ < 1 → -max Av Aw ≤ w y := fun y hy => by
    have h := hAw y (by rw [mem_closedBall, dist_zero_right]; exact hy.le)
    rw [Real.norm_eq_abs] at h
    have := neg_abs_le (w y)
    linarith [le_max_right Av Aw]
  -- near the origin `v + G - W_s ≤ 0`
  obtain ⟨ρ, hρ, hρG⟩ := exists_le_fundamentalSolution hd
    ((max Av Aw + s ^ 2 * max Av Aw) / (s ^ 2 - 1))
  have hρ1 : 0 < min ρ 1 := lt_min hρ one_pos
  have hnear : ∀ y : Rd d, y ≠ 0 → ‖y‖ < min ρ 1 →
      v y + fundamentalSolution d y -
        s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)) ≤ 0 := by
    intro y hy hyρ
    have hy1 : ‖y‖ < 1 := lt_of_lt_of_le hyρ (min_le_right _ _)
    have hyρ' : ‖y‖ < ρ := lt_of_lt_of_le hyρ (min_le_left _ _)
    have h1 := hvA y hy1
    have h2 := hwA (s⁻¹ • y) (lt_of_le_of_lt (hnorm y) hy1)
    have h3 : fundamentalSolution d y ≤ fundamentalSolution d (s⁻¹ • y) :=
      fundamentalSolution_le_of_norm_le hd (hsx y hy) (hnorm y)
    have h4 := hρG y hy hyρ'
    have hne : s ^ 2 - 1 ≠ 0 := by linarith
    have h5 : (s ^ 2 - 1) * ((max Av Aw + s ^ 2 * max Av Aw) / (s ^ 2 - 1)) =
        max Av Aw + s ^ 2 * max Av Aw := by
      rw [mul_div_assoc']
      exact mul_div_cancel_left₀ _ hne
    have p1 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ s ^ 2)
    have p2 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ s ^ 2)
    have p3 := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ s ^ 2 - 1)
    linarith
  intro x₁ hx₁
  by_contra hlt
  have hlt' := not_le.1 hlt
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = (v x₁ + fundamentalSolution d x₁ -
      s ^ 2 * (w (s⁻¹ • x₁) + fundamentalSolution d (s⁻¹ • x₁))) / 2 := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hm_def]; linarith
  obtain ⟨R, hR⟩ := hR (m / 2) (by linarith)
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = max R 0 + 1 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Set (Rd d), D = ({y : Rd d | y ≠ 0} ∩
      (fun y => v y + fundamentalSolution d y -
        s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y))) ⁻¹' Set.Ioi m) ∩
      ball 0 R' := ⟨_, rfl⟩
  have hDo : IsOpen D := by
    rw [hD]
    exact ((hUc.sub hWc).isOpen_inter_preimage isOpen_ne isOpen_Ioi).inter isOpen_ball
  have hDb : Bornology.IsBounded D := by
    rw [hD]
    exact isBounded_ball.subset Set.inter_subset_right
  -- points of `D` stay away from the origin
  have hDρ : D ⊆ {y : Rd d | min ρ 1 ≤ ‖y‖} := by
    rw [hD]
    rintro y ⟨⟨hy0, hym⟩, -⟩
    show min ρ 1 ≤ ‖y‖
    by_contra hy
    have := hnear y hy0 (not_le.1 hy)
    simp only [Set.mem_preimage, Set.mem_Ioi] at hym
    linarith
  have hcl : closure D ⊆ {y : Rd d | min ρ 1 ≤ ‖y‖} ∩
      (fun y => v y + fundamentalSolution d y -
        s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y))) ⁻¹' Set.Ici m := by
    refine closure_minimal (fun y hy => ⟨hDρ hy, ?_⟩) ?_
    · rw [hD] at hy
      have h' : m < v y + fundamentalSolution d y -
          s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)) := hy.1.2
      exact h'.le
    · have hK : IsClosed {y : Rd d | min ρ 1 ≤ ‖y‖} :=
        isClosed_le continuous_const continuous_norm
      exact ((hUc.sub hWc).mono fun y hy => norm_pos_iff.1 (lt_of_lt_of_le hρ1 hy)
        ).preimage_isClosed_of_isClosed hK isClosed_Ici
  have hcl0 : ∀ y ∈ closure D, y ≠ 0 := fun y hy =>
    norm_pos_iff.1 (lt_of_lt_of_le hρ1 (hcl hy).1)
  have hsubD : ViscFromAboveLE F D (fun y => v y + fundamentalSolution d y) := by
    intro y hy φ hφ hloc
    refine hsub y ⟨hcl0 y (subset_closure hy), ?_⟩ φ hφ hloc
    have hy' := hy
    rw [hD] at hy'
    have h1 : m < v y + fundamentalSolution d y -
        s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)) := hy'.1.2
    have h2 := hW0 y (hcl0 y (subset_closure hy))
    linarith
  have hsupD : ViscFromBelowGE F D
      (fun y => s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)) + m) :=
    viscFromBelowGE_add_const_mono (viscFromBelowGE_rescale hsup hs0)
      (fun y hy => hcl0 y (subset_closure hy)) m
  have hbd : ∀ y ∈ frontier D, (fun y => v y + fundamentalSolution d y) y ≤
      (fun y => s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)) + m) y := by
    intro y hy
    have hycl : y ∈ closure D := frontier_subset_closure hy
    have hyD : y ∉ D := fun h => (hDo.frontier_eq ▸ hy).2 h
    have hy0 := hcl0 y hycl
    show v y + fundamentalSolution d y ≤
      s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)) + m
    by_cases hyb : y ∈ ball (0 : Rd d) R'
    · have hn : ¬ m < v y + fundamentalSolution d y -
          s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)) := fun h =>
        hyD (by rw [hD]; exact ⟨⟨hy0, h⟩, hyb⟩)
      linarith [not_lt.1 hn]
    · have hyR : R < ‖y‖ := by
        rw [mem_ball, dist_zero_right, not_lt] at hyb
        have : R ≤ max R 0 := le_max_left _ _
        linarith
      have hu0 := hR y hyR.le
      have := hW0 y hy0
      linarith
  have hcmp := hCIL d (by omega) F hDE hshift D hDo hDb
    (fun y => v y + fundamentalSolution d y)
    (fun y => s ^ 2 * (w (s⁻¹ • y) + fundamentalSolution d (s⁻¹ • y)) + m)
    (hUc.mono fun y hy => hcl0 y hy) ((hWc.add continuousOn_const).mono fun y hy => hcl0 y hy)
    hsubD hsupD hbd
  have hx₁D : x₁ ∈ D := by
    rw [hD]
    refine ⟨⟨hx₁, ?_⟩, ?_⟩
    · show m < v x₁ + fundamentalSolution d x₁ -
        s ^ 2 * (w (s⁻¹ • x₁) + fundamentalSolution d (s⁻¹ • x₁))
      rw [hm_def]; linarith
    · rw [mem_ball, dist_zero_right]
      by_contra hge
      have hxR : R < ‖x₁‖ := by
        have : R ≤ max R 0 := le_max_left _ _
        linarith [not_lt.1 hge]
      have hu0 := hR x₁ hxR.le
      have := hW0 x₁ hx₁
      linarith
  have key : v x₁ + fundamentalSolution d x₁ ≤
      s ^ 2 * (w (s⁻¹ • x₁) + fundamentalSolution d (s⁻¹ • x₁)) + m :=
    hcmp x₁ (subset_closure hx₁D)
  rw [hm_def] at key
  linarith

/-- **Deterministic core of step.** Under the hypotheses of `scaled_comparison`, `v ≤ w`
everywhere: let `s ↓ 1` off the origin, then use continuity at the origin. -/
theorem le_of_scaled_comparison_of_decay (hd : 2 ≤ d) {F : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hDE : DegenerateElliptic F)
    (hshift : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ t : ℝ,
      F (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) = F M - d * t)
    (hCIL : ShiftComparisonStmt) {v w : Rd d → ℝ} (hvc : Continuous v) (hwc : Continuous w)
    (hsub : ViscFromAboveLE F {x | x ≠ 0 ∧ 0 < v x + fundamentalSolution d x}
      (fun x => v x + fundamentalSolution d x))
    (hR : VanishesAboveAtInfinity (fun x : Rd d => v x + fundamentalSolution d x))
    (hwG : ∀ x : Rd d, x ≠ 0 → -fundamentalSolution d x ≤ w x)
    (hsup : ViscFromBelowGE F {x | x ≠ 0} (fun x => w x + fundamentalSolution d x)) :
    ∀ x, v x ≤ w x := by
  have hstep : ∀ x : Rd d, x ≠ 0 → v x ≤ w x := by
    intro x hx
    have hGx : ContinuousAt (fundamentalSolution d) x :=
      (SingleSourceMin.continuousOn_fundamentalSolution d).continuousAt (isOpen_ne.mem_nhds hx)
    have hinv : ContinuousAt (fun t : ℝ => t⁻¹ • x) 1 :=
      (continuousAt_inv₀ one_ne_zero).smul continuousAt_const
    have hG1 : ContinuousAt (fun t : ℝ => fundamentalSolution d (t⁻¹ • x)) 1 :=
      ContinuousAt.comp_of_eq hGx hinv (by simp)
    have hcont : ContinuousAt
        (fun t : ℝ => t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x))) 1 :=
      (continuousAt_id.pow 2).mul ((hwc.continuousAt.comp hinv).add hG1)
    have hlim : Tendsto (fun t : ℝ => t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x)))
        (𝓝[>] 1) (𝓝 (w x + fundamentalSolution d x)) := by
      have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using h
    have hle : ∀ᶠ t in 𝓝[>] (1 : ℝ), v x + fundamentalSolution d x ≤
        t ^ 2 * (w (t⁻¹ • x) + fundamentalSolution d (t⁻¹ • x)) :=
      eventually_nhdsWithin_of_forall fun t ht =>
        scaled_comparison_of_decay hd hDE hshift hCIL hvc hwc hsub hR hwG hsup ht x hx
    have := ge_of_tendsto hlim hle
    linarith
  intro x
  by_cases hx : x = 0
  · subst hx
    by_contra hlt
    have hlt' := not_le.1 hlt
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt hwc hvc) 0 hlt'
    obtain ⟨e, he⟩ : ∃ e : Rd d, ‖e‖ = 1 :=
      ⟨EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ),
        by simp⟩
    have hε2 : 0 < ε / 2 := by linarith
    have hnrm : ‖(ε / 2) • e‖ = ε / 2 := by
      rw [norm_smul, he, Real.norm_eq_abs, abs_of_pos hε2, mul_one]
    have hy : (ε / 2) • e ∈ ball (0 : Rd d) ε := by
      rw [mem_ball, dist_zero_right, hnrm]
      linarith
    have hy0 : (ε / 2) • e ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnrm
      linarith
    exact absurd (hstep _ hy0) (not_le.2 (hball hy))
  · exact hstep x hx

/-- Recurrent punctured-domain comparison follows from viscosity comparison. -/
theorem recurrentSSComparison_of_shiftComparison (hCIL : ShiftComparisonStmt) :
    RecurrentSSComparisonStmt := by
  intro d hd E v hvc hvpos hsub hdecay w hw x
  apply le_of_scaled_comparison_of_decay hd (recurrent_degenerateElliptic hd E)
    (fun M _ t => effOpRecurrent_shift hd E M t) hCIL hvc hw.1 hsub hdecay
    (fun y hy => by linarith [hw.2.1 y hy]) hw.2.2 x

/-- Recurrent punctured-domain comparison from Alexandrov's theorem. -/
theorem recurrentSSComparison_of_alexandrov (hA : AlexandrovStmt) :
    RecurrentSSComparisonStmt :=
  recurrentSSComparison_of_shiftComparison (shiftComparison_of_alexandrov hA)

end RandomSandpile

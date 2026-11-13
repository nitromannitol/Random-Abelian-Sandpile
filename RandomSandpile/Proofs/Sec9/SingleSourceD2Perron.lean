import RandomSandpile.Proofs.Sec9.SingleSourceD2PerronPrep

/-!
# Theorem 9.2 in dimension two: Perron's method on annuli

`annulus_solution` (from CIL Theorem 4.1, `CILPerronStmt`, with the comparison `obsComparison`
from CIL Theorem 3.2): on `A_r = {r < |x| < L}` there is `u ∈ C(Ā_r)` with `V_1 ≤ u ≤ U`, a
viscosity supersolution of `F_ε = 0` on `A_r` and a subsolution where `u > 0`.

The Dirichlet data `u = M_r = V_1(r)` on `|x| = r`, `u = 0` on `|x| = L` are removed by subtracting
the quadratic `g(x) = a + κ|x|²` with these boundary values (CIL's (DP) has zero data). Then
`w = u - g` solves `min{w + g(x), F_ε(D²w + 2κI)} = 0`, with the explicit barriers
`V_1 - g` (subsolution: where `V_1 > 0`, `ΔV_1 ≥ c = K + 2` forces `F_ε < 0`) and
`min{U, M_r} - g` (supersolution: `U` and the constant `M_r` are `F_ε`-supersolutions); both vanish on
`∂A_r`, so boundary attainment comes from the barriers.
-/

noncomputable section

open Filter Topology Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

open CrandallIshiiLions

theorem sSup_eval_bounds {S : Set (Rd 2 → ℝ)} {ul uu : Rd 2 → ℝ} {x : Rd 2} (hul : ul ∈ S)
    (hS : ∀ w ∈ S, w x ≤ uu x) :
    ul x ≤ sSup ((fun w : Rd 2 → ℝ => w x) '' S) ∧
      sSup ((fun w : Rd 2 → ℝ => w x) '' S) ≤ uu x := by
  have hbdd : BddAbove ((fun w : Rd 2 → ℝ => w x) '' S) := by
    refine ⟨uu x, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hS w hw
  refine ⟨le_csSup hbdd ⟨ul, hul, rfl⟩, csSup_le ⟨ul x, ul, hul, rfl⟩ ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hS w hw

/-- CIL Theorem 4.1 with the Perron function between the barriers. -/
theorem perron_exists (hP : CILPerronStmt) {F : Rd 2 → ℝ → Rd 2 → Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    {Ω : Set (Rd 2)} (hΩ : IsOpen Ω) (hprop : IsProper F)
    (hcont : Continuous (fun w : Rd 2 × ℝ × Rd 2 × Matrix (Fin 2) (Fin 2) ℝ =>
      F w.1 w.2.1 w.2.2.1 w.2.2.2))
    (hcomp : ∀ w v : Rd 2 → ℝ, IsSubsolutionDP F Ω w → IsSupersolutionDP F Ω v →
      ∀ x ∈ closure Ω, w x ≤ v x)
    {ul uu : Rd 2 → ℝ} (hul : IsSubsolutionDP F Ω ul) (huu : IsSupersolutionDP F Ω uu)
    (henv : ∀ x ∈ frontier Ω, LowerEnvelopeZeroAt Ω ul x ∧ UpperEnvelopeZeroAt Ω uu x)
    (hle : ∀ y ∈ closure Ω, ul y ≤ uu y) :
    ∃ W : Rd 2 → ℝ, ContinuousOn W (closure Ω) ∧ IsSubsolution F Ω W ∧ IsSupersolution F Ω W ∧
      (∀ x ∈ frontier Ω, W x = 0) ∧ ∀ x ∈ closure Ω, ul x ≤ W x ∧ W x ≤ uu x := by
  have h := hP 2 F Ω hΩ hprop hcont hcomp ul uu hul huu henv
  exact ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2, fun x hx =>
    sSup_eval_bounds
      (S := {w | (∀ y ∈ closure Ω, ul y ≤ w y ∧ w y ≤ uu y) ∧ IsSubsolutionDP F Ω w})
      (And.intro (fun y hy => ⟨le_refl _, hle y hy⟩) hul) fun w hw => (hw.1 x hx).2⟩

theorem trace_sub_hasTraceShift (c : ℝ) :
    HasTraceShift (fun M : Matrix (Fin 2) (Fin 2) ℝ => c - M.trace) := by
  intro M _ t
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

theorem superJet2_of_open {O O' : Set (Rd 2)} (hO : IsOpen O) (hO' : IsOpen O') {u : Rd 2 → ℝ}
    {x : Rd 2} (hx : x ∈ O) (hx' : x ∈ O') {pX : Rd 2 × Matrix (Fin 2) (Fin 2) ℝ}
    (h : pX ∈ superJet2 O u x) : pX ∈ superJet2 O' u x := by
  simp only [superJet2, Set.mem_ofPred_eq] at h ⊢
  rw [nhdsWithin_eq_nhds.2 (hO.mem_nhds hx)] at h
  rw [nhdsWithin_eq_nhds.2 (hO'.mem_nhds hx')]
  exact h

/-- **Perron's method on annuli**. -/
theorem annulus_solution (hTS : CILTheoremOfSumsStmt) (hP : CILPerronStmt)
    {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F) (hdeg : DegenerateElliptic F)
    {K : ℝ} (hK : 1 ≤ K) (hTr : ∀ z, traceGraph F z ≤ K) (hF0 : 0 ≤ F 0)
    {v : Rd 2 → ℝ} (hv : Continuous v)
    (hU : IsSourceProfile F (fun x => v x + fundamentalSolution 2 x))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {L : ℝ}
    (hLU : ∀ x : Rd 2, L ≤ ‖x‖ → v x + fundamentalSolution 2 x = 0)
    (hLR : rad2 (K + 2) 1 ≤ L ^ 2) {r : ℝ} (hr : 0 < r) (hrR : r ^ 2 < rad2 (K + 2) 1) :
    ∃ u : Rd 2 → ℝ, ContinuousOn u (closure (annSet r L)) ∧
      (∀ x ∈ closure (annSet r L),
        Vbar (K + 2) 1 x ≤ u x ∧ u x ≤ v x + fundamentalSolution 2 x) ∧
      ViscFromBelowGE (regOp F K ε) (annSet r L) u ∧
      ViscFromAboveLE (regOp F K ε) {x | x ∈ annSet r L ∧ 0 < u x} u := by
  have hc : (0 : ℝ) < K + 2 := by linarith
  have hR := rad2_pos hc one_pos
  have hrL : r ^ 2 < L ^ 2 := lt_of_lt_of_le hrR hLR
  have hD : 0 < L ^ 2 - r ^ 2 := by linarith
  -- the boundary value and the quadratic
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = kap (K + 2) 1 (r ^ 2) := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hM_def]; exact kap_nonneg hc one_pos (by positivity)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = -M / (L ^ 2 - r ^ 2) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = M - κ * r ^ 2 := ⟨_, rfl⟩
  set g : Rd 2 → ℝ := fun x => a + κ * ‖x‖ ^ 2 with hg_def
  have hgc : Continuous g := by rw [hg_def]; fun_prop
  have hgr : ∀ x : Rd 2, ‖x‖ = r → g x = M := fun x hx => by
    show a + κ * ‖x‖ ^ 2 = M
    rw [hx, ha]
    ring
  have hgL : ∀ x : Rd 2, ‖x‖ = L → g x = 0 := fun x hx => by
    show a + κ * ‖x‖ ^ 2 = 0
    have h1 : -M / (L ^ 2 - r ^ 2) * (L ^ 2 - r ^ 2) = -M := div_mul_cancel₀ (-M) hD.ne'
    rw [hx, ha, hκ]
    linarith
  -- the operator
  set A := shOp F K ε κ with hA_def
  have hAshift : HasTraceShift A := shOp_hasTraceShift F K ε κ
  have hAdeg : DegenerateElliptic A :=
    shOp_degenerateElliptic hF hdeg K hε0.le hε1.le κ
  have hAc : Continuous A := continuous_shOp hF hdeg K ε κ
  set Ω := annSet r L with hΩ_def
  have hΩ : IsOpen Ω := isOpen_annSet r L
  have hΩ0 : ∀ x ∈ closure Ω, x ≠ 0 := fun x hx => ne_zero_of_mem_closure_annSet hr hx
  have hΩ0' : ∀ x ∈ Ω, x ≠ 0 := fun x hx => hΩ0 x (subset_closure hx)
  set U : Rd 2 → ℝ := fun x => v x + fundamentalSolution 2 x with hU_def
  -- values on the two circles
  have hVr : ∀ x : Rd 2, ‖x‖ = r → Vbar (K + 2) 1 x = M := fun x hx => by
    rw [Vbar, hx, min_eq_left hrR.le, hM_def]
  have hVL : ∀ x : Rd 2, ‖x‖ = L → Vbar (K + 2) 1 x = 0 := fun x hx =>
    Vbar_eq_zero hc one_pos (by rw [hx]; exact hLR)
  have hVU : ∀ x : Rd 2, x ≠ 0 → Vbar (K + 2) 1 x ≤ U x := fun x hx =>
    Vbar_one_le hF hK hTr hv hU hx
  have hUL : ∀ x : Rd 2, ‖x‖ = L → U x = 0 := fun x hx => hLU x hx.ge
  -- the barriers
  set ul : Rd 2 → ℝ := fun x => Vbar (K + 2) 1 x - g x with hul_def
  set uu : Rd 2 → ℝ := fun x => min (U x) M - g x with huu_def
  have hulc : ContinuousOn ul (closure Ω) :=
    ((continuousOn_Vbar hc one_pos).mono fun x hx => hΩ0 x hx).sub hgc.continuousOn
  have hminc : ContinuousOn (fun x => min (U x) M) (closure Ω) :=
    Continuous.comp_continuousOn (g := fun t : ℝ => min t M) (by fun_prop)
      (hU.continuousOn.mono fun x hx => hΩ0 x hx)
  have huuc : ContinuousOn uu (closure Ω) := hminc.sub hgc.continuousOn
  have hul0 : ∀ x ∈ frontier Ω, ul x = 0 := by
    intro x hx
    show Vbar (K + 2) 1 x - g x = 0
    rcases norm_of_mem_frontier_annSet hx with h | h
    · rw [hVr x h, hgr x h, sub_self]
    · rw [hVL x h, hgL x h, sub_self]
  have huu0 : ∀ x ∈ frontier Ω, uu x = 0 := by
    intro x hx
    show min (U x) M - g x = 0
    have hx0 := hΩ0 x (frontier_subset_closure hx)
    rcases norm_of_mem_frontier_annSet hx with h | h
    · have h1 := hVU x hx0
      rw [hVr x h] at h1
      rw [min_eq_right h1, hgr x h, sub_self]
    · rw [hUL x h, min_eq_left hM, hgL x h, sub_self]
  have hle : ∀ y ∈ closure Ω, ul y ≤ uu y := by
    intro y hy
    show Vbar (K + 2) 1 y - g y ≤ min (U y) M - g y
    have hy0 := hΩ0 y hy
    have hyr : r ≤ ‖y‖ := (closure_annSet_subset r L hy).1
    have hVM : Vbar (K + 2) 1 y ≤ M := by
      by_cases h : rad2 (K + 2) 1 ≤ ‖y‖ ^ 2
      · rw [Vbar_eq_zero hc one_pos h]
        exact hM
      · rw [Vbar_eq_Vsm (not_le.1 h).le, Vsm, hM_def]
        exact kap_antitone hc (by positivity) (pow_le_pow_left₀ hr.le hyr 2) (not_le.1 h).le
    have := le_min (hVU y hy0) hVM
    linarith
  -- the lower barrier is a subsolution of (DP)
  have hsubDP : IsSubsolutionDP (obsOp g A) Ω ul := by
    refine ⟨hulc.upperSemicontinuousOn, ⟨(hulc.mono subset_closure).upperSemicontinuousOn,
      fun x hx pX hpX => ?_⟩, fun x hx => (hul0 x hx).le⟩
    show min (ul x + g x) (A pX.2) ≤ 0
    have he : ul x + g x = Vbar (K + 2) 1 x := by
      show Vbar (K + 2) 1 x - g x + g x = Vbar (K + 2) 1 x
      ring
    rw [he]
    by_cases hpos : 0 < Vbar (K + 2) 1 x
    · have hxR := lt_of_Vbar_pos hc one_pos hpos
      have hshift : ∀ y, Vbar (K + 2) 1 y = ul y + (a + κ * ‖y‖ ^ 2) := fun y => by
        show Vbar (K + 2) 1 y = Vbar (K + 2) 1 y - (a + κ * ‖y‖ ^ 2) + (a + κ * ‖y‖ ^ 2)
        ring
      have hj := mem_superJet2_add_quad hshift (p := pX.1) (X := pX.2) hpX
      have hO : IsOpen {y : Rd 2 | y ≠ 0 ∧ ‖y‖ ^ 2 < rad2 (K + 2) 1} :=
        isOpen_ne.inter (isOpen_lt (continuous_norm.pow 2) continuous_const)
      have hxO : x ∈ {y : Rd 2 | y ≠ 0 ∧ ‖y‖ ^ 2 < rad2 (K + 2) 1} := ⟨hΩ0' x hx, hxR⟩
      have hj' := superJet2_of_open hΩ hO hx hxO hj
      have htr := nonpos_of_mem_superJet2 hO (trace_sub_hasTraceShift (K + 2))
        (visc_sub_Vbar hc one_pos) hxO hj'
      have hA : A pX.2 ≤ 0 := by
        show regOp F K ε (pX.2 + (2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ≤ 0
        have hf := hTr (traceFreeCoord (pX.2 + (2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
        have htr' : K + 2 - (pX.2 + (2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).trace ≤ 0 := htr
        have hp := mul_le_mul_of_nonneg_left hf (by linarith : (0 : ℝ) ≤ 1 - ε)
        unfold regOp
        nlinarith
      exact (min_le_right _ _).trans hA
    · exact (min_le_left _ _).trans (not_lt.1 hpos)
  -- the upper barrier is a supersolution of (DP)
  have hsupDP : IsSupersolutionDP (obsOp g A) Ω uu := by
    refine ⟨huuc.lowerSemicontinuousOn, ⟨(huuc.mono subset_closure).lowerSemicontinuousOn,
      fun x hx pX hpX => ?_⟩, fun x hx => (huu0 x hx).ge⟩
    show 0 ≤ min (uu x + g x) (A pX.2)
    have hx0 := hΩ0' x hx
    have he : uu x + g x = min (U x) M := by
      show min (U x) M - g x + g x = min (U x) M
      ring
    rw [he]
    refine le_min (le_min (hU.nonneg x hx0) hM) ?_
    have hshift : ∀ y, min (U y) M = uu y + (a + κ * ‖y‖ ^ 2) := fun y => by
      show min (U y) M = min (U y) M - (a + κ * ‖y‖ ^ 2) + (a + κ * ‖y‖ ^ 2)
      ring
    have hj := mem_subJet2_add_quad hshift (p := pX.1) (X := pX.2) hpX
    show 0 ≤ regOp F K ε (pX.2 + (2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    by_cases hUM : U x ≤ M
    · have hjU := mem_subJet2_of_le (h := U) (fun y => min_le_left _ _) (min_eq_left hUM) hj
      have hsup : ViscFromBelowGE (regOp F K ε) Ω U :=
        viscFromBelowGE_regOp hF hε0.le hTr fun y hy => hU.supersolution y (hΩ0' y hy)
      exact nonneg_of_mem_subJet2 hΩ (regOp_hasTraceShift F K ε) hsup hx hjU
    · have hjM := mem_subJet2_of_le (h := fun _ => M) (fun y => min_le_right _ _)
        (min_eq_right (not_le.1 hUM).le) hj
      exact nonneg_of_mem_subJet2 hΩ (regOp_hasTraceShift F K ε)
        (viscFromBelowGE_regOp_const hF hdeg hK hε0.le hε1.le hF0 Ω M) hx hjM
  -- the envelopes
  have henv : ∀ x ∈ frontier Ω, LowerEnvelopeZeroAt Ω ul x ∧ UpperEnvelopeZeroAt Ω uu x := by
    intro x hx
    have hxc := frontier_subset_closure hx
    exact ⟨(envelopes_of_continuousWithinAt hxc (hulc x hxc) (hul0 x hx)).1,
      (envelopes_of_continuousWithinAt hxc (huuc x hxc) (huu0 x hx)).2⟩
  -- Perron's method
  obtain ⟨W, hWc, hWsub, hWsup, -, hWb⟩ := perron_exists hP hΩ (isProper_obsOp hAdeg)
    (continuous_obsOp hgc hAc)
    (fun w w' hw hw' => obsComparison hTS hΩ (isBounded_annSet r L) hgc hAshift hAdeg
      hAc.continuousOn hw hw') hsubDP hsupDP henv hle
  have hmat : ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
      X + (2 * -κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (2 * κ) • 1 = X := fun X => by
    rw [add_assoc, ← add_smul, show 2 * -κ + 2 * κ = (0 : ℝ) by ring, zero_smul, add_zero]
  have hWu : ∀ y, W y = (W y + g y) + (-a + -κ * ‖y‖ ^ 2) := fun y => by
    show W y = W y + (a + κ * ‖y‖ ^ 2) + (-a + -κ * ‖y‖ ^ 2)
    ring
  refine ⟨fun x => W x + g x, hWc.add hgc.continuousOn, fun x hx => ?_, ?_, ?_⟩
  · have h1 := hWb x hx
    have h2 : min (U x) M ≤ U x := min_le_left _ _
    constructor
    · show Vbar (K + 2) 1 x ≤ W x + g x
      have : ul x ≤ W x := h1.1
      have e : ul x = Vbar (K + 2) 1 x - g x := rfl
      linarith
    · show W x + g x ≤ U x
      have : W x ≤ uu x := h1.2
      have e : uu x = min (U x) M - g x := rfl
      linarith
  · intro x hx φ hφ hmin
    have hj := mem_subJet2_of_isLocalMin Ω hφ hmin
    have hj' := mem_subJet2_add_quad hWu hj
    have h0 := hWsup.2 x hx _ hj'
    have h : 0 ≤ min (W x + g x)
        (A (hessian φ x + (2 * -κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) := h0
    have h2 := (le_min_iff.1 h).2
    have e : A (hessian φ x + (2 * -κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        regOp F K ε (hessian φ x) := by
      show regOp F K ε (hessian φ x + (2 * -κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (2 * κ) • 1) =
        regOp F K ε (hessian φ x)
      rw [hmat]
    rw [e] at h2
    exact h2
  · intro x hx φ hφ hmax
    have hj := mem_superJet2_of_isLocalMax Ω hφ hmax
    have hj' := mem_superJet2_add_quad hWu hj
    have h0 := hWsub.2 x hx.1 _ hj'
    have h : min (W x + g x)
        (A (hessian φ x + (2 * -κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) ≤ 0 := h0
    have e : A (hessian φ x + (2 * -κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        regOp F K ε (hessian φ x) := by
      show regOp F K ε (hessian φ x + (2 * -κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (2 * κ) • 1) =
        regOp F K ε (hessian φ x)
      rw [hmat]
    rw [e] at h
    rcases min_le_iff.1 h with h1 | h1
    · have : 0 < W x + g x := hx.2
      linarith
    · exact h1

end SingleSourceD2

end RandomSandpile

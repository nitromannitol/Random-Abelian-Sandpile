import RandomSandpile.Proofs.Sec9.SingleSourceD2Barrier

/-!
# Theorem 9.2 in dimension two: the barrier lies below the source profile

SIMPLE-PROOF (7.3), `V_1 ≤ U`, with `c = K + 2`: for `m < 1`, `V_m - U → -∞` at the origin
(`V_m - mG` is bounded and `U - G = v` is continuous) and `V_m - U ≤ 0` outside `B_R`; a positive
maximum would be a point where `V_m` is smooth and `U - V_m` has a local minimum, so the supersolution
property of `U` gives `0 ≤ F(D²V_m) = f(Z) - c ≤ K - c < 0` (`Vbar_le_of_lt_one`). Letting `m → 1`
gives `V_1 ≤ U` (`Vbar_one_le`). Moreover `V_1 ≥ G - B` near the origin (`fundamentalSolution_sub_le`).
-/

noncomputable section

open Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

theorem fundamentalSolution_two_eq' (x : Rd 2) :
    fundamentalSolution 2 x = -(1 / (2 * Real.pi)) * Real.log ‖x‖ := by
  rw [fundamentalSolution, if_pos rfl]

/-- `V = m G + c/4 (|x|² - R²) + m/(4π) log R²` off the origin. -/
theorem Vsm_eq {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {x : Rd 2} (hx : x ≠ 0) :
    Vsm c m x = m * fundamentalSolution 2 x + c / 4 * (‖x‖ ^ 2 - rad2 c m) +
      m / (4 * Real.pi) * Real.log (rad2 c m) := by
  have hR := (rad2_pos hc hm).ne'
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [Vsm, kap, Real.log_div (pow_ne_zero 2 hn) hR, Real.log_pow, fundamentalSolution_two_eq']
  push_cast
  ring

/-- The lower bound `G - B ≤ V_1` inside `B_R`. -/
theorem fundamentalSolution_sub_le {c : ℝ} (hc : 0 < c) {x : Rd 2} (hx : x ≠ 0)
    (hxR : ‖x‖ ^ 2 ≤ rad2 c 1) :
    fundamentalSolution 2 x - (c / 4 * rad2 c 1 - 1 / (4 * Real.pi) * Real.log (rad2 c 1)) ≤
      Vbar c 1 x := by
  rw [Vbar_eq_Vsm hxR, Vsm_eq hc one_pos hx]
  have h := mul_nonneg (by linarith : (0 : ℝ) ≤ c / 4) (sq_nonneg ‖x‖)
  linarith

/-- **`V_m ≤ U` for `m < 1`.** -/
theorem Vbar_le_of_lt_one {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F) {K : ℝ}
    (hK : 1 ≤ K) (hTr : ∀ z, traceGraph F z ≤ K) {v : Rd 2 → ℝ} (hv : Continuous v)
    (hU : IsSourceProfile F (fun x => v x + fundamentalSolution 2 x)) {m : ℝ} (hm0 : 0 < m)
    (hm1 : m < 1) {x0 : Rd 2} (hx0 : x0 ≠ 0) :
    Vbar (K + 2) m x0 ≤ v x0 + fundamentalSolution 2 x0 := by
  have hc : (0 : ℝ) < K + 2 := by linarith
  have hR := rad2_pos hc hm0
  by_contra hlt
  obtain ⟨D, hD⟩ : ∃ D : Rd 2 → ℝ,
      D = fun y => Vbar (K + 2) m y - (v y + fundamentalSolution 2 y) := ⟨_, rfl⟩
  have hDy : ∀ y, D y = Vbar (K + 2) m y - (v y + fundamentalSolution 2 y) := fun y => by
    rw [hD]
  have hD0 : 0 < D x0 := by rw [hDy]; linarith [not_le.1 hlt]
  have hx0R : ‖x0‖ ^ 2 < rad2 (K + 2) m := by
    have := hU.nonneg x0 hx0
    exact lt_of_Vbar_pos hc hm0 (by linarith)
  -- `D < D x0` near the origin
  obtain ⟨Mv, hMv⟩ := (isCompact_closedBall (0 : Rd 2) 1).exists_bound_of_continuousOn
    hv.continuousOn
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℝ, C1 = (K + 2) / 4 + m / (4 * Real.pi) * Real.log (rad2 (K + 2) m) +
      Mv := ⟨_, rfl⟩
  have hm1' : 0 < 1 - m := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (D x0 - C1) * (2 * Real.pi) / (1 - m) := ⟨_, rfl⟩
  have hLid : (1 - m) / (2 * Real.pi) * L = D x0 - C1 := by
    rw [hL]
    field_simp
  obtain ⟨δ0, hδ0⟩ : ∃ δ0 : ℝ, δ0 = min (min 1 ‖x0‖) (Real.exp L) := ⟨_, rfl⟩
  have hδ0pos : 0 < δ0 := by
    rw [hδ0]
    exact lt_min (lt_min one_pos (norm_pos_iff.2 hx0)) (Real.exp_pos L)
  have hδ1 : δ0 ≤ 1 := by
    rw [hδ0]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hδx : δ0 ≤ ‖x0‖ := by
    rw [hδ0]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hδe : δ0 ≤ Real.exp L := by
    rw [hδ0]
    exact min_le_right _ _
  have hsmall : ∀ y : Rd 2, y ≠ 0 → ‖y‖ < δ0 → D y < D x0 := by
    intro y hy hyδ
    have hy1 : ‖y‖ < 1 := lt_of_lt_of_le hyδ hδ1
    have hyx : ‖y‖ < ‖x0‖ := lt_of_lt_of_le hyδ hδx
    have hye : ‖y‖ < Real.exp L := lt_of_lt_of_le hyδ hδe
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hlog : Real.log ‖y‖ < L := (Real.log_lt_iff_lt_exp hypos).2 hye
    have hyR : ‖y‖ ^ 2 ≤ rad2 (K + 2) m := by nlinarith
    have hvy : -v y ≤ Mv := by
      have := hMv y (by rw [mem_closedBall, dist_zero_right]; exact hy1.le)
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (v y)]
    have hsq : ‖y‖ ^ 2 ≤ 1 := by nlinarith
    have hmul := mul_lt_mul_of_pos_left hlog (by positivity : 0 < (1 - m) / (2 * Real.pi))
    rw [hDy, Vbar_eq_Vsm hyR, Vsm_eq hc hm0 hy, fundamentalSolution_two_eq']
    have hq : (K + 2) / 4 * (‖y‖ ^ 2 - rad2 (K + 2) m) ≤ (K + 2) / 4 := by
      have := mul_le_mul_of_nonneg_left (show ‖y‖ ^ 2 - rad2 (K + 2) m ≤ 1 by linarith)
        (by linarith : (0 : ℝ) ≤ (K + 2) / 4)
      linarith
    have e : m * (-(1 / (2 * Real.pi)) * Real.log ‖y‖) - -(1 / (2 * Real.pi)) * Real.log ‖y‖ =
        (1 - m) / (2 * Real.pi) * Real.log ‖y‖ := by ring
    linarith
  -- the maximum over a closed annulus
  obtain ⟨S, hS⟩ : ∃ S : Set (Rd 2), S = {y | δ0 ≤ ‖y‖ ∧ ‖y‖ ≤ rad2 (K + 2) m + 1} := ⟨_, rfl⟩
  have hSc : IsCompact S := by rw [hS]; exact isCompact_closedAnnulus _ _
  have hS0 : S ⊆ {y | y ≠ 0} := fun y hy => by
    rw [hS] at hy
    have h1 : δ0 ≤ ‖y‖ := hy.1
    intro h
    rw [h, norm_zero] at h1
    linarith
  have hx0S : x0 ∈ S := by
    rw [hS]
    refine ⟨hδx, ?_⟩
    nlinarith [sq_nonneg (‖x0‖ - 1 / 2)]
  have hDc : ContinuousOn D S := by
    rw [hD]
    exact ((continuousOn_Vbar hc hm0).sub hU.continuousOn).mono hS0
  obtain ⟨xs, hxsS, hxsmax⟩ := hSc.exists_isMaxOn ⟨x0, hx0S⟩ hDc
  have hDxs : D x0 ≤ D xs := isMaxOn_iff.1 hxsmax x0 hx0S
  have hxs0 : xs ≠ 0 := hS0 hxsS
  have hxsR : ‖xs‖ ^ 2 < rad2 (K + 2) m := by
    have h1 := hU.nonneg xs hxs0
    have h2 := hDy xs
    exact lt_of_Vbar_pos hc hm0 (by linarith)
  have hglob : ∀ y : Rd 2, y ≠ 0 → D y ≤ D xs := by
    intro y hy
    by_cases h1 : ‖y‖ < δ0
    · linarith [hsmall y hy h1]
    · by_cases h2 : rad2 (K + 2) m ≤ ‖y‖ ^ 2
      · have h3 := hU.nonneg y hy
        rw [hDy y, Vbar_eq_zero hc hm0 h2]
        linarith
      · have hyS : y ∈ S := by
          rw [hS]
          refine ⟨not_lt.1 h1, ?_⟩
          nlinarith [sq_nonneg (‖y‖ - 1 / 2), not_le.1 h2]
        exact isMaxOn_iff.1 hxsmax y hyS
  -- `U - V` has a local minimum at `xs`
  have hopen : IsOpen {y : Rd 2 | y ≠ 0 ∧ ‖y‖ ^ 2 < rad2 (K + 2) m} :=
    isOpen_ne.inter (isOpen_lt (continuous_norm.pow 2) continuous_const)
  have hmin : IsLocalMin (fun y => (v y + fundamentalSolution 2 y) - Vsm (K + 2) m y) xs := by
    filter_upwards [hopen.mem_nhds ⟨hxs0, hxsR⟩] with y hy
    have h1 := hglob y hy.1
    rw [hDy, hDy, Vbar_eq_Vsm hy.2.le, Vbar_eq_Vsm hxsR.le] at h1
    show v xs + fundamentalSolution 2 xs - Vsm (K + 2) m xs ≤
      v y + fundamentalSolution 2 y - Vsm (K + 2) m y
    linarith
  have hV := contDiffAt_Vsm hc hm0 hxs0
  have h := hU.supersolution xs hxs0 (Vsm (K + 2) m) hV hmin
  rw [eq_traceGraph_sub_trace hF (hessian_isSymm_of_contDiffAt hV),
    trace_hessian_Vsm hc hm0 hxs0] at h
  have := hTr (traceFreeCoord (hessian (Vsm (K + 2) m) xs))
  linarith

theorem continuousAt_Vbar_m {c : ℝ} (hc : 0 < c) {x : Rd 2} (hx : x ≠ 0) :
    ContinuousAt (fun m => Vbar c m x) 1 := by
  have hR : ContinuousAt (fun m : ℝ => rad2 c m) 1 := by
    unfold rad2
    fun_prop
  have hmin : ContinuousAt (fun m : ℝ => min (‖x‖ ^ 2) (rad2 c m)) 1 := continuousAt_const.min hR
  have hR1 : rad2 c 1 ≠ 0 := (rad2_pos hc one_pos).ne'
  have hpos : min (‖x‖ ^ 2) (rad2 c 1) / rad2 c 1 ≠ 0 :=
    (div_pos (lt_min (pow_pos (norm_pos_iff.2 hx) 2) (rad2_pos hc one_pos))
      (rad2_pos hc one_pos)).ne'
  have hlog : ContinuousAt (fun m => Real.log (min (‖x‖ ^ 2) (rad2 c m) / rad2 c m)) 1 :=
    (hmin.div hR hR1).log hpos
  show ContinuousAt (fun m => c / 4 * (min (‖x‖ ^ 2) (rad2 c m) - rad2 c m) -
    m / (4 * Real.pi) * Real.log (min (‖x‖ ^ 2) (rad2 c m) / rad2 c m)) 1
  exact (continuousAt_const.mul (hmin.sub hR)).sub ((continuousAt_id.div_const _).mul hlog)

/-- **`V_1 ≤ U`** off the origin. -/
theorem Vbar_one_le {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F) {K : ℝ}
    (hK : 1 ≤ K) (hTr : ∀ z, traceGraph F z ≤ K) {v : Rd 2 → ℝ} (hv : Continuous v)
    (hU : IsSourceProfile F (fun x => v x + fundamentalSolution 2 x)) {x : Rd 2} (hx : x ≠ 0) :
    Vbar (K + 2) 1 x ≤ v x + fundamentalSolution 2 x := by
  have hc : (0 : ℝ) < K + 2 := by linarith
  have hT : Tendsto (fun m => Vbar (K + 2) m x) (𝓝[<] 1) (𝓝 (Vbar (K + 2) 1 x)) :=
    (continuousAt_Vbar_m hc hx).tendsto.mono_left nhdsWithin_le_nhds
  have h0 : ∀ᶠ m in 𝓝[<] (1 : ℝ), 0 < m := (lt_mem_nhds one_pos).filter_mono nhdsWithin_le_nhds
  have h1 : ∀ᶠ m in 𝓝[<] (1 : ℝ), m < 1 := self_mem_nhdsWithin
  refine le_of_tendsto hT ?_
  filter_upwards [h0, h1] with m hm0 hm1
  exact Vbar_le_of_lt_one hF hK hTr hv hU hm0 hm1 hx

end SingleSourceD2

end RandomSandpile

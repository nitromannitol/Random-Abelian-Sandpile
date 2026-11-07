import RandomSandpile.Proofs.Sec9.SingleSourceD2Approx
import RandomSandpile.Proofs.Sec9.SingleSourceFstarDilation

/-!
# Theorem 9.2 in dimension two: leastness by dilation

`dilationLeast : DilationLeastStmt`. Let `U = v + G` be a source profile of `F` (shift identity,
degenerate elliptic) and `W` a nonnegative `F`-supersolution off the origin, continuous there, with
`W ≥ G - B` near the origin. For `t > 1` the dilation `W_t(x) = t² W(x/t)` is again a supersolution
(`viscFromBelowGE_dilate_of_shift`: the Hessian of a touching quadratic is unchanged), and
`W_t - U ≥ (t² - 1) G - C → +∞` at the origin. The comparison principle on
`D = {U > 0} ∩ (B_R ∖ B̄_ρ)` gives `U ≤ W_t` off the origin; `t ↓ 1` gives `U ≤ W`. This is the
argument of `Proofs/Sec9/SingleSourceFstarDilation.lean` (`ssLimitMinimalStar_of_sub`) for a general
operator, with `W - G` only bounded below at the origin (SIMPLE-PROOF §7.5; it replaces the
removability argument of §7.4).
-/

noncomputable section

open MeasureTheory Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

open SingleSourceFstar

/-- **Dilation of a viscosity supersolution** of an operator with the shift identity. -/
theorem viscFromBelowGE_dilate_of_shift {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    {W : Rd 2 → ℝ} (hW : ViscFromBelowGE F {x | x ≠ 0} W) {t : ℝ} (ht : 0 < t) :
    ViscFromBelowGE F {x | x ≠ 0} (fun x => t ^ 2 * W (t⁻¹ • x)) := by
  intro x hx φ hφ hmin
  have hx0 : x ≠ 0 := hx
  have hHs : (hessian φ x).IsSymm := hessian_isSymm_of_contDiffAt hφ
  have key : ∀ κ : ℝ, 0 < κ →
      0 ≤ F (hessian φ x - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    intro κ hκ
    have htouch := touch_below_of_isLocalMin hφ hmin hκ
    have hY : (hessian φ x - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm :=
      hHs.sub (Matrix.isSymm_one.smul κ)
    have hx₁ : t⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero ht.ne') hx0
    refine ViscFromBelowGE.le_of_touch hW hY (b := t⁻¹ • x)
      (q := t⁻¹ • (InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x)) hx₁ ?_
    have hcont : Tendsto (fun y : Rd 2 => t • y) (𝓝 (t⁻¹ • x)) (𝓝 x) := by
      have h := (continuous_const_smul t).tendsto (t⁻¹ • x)
      rwa [smul_inv_smul₀ ht.ne'] at h
    filter_upwards [hcont.eventually htouch] with y hy
    have hy' : t ^ 2 * W (t⁻¹ • x) +
        inner ℝ ((InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x)) (t • y - x) +
        qM (hessian φ x - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (t • y - x) ≤
        t ^ 2 * W (t⁻¹ • (t • y)) := hy
    rw [inv_smul_smul₀ ht.ne'] at hy'
    have e1 : t • y - x = t • (y - t⁻¹ • x) := by rw [smul_sub, smul_inv_smul₀ ht.ne']
    rw [e1, real_inner_smul_right, qM_smul] at hy'
    rw [real_inner_smul_left]
    have ht2 : 0 < t ^ 2 := by positivity
    have htt : t ^ 2 * t⁻¹ = t := by rw [sq, mul_assoc, mul_inv_cancel₀ ht.ne', mul_one]
    refine le_of_mul_le_mul_left ?_ ht2
    calc t ^ 2 * (W (t⁻¹ • x) +
          t⁻¹ * inner ℝ ((InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x))
            (y - t⁻¹ • x) +
          qM (hessian φ x - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - t⁻¹ • x))
        = t ^ 2 * W (t⁻¹ • x) +
          (t ^ 2 * t⁻¹) * inner ℝ ((InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x))
            (y - t⁻¹ • x) +
          t ^ 2 * qM (hessian φ x - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - t⁻¹ • x) := by
          ring
      _ ≤ t ^ 2 * W y := by rw [htt]; exact hy'
  have hshift : ∀ κ : ℝ, F (hessian φ x - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      F (hessian φ x) + 2 * κ := by
    intro κ
    have h := hF (hessian φ x) hHs (-κ)
    rw [neg_smul, ← sub_eq_add_neg] at h
    rw [h]
    ring
  by_contra hneg
  have hlt : F (hessian φ x) < 0 := not_le.1 hneg
  have h := key (-(F (hessian φ x)) / 4) (by linarith)
  rw [hshift] at h
  linarith

/-- Near the origin the dilation dominates the profile. -/
theorem dilate_ge_near {v W : Rd 2 → ℝ} (hv : Continuous v) {ρ B : ℝ} (hρ : 0 < ρ)
    (hWB : ∀ x : Rd 2, x ≠ 0 → ‖x‖ < ρ → fundamentalSolution 2 x - B ≤ W x) {t : ℝ}
    (ht : 1 < t) : ∃ ρ' > 0, ∀ x : Rd 2, x ≠ 0 → ‖x‖ ≤ ρ' →
      v x + fundamentalSolution 2 x ≤ t ^ 2 * W (t⁻¹ • x) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨Mv, hMv⟩ := (isCompact_closedBall (0 : Rd 2) 1).exists_bound_of_continuousOn
    hv.continuousOn
  have htd : 0 < t ^ 2 - 1 := by nlinarith
  obtain ⟨ρ₁, hρ₁, hGl⟩ := fundamentalSolution_large (d := 2) le_rfl
    ((Mv + t ^ 2 * |B|) / (t ^ 2 - 1))
  refine ⟨min (min ρ₁ 1) (ρ / 2), lt_min (lt_min hρ₁ one_pos) (half_pos hρ), fun x hx hxρ => ?_⟩
  have hx1 : ‖x‖ ≤ 1 := hxρ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hxρ₁ : ‖x‖ ≤ ρ₁ := hxρ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hxρ2 : ‖x‖ ≤ ρ / 2 := hxρ.trans (min_le_right _ _)
  have hx₁ : t⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero ht0.ne') hx
  have hnt : ‖t⁻¹ • x‖ < ρ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]
    have : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht.le
    have hn := norm_nonneg x
    nlinarith
  have hW1 := hWB _ hx₁ hnt
  have hv1 := hMv x (by rw [mem_closedBall, dist_zero_right]; exact hx1)
  rw [Real.norm_eq_abs] at hv1
  have hGx := (div_le_iff₀ htd).1 (hGl x hx hxρ₁)
  have hscale := pow_mul_fundamentalSolution_le (d := 2) ht.le hx
  have h3 : t ^ 2 * (fundamentalSolution 2 (t⁻¹ • x) - B) ≤ t ^ 2 * W (t⁻¹ • x) :=
    mul_le_mul_of_nonneg_left hW1 (sq_nonneg t)
  have h4 := (abs_le.1 hv1).2
  have h5 : t ^ 2 * B ≤ t ^ 2 * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) (sq_nonneg t)
  have e1 : fundamentalSolution 2 x * (t ^ 2 - 1) =
      t ^ 2 * fundamentalSolution 2 x - fundamentalSolution 2 x := by ring
  rw [e1] at hGx
  have e2 : t ^ 2 * (fundamentalSolution 2 (t⁻¹ • x) - B) =
      t ^ 2 * fundamentalSolution 2 (t⁻¹ • x) - t ^ 2 * B := by ring
  rw [e2] at h3
  linarith

/-- ** Leastness by dilation.** -/
theorem dilationLeast : DilationLeastStmt := by
  intro hCIL F hF hDE v hv hprof W hWc hW0 hWsup hWB
  obtain ⟨ρ, B, hρ, hWB⟩ := hWB
  set U : Rd 2 → ℝ := fun x => v x + fundamentalSolution 2 x with hU
  have hGc : ContinuousOn (fundamentalSolution 2) {x : Rd 2 | x ≠ 0} :=
    SingleSourceMin.continuousOn_fundamentalSolution 2
  have hopen : IsOpen {x : Rd 2 | x ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hUc : ContinuousOn U {x : Rd 2 | x ≠ 0} := hv.continuousOn.add hGc
  obtain ⟨R₀, hR₀⟩ := hprof.eventually_zero
  have hshift : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm → ∀ s : ℝ,
      F (M + s • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = F M - ((2 : ℕ) : ℝ) * s := by
    intro M hM s
    rw [hF M hM s, Nat.cast_ofNat]
  have hdil : ∀ t : ℝ, 1 < t → ∀ x : Rd 2, x ≠ 0 → U x ≤ t ^ 2 * W (t⁻¹ • x) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    set Wt : Rd 2 → ℝ := fun x => t ^ 2 * W (t⁻¹ • x) with hWt
    have hWt0 : ∀ x : Rd 2, x ≠ 0 → 0 ≤ Wt x := fun x hx =>
      mul_nonneg (sq_nonneg t) (hW0 _ (smul_ne_zero (inv_ne_zero ht0.ne') hx))
    obtain ⟨ρ', hρ', hnear⟩ := dilate_ge_near hv hρ hWB ht
    set R' : ℝ := max R₀ ρ' + 1 with hR'
    set D : Set (Rd 2) := {x | x ≠ 0 ∧ 0 < U x} ∩ (ball 0 R' ∩ (closedBall 0 ρ')ᶜ) with hD
    have hDo : IsOpen D := by
      refine IsOpen.inter ?_ (isOpen_ball.inter isClosed_closedBall.isOpen_compl)
      exact hUc.isOpen_inter_preimage hopen isOpen_Ioi
    have hDb : Bornology.IsBounded D := isBounded_ball.subset fun x hx => hx.2.1
    have hcl : closure D ⊆ {x | ρ' ≤ ‖x‖} := by
      refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const continuous_norm)
      have h := hx.2.2
      simp only [Set.mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at h
      exact h.le
    have hcl0 : ∀ x ∈ closure D, x ≠ 0 := fun x hx h => by
      have h' : ρ' ≤ ‖x‖ := hcl hx
      rw [h, norm_zero] at h'
      linarith
    have hWtc : ContinuousOn Wt (closure D) := by
      have hsm : Continuous (fun x : Rd 2 => t⁻¹ • x) := continuous_const_smul _
      exact continuousOn_const.mul (hWc.comp hsm.continuousOn
        (fun x hx => smul_ne_zero (inv_ne_zero ht0.ne') (hcl0 x hx)))
    have hUcl : ContinuousOn U (closure D) := hUc.mono fun x hx => hcl0 x hx
    have hsub : ViscFromAboveLE F D U := fun x hx φ hφ hloc =>
      hprof.subsolution x hx.1 φ hφ hloc
    have hsup : ViscFromBelowGE F D Wt := fun x hx =>
      viscFromBelowGE_dilate_of_shift hF hWsup ht0 x hx.1.1
    have hout : ∀ x : Rd 2, x ≠ 0 → x ∉ D → U x ≤ Wt x := by
      intro x hx hxD
      by_cases h1 : ‖x‖ ≤ ρ'
      · exact hnear x hx h1
      by_cases h2 : R' ≤ ‖x‖
      · have hle : R₀ ≤ ‖x‖ := by
          have := le_max_left R₀ ρ'
          linarith
        rw [show U x = 0 from hR₀ x hle]
        exact hWt0 x hx
      · have hU0 : ¬ 0 < U x := fun h => hxD ⟨⟨hx, h⟩,
          by simpa [mem_ball, dist_zero_right, not_le] using h2,
          by simpa [mem_closedBall, dist_zero_right] using h1⟩
        exact (not_lt.1 hU0).trans (hWt0 x hx)
    have hbd : ∀ x ∈ frontier D, U x ≤ Wt x := fun x hx =>
      hout x (hcl0 x (frontier_subset_closure hx)) fun h => (hDo.frontier_eq ▸ hx).2 h
    have hcmp := hCIL 2 (by norm_num) F hDE hshift D hDo hDb U Wt hUcl hWtc hsub hsup hbd
    intro x hx
    by_cases hxD : x ∈ D
    · exact hcmp x (subset_closure hxD)
    · exact hout x hx hxD
  intro x hx
  have hc : ContinuousAt (fun t : ℝ => t ^ 2 * W (t⁻¹ • x)) 1 := by
    have h1 : ContinuousAt (fun t : ℝ => t⁻¹ • x) 1 :=
      (continuousAt_inv₀ one_ne_zero).smul continuousAt_const
    have h2 : ContinuousAt W x := hWc.continuousAt (hopen.mem_nhds hx)
    exact (continuousAt_id.pow 2).mul (h2.comp_of_eq h1 (by simp))
  have hlim : Tendsto (fun t : ℝ => t ^ 2 * W (t⁻¹ • x)) (𝓝[>] 1) (𝓝 (W x)) := by
    have h := hc.tendsto
    simp only [one_pow, inv_one, one_smul, one_mul] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  have hev : ∀ᶠ t in 𝓝[>] (1 : ℝ), U x ≤ t ^ 2 * W (t⁻¹ • x) :=
    eventually_nhdsWithin_of_forall fun t ht => hdil t ht x hx
  exact ge_of_tendsto hlim hev

end SingleSourceD2

end RandomSandpile

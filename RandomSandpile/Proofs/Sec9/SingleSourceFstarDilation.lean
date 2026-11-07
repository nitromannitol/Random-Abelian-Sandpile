import RandomSandpile.Proofs.Sec9.SingleSourceFlatnessStar
import RandomSandpile.Proofs.Sec7.LimitObstacleGamma

/-!
# Theorem 9.2, `F*`-variant: minimality by dilation, the origin included

The minimality step
`SSLimitMinimalStarStmt` follows from the subsolution step `SSLimitSubStarStmt`, the support
of the limits `SSLimitSupportStmt` and the Crandall-Ishii-Lions comparison principle
`ShiftComparisonStmt`; the origin step (O*) `SSOriginStarStmt` of
`Proofs/Sec9/SingleSourceFlatnessStar.lean` is not needed.

Let `U = v + G` be a subsequential limit and `W = w + G` with `w` in the `F*`-obstacle set. For
`λ > 1` the dilation `W_λ(x) = λ² W(x/λ)` is again a viscosity supersolution of
`F*(D²W) ≥ 0` off the origin (`viscFromBelowGE_dilate`: a quadratic touching `W_λ` from below at `x`
pulls back to a quadratic with the same Hessian touching `W` from below at `x/λ`). Since
`λ² G(x/λ) ≥ λ^d G(x)` (`pow_mul_fundamentalSolution_le`; equality for `d ≥ 3`, an extra
`(λ²/2π) log λ` for `d = 2`) and `G → ∞` at the origin (`fundamentalSolution_large`),
`W_λ - U ≥ λ² w(x/λ) - v(x) + (λ^d - 1) G(x) → ∞` as `x → 0`. Comparison on
`D = {U > 0} ∩ (B_R ∖ B̄_ρ)`, whose closure avoids the origin, gives `U ≤ W_λ` off the origin;
`λ ↓ 1` gives `v ≤ w` off the origin, and continuity gives it at the origin.

* `ssLimitMinimalStar_of_sub`:, support, comparison ⟹.
* `singleSourceTheoremStar_of_sub`: `SingleSourceTheoremStarStmt` from compactness, outer bound
  `SSOuterBoundStmt`, and the comparison principle.
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceFstar

variable {d : ℕ}

/-! ### The fundamental solution under dilations and near the origin -/

/-- `λ^d G(x) ≤ λ² G(x/λ)` for `λ ≥ 1`, `x ≠ 0` (equality for `d ≥ 3`; for `d = 2` the
difference is `(λ²/2π) log λ ≥ 0`). -/
theorem pow_mul_fundamentalSolution_le {t : ℝ} (ht : 1 ≤ t) {x : Rd d} (hx : x ≠ 0) :
    t ^ d * fundamentalSolution d x ≤ t ^ 2 * fundamentalSolution d (t⁻¹ • x) := by
  have ht0 : 0 < t := by linarith
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hnorm : ‖t⁻¹ • x‖ = t⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)]
  by_cases h2 : d = 2
  · have htd : t ^ d = t ^ 2 := by rw [h2]
    simp only [fundamentalSolution, if_pos h2]
    rw [htd, hnorm, Real.log_mul (inv_ne_zero ht0.ne') hn.ne', Real.log_inv]
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
    have hc : 0 ≤ t ^ 2 * (1 / (2 * Real.pi)) * Real.log t :=
      mul_nonneg (by positivity) hlog
    have e : t ^ 2 * (-(1 / (2 * Real.pi)) * (-Real.log t + Real.log ‖x‖)) =
        t ^ 2 * (-(1 / (2 * Real.pi)) * Real.log ‖x‖) +
          t ^ 2 * (1 / (2 * Real.pi)) * Real.log t := by ring
    rw [e]
    linarith
  · simp only [fundamentalSolution, if_neg h2]
    have key : t ^ 2 * (t⁻¹ * ‖x‖) ^ (2 - (d : ℝ)) = t ^ d * ‖x‖ ^ (2 - (d : ℝ)) := by
      rw [Real.mul_rpow (inv_nonneg.2 ht0.le) hn.le, Real.inv_rpow ht0.le,
        ← Real.rpow_neg ht0.le]
      have h1 : t ^ 2 * t ^ (-(2 - (d : ℝ))) = t ^ d := by
        rw [← Real.rpow_natCast t d, ← Real.rpow_two, ← Real.rpow_add ht0]
        congr 1
        ring
      calc t ^ 2 * (t ^ (-(2 - (d : ℝ))) * ‖x‖ ^ (2 - (d : ℝ)))
          = (t ^ 2 * t ^ (-(2 - (d : ℝ)))) * ‖x‖ ^ (2 - (d : ℝ)) := by ring
        _ = t ^ d * ‖x‖ ^ (2 - (d : ℝ)) := by rw [h1]
    apply le_of_eq
    rw [hnorm, mul_div_assoc', mul_div_assoc', key]

/-- `G(x) → +∞` as `x → 0`: for every `T` there is `ρ > 0` with `G ≥ T` on `0 < |x| ≤ ρ`. -/
theorem fundamentalSolution_large (hd : 2 ≤ d) (T : ℝ) :
    ∃ ρ > 0, ∀ x : Rd d, x ≠ 0 → ‖x‖ ≤ ρ → T ≤ fundamentalSolution d x := by
  by_cases h2 : d = 2
  · refine ⟨Real.exp (-(2 * Real.pi * T)), Real.exp_pos _, fun x hx hxρ => ?_⟩
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h := Real.log_le_log hn hxρ
    rw [Real.log_exp] at h
    simp only [fundamentalSolution, if_pos h2]
    have hpi : 0 < 2 * Real.pi := by positivity
    have e : -(1 / (2 * Real.pi)) * (-(2 * Real.pi * T)) = T := by
      rw [neg_mul_neg, ← mul_assoc, one_div_mul_cancel hpi.ne', one_mul]
    calc T = -(1 / (2 * Real.pi)) * (-(2 * Real.pi * T)) := e.symm
      _ ≤ -(1 / (2 * Real.pi)) * Real.log ‖x‖ :=
          mul_le_mul_of_nonpos_left h (by rw [neg_nonpos]; positivity)
  · have hd3 : 3 ≤ d := by omega
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    have hω := unitBallVolume_pos (d := d) (by omega)
    have hcpos : 0 < (d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d :=
      mul_pos (mul_pos (by linarith) (by linarith)) hω
    refine ⟨min 1 (((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d) * (|T| + 1))⁻¹,
      lt_min one_pos (by positivity), fun x hx hxρ => ?_⟩
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hx1 : ‖x‖ ≤ 1 := hxρ.trans (min_le_left _ _)
    have hx2 : ‖x‖ ≤ (((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d) * (|T| + 1))⁻¹ :=
      hxρ.trans (min_le_right _ _)
    simp only [fundamentalSolution, if_neg h2]
    have h1 : ‖x‖ ^ (-1 : ℝ) ≤ ‖x‖ ^ (2 - (d : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hn hx1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2' : ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d) * (|T| + 1) ≤ ‖x‖⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hn]
      exact hx2
    rw [le_div_iff₀ hcpos]
    have hT : T ≤ |T| + 1 := by linarith [le_abs_self T]
    calc T * ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d)
        ≤ (|T| + 1) * ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d) :=
          mul_le_mul_of_nonneg_right hT hcpos.le
      _ = ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d) * (|T| + 1) := mul_comm _ _
      _ ≤ ‖x‖⁻¹ := h2'
      _ ≤ ‖x‖ ^ (2 - (d : ℝ)) := h1

/-! ### Dilations of supersolutions -/

/-- **Dilation of a viscosity supersolution.** If `F*(D²W) ≥ 0` off the origin (tested from below),
then so does `W_λ(x) = λ² W(x/λ)`, `λ > 0`: a quadratic with Hessian `D²φ(x) - κI` touching `W_λ`
from below at `x` (`touch_below_of_isLocalMin`) pulls back to a quadratic with the same Hessian
touching `W` from below at `x/λ`, so `F*(D²φ(x) - κI) ≥ 0` for every `κ > 0`, and the shift
identity `F*(M - κI) = F*(M) + dκ` concludes. -/
theorem viscFromBelowGE_dilate (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) {W : Rd d → ℝ}
    (hW : ViscFromBelowGE (effOpStar E) {x | x ≠ 0} W) {t : ℝ} (ht : 0 < t) :
    ViscFromBelowGE (effOpStar E) {x | x ≠ 0} (fun x => t ^ 2 * W (t⁻¹ • x)) := by
  intro x hx φ hφ hmin
  have hx0 : x ≠ 0 := hx
  have hHs : (hessian φ x).IsSymm := hessian_isSymm_of_contDiffAt hφ
  have key : ∀ κ : ℝ, 0 < κ →
      0 ≤ effOpStar E (hessian φ x - κ • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    intro κ hκ
    have htouch := touch_below_of_isLocalMin hφ hmin hκ
    have hY : (hessian φ x - κ • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
      hHs.sub (Matrix.isSymm_one.smul κ)
    have hx₁ : t⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero ht.ne') hx0
    refine ViscFromBelowGE.le_of_touch hW hY (b := t⁻¹ • x)
      (q := t⁻¹ • (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x)) hx₁ ?_
    have hcont : Tendsto (fun y : Rd d => t • y) (𝓝 (t⁻¹ • x)) (𝓝 x) := by
      have h := (continuous_const_smul t).tendsto (t⁻¹ • x)
      rwa [smul_inv_smul₀ ht.ne'] at h
    filter_upwards [hcont.eventually htouch] with y hy
    have hy' : t ^ 2 * W (t⁻¹ • x) +
        inner ℝ ((InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x)) (t • y - x) +
        qM (hessian φ x - κ • (1 : Matrix (Fin d) (Fin d) ℝ)) (t • y - x) ≤
        t ^ 2 * W (t⁻¹ • (t • y)) := hy
    rw [inv_smul_smul₀ ht.ne'] at hy'
    have e1 : t • y - x = t • (y - t⁻¹ • x) := by rw [smul_sub, smul_inv_smul₀ ht.ne']
    rw [e1, real_inner_smul_right, qM_smul] at hy'
    rw [real_inner_smul_left]
    have ht2 : 0 < t ^ 2 := by positivity
    have htt : t ^ 2 * t⁻¹ = t := by rw [sq, mul_assoc, mul_inv_cancel₀ ht.ne', mul_one]
    refine le_of_mul_le_mul_left ?_ ht2
    calc t ^ 2 * (W (t⁻¹ • x) +
          t⁻¹ * inner ℝ ((InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x))
            (y - t⁻¹ • x) +
          qM (hessian φ x - κ • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - t⁻¹ • x))
        = t ^ 2 * W (t⁻¹ • x) +
          (t ^ 2 * t⁻¹) * inner ℝ ((InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x))
            (y - t⁻¹ • x) +
          t ^ 2 * qM (hessian φ x - κ • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - t⁻¹ • x) := by
          ring
      _ ≤ t ^ 2 * W y := by rw [htt]; exact hy'
  -- `F*(D²φ(x) - κI) = F*(D²φ(x)) + dκ`
  have hshift : ∀ κ : ℝ, effOpStar E (hessian φ x - κ • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      effOpStar E (hessian φ x) + d * κ := by
    intro κ
    have h := effOpStar_add_smul_one hd E hE hHs (-κ)
    rw [neg_smul, ← sub_eq_add_neg] at h
    rw [h]
    ring
  by_contra hneg
  have hlt : effOpStar E (hessian φ x) < 0 := not_le.1 hneg
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h := key (-(effOpStar E (hessian φ x)) / (2 * d)) (div_pos (by linarith) (by positivity))
  rw [hshift] at h
  have e : (d : ℝ) * (-(effOpStar E (hessian φ x)) / (2 * d)) =
      -(effOpStar E (hessian φ x)) / 2 := by
    rw [mul_div_assoc', mul_comm (2 : ℝ) d, mul_div_mul_left _ _ hdpos.ne']
  rw [e] at h
  linarith

/-! ### Minimality by dilation -/

/-- **Step without an origin step**:, the support of the limits and the comparison
principle give `v ≤ w` on all of `ℝ^d` for every subsequential limit `v + G` and every member `w`
of the `F*`-obstacle set. -/
theorem ssLimitMinimalStar_of_sub (hS : SSLimitSubStarStmt) (hB : SSLimitSupportStmt)
    (hCIL : ShiftComparisonStmt) : SSLimitMinimalStarStmt := by
  intro d hd E hmax
  have hd1 : 1 ≤ d := by omega
  have hE : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hmax]; omega
  filter_upwards [hS d hd E hmax, hB d hd E hmax] with η hSη hBη
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

/-- **Theorem 9.2, `F*`-variant**, from compactness, outer bound, the subsolution step
(S*) and the comparison principle: no origin step. -/
theorem singleSourceTheoremStar_of_sub (hComp : SSCompactnessStmt) (hOB : SSOuterBoundStmt)
    (hS : SSLimitSubStarStmt) (hCIL : ShiftComparisonStmt) : SingleSourceTheoremStarStmt :=
  singleSourceTheoremStar_of_compactness_minimal hComp
    (ssLimitMinimalStar_of_sub hS (ssLimitSupport_of_outerBound hOB) hCIL)

end SingleSourceFstar

end RandomSandpile

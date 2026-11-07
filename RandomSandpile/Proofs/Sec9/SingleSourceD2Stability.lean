import RandomSandpile.Proofs.Sec9.SingleSourceD2Approx

/-!
# Theorem 9.2 in dimension two: stability of supersolutions

`viscSuperStability : ViscSuperStabilityStmt` (Crandall-Ishii-Lions Lemma 6.1, Remarks 6.2-6.3, in
the form of SIMPLE-PROOF §7.4). Let `w - φ` have a local minimum at `x`, `H = D²φ(x)`. For `κ > 0`
the quadratic `Q` with Hessian `H - 2κI` touching `w` from below at `x` is strict:
`w - Q ≥ (κ/2)|y - x|²` on a small ball `B̄_r(x)`. For `n` large, `|u_n - w| < κr²/8` there, so
`u_n - Q` attains its minimum over the ball in the interior, and the supersolution property of
`u_n` gives `F_n(H - 2κI) ≥ 0`. Letting `n → ∞` and then `κ → 0` (continuity of `F` on symmetric
matrices) gives `F(H) ≥ 0`. Only quadratic tests are used, so no convergence of Hessians at nearby
points is needed.
-/

noncomputable section

open MeasureTheory Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

/-- The strict quadratic minorant step: for `n` large, `F_n(M) ≥ 0`. -/
theorem eventually_nonneg_of_strict {V : Set (Rd 2)} (hV : IsOpen V)
    {Fn : ℕ → Matrix (Fin 2) (Fin 2) ℝ → ℝ} {u : ℕ → Rd 2 → ℝ} {w : Rd 2 → ℝ}
    (huc : ∀ n, ContinuousOn (u n) V) (hconv : TendstoLocallyUniformlyOn u w atTop V)
    (hsup : ∀ n, ViscFromBelowGE (Fn n) V (u n)) {x p : Rd 2} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hMs : M.IsSymm) {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hsubV : closedBall x r ⊆ V)
    (hgap : ∀ y ∈ closedBall x r,
      κ / 2 * ‖y - x‖ ^ 2 ≤ w y - (w x + innerSL ℝ p (y - x) + qM M (y - x))) :
    ∀ᶠ n in atTop, 0 ≤ Fn n M := by
  set Q : Rd 2 → ℝ := fun y => w x + innerSL ℝ p (y - x) + qM M (y - x) with hQ
  have hQc : Continuous Q := (contDiff_paraboloid (n := 0) (w x) p x M).continuous
  have hQx : Q x = w x := by simp [hQ, qM]
  have hcK := (tendstoLocallyUniformlyOn_iff_forall_isCompact hV).1 hconv (closedBall x r) hsubV
    (isCompact_closedBall x r)
  set δ : ℝ := κ * r ^ 2 / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hcK δ hδ0] with n hclose
  have hcont : ContinuousOn (fun y => u n y - Q y) (closedBall x r) :=
    ((huc n).mono hsubV).sub hQc.continuousOn
  obtain ⟨xn, hxn, hmin⟩ := (isCompact_closedBall x r).exists_isMinOn
    ⟨x, mem_closedBall_self hr.le⟩ hcont
  have hx0 : x ∈ closedBall x r := mem_closedBall_self hr.le
  have hxn_int : xn ∈ ball x r := by
    by_contra hnot
    have hd : r ≤ ‖xn - x‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hnot
      exact hnot
    have h1 := hclose xn hxn
    have h2 := hclose x hx0
    rw [dist_eq_norm, Real.norm_eq_abs] at h1 h2
    have h3 := hgap xn hxn
    have h4 : u n xn - Q xn ≤ u n x - Q x := hmin hx0
    have h5 : r ^ 2 ≤ ‖xn - x‖ ^ 2 := pow_le_pow_left₀ hr.le hd 2
    have h6 : κ / 2 * r ^ 2 ≤ κ / 2 * ‖xn - x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    rw [hQx] at h4
    have a1 := (abs_lt.1 h1).2
    have a2 := (abs_lt.1 h2).1
    have h3' : κ / 2 * ‖xn - x‖ ^ 2 ≤ w xn - Q xn := h3
    nlinarith
  have hloc : IsLocalMin (fun y => u n y - Q y) xn :=
    hmin.isLocalMin (Filter.mem_of_superset (isOpen_ball.mem_nhds hxn_int) ball_subset_closedBall)
  have h := hsup n xn (hsubV hxn) Q (contDiff_paraboloid (w x) p x M).contDiffAt hloc
  have hHQ : hessian Q xn = M := hessian_quadratic _ _ _ hMs xn
  rwa [hHQ] at h

/-- ** Stability of supersolutions.** -/
theorem viscSuperStability : ViscSuperStabilityStmt := by
  intro V hV F Fn u w hFc hFn huc _hwc hconv hsup x hx φ hφ hmin
  set H := hessian φ x
  have hHs : H.IsSymm := hessian_isSymm_of_contDiffAt hφ
  have key : ∀ κ : ℝ, 0 < κ → 0 ≤ F (H + (-(2 * κ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    intro κ hκ
    set M := H + (-(2 * κ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
    have hMs : M.IsSymm := hHs.add (Matrix.isSymm_one.smul _)
    have htouch := touch_below_of_isLocalMin hφ hmin hκ
    set p := (InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x)
    obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff_ball.1 (htouch.and (hV.mem_nhds hx))
    have hr : 0 < r₀ / 2 := half_pos hr₀
    have hsb : closedBall x (r₀ / 2) ⊆ ball x r₀ := closedBall_subset_ball (half_lt_self hr₀)
    have hsubV : closedBall x (r₀ / 2) ⊆ V := fun y hy => (hball y (hsb hy)).2
    have hgap : ∀ y ∈ closedBall x (r₀ / 2),
        κ / 2 * ‖y - x‖ ^ 2 ≤ w y - (w x + innerSL ℝ p (y - x) + qM M (y - x)) := by
      intro y hy
      have h1 := (hball y (hsb hy)).1
      have e0 : H - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
          H + (-κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        rw [neg_smul, sub_eq_add_neg]
      have e1 : qM (H - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - x) =
          qM H (y - x) + -κ / 2 * ‖y - x‖ ^ 2 := by
        rw [e0, qM_add_smul_one]
      have e2 : qM M (y - x) = qM H (y - x) + -(2 * κ) / 2 * ‖y - x‖ ^ 2 :=
        qM_add_smul_one H _ (y - x)
      rw [e1] at h1
      rw [e2, innerSL_apply_apply]
      linarith
    have hev := eventually_nonneg_of_strict hV huc hconv hsup hMs hr hκ hsubV hgap
    by_contra hneg
    have hlt : F M < 0 := not_le.mp hneg
    obtain ⟨n, hn1, hn2⟩ := (hev.and (hFn (-(F M) / 2) (by linarith))).exists
    have := abs_le.1 (hn2 M hMs)
    linarith [this.1, this.2]
  have hg : Continuous fun κ : ℝ => H + (-(2 * κ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    fun_prop
  have hlim : Tendsto (fun κ : ℝ => F (H + (-(2 * κ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (𝓝[>] 0) (𝓝 (F H)) := by
    have h1 : Tendsto (fun κ : ℝ => H + (-(2 * κ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (𝓝[>] 0)
        (𝓝[{M : Matrix (Fin 2) (Fin 2) ℝ | M.IsSymm}] H) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun κ =>
        hHs.add (Matrix.isSymm_one.smul _)⟩
      have h := hg.tendsto 0
      simp only [mul_zero, neg_zero, zero_smul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact (hFc H hHs).tendsto.comp h1
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun κ hκ => key κ hκ)

end SingleSourceD2

end RandomSandpile

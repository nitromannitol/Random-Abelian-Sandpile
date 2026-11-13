import RandomSandpile.Proofs.Sec9.SingleSourceFlatnessStar
import RandomSandpile.Proofs.Sec9.OpenBoundaryComparison
import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasicFinal
import RandomSandpile.Proofs.Sec5.SubadditiveErgodicFinal

/-!
# Theorem 9.2: minimality of the single-source limits

Target: `SSLimitMinimalStmt` (`Steps/Sec9/SingleSource.lean`). The obstacle set `singleSourceObstacleSet` needs no constraint at the origin.
The origin is handled here by the scaling `W_s(x) = s² W(x / s)`, `s > 1`, not by a removable-singularity argument:

* the constraint `F̄_η(D²W) ≥ 0` off the origin, tested from below, is invariant under
  `W ↦ W_s` (Hessians of test functions are preserved, `viscFromBelowGE_rescale`);
* for `W = w + G`, `s² G(x / s) ≥ s² G(x)` (`G` is radially nonincreasing,
  `fundamentalSolution_le_of_norm_le`) and `G(x) → +∞` as `x → 0`
  (`exists_le_fundamentalSolution`), so `W_s - (v + G) → +∞` at the origin;
* on the bounded open set `{x ≠ 0 : v + G - W_s > m}`, which therefore stays away from the
  origin, the Crandall-Ishii-Lions comparison principle (`ShiftComparisonStmt`) applies to the
  subsolution `v + G` (step, `SSLimitSubsolutionStmt`) and the supersolution `W_s + m`;
* `v + G ≤ W_s` off the origin for every `s > 1`; letting `s ↓ 1` and using the continuity of
  `v`, `w` gives `v ≤ w` everywhere (`le_of_scaled_comparison`).

Main results:
* `SSLimitSubsolutionStmt` (step, open): the limits are viscosity subsolutions of
  `F̄_η(D²u) ≤ 0` where they are positive, off the origin.
* `ssLimitMinimal_of_steps`: `SSLimitMinimalStmt` from (S), the support of the limits
  (`SSLimitSupportStmt`) and the comparison principle.
* `ssLimitMinimal_of_outerBound`: the same from (S), the outer bound `SSOuterBoundStmt`
  and Alexandrov's theorem.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric

namespace RandomSandpile

open EffectiveOperatorBasic

variable {d : ℕ}

namespace SingleSourceLimitMinimal

/-! ### Rescaling of test functions -/

/-- The Hessian of `y ↦ c φ(s y)` at `y₀` is `c s² D²φ(s y₀)`. -/
theorem hessian_const_mul_comp_smul {φ : Rd d → ℝ} {y₀ : Rd d} (c s : ℝ)
    (hφ : ContDiffAt ℝ 2 φ (s • y₀)) :
    hessian (fun y => c * φ (s • y)) y₀ = (c * s ^ 2) • hessian φ (s • y₀) := by
  have hL : ∀ y : Rd d, HasFDerivAt (fun z : Rd d => s • z)
      (s • ContinuousLinearMap.id ℝ (Rd d)) y := fun y => (hasFDerivAt_id y).const_smul s
  have hev : ∀ᶠ y in 𝓝 (s • y₀), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hcont : ContinuousAt (fun y : Rd d => s • y) y₀ := (continuous_const_smul s).continuousAt
  have hev' : ∀ᶠ y in 𝓝 y₀, DifferentiableAt ℝ φ (s • y) := Filter.Tendsto.eventually hcont hev
  have h1 : fderiv ℝ (fun y => c * φ (s • y)) =ᶠ[𝓝 y₀]
      fun y => (c * s) • fderiv ℝ φ (s • y) := by
    filter_upwards [hev'] with y hy
    have hcomp : HasFDerivAt (fun z : Rd d => φ (s • z))
        ((fderiv ℝ φ (s • y)).comp (s • ContinuousLinearMap.id ℝ (Rd d))) y :=
      hy.hasFDerivAt.comp y (hL y)
    rw [(hcomp.const_mul c).fderiv]
    refine ContinuousLinearMap.ext fun h => ?_
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    ring
  have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (s • y₀)) (s • y₀) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt (fun y => (c * s) • fderiv ℝ φ (s • y))
      ((c * s) • (fderiv ℝ (fderiv ℝ φ) (s • y₀)).comp (s • ContinuousLinearMap.id ℝ (Rd d)))
      y₀ :=
    (hD.comp y₀ (hL y₀)).const_smul (c * s)
  ext i j
  rw [hessian_apply, h1.fderiv_eq, h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, Matrix.smul_apply, hessian_apply]
  ring

/-- `F(D²W) ≥ 0` off the origin, tested from below, is invariant under `W ↦ s² W(·/s)`. -/
theorem viscFromBelowGE_rescale {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {W : Rd d → ℝ}
    (hW : ViscFromBelowGE F {x | x ≠ 0} W) {s : ℝ} (hs : 0 < s) :
    ViscFromBelowGE F {x | x ≠ 0} (fun x => s ^ 2 * W (s⁻¹ • x)) := by
  intro x hx φ hφ hloc
  obtain ⟨y₀, rfl⟩ : ∃ y₀ : Rd d, x = s • y₀ :=
    ⟨s⁻¹ • x, by rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]⟩
  have hy₀ : y₀ ≠ 0 := fun h => hx (by rw [h, smul_zero])
  have hs2 : 0 < s ^ 2 := by positivity
  have hψ : ContDiffAt ℝ 2 (fun y => (s ^ 2)⁻¹ * φ (s • y)) y₀ :=
    contDiffAt_const.mul (hφ.comp y₀ (contDiffAt_id.const_smul s))
  have hloc' : IsLocalMin (fun y => W y - (s ^ 2)⁻¹ * φ (s • y)) y₀ := by
    have hg : ContinuousAt (fun y : Rd d => s • y) y₀ := (continuous_const_smul s).continuousAt
    unfold IsLocalMin IsMinFilter at hloc ⊢
    have h1 := Filter.Tendsto.eventually hg hloc
    filter_upwards [h1] with y hy
    simp only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at hy
    have e1 : ∀ z : Rd d, W z - (s ^ 2)⁻¹ * φ (s • z) =
        (s ^ 2)⁻¹ * (s ^ 2 * W z - φ (s • z)) := by
      intro z
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hs2.ne', one_mul]
    rw [e1, e1]
    exact mul_le_mul_of_nonneg_left hy (inv_nonneg.2 hs2.le)
  have h := hW y₀ hy₀ _ hψ hloc'
  rwa [hessian_const_mul_comp_smul _ _ hφ, inv_mul_cancel₀ hs2.ne', one_smul] at h

/-- Adding a constant and shrinking the set preserve `F(D²W) ≥ 0` tested from below. -/
theorem viscFromBelowGE_add_const_mono {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U V : Set (Rd d)}
    {W : Rd d → ℝ} (hW : ViscFromBelowGE F U W) (hVU : V ⊆ U) (m : ℝ) :
    ViscFromBelowGE F V (fun x => W x + m) := by
  intro x hx φ hφ hloc
  have hloc' : IsLocalMin (fun y => W y - (φ y - m)) x := by
    refine hloc.congr (Eventually.of_forall fun y => ?_); ring
  have hφ' : ContDiffAt ℝ 2 (fun y => φ y - m) x := hφ.sub contDiffAt_const
  have h := hW x (hVU hx) (fun y => φ y - m) hφ' hloc'
  have hH : hessian (fun y => φ y - m) x = hessian φ x := by
    unfold hessian
    congr 1
    ext i j
    have : fderiv ℝ (fun y => φ y - m) = fderiv ℝ φ := by
      funext y; exact fderiv_sub_const _
    rw [this]
  rwa [hH] at h

/-! ### The fundamental solution near the origin -/

/-- `G` is radially nonincreasing (`d ≥ 2`). -/
theorem fundamentalSolution_le_of_norm_le (hd : 2 ≤ d) {x y : Rd d} (hy : y ≠ 0)
    (hxy : ‖y‖ ≤ ‖x‖) : fundamentalSolution d x ≤ fundamentalSolution d y := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  by_cases h2 : d = 2
  · simp only [fundamentalSolution, ite_eq_left h2]
    have hlog : Real.log ‖y‖ ≤ Real.log ‖x‖ := Real.log_le_log hy0 hxy
    have hc : 0 < 1 / (2 * Real.pi) := by positivity
    have := mul_le_mul_of_nonneg_left hlog hc.le
    linarith
  · simp only [fundamentalSolution, ite_eq_right h2]
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
    have hc : 0 < (d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d :=
      mul_pos (mul_pos (by linarith) (by linarith)) (unitBallVolume_pos (by omega))
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hy0 hxy (by linarith)) hc.le

/-- `G(x) → +∞` as `x → 0` (`d ≥ 2`). -/
theorem exists_le_fundamentalSolution (hd : 2 ≤ d) (B : ℝ) :
    ∃ ρ > 0, ∀ x : Rd d, x ≠ 0 → ‖x‖ < ρ → B ≤ fundamentalSolution d x := by
  by_cases h2 : d = 2
  · refine ⟨Real.exp (-(2 * Real.pi) * B), Real.exp_pos _, fun x hx hxρ => ?_⟩
    simp only [fundamentalSolution, ite_eq_left h2]
    have hlt : Real.log ‖x‖ < -(2 * Real.pi) * B := by
      have := Real.log_lt_log (norm_pos_iff.2 hx) hxρ
      rwa [Real.log_exp] at this
    have hπ : 0 < 2 * Real.pi := by positivity
    have hc : 0 < 1 / (2 * Real.pi) := by positivity
    have hcc : 1 / (2 * Real.pi) * (2 * Real.pi) = 1 := one_div_mul_cancel hπ.ne'
    have hprod := mul_lt_mul_of_pos_left hlt hc
    have e : 1 / (2 * Real.pi) * (-(2 * Real.pi) * B) = -B := by
      rw [neg_mul, mul_neg, ← mul_assoc, hcc, one_mul]
    rw [e] at hprod
    linarith
  · have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
    have hc : 0 < (d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d :=
      mul_pos (mul_pos (by linarith) (by linarith)) (unitBallVolume_pos (by omega))
    have hB' : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hBc : 0 < max B 1 * ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d) := mul_pos hB' hc
    have hne : (2 - (d : ℝ)) ≠ 0 := (by linarith : 2 - (d : ℝ) < 0).ne
    refine ⟨(max B 1 * ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d)) ^ (1 / (2 - (d : ℝ))),
      Real.rpow_pos_of_pos hBc _, fun x hx hxρ => ?_⟩
    simp only [fundamentalSolution, ite_eq_right h2]
    have hpow : ((max B 1 * ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d)) ^
        (1 / (2 - (d : ℝ)))) ^ (2 - (d : ℝ)) =
        max B 1 * ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d) := by
      rw [← Real.rpow_mul hBc.le, one_div_mul_cancel hne, Real.rpow_one]
    have hle := Real.rpow_le_rpow_of_nonpos (norm_pos_iff.2 hx) hxρ.le
      (by linarith : 2 - (d : ℝ) ≤ 0)
    rw [hpow] at hle
    rw [le_div_iff₀ hc]
    calc B * ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d)
        ≤ max B 1 * ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hc.le
      _ ≤ ‖x‖ ^ (2 - (d : ℝ)) := hle

/-! ### The comparison with the rescaled competitors -/

/-- **Comparison with `W_s = s² W(·/s)`**, `W = w + G`, `s > 1`: if `v + G` is a subsolution of
`F(D²u) ≤ 0` where it is positive, vanishes outside a ball, and `w + G ≥ 0` is a supersolution of
`F(D²u) ≥ 0` off the origin, then `v + G ≤ W_s` off the origin. -/
theorem scaled_comparison (hd : 2 ≤ d) {F : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hDE : DegenerateElliptic F)
    (hshift : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ t : ℝ,
      F (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) = F M - d * t)
    (hCIL : ShiftComparisonStmt) {v w : Rd d → ℝ} (hvc : Continuous v) (hwc : Continuous w)
    (hsub : ViscFromAboveLE F {x | x ≠ 0 ∧ 0 < v x + fundamentalSolution d x}
      (fun x => v x + fundamentalSolution d x))
    (hR : ∃ R : ℝ, ∀ x : Rd d, R < ‖x‖ → v x + fundamentalSolution d x = 0)
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
  obtain ⟨R, hR⟩ := hR
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
      have hu0 := hR y hyR
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
      have hu0 := hR x₁ hxR
      have := hW0 x₁ hx₁
      linarith
  have key : v x₁ + fundamentalSolution d x₁ ≤
      s ^ 2 * (w (s⁻¹ • x₁) + fundamentalSolution d (s⁻¹ • x₁)) + m :=
    hcmp x₁ (subset_closure hx₁D)
  rw [hm_def] at key
  linarith

/-- **Deterministic core of step.** Under the hypotheses of `scaled_comparison`, `v ≤ w`
everywhere: let `s ↓ 1` off the origin, then use continuity at the origin. -/
theorem le_of_scaled_comparison (hd : 2 ≤ d) {F : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hDE : DegenerateElliptic F)
    (hshift : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ t : ℝ,
      F (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) = F M - d * t)
    (hCIL : ShiftComparisonStmt) {v w : Rd d → ℝ} (hvc : Continuous v) (hwc : Continuous w)
    (hsub : ViscFromAboveLE F {x | x ≠ 0 ∧ 0 < v x + fundamentalSolution d x}
      (fun x => v x + fundamentalSolution d x))
    (hR : ∃ R : ℝ, ∀ x : Rd d, R < ‖x‖ → v x + fundamentalSolution d x = 0)
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
        scaled_comparison hd hDE hshift hCIL hvc hwc hsub hR hwG hsup ht x hx
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

end SingleSourceLimitMinimal

open SingleSourceLimitMinimal

/-! ### Step and the reduction of step -/

/-- **Step: the limits are viscosity subsolutions of `F̄_η(D²u) ≤ 0` where they are positive**
(off the origin, tested from above), under flatness. Route (Theorem 1.1's
`InteriorMaxPrincipleStmt`, and `OpenInteriorMaxPrincipleStmt` for the open odometer): if `φ`
touches `u` from above at `x ≠ 0` with `u(x) > 0` and `F̄_η(D²φ(x)) > 0`, flatness
(`MuVanishFlatStmt`) gives `μ(l, D²φ(x)) = 0` for `0 < l < F̄_η(D²φ(x))`; Lemma 5.2 (perturbed
subsolutions) for the legal toppling `v_n` on `B_{rh}(h x) ∩ ℤ^d`, `h = n^{1/d}`, rescaling and
Lemma 5.5 give a maximum principle for `u - φ - q_l(· - x)` on small balls about `x`, contradicted
by its strict maximum at `x`. -/
def SSLimitSubsolutionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 → FlatEff E →
    ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
      ViscFromAboveLE (effOp E) {x : Rd d | x ≠ 0 ∧ 0 < u x} u

/-- **Step** (`SSLimitMinimalStmt`) from step, the support of the limits and the
Crandall-Ishii-Lions comparison principle; the origin is handled by the scaling
`W_s = s² W(·/s)` (`le_of_scaled_comparison`), so no constraint at the origin is needed.
Lemma 6.4(1) and the shift identity for `F̄_η` come from Lemma 5.5 (`muConvergence_unconditional`). -/
theorem ssLimitMinimal_of_steps (hS : SSLimitSubsolutionStmt) (hB : SSLimitSupportStmt)
    (hCIL : ShiftComparisonStmt) : SSLimitMinimalStmt := by
  intro d hd E hmax hflat
  have h64 := effectiveOperatorBasic_of_muConvergence muConvergence_unconditional
  have hDE : DegenerateElliptic (effOp E) := by
    obtain ⟨C, -, hC⟩ := h64 d hd E.ηmin E.ηmax
    intro X Y hX hY hXY
    exact (hC E rfl rfl X Y hX hY).1 hXY
  have hshift : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ t : ℝ,
      effOp E (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) = effOp E M - d * t :=
    fun M hM t => effOp_add_smul_one muConvergence_unconditional hd E hM t
  filter_upwards [hS d hd E hmax hflat, hB d hd E hmax] with η hSη hBη
  intro v hvc hv w hw x
  exact le_of_scaled_comparison hd hDE hshift hCIL hvc hw.1 (hSη _ hv) (hBη _ hv) hw.2.1 hw.2.2 x

/-- **Minimality of the limits** from the outer bound for the toppled sets (`SSOuterBoundStmt`,
Fey-Levine-Peres 2010, Theorem 1.1) and Alexandrov's theorem (`AlexandrovStmt`, through the comparison
principle `shiftComparison_of_alexandrov`). -/
theorem ssLimitMinimal_of_outerBound (hS : SSLimitSubsolutionStmt) (hOB : SSOuterBoundStmt)
    (hA : AlexandrovStmt) : SSLimitMinimalStmt :=
  ssLimitMinimal_of_steps hS (ssLimitSupport_of_outerBound hOB) (shiftComparison_of_alexandrov hA)

end RandomSandpile

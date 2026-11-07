import RandomSandpile.Proofs.Sec9.SingleSourceD2Steps
import RandomSandpile.Proofs.Sec9.SingleSourceMinPrinciple
import RandomSandpile.Proofs.Sec5.SubadditiveErgodicFinal
import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasicFinal
import RandomSandpile.Proofs.Sec7.MainTheoremViscEff
import RandomSandpile.Infra.Touching
import RandomSandpile.Infra.SupConvolution

/-!
# Theorem 9.2 in dimension two: the supersolution step

`viscFromBelowGE_effOp_of_noPosDef`: the starred limit `U* = v* + G` is a viscosity supersolution
of `F̄_η = 0` off the origin, from
* no positive definite lower test of `U*` at positive points,
* through D2-PROOF (4.4) (`effOp_nonneg_of_not_posDef`),
* a locally bounded weak Laplacian of `U*` off the origin,
* Pegden-Smart Proposition 2.5 on a ball, in the paraboloid form `PS25ParaboloidStmt`.

Route. Given a lower test `φ`
at `a ≠ 0` and `δ > 0`, the paraboloid `P` with matrix `D²φ(a) - 2δI` lies strictly below `U*` on
a small sphere around `a` and touches at `a`; PS 2.5 gives a positive-measure set of Peano points
`b` with `D²U*(b) > D²P`. Isolated zeros of `U*` are countable, so some such `b` is not one. At
`b`, `F*(D²U*(b)) ≥ 0` (supersolution) and `D²U*(b)` is not positive definite (by (F1) if
`U*(b) > 0`, otherwise because a positive definite Peano Hessian at a minimum makes `b` an isolated
zero); (4.4) gives `F̄(D²U*(b)) ≥ 0`, monotonicity `F̄(D²φ(a) - 2δI) ≥ 0`, and the shift
`F̄(D²φ(a)) ≥ -4δ`.
-/

noncomputable section

open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

/-- **Pegden-Smart Proposition 2.5 on a ball, paraboloid form.** If `u ∈ C(B̄_r(a))` is a weak solution of
`Δu = s`, `s ∈ L^∞`, in `B_r(a)`, and the paraboloid `P(x) = u(a) + L(x - a) + ½(x - a)ᵀX(x - a)`
lies strictly below `u` on `∂B_r(a)`, then the set of `b ∈ B_r(a)` at which `u` has a Peano
expansion with a symmetric matrix `Y > X` has positive measure. (From `PegdenSmartProp25Stmt`
applied to `(P - u)(a + r ·)`; proof in a later step.) -/
def PS25ParaboloidStmt : Prop :=
  ∀ (u s : Rd 2 → ℝ) (a : Rd 2) (r C : ℝ), 0 < r → ContinuousOn u (closedBall a r) →
    Measurable s → (∀ x, |s x| ≤ C) → IsWeakSolutionLaplace (ball a r) u s →
    ∀ (L : Rd 2 →L[ℝ] ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ), X.IsSymm →
      (∀ x ∈ sphere a r, u a + L (x - a) + qM X (x - a) < u x) →
      0 < volume {b : Rd 2 | b ∈ ball a r ∧ ∃ (p : Rd 2) (Y : Matrix (Fin 2) (Fin 2) ℝ),
        Y.IsSymm ∧ HasSecondOrderTaylorAt u b p Y ∧ (Y - X).PosDef}

/-- The starred limit has a locally bounded weak Laplacian off the origin. -/
def SSStarWeakLaplaceD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    LocWeakLaplaceBdd {x | x ≠ 0}
      (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x)

/-! ### Elementary lemmas -/

theorem qM_zero_right (M : Matrix (Fin 2) (Fin 2) ℝ) : qM M (0 : Rd 2) = 0 := by simp [qM]

/-- A positive definite `2 × 2` matrix has `q_Y(h) ≥ c|h|²` for some `c > 0`. -/
theorem exists_qM_ge_of_posDef {Y : Matrix (Fin 2) (Fin 2) ℝ} (hY : Y.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : Rd 2, c * ‖h‖ ^ 2 ≤ qM Y h := by
  have hne : (sphere (0 : Rd 2) 1).Nonempty :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨h₀, hh₀, hmin⟩ := (isCompact_sphere (0 : Rd 2) 1).exists_isMinOn hne
    (contDiff_qM Y (n := 0)).continuous.continuousOn
  have hn₀ : ‖h₀‖ = 1 := by simpa using hh₀
  have hpos : 0 < qM Y h₀ := by
    have hne0 : WithLp.ofLp h₀ ≠ 0 := by
      intro h0
      have h00 : ‖h₀‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        simp [h0]
      rw [h00] at hn₀
      exact zero_ne_one hn₀
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 hY).2 hne0
    simp only [star_trivial] at this
    simp only [qM]
    linarith
  refine ⟨qM Y h₀, hpos, fun h => ?_⟩
  by_cases h0 : h = 0
  · subst h0; simp [qM]
  · have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
    have hk : ‖h‖⁻¹ • h ∈ sphere (0 : Rd 2) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 := isMinOn_iff.mp hmin _ hk
    have h2 : qM Y h = ‖h‖ ^ 2 * qM Y (‖h‖⁻¹ • h) := by
      rw [qM_smul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn.ne', one_pow, one_mul]
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖h‖)]

/-- At a local minimum, the gradient of a second-order Peano expansion vanishes. -/
theorem taylor_grad_eq_zero_of_isLocalMin {u : Rd 2 → ℝ} {b p : Rd 2}
    {Y : Matrix (Fin 2) (Fin 2) ℝ} (hT : HasSecondOrderTaylorAt u b p Y) (hmin : IsLocalMin u b) :
    p = 0 := by
  by_contra hp
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp
  obtain ⟨r₁, hr₁, H₁⟩ := Metric.eventually_nhds_iff.1 hmin
  obtain ⟨r₂, hr₂, H₂⟩ := hT.bound (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |qM Y p| + ‖p‖ ^ 2 + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hKq : qM Y p + ‖p‖ ^ 2 ≤ K := by rw [hK]; linarith [le_abs_self (qM Y p)]
  have hm : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (min r₁ r₂ / (2 * (‖p‖ + 1))) (‖p‖ ^ 2 / (2 * K)) :=
    ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact lt_min (div_pos hm (by positivity)) (div_pos (pow_pos hpn 2) (mul_pos two_pos hK0))
  have ht1 : t * (2 * (‖p‖ + 1)) ≤ min r₁ r₂ := by
    have : t ≤ min r₁ r₂ / (2 * (‖p‖ + 1)) := by rw [ht]; exact min_le_left _ _
    rwa [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (‖p‖ + 1))] at this
  have ht2 : t * (2 * K) ≤ ‖p‖ ^ 2 := by
    have : t ≤ ‖p‖ ^ 2 / (2 * K) := by rw [ht]; exact min_le_right _ _
    rwa [le_div_iff₀ (mul_pos two_pos hK0)] at this
  have hnorm : ‖b + (-t) • p - b‖ < min r₁ r₂ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht0]
    nlinarith [mul_nonneg ht0.le (norm_nonneg p)]
  have h1 := H₁ (show dist (b + (-t) • p) b < r₁ by
    rw [dist_eq_norm]; exact lt_of_lt_of_le hnorm (min_le_left _ _))
  have h2 := H₂ _ (lt_of_lt_of_le hnorm (min_le_right _ _))
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, qM_smul, real_inner_smul_right,
    real_inner_self_eq_norm_sq, mul_pow, sq_abs] at h2
  have h3 := (abs_le.1 h2).2
  have h4 : t * ‖p‖ ^ 2 ≤ t ^ 2 * K := by
    nlinarith [mul_le_mul_of_nonneg_left hKq (sq_nonneg t)]
  have h5 : ‖p‖ ^ 2 ≤ t * K := by
    have : t * ‖p‖ ^ 2 ≤ t * (t * K) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  nlinarith [pow_pos hpn 2]

/-- The paraboloid `u(b) + p·(y - b) + q_{Y - ηI}(y - b)` touches `u` from below at a point `b` of
second-order Peano expansion `(p, Y)`, for `η > 0`. -/
theorem isLocalMin_sub_paraboloid_of_taylor {u : Rd 2 → ℝ} {b p : Rd 2}
    {Y : Matrix (Fin 2) (Fin 2) ℝ} (hT : HasSecondOrderTaylorAt u b p Y) {η : ℝ} (hη : 0 < η) :
    IsLocalMin (fun y => u y - (u b + innerSL ℝ p (y - b) +
      qM (Y + (-η) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - b))) b := by
  obtain ⟨ρ, hρ, hb⟩ := hT.bound (half_pos hη)
  refine Metric.eventually_nhds_iff.2 ⟨ρ, hρ, fun z hz => ?_⟩
  have hz' := hb z (by rw [← dist_eq_norm]; exact hz)
  simp only [sub_self, innerSL_apply_apply, inner_zero_right, qM_zero_right, add_zero]
  rw [qM_add_smul_one]
  have h1 := (abs_le.1 hz').1
  have h2 : 0 ≤ ‖z - b‖ ^ 2 := sq_nonneg _
  nlinarith

/-- The supersolution inequality at a Peano point: if `u` is a viscosity supersolution of `F = 0`
on `V ∋ b`, `F` has the shift identity, and `u` has a Peano expansion `(p, Y)` at `b`, then
`F(Y) ≥ 0`. -/
theorem nonneg_of_taylor_of_super {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {V : Set (Rd 2)}
    {u : Rd 2 → ℝ} (hsuper : ViscFromBelowGE F V u) (hshift : HasTraceShift F) {b p : Rd 2}
    (hb : b ∈ V) {Y : Matrix (Fin 2) (Fin 2) ℝ} (hYs : Y.IsSymm)
    (hT : HasSecondOrderTaylorAt u b p Y) : 0 ≤ F Y := by
  have key : ∀ η : ℝ, 0 < η → 0 ≤ F Y + 2 * η := by
    intro η hη
    have h := hsuper b hb _ (contDiff_paraboloid (u b) p b
      (Y + (-η) • (1 : Matrix (Fin 2) (Fin 2) ℝ))).contDiffAt
      (isLocalMin_sub_paraboloid_of_taylor hT hη)
    rw [hessian_paraboloid, hessian_qM_of_isSymm (hYs.add (Matrix.isSymm_one.smul _)),
      hshift Y hYs] at h
    linarith
  by_contra hneg
  have hneg' : F Y < 0 := not_le.mp hneg
  have := key (-(F Y) / 4) (by linarith)
  linarith

/-- A subset of `ℝ²` all of whose points are isolated in it is countable. -/
theorem countable_of_forall_isolated {J : Set (Rd 2)}
    (hJ : ∀ b ∈ J, ∃ ρ > 0, ∀ x ∈ J, dist x b < ρ → x = b) : J.Countable := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rd 2)
  have key : ∀ b : J, ∃ (q : D) (n : ℕ), dist (b : Rd 2) (q : Rd 2) < 1 / ((n : ℝ) + 1) ∧
      ∀ x ∈ J, dist x b < 2 / ((n : ℝ) + 1) → x = b := by
    intro b
    obtain ⟨ρ, hρ, hiso⟩ := hJ b b.2
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hρ)
    obtain ⟨q, hqD, hq⟩ := hDd.exists_dist_lt (b : Rd 2)
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    refine ⟨⟨q, hqD⟩, n, hq, fun x hx hxd => hiso x hx ?_⟩
    have h2 : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
    rw [h2] at hxd
    linarith
  choose f g hf using key
  haveI : Countable D := hDc.to_subtype
  have hinj : Function.Injective (fun b : J => (f b, g b)) := by
    intro b b' hbb'
    simp only [Prod.mk.injEq] at hbb'
    obtain ⟨hfb, hgb⟩ := hbb'
    apply Subtype.ext
    have h1 := (hf b).1
    have h2 := (hf b').1
    rw [hfb, hgb] at h1
    have hd : dist (b : Rd 2) b' < 2 / ((g b' : ℝ) + 1) := by
      calc dist (b : Rd 2) b' ≤ dist (b : Rd 2) (f b' : Rd 2) + dist (f b' : Rd 2) b' :=
            dist_triangle _ _ _
        _ < 1 / ((g b' : ℝ) + 1) + 1 / ((g b' : ℝ) + 1) := by
            rw [dist_comm (f b' : Rd 2)]; exact add_lt_add h1 h2
        _ = 2 / ((g b' : ℝ) + 1) := by ring
    exact (hf b').2 b b.2 hd
  exact Set.countable_coe_iff.mp hinj.countable

/-- Weak solutions restrict to smaller open sets. -/
theorem isWeakSolutionLaplace_mono {U V : Set (Rd 2)} {u s : Rd 2 → ℝ}
    (h : IsWeakSolutionLaplace U u s) (hVU : V ⊆ U) : IsWeakSolutionLaplace V u s :=
  fun φ hφ hc hsupp => h φ hφ hc (hsupp.trans hVU)

/-! ### The supersolution step -/

/-- **, deterministic core**: the supersolution inequality for `F̄_η` off the origin. -/
theorem viscFromBelowGE_effOp_of_noPosDef (hPS : PS25ParaboloidStmt)
    (hOP2 : EffOpEqStarOfNotPosDefD2Stmt) (E : RandomEnvironment 2)
    (hE : E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2)
    (hv : singleSourceObstacleSolutionStar E ∈ singleSourceObstacleSetStar E)
    (hF1 : NoPosDefLowerTest
      (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x))
    (hW : LocWeakLaplaceBdd {x | x ≠ 0}
      (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x)) :
    ViscFromBelowGE (effOp E) {x : Rd 2 | x ≠ 0}
      (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x) := by
  set U : Rd 2 → ℝ := fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x
    with hU
  have hE1 : E.ηmax ≤ 2 * ((2 : ℕ) : ℤ) - 1 := by rw [hE]; norm_num
  have hsuper : ViscFromBelowGE (effOpStar E) {x : Rd 2 | x ≠ 0} U :=
    (viscFromBelowMuStar_iff (by norm_num) E hE1 _ _).1 hv.2.2
  have hcont : ContinuousOn U {x : Rd 2 | x ≠ 0} :=
    hv.1.continuousOn.add (SingleSourceMin.continuousOn_fundamentalSolution 2)
  have hnn : ∀ x : Rd 2, x ≠ 0 → 0 ≤ U x := fun x hx => by
    have := hv.2.1 x hx
    simp only [hU]
    linarith
  have hshift : HasTraceShift (effOp E) := fun M hM t =>
    (effOp_add_smul_one muConvergence_unconditional le_rfl E hM t).trans (by norm_num)
  have hshiftStar : HasTraceShift (effOpStar E) := fun M hM t =>
    (effOpStar_add_smul_one (by norm_num) E hE1 hM t).trans (by norm_num)
  have hdeg : ∀ M N : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm → N.IsSymm → (N - M).PosSemidef →
      effOp E N ≤ effOp E M := by
    obtain ⟨C, -, hC⟩ := effectiveOperatorBasic_of_muConvergence muConvergence_unconditional 2
      le_rfl E.ηmin E.ηmax
    exact fun M N hM hN h => (hC E rfl rfl M N hM hN).1 h
  intro a ha φ hφ hmin
  have ha0 : a ≠ 0 := ha
  have hX0 : (hessian φ a).IsSymm := hessian_isSymm_of_contDiffAt hφ
  -- reduce to `F̄(D²φ(a) - 2δI) ≥ 0` for every `δ > 0`
  suffices key : ∀ δ : ℝ, 0 < δ →
      0 ≤ effOp E (hessian φ a + (-(2 * δ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) by
    by_contra hneg
    have hneg' : effOp E (hessian φ a) < 0 := not_le.mp hneg
    have h := key (-(effOp E (hessian φ a)) / 8) (by linarith)
    rw [hshift (hessian φ a) hX0] at h
    linarith
  intro δ hδ
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      X = hessian φ a + (-(2 * δ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := ⟨_, rfl⟩
  rw [← hXdef]
  have hXs : X.IsSymm := by rw [hXdef]; exact hX0.add (Matrix.isSymm_one.smul _)
  obtain ⟨L, hL⟩ : ∃ L : Rd 2 →L[ℝ] ℝ, L = fderiv ℝ φ a := ⟨_, rfl⟩
  -- the paraboloid lies below `U` with a quadratic gap near `a`
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ (half_pos hδ)
  obtain ⟨ε₁, hε₁, hloc⟩ := Metric.eventually_nhds_iff.1 hmin
  obtain ⟨r₀, hr₀, -, s, C, hsm, hsC, hweak⟩ := hW a ha
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hm : 0 < min (min ρ₁ ε₁) (min ‖a‖ r₀) := lt_min (lt_min hρ₁ hε₁) (lt_min hna hr₀)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (min ρ₁ ε₁) (min ‖a‖ r₀) / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact half_pos hm
  have hrm : r < min (min ρ₁ ε₁) (min ‖a‖ r₀) := by rw [hr]; linarith
  have hrle : ∀ y, dist y a ≤ r → dist y a < ρ₁ ∧ dist y a < ε₁ ∧ dist y a < ‖a‖ ∧
      dist y a < r₀ := by
    intro y hy
    have h1 : min (min ρ₁ ε₁) (min ‖a‖ r₀) ≤ min ρ₁ ε₁ := min_le_left _ _
    have h2 : min (min ρ₁ ε₁) (min ‖a‖ r₀) ≤ min ‖a‖ r₀ := min_le_right _ _
    have h3 := min_le_left ρ₁ ε₁
    have h4 := min_le_right ρ₁ ε₁
    have h5 := min_le_left ‖a‖ r₀
    have h6 := min_le_right ‖a‖ r₀
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hne0 : ∀ y, dist y a < ‖a‖ → y ≠ 0 := by
    intro y hy h0
    rw [h0, dist_zero_left] at hy
    exact lt_irrefl _ hy
  have hgap : ∀ y, dist y a ≤ r →
      U a + L (y - a) + qM X (y - a) + δ / 2 * ‖y - a‖ ^ 2 ≤ U y := by
    intro y hy
    obtain ⟨hy1, hy2, -, -⟩ := hrle y hy
    have hT' := hT y (by rw [← dist_eq_norm]; exact hy1)
    have hl : U a - φ a ≤ U y - φ y := hloc hy2
    rw [← hL] at hT'
    rw [hXdef, qM_add_smul_one]
    have := (abs_le.1 hT').1
    linarith
  have hcball : closedBall a r ⊆ {x : Rd 2 | x ≠ 0} := fun y hy =>
    hne0 y (hrle y (mem_closedBall.1 hy)).2.2.1
  have hballr : ball a r ⊆ ball a r₀ := fun y hy =>
    mem_ball.2 (hrle y (mem_ball.1 hy).le).2.2.2
  have hPSa := hPS U s a r C hr0 (hcont.mono hcball) hsm hsC
    (isWeakSolutionLaplace_mono hweak hballr) L X hXs
    (fun y hy => by
      have hy' : dist y a = r := mem_sphere.1 hy
      have h := hgap y hy'.le
      rw [← dist_eq_norm, hy'] at h
      have : 0 < δ / 2 * r ^ 2 := mul_pos (half_pos hδ) (pow_pos hr0 2)
      linarith)
  -- isolated zeros of `U` are negligible
  set I : Set (Rd 2) := {b | U b = 0 ∧ ∃ ρ > 0, ∀ x, dist x b < ρ → x ≠ b → U x ≠ 0}
  have hIc : I.Countable := by
    refine countable_of_forall_isolated fun b hb => ?_
    obtain ⟨-, ρ, hρ, hiso⟩ := hb
    refine ⟨ρ, hρ, fun x hx hxb => ?_⟩
    by_contra hne
    exact hiso x hxb hne hx.1
  have hI0 : volume I = 0 := hIc.measure_zero volume
  set S : Set (Rd 2) := {b : Rd 2 | b ∈ ball a r ∧ ∃ (p : Rd 2) (Y : Matrix (Fin 2) (Fin 2) ℝ),
    Y.IsSymm ∧ HasSecondOrderTaylorAt U b p Y ∧ (Y - X).PosDef}
  obtain ⟨b, hbS, hbI⟩ : ∃ b ∈ S, b ∉ I := by
    by_contra hcon
    have hsub : S ⊆ I := fun b hb => by
      by_contra hbI
      exact hcon ⟨b, hb, hbI⟩
    have h1 : volume S ≤ volume I := measure_mono hsub
    rw [hI0] at h1
    exact absurd hPSa (not_lt.2 h1)
  obtain ⟨hbr, p, Y, hYs, hTb, hYX⟩ := hbS
  have hb0 : b ≠ 0 := hne0 b (hrle b (mem_ball.1 hbr).le).2.2.1
  -- `F*(D²U(b)) ≥ 0`
  have hstar : 0 ≤ effOpStar E Y := nonneg_of_taylor_of_super hsuper hshiftStar hb0 hYs hTb
  -- `D²U(b)` is not positive definite
  have hnot : ¬ Y.PosDef := by
    intro hYpd
    obtain ⟨c, hc, hcY⟩ := exists_qM_ge_of_posDef hYpd
    rcases (hnn b hb0).lt_or_eq with hpos | hzero
    · have hmin' := isLocalMin_sub_paraboloid_of_taylor hTb (half_pos hc)
      refine hF1 b hb0 hpos _ (contDiff_paraboloid (U b) p b
        (Y + (-(c / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ))).contDiffAt hmin' ?_
      rw [hessian_paraboloid, hessian_qM_of_isSymm (hYs.add (Matrix.isSymm_one.smul _))]
      have hpd := posDef_of_qM_sub_le Matrix.isSymm_zero hYs (half_pos hc) (fun h => by
          have := hcY h
          have h0 : qM (0 : Matrix (Fin 2) (Fin 2) ℝ) h = 0 := by simp [qM]
          have hh : 0 ≤ ‖h‖ ^ 2 := sq_nonneg _
          rw [h0]
          nlinarith)
      have e : -((c / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) - ((0 : Matrix (Fin 2) (Fin 2) ℝ) - Y) =
          Y + (-(c / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        rw [neg_smul]; abel
      rwa [e] at hpd
    · -- `U(b) = 0`: a positive definite Peano Hessian at a minimum makes `b` an isolated zero
      apply hbI
      have hev : ∀ᶠ y in 𝓝 b, y ≠ 0 := isOpen_compl_singleton.mem_nhds hb0
      have hlocmin : IsLocalMin U b := by
        show ∀ᶠ y in 𝓝 b, U b ≤ U y
        filter_upwards [hev] with y hy
        rw [← hzero]
        exact hnn y hy
      have hp0 : p = 0 := taylor_grad_eq_zero_of_isLocalMin hTb hlocmin
      subst hp0
      obtain ⟨ρ, hρ, hρb⟩ := hTb.bound (half_pos hc)
      refine ⟨hzero.symm, ρ, hρ, fun x hx hxb => ?_⟩
      have h1 := hρb x (by rw [← dist_eq_norm]; exact hx)
      rw [inner_zero_left, ← hzero] at h1
      have h2 := (abs_le.1 h1).1
      have h3 := hcY (x - b)
      have h4 : 0 < ‖x - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hxb)
      have h5 : 0 < ‖x - b‖ ^ 2 := pow_pos h4 2
      intro hx0
      nlinarith
  -- conclude
  have hYeff : 0 ≤ effOp E Y := effOp_nonneg_of_not_posDef hOP2 E hE hYs hnot hstar
  exact hYeff.trans (hdeg X Y hXs hYs hYX.posSemidef)

/-- from the starred theorem, the weak Laplacian of the starred limit and
Pegden-Smart Proposition 2.5 (paraboloid form). -/
theorem ssLimitSuperEffD2_of_steps (hStar : SingleSourceTheoremStarD2Stmt)
    (hPS : PS25ParaboloidStmt) (hOP2 : EffOpEqStarOfNotPosDefD2Stmt)
    (hF1 : SSNoPosDefLowerTestD2Stmt) (hW : SSStarWeakLaplaceD2Stmt) : SSLimitSuperEffD2Stmt :=
  fun E hE => viscFromBelowGE_effOp_of_noPosDef hPS hOP2 E hE (hStar E hE).1.1
    (hF1 E hE) (hW E hE)

end SingleSourceD2

end RandomSandpile

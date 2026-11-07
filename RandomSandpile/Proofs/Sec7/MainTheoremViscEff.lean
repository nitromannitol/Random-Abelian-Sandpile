import RandomSandpile.Proofs.Sec7.MainTheoremUniqueness

/-!
# Theorem 1.1, step: the limit is a viscosity supersolution of `F̄_η(D²v) ≥ 0` in `W`

`limitViscEff_of_steps` derives `LimitViscEffStmt` from Lemma 6.4(1) (`EffectiveOperatorBasicStmt`,
monotonicity of `F̄_η`), the vanishing range of `μ*` (`MuVanishStmt`) and the interior minimum
principle (`InteriorMinPrincipleStmt`).

Route (Crandall-Ishii-Lions supersolution test, [C3] sign). Let a `C²` test function `φ` touch a
subsequential limit `v` from below at `x ∈ W` and suppose `l₀ = F̄_η(D²φ(x)) < 0`. Take a rational
symmetric `M ≥ D²φ(x)` within `τ = |l₀|/(4d)` of `D²φ(x) + τI`; then `F̄_η(M) ≤ l₀` (Lemma 6.4(1)),
so `μ*(q, M) = 0` for a rational `q ∈ (l₀, l₀/2)`. By Taylor's theorem for `φ`, the function
`v - (Dφ(x)·(· - x) + q_M(· - x) + q_q(· - x))` has a strict local minimum at `x` (its quadratic
part has Hessian `D²φ(x) - M - (q/d)I ≥ -(3τ/2)I + (|l₀|/(2d))I = (τ/2)I`), contradicting the
minimum principle on a small sphere.

Elementary ingredients: the coordinate formula `D²φ(x)(h, h) = 2 q_{hessian φ x}(h)` and the
second-order Taylor bound for `C²` functions (`ContDiffAt.taylor_two`), proved by the
one-dimensional mean value theorem along the segment `[x, y]`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-! ### Second-order Taylor bound -/

/-- A continuous bilinear form on `ℝ^d` on the diagonal, in coordinates. -/
theorem bilin_diag_eq_qM (B : Rd d →L[ℝ] Rd d →L[ℝ] ℝ) (h : Rd d) :
    B h h = 2 * qM (Matrix.of fun i j =>
      B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) h := by
  have hh : h = ∑ i, h i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr h]
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  conv_lhs => rw [hh]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  unfold qM
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem fderiv_fderiv_diag_eq_qM (φ : Rd d → ℝ) (x h : Rd d) :
    fderiv ℝ (fderiv ℝ φ) x h h = 2 * qM (hessian φ x) h :=
  bilin_diag_eq_qM _ h

/-- **Taylor's theorem for `C²` functions** (Peano remainder):
`|φ(y) - φ(x) - Dφ(x)(y - x) - q_{D²φ(x)}(y - x)| ≤ κ |y - x|²` near `x`. -/
theorem ContDiffAt.taylor_two {φ : Rd d → ℝ} {x : Rd d} (hφ : ContDiffAt ℝ 2 φ x) {κ : ℝ}
    (hκ : 0 < κ) : ∃ ρ > 0, ∀ y, ‖y - x‖ < ρ →
      |φ y - φ x - fderiv ℝ φ x (y - x) - qM (hessian φ x) (y - x)| ≤ κ * ‖y - x‖ ^ 2 := by
  set D := fderiv ℝ φ with hD_def
  set B := fderiv ℝ D x with hB_def
  have hD : HasFDerivAt D B x :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hev.and (hD.isLittleO.def hκ))
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  set h := y - x with hh_def
  have hmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → x + t • h ∈ Metric.ball x ρ := fun t ht0 ht1 => by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    calc t * ‖h‖ ≤ 1 * ‖h‖ := by gcongr
      _ < ρ := by rw [one_mul]; exact hy
  let χ : ℝ → ℝ := fun t => φ (x + t • h) - t * D x h - t ^ 2 / 2 * B h h
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt χ (D (x + t • h) h - D x h - t * B h h) (Set.Icc 0 1) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h2 : HasDerivAt (fun t => φ (x + t • h)) (D (x + t • h) h) t :=
      (hball _ (hmem t ht.1 ht.2)).1.hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t * D x h) (D x h) t := by
      simpa using (hasDerivAt_id t).mul_const (D x h)
    have h4 : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * B h h) (t * B h h) t := by
      have h5 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      exact ((h5.div_const 2).mul_const (B h h)).congr_deriv (by ring)
    exact ((h2.sub h3).sub h4).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖D (x + t • h) h - D x h - t * B h h‖ ≤ κ * ‖h‖ ^ 2 := by
    intro t ht
    have hlo := (hball _ (hmem t ht.1 ht.2.le)).2
    rw [add_sub_cancel_left] at hlo
    have heq : D (x + t • h) h - D x h - t * B h h = (D (x + t • h) - D x - B (t • h)) h := by
      simp
    rw [heq]
    have hth : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
    calc ‖(D (x + t • h) - D x - B (t • h)) h‖
        ≤ ‖D (x + t • h) - D x - B (t • h)‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ κ * ‖t • h‖ * ‖h‖ := by gcongr
      _ ≤ κ * ‖h‖ * ‖h‖ := by gcongr
      _ = κ * ‖h‖ ^ 2 := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 (by simp)
  have hBq : B h h = 2 * qM (hessian φ x) h := fderiv_fderiv_diag_eq_qM φ x h
  simp only [χ, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, one_pow,
    Real.norm_eq_abs, mul_one] at key
  have hxy : x + h = y := by rw [hh_def, add_sub_cancel]
  rw [hxy] at key
  rw [hBq] at key
  convert key using 2
  ring

/-! ### The minimum principle at rational parameters -/

theorem ae_interiorMinPrinciple_rat (hVan : MuVanishStmt) (hMin : InteriorMinPrincipleStmt)
    (hd : 2 ≤ d) (E : RandomEnvironment d) (hHD : HighDensity E.P) (W : Set (Rd d))
    (hW : IsLipschitzDomain W) :
    ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), effOp E (symQ A) ≤ (q : ℝ) →
      ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) ≤
              v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) := by
  rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro A
  by_cases hq : effOp E (symQ A) ≤ (q : ℝ)
  · filter_upwards [hMin d hd E W hW q (symQ A) (symQ_isSymm A)
      ((hVan d hd E hHD (symQ A) (symQ_isSymm A) q).2 hq)] with η hη
    exact fun _ => hη
  · exact Eventually.of_forall fun η h => absurd h hq

/-! ### The reduction -/

/-- The deterministic core of step: a function satisfying the minimum principle relative to
the quadratics `p·(· - a) + q_M(· - a) + q_q(· - a)` on the closed balls of the open set `W`, at all
rational parameters with `F̄_η(M) ≤ q`, is a viscosity supersolution of `F̄_η(D²v) ≥ 0` in `W`.
Shared with Theorem 9.1 (`Proofs/Sec9/OpenBoundary*.lean`). -/
theorem viscFromBelowGE_effOp_of_minPrinciple (h64 : EffectiveOperatorBasicStmt) (hd : 2 ≤ d)
    (E : RandomEnvironment d) {W : Set (Rd d)} (hWo : IsOpen W) {v : Rd d → ℝ}
    (hη : ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), effOp E (symQ A) ≤ (q : ℝ) →
      ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
        ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
          v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) ≤
            v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a))) :
    ViscFromBelowGE (effOp E) W v := by
  refine fun x hxW φ (hφ : ContDiffAt ℝ 2 φ x)
    (hloc : IsLocalMin (fun y => v y - φ y) x) => ?_
  by_contra hneg
  have hl₀ : effOp E (hessian φ x) < 0 := not_le.1 hneg
  set H := hessian φ x with hH_def
  set l₀ := effOp E H with hl₀_def
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  -- symmetry of the Hessian of a `C²` function
  have hsym := ContDiffAt.isSymmSndFDerivAt hφ (by simp)
  have hH : H.IsSymm := by
    ext i j
    simp only [hH_def, hessian, Matrix.transpose_apply, Matrix.of_apply]
    exact hsym _ _
  -- the rational matrix `M ≥ H`
  set τ : ℝ := -l₀ / (4 * d) with hτ_def
  have hτ : 0 < τ := by rw [hτ_def]; apply div_pos <;> linarith
  have hHτ : (H + τ • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    hH.add (Matrix.isSymm_one.smul _)
  obtain ⟨A, hA⟩ := exists_symQ_near (H + τ • (1 : Matrix (Fin d) (Fin d) ℝ)) hHτ
    (ε := τ / (4 * (d : ℝ) ^ 2)) (by positivity)
  set M := symQ A with hM_def
  have hMerr : ∀ z : Rd d,
      |qM M z - qM (H + τ • (1 : Matrix (Fin d) (Fin d) ℝ)) z| ≤ τ / 4 * ‖z‖ ^ 2 := fun z => by
    rw [← qM_sub_mat]
    refine (abs_qM_le _ (by positivity) hA z).trans (le_of_eq ?_)
    field_simp
  have hMH : ∀ z : Rd d, τ / 4 * ‖z‖ ^ 2 ≤ qM M z - qM H z ∧
      qM M z - qM H z ≤ 3 * τ / 4 * ‖z‖ ^ 2 := fun z => by
    have h1 := abs_le.1 (hMerr z)
    rw [qM_add_mat, qM_smul_one] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hPSD : (M - H).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
    · exact Matrix.isHermitian_iff_isSymm.2 ((symQ_isSymm A).sub hH)
    · have h1 := (hMH (WithLp.toLp 2 w)).1
      have h2 : 0 ≤ qM (M - H) (WithLp.toLp 2 w) := by
        rw [qM_sub_mat]; nlinarith [sq_nonneg ‖(WithLp.toLp 2 w : Rd d)‖]
      unfold qM at h2
      simp only [star_trivial]
      simpa using h2
  have hle : effOp E M ≤ l₀ := by
    obtain ⟨C, -, hC⟩ := h64 d hd E.ηmin E.ηmax
    exact (hC E rfl rfl H M hH (symQ_isSymm A)).1 hPSD
  -- the rational level `q ∈ (l₀, l₀ / 2)`
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show l₀ < l₀ / 2 by linarith)
  have hqM : effOp E M ≤ (q : ℝ) := hle.trans hq1.le
  -- radii
  obtain ⟨ρ₀, hρ₀, hρ₀W⟩ := Metric.isOpen_iff.1 hWo x hxW
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ (κ := τ / 8) (by positivity)
  obtain ⟨ρ₂, hρ₂, hmin⟩ := Metric.eventually_nhds_iff.1 hloc
  set r := min ρ₀ (min ρ₁ ρ₂) / 2 with hr_def
  have hm : 0 < min ρ₀ (min ρ₁ ρ₂) := lt_min hρ₀ (lt_min hρ₁ hρ₂)
  have hr : 0 < r := half_pos hm
  have hrm : r < min ρ₀ (min ρ₁ ρ₂) := half_lt_self hm
  have hr0 : r < ρ₀ := hrm.trans_le (min_le_left _ _)
  have hr1 : r < ρ₁ := hrm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr2 : r < ρ₂ := hrm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrW : Metric.closedBall x r ⊆ W := (Metric.closedBall_subset_ball hr0).trans hρ₀W
  set p : Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x) with hp_def
  obtain ⟨y, hy, hle'⟩ := hη q A hqM x p r hr hrW x (Metric.mem_closedBall_self hr.le)
  simp only [sub_self, inner_zero_right, qM_zero_right, ql_zero_right, add_zero] at hle'
  have hya : ‖y - x‖ = r := by rw [← dist_eq_norm]; exact Metric.mem_sphere.1 hy
  have hp : inner ℝ p (y - x) = fderiv ℝ φ x (y - x) := by
    rw [hp_def, InnerProductSpace.toDual_symm_apply]
  have h1 := abs_le.1 (hT y (by rw [hya]; exact hr1))
  have h2 : v x - φ x ≤ v y - φ y := hmin (show dist y x < ρ₂ by rw [dist_eq_norm, hya]; exact hr2)
  have h3 := (hMH (y - x)).2
  have hH2 : 0 < ‖y - x‖ ^ 2 := by rw [hya]; positivity
  have hq : (q : ℝ) * ‖y - x‖ ^ 2 / (2 * d) < -τ * ‖y - x‖ ^ 2 := by
    rw [div_lt_iff₀ (by positivity), hτ_def]
    have : (q : ℝ) < l₀ / 2 := hq2
    have e : -(-l₀ / (4 * d)) * ‖y - x‖ ^ 2 * (2 * d) = l₀ / 2 * ‖y - x‖ ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith
  have hτH := mul_pos hτ hH2
  unfold ql at hle'
  rw [hp] at hle'
  nlinarith [h1.1, h2, h3, hq, hH2, hτH]

/-- **Step** of Theorem 1.1 from Lemma 6.4(1), `MuVanishStmt` and the interior minimum
principle. -/
theorem limitViscEff_of_steps (h64 : EffectiveOperatorBasicStmt) (hVan : MuVanishStmt)
    (hMin : InteriorMinPrincipleStmt) : LimitViscEffStmt := by
  intro d hd E hHD W hW
  filter_upwards [ae_interiorMinPrinciple_rat hVan hMin hd E hHD W hW] with η hη
  exact fun v hv => viscFromBelowGE_effOp_of_minPrinciple h64 hd E hW.2.1
    fun q A hq => hη q A hq v hv

end RandomSandpile

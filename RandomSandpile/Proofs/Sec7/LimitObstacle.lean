import RandomSandpile.Proofs.Sec7.LimitObstacleGamma

/-!
# Theorem 1.1, steps and: the limit solves the obstacle problem

Reductions of `LimitViscZeroStmt` and `LimitMinimalStmt` of
`RandomSandpile/Steps/Sec7/MainTheorem.lean` (`paper/random_piles-corrected.tex`; the paper
prints no proof) to two new step statements and to steps already decomposed.

## New step statements

* `SplitTouchingStmt`: Jensen's lemma for sup- and inf-convolutions (Crandall-Ishii-Lions), in
  the form a comparison argument consumes. If `u` is a viscosity subsolution of `-Δu - K = 0`, `w`
  a viscosity supersolution of `-Δw + K = 0`, and `u - w` exceeds in `U` its maximum `m` on `∂U`,
  then for every closed Lebesgue-null `N` there are points `a, b` in one ball `B ⊆ U \ N` with
  `u(a) - w(b) > m`, a quadratic with matrix `X` touching `u` from above at `a`, a quadratic with
  matrix `Y` touching `w` from below at `b`, and `Y - X ≥ δI` for some `δ > 0`.
  Proof route (provable from `AlexandrovStmt`, `RandomSandpile/Inputs/Alexandrov.lean`):
  `Φ_ε = u^ε - w_ε` (sup- and inf-convolutions over `Ū`, `Infra/SupConvolution.lean`) is
  semiconvex and tends to `u - w` uniformly; for the maximum points `x` of
  `Φ_ε + δ|· - x₀|² + p·(·)`, `|p| < σ`, the gradient map covers `B_σ`; at Alexandrov points
  of `u^ε` and `w_ε` with maximizers `x̂, x̌` in `U`, `tr D²u^ε ≥ -K`, `tr D²w_ε ≤ K`
  (`ViscFromAboveGE.supConv_at`, `trace_add_nonneg_of_taylor`) and `D²Φ_ε ≤ -2δI`, so
  `|det D²Φ_ε| ≤ (2K/d)^d` (AM-GM) and, by the area formula, these points have measure
  `≥ c > 0` uniformly in `ε`; the `C√ε`-neighbourhood of `N ∩ Ū` has measure `→ 0`, so one such
  point `x` has `dist(x, N) > 2C√ε`; then `a = x̂`, `b = x̌`, `X = D²u^ε(x) + κI`,
  `Y = D²w_ε(x) - κI`. This is the form in which Pegden-Smart's Proposition 2.5
  (`PegdenSmartTouchingStmt`) is needed when only one of the two functions has a two-sided
  Laplacian bound: a member `w` of `obstacleSet E W` has only `Δw ≤ 2d - 1` (from
  `F̄_0(D²w) ≤ 0`, `ViscFromBelowLE.trace_le_of_effOp0`), so `PegdenSmartTouchingStmt`, which needs
  `|Δw| ≤ K`, does not apply to `v - w`.
* `LimitTraceInteriorStmt`: almost surely, a quadratic with matrix `N` touching a subsequential
  limit `v` from below at `a ∈ W` has `tr N ≤ 2d - 1 - E(η(0))`; this is the viscosity form of
  `Δv ≤ 2d - 1 - E(η(0))` in `W`, the homogenized limit of `Δ_{ℤ^d} v_n + η ≤ 2d - 1` in `W_n`.
  Proof route: on `B_{rn}([na])`, write `f_n = v_n - n²P(·/n)` (with `P` the strict touching
  quadratic) through the Green's function of the ball: `f_n([na]) ≥ min_{∂B} f_n +
  (E η(0) - (2d - 1) + tr N) Σ_y g(·, y) - o(n²)` by the ergodic theorem for Green potentials
  (Lemma 7.3 `DivisibleHomogenizeStmt` and its off-centre form), against
  `min_{∂B} f_n ≥ f_n([na]) + c r² n² - o(n²)`. It implies the Peano form
  `FreeOdometerLimitHessianTraceStmt` (Steps/Sec7/PegdenSmartRegularity.lean).

## The reductions

 `limitViscZero_of_steps`. With `Γ` the integer superharmonic matrices
(`IsIntSuperharmonicMatrix`), `F̄_0(D²φ(x)) ≤ 0` follows from `D²φ(x) - εI ∈ Γ` for all `ε > 0`
(`effOp0_nonpos_of_forall`), and a `C²` test function gives touching quadratics
(`touch_below_of_isLocalMin`). For a quadratic with matrix `N` touching `v` from below at `a`:
* `a ∉ W̄`: `ExteriorSupersolutionStmt` (Pegden-Smart, Lemma 4.1);
* `a ∈ W`: `tr N ≤ 2d - 1 - E(η(0)) < 0 < d` (`LimitTraceInteriorStmt`, high density), so
  `N - εI ∈ Γ` by Rossin's observation (`integerSuperharmonicOfTrace`). The argument of
  Pegden-Smart's Lemma 4.1 does not apply in `W`: there `Δ_{ℤ^d} v_n ≤ 2d - 1 - η`, and `η` may
  be negative (`E.ηmin` is any integer);
* `a ∈ ∂W`: make the quadratic `P` strict (`N - σI`), apply `SplitTouchingStmt` to `P` and `v`
  on a small ball with `N = ∂W` (Lebesgue-null, `LipschitzDomainFrontierNullStmt`;
  `|Δv| ≤ K` from `FreeOdometerLimitRegularStmt`): some `b ∉ ∂W` has a quadratic touching `v`
  from below with matrix `Y ≥ X + δI ≥ N - σI` (`qM_le_hessian_of_isLocalMax`), and `Γ` is closed
  downward.

 `limitMinimal_of_steps`. If `v(x₀) > w(x₀)` for some `w ∈ obstacleSet E W`, take a ball `U`
outside of which `v = 0 ≤ w` and apply `SplitTouchingStmt` to `v` (`Δv ≥ -K`) and `w`
(`Δw ≤ 2d - 1`) with `m = 0` and `N = ∂W`. The ball containing `a, b` lies in `W` or in `W̄ᶜ`.
* In `W`: for a rational `M` with `X < M ≤ Y`, the strict local maximum of `v - p·(· - a) - q_M`
  at `a` contradicts the maximum principle (`InteriorMaxPrincipleStmt` with `μ(0, M) = 0` from
  `MuVanishStmt`) unless `F̄_η(M) < 0` (`ae_effOp_lt_of_touch_above`), while
  `F̄_η(M) ≥ F̄_η(Y) ≥ 0` (Lemma 6.4(1), `w ∈ obstacleSet`).
* Outside `W̄`: `v(a) > w(b) ≥ 0`, so `X + (δ/2)I ∉ Γ` (`ExteriorSubsolutionStmt`), while
  `F̄_0(Y) ≤ 0` gives `Y - (δ/2)I ∈ Γ` and `X + (δ/2)I ≤ Y - (δ/2)I`.

The route of rounding a smooth approximation of `w` to an integer stabilizing
toppling of `η 𝟙_{W_n}`, is not available: a viscosity supersolution has no smooth approximation
preserving `F̄_η(D²w) ≥ 0`, and stabilizing `η + Δ q_M` requires the correctors of `μ*`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-! ### Step statements -/

/-- **Step: Jensen's lemma for sup- and inf-convolutions, split at nearby points**
(Crandall-Ishii-Lions; the form of Pegden-Smart's Proposition 2.5 needed when only `u` has a lower
and only `w` an upper Laplacian bound). Let `U ⊆ ℝ^d` be bounded and open, `u, w ∈ C(Ū)`, `u` a
viscosity subsolution of `-Δu - K = 0` and `w` a viscosity supersolution of `-Δw + K = 0` in `U`.
If `u - w ≤ m` on `∂U` and `u - w > m` somewhere in `U`, then for every closed Lebesgue-null set
`N` there are a ball `B_r(c) ⊆ U \ N`, points `a, b ∈ B_r(c)` with `u(a) - w(b) > m`, a quadratic
with symmetric matrix `X` touching `u` from above at `a`, and a quadratic with symmetric matrix
`Y` touching `w` from below at `b`, with `Y - X ≥ δI` for some `δ > 0`. Proof route: module
docstring (from `AlexandrovStmt` and the area formula). -/
def SplitTouchingStmt : Prop :=
  ∀ (d : ℕ) (U : Set (Rd d)), IsOpen U → Bornology.IsBounded U →
    ∀ (K : ℝ) (u w : Rd d → ℝ), ContinuousOn u (closure U) → ContinuousOn w (closure U) →
      ViscFromAboveGE (fun X => X.trace + K) U u → ViscFromBelowLE (fun X => X.trace - K) U w →
      ∀ m : ℝ, (∀ x ∈ frontier U, u x - w x ≤ m) → (∃ x ∈ U, m < u x - w x) →
      ∀ N : Set (Rd d), IsClosed N → volume N = 0 →
        ∃ (c : Rd d) (r : ℝ), Metric.ball c r ⊆ U ∧ Disjoint (Metric.ball c r) N ∧
          ∃ (a b p q : Rd d) (X Y : Matrix (Fin d) (Fin d) ℝ),
            a ∈ Metric.ball c r ∧ b ∈ Metric.ball c r ∧ m < u a - w b ∧
            X.IsSymm ∧ Y.IsSymm ∧
            (∃ δ : ℝ, 0 < δ ∧ (Y - X - δ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) ∧
            (∀ᶠ y in 𝓝 a, u y ≤ u a + inner ℝ p (y - a) + qM X (y - a)) ∧
            (∀ᶠ y in 𝓝 b, w b + inner ℝ q (y - b) + qM Y (y - b) ≤ w y)

/-- **Step: `Δv ≤ 2d - 1 - E(η(0))` in `W`** for the subsequential limits, in the viscosity sense
(quadratics touching from below). Almost surely, if a quadratic with symmetric matrix `N` touches a
subsequential limit `v` of the rescaled free odometers from below at `a ∈ W`, then
`tr N ≤ 2d - 1 - E(η(0))`. Homogenized limit of `Δ_{ℤ^d} v_n + η ≤ 2d - 1` in `W_n`; proof route in
the module docstring. -/
def LimitTraceInteriorStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
      ∀ a ∈ W, ∀ (p : Rd d) (N : Matrix (Fin d) (Fin d) ℝ), N.IsSymm →
        (∀ᶠ y in 𝓝 a, v a + inner ℝ p (y - a) + qM N (y - a) ≤ v y) →
          N.trace ≤ 2 * (d : ℝ) - 1 - meanEta E.P

/-! ### Elementary facts -/

theorem ViscFromAboveGE.trace_mono {U : Set (Rd d)} {u : Rd d → ℝ} {K K' : ℝ}
    (h : ViscFromAboveGE (fun X => X.trace + K) U u) (hK : K ≤ K') :
    ViscFromAboveGE (fun X => X.trace + K') U u := fun x hx φ hφ hm => by
  have := h x hx φ hφ hm
  simp only at this ⊢
  linarith

theorem ViscFromBelowLE.trace_mono {U : Set (Rd d)} {w : Rd d → ℝ} {K K' : ℝ}
    (h : ViscFromBelowLE (fun X => X.trace - K) U w) (hK : K ≤ K') :
    ViscFromBelowLE (fun X => X.trace - K') U w := fun x hx φ hφ hm => by
  have := h x hx φ hφ hm
  simp only at this ⊢
  linarith

theorem isLocalMax_sub_quadratic {u : Rd d → ℝ} {a p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ}
    (ht : ∀ᶠ y in 𝓝 a, u y ≤ u a + inner ℝ p (y - a) + qM X (y - a)) :
    IsLocalMax (fun y => u y - (u a + innerSL ℝ p (y - a) + qM X (y - a))) a := by
  filter_upwards [ht] with y hy
  simp only [innerSL_apply_apply, sub_self, inner_zero_right, qM_zero_right, add_zero]
  linarith

/-- A ball disjoint from the frontier of an open set lies in it or outside its closure. -/
theorem ball_subset_or_of_disjoint_frontier {W : Set (Rd d)} (hW : IsOpen W) {c : Rd d} {r : ℝ}
    (h : Disjoint (Metric.ball c r) (frontier W)) :
    Metric.ball c r ⊆ W ∨ Metric.ball c r ⊆ (closure W)ᶜ := by
  refine (convex_ball c r).isPreconnected.subset_or_subset hW isClosed_closure.isOpen_compl
    (Set.disjoint_compl_right_iff_subset.2 subset_closure) fun y hy => ?_
  by_cases hyW : y ∈ W
  · exact Or.inl hyW
  · refine Or.inr fun hcl => Set.disjoint_left.1 h hy ⟨hcl, ?_⟩
    rwa [hW.interior_eq]

theorem not_mem_closure_of_not_mem_frontier {W : Set (Rd d)} (hW : IsOpen W) {a : Rd d}
    (ha : a ∉ W) (hfr : a ∉ frontier W) : a ∉ closure W := fun hcl =>
  hfr ⟨hcl, by rwa [hW.interior_eq]⟩

/-! ###: the subsolution property in `W` -/

/-- **The maximum principle at rational parameters gives `F̄_η(D²v) ≤ 0` in `W`** (tested from
above, in the strict form used by the comparison). Almost surely, if a quadratic with matrix `X`
touches a subsequential limit `v` from above at `a ∈ W`, then `F̄_η(M) < l` for all rational
`l`, `M` with `q_M + q_l > q_X` strictly. -/
theorem ae_effOp_lt_of_touch_above (hVan : MuVanishStmt) (hMax : InteriorMaxPrincipleStmt)
    (hd : 2 ≤ d) (E : RandomEnvironment d) (hHD : HighDensity E.P) (W : Set (Rd d))
    (hW : IsLipschitzDomain W) :
    ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v → ∀ a ∈ W, ∀ (p : Rd d)
      (X : Matrix (Fin d) (Fin d) ℝ),
      (∀ᶠ y in 𝓝 a, v y ≤ v a + inner ℝ p (y - a) + qM X (y - a)) →
      ∀ (q : ℚ) (A : Fin d → Fin d → ℚ) (κ : ℝ), 0 < κ →
        (∀ h : Rd d, qM X h + κ * ‖h‖ ^ 2 ≤ qM (symQ A) h + ql (q : ℝ) h) →
          effOp E (symQ A) < q := by
  have hrat : ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), (q : ℝ) ≤ effOp E (symQ A) →
      ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) ≤
              v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro A
    by_cases hq : (q : ℝ) ≤ effOp E (symQ A)
    · filter_upwards [hMax d hd E W hW q (symQ A) (symQ_isSymm A)
        ((hVan d hd E hHD (symQ A) (symQ_isSymm A) q).1 hq)] with η hη
      exact fun _ => hη
    · exact Eventually.of_forall fun η h => absurd h hq
  filter_upwards [hrat] with η hη
  intro v hv a haW p X hta q A κ hκ hle
  by_contra hge
  have hq : (q : ℝ) ≤ effOp E (symQ A) := not_lt.1 hge
  obtain ⟨ρ₀, hρ₀, hρ₀W⟩ := Metric.isOpen_iff.1 hW.2.1 a haW
  obtain ⟨ρ₁, hρ₁, hloc⟩ := Metric.eventually_nhds_iff.1 hta
  have hm : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
  set r := min ρ₀ ρ₁ / 2 with hr_def
  have hr : 0 < r := half_pos hm
  have hrm : r < min ρ₀ ρ₁ := half_lt_self hm
  have hr0 : r < ρ₀ := hrm.trans_le (min_le_left _ _)
  have hr1 : r < ρ₁ := hrm.trans_le (min_le_right _ _)
  have hrW : Metric.closedBall a r ⊆ W := (Metric.closedBall_subset_ball hr0).trans hρ₀W
  obtain ⟨y, hy, hle'⟩ := hη q A hq v hv a p r hr hrW a (Metric.mem_closedBall_self hr.le)
  simp only [sub_self, inner_zero_right, qM_zero_right, ql_zero_right, add_zero] at hle'
  have hya : ‖y - a‖ = r := by rw [← dist_eq_norm]; exact Metric.mem_sphere.1 hy
  have h1 : v y ≤ v a + inner ℝ p (y - a) + qM X (y - a) :=
    hloc (show dist y a < ρ₁ by rw [dist_eq_norm, hya]; exact hr1)
  have h2 := hle (y - a)
  have h3 : 0 < κ * ‖y - a‖ ^ 2 := by rw [hya]; positivity
  linarith

/-! ### Matrix bookkeeping -/

/-- From `Y - X - δI ⪰ 0`: `q_Y ≥ q_X + (δ/2)|·|²`. -/
theorem qM_sub_ge_of_psd {X Y : Matrix (Fin d) (Fin d) ℝ} {δ : ℝ}
    (h : (Y - X - δ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) (x : Rd d) :
    qM X x + δ / 2 * ‖x‖ ^ 2 ≤ qM Y x := by
  have := qM_nonneg_of_posSemidef h x
  rw [qM_sub_mat, qM_sub_mat, qM_smul_one] at this
  linarith

theorem posSemidef_of_qM_nonneg {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm)
    (h : ∀ x : Rd d, 0 ≤ qM A x) : A.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.2 hA)
    fun w => ?_
  have h2 := h (WithLp.toLp 2 w)
  unfold qM at h2
  simp only [star_trivial]
  simpa using h2

/-- A rational symmetric `M` strictly between `X` and `Y` when `Y - X ⪰ δI`. -/
theorem exists_symQ_between {X Y : Matrix (Fin d) (Fin d) ℝ} (hX : X.IsSymm) (hY : Y.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) (h : (Y - X - δ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) :
    ∃ A : Fin d → Fin d → ℚ, (∀ x : Rd d, qM X x + δ / 8 * ‖x‖ ^ 2 ≤ qM (symQ A) x) ∧
      (Y - symQ A).PosSemidef := by
  have hdpos : (0 : ℝ) < (d : ℝ) ^ 2 + 1 := by positivity
  have hXδ : (X + (δ / 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    hX.add (Matrix.isSymm_one.smul _)
  obtain ⟨A, hA⟩ := exists_symQ_near (X + (δ / 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) hXδ
    (ε := δ / (8 * ((d : ℝ) ^ 2 + 1))) (by positivity)
  have herr : ∀ x : Rd d, |qM (symQ A) x - qM (X + (δ / 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) x|
      ≤ δ / 8 * ‖x‖ ^ 2 := fun x => by
    rw [← qM_sub_mat]
    refine (abs_qM_le _ (by positivity) hA x).trans ?_
    have hx := sq_nonneg ‖x‖
    have : (d : ℝ) ^ 2 * (δ / (8 * ((d : ℝ) ^ 2 + 1))) ≤ δ / 8 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  refine ⟨A, fun x => ?_, posSemidef_of_qM_nonneg (hY.sub (symQ_isSymm A)) fun x => ?_⟩
  · have h1 := abs_le.1 (herr x)
    rw [qM_add_mat, qM_smul_one] at h1
    nlinarith [h1.1, sq_nonneg ‖x‖]
  · have h1 := abs_le.1 (herr x)
    rw [qM_add_mat, qM_smul_one] at h1
    have h2 := qM_sub_ge_of_psd h x
    rw [qM_sub_mat]
    nlinarith [h1.2, sq_nonneg ‖x‖]

/-! ### `LimitMinimalStmt` -/

/-- **Step of Theorem 1.1 from its steps.** -/
theorem limitMinimal_of_steps (h64 : EffectiveOperatorBasicStmt) (hVan : MuVanishStmt)
    (hMax : InteriorMaxPrincipleStmt) (hExtSub : ExteriorSubsolutionStmt)
    (hReg : FreeOdometerLimitRegularStmt) (hNull : LipschitzDomainFrontierNullStmt)
    (hSplit : SplitTouchingStmt) : LimitMinimalStmt := by
  intro d hd E hHD W hW
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Ω₁, hΩ₁, K₀, hReg'⟩ := hReg d hd E W hW
  have hΩ : ∀ᵐ η ∂E.P, η ∈ Ω₁ := ae_iff.2 hΩ₁
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  filter_upwards [hΩ, hbdd, ae_effOp_lt_of_touch_above hVan hMax hd E hHD W hW]
    with η hη₁ hηb hηsub
  intro v hv w hw x₀
  by_contra hlt
  have hlt' : w x₀ < v x₀ := not_le.1 hlt
  obtain ⟨nk, hnk, hconv⟩ := hv
  obtain ⟨hcont, ⟨R, hR⟩, hsubv, -⟩ := hReg' η hη₁ nk hnk v hconv
  obtain ⟨hwc, hw0, hwEff, hwZero⟩ := hw
  set K : ℝ := max K₀ (2 * (d : ℝ) - 1) with hK_def
  set ρ : ℝ := |R| + ‖x₀‖ + 1 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hfr : ∀ x ∈ frontier (Metric.ball (0 : Rd d) ρ), v x - w x ≤ 0 := fun x hx => by
    rw [frontier_ball _ hρ.ne', mem_sphere_zero_iff_norm] at hx
    have hvx : v x = 0 := hR x (by rw [hx]; linarith [le_abs_self R, norm_nonneg x₀])
    rw [hvx]
    linarith [show (0 : ℝ) ≤ w x from hw0 x]
  have hx₀ : x₀ ∈ Metric.ball (0 : Rd d) ρ := by
    rw [mem_ball_zero_iff]; linarith [abs_nonneg R]
  have hsubv' : ViscFromAboveGE (fun X => X.trace + K) (Metric.ball (0 : Rd d) ρ) v :=
    (hsubv.mono (Set.subset_univ _)).trace_mono (le_max_left _ _)
  have hsupw : ViscFromBelowLE (fun X => X.trace - K) (Metric.ball (0 : Rd d) ρ) w :=
    ((hwZero.trace_le_of_effOp0 hd1).mono (Set.subset_univ _)).trace_mono (le_max_right _ _)
  obtain ⟨c, r, -, hdisj, a, b, p, q, X, Y, ha, hb, hab, hX, hY, ⟨δ, hδ, hpsd⟩, hta, htb⟩ :=
    hSplit d _ Metric.isOpen_ball Metric.isBounded_ball K v w hcont.continuousOn
      hwc.continuousOn hsubv' hsupw 0 hfr ⟨x₀, hx₀, by linarith⟩ (frontier W) isClosed_frontier
      (hNull d hd W hW)
  rcases ball_subset_or_of_disjoint_frontier hW.2.1 hdisj with hcW | hcW
  · -- both points in `W`: compare `F̄_η` at a rational matrix between `X` and `Y`
    obtain ⟨A, hAX, hAY⟩ := exists_symQ_between hX hY hδ hpsd
    have hlt0 : effOp E (symQ A) < ((0 : ℚ) : ℝ) :=
      hηsub v ⟨nk, hnk, hconv⟩ a (hcW ha) p X hta 0 A (δ / 8) (by positivity) fun x => by
        rw [Rat.cast_zero]; simp only [ql, zero_mul, zero_div, add_zero]; exact hAX x
    have hwY : 0 ≤ effOp E Y := hwEff.le_of_touch hY (hcW hb) htb
    obtain ⟨C, -, hC⟩ := h64 d hd E.ηmin E.ηmax
    have hmono := (hC E rfl rfl (symQ A) Y (symQ_isSymm A) hY).1 hAY
    rw [Rat.cast_zero] at hlt0
    linarith
  · -- both points outside `W̄`: `Γ` on both sides
    have hva : 0 < v a := by linarith [show (0 : ℝ) ≤ w b from hw0 b]
    have hnot := hExtSub d hd W hW E.ηmin E.ηmax η hηb v ⟨nk, hnk, hconv⟩ a p X (hcW ha) hX hva
      hta (δ / 2) (half_pos hδ)
    have hY0 : effOp0 d Y ≤ 0 := hwZero.le_of_touch hY (Set.mem_univ b) htb
    refine hnot ((IsIntSuperharmonicMatrix.of_effOp0_nonpos hd1 hY0 (half_pos hδ)).mono
      fun x => ?_)
    have h2 := qM_sub_ge_of_psd hpsd x
    rw [qM_add_mat, qM_sub_mat, qM_smul_one]
    linarith

/-! ### `LimitViscZeroStmt` -/

/-- **Step of Theorem 1.1 from its steps.** -/
theorem limitViscZero_of_steps (hExtSup : ExteriorSupersolutionStmt)
    (hTr : LimitTraceInteriorStmt) (hReg : FreeOdometerLimitRegularStmt)
    (hNull : LipschitzDomainFrontierNullStmt) (hSplit : SplitTouchingStmt) :
    LimitViscZeroStmt := by
  intro d hd E hHD W hW
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨Ω₁, hΩ₁, K₀, hReg'⟩ := hReg d hd E W hW
  have hΩ : ∀ᵐ η ∂E.P, η ∈ Ω₁ := ae_iff.2 hΩ₁
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  filter_upwards [hΩ, hbdd, hTr d hd E W hW] with η hη₁ hηb hηtr
  intro v hv
  obtain ⟨nk, hnk, hconv⟩ := hv
  have hv : IsOdoSubseqLimit η W v := ⟨nk, hnk, hconv⟩
  obtain ⟨hcont, -, -, hsupv⟩ := hReg' η hη₁ nk hnk v hconv
  -- off `∂W`: Pegden-Smart outside `W̄`, the trace bound in `W`
  have hoff : ∀ b : Rd d, b ∉ frontier W → ∀ (q : Rd d) (Y : Matrix (Fin d) (Fin d) ℝ),
      Y.IsSymm → (∀ᶠ y in 𝓝 b, v b + inner ℝ q (y - b) + qM Y (y - b) ≤ v y) →
      ∀ ε : ℝ, 0 < ε →
        IsIntSuperharmonicMatrix (Y - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    intro b hbfr q Y hY htb ε hε
    by_cases hbW : b ∈ W
    · have htr := hηtr v hv b hbW q Y hY htb
      have hHD' : 2 * (d : ℝ) - 1 < meanEta E.P := hHD
      obtain ⟨u, hu1, hu2⟩ := integerSuperharmonicOfTrace d (Y - ε • 1)
        (hY.sub (Matrix.isSymm_one.smul _)) (by
          rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
            smul_eq_mul]
          nlinarith)
      exact ⟨u, fun y => ⟨hu1 y, hu2 y⟩⟩
    · exact hExtSup d hd W hW E.ηmin E.ηmax η hηb v hv b q Y
        (not_mem_closure_of_not_mem_frontier hW.2.1 hbW hbfr) hY htb ε hε
  -- every point, through `SplitTouchingStmt` on a small ball
  have hquad : ∀ (a q : Rd d) (N : Matrix (Fin d) (Fin d) ℝ), N.IsSymm →
      (∀ᶠ y in 𝓝 a, v a + inner ℝ q (y - a) + qM N (y - a) ≤ v y) →
      ∀ ε : ℝ, 0 < ε →
        IsIntSuperharmonicMatrix (N - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    intro a q N hN hta ε hε
    set σ : ℝ := ε / 2 with hσ
    have hσ0 : 0 < σ := half_pos hε
    set N' := N - σ • (1 : Matrix (Fin d) (Fin d) ℝ) with hN'
    have hN's : N'.IsSymm := hN.sub (Matrix.isSymm_one.smul _)
    set P : Rd d → ℝ := fun y => v a + inner ℝ q (y - a) + qM N' (y - a) with hP
    obtain ⟨ρ₁, hρ₁, hloc⟩ := Metric.eventually_nhds_iff.1 hta
    set r : ℝ := ρ₁ / 2 with hr_def
    have hr : 0 < r := half_pos hρ₁
    have hgap : ∀ y, dist y a < ρ₁ → P y - v y ≤ -(σ / 2 * ‖y - a‖ ^ 2) := fun y hy => by
      have h1 := hloc hy
      simp only [hP, hN', qM_sub_mat, qM_smul_one]
      linarith
    set K : ℝ := max K₀ (-N'.trace) with hK_def
    have hPc : Continuous P :=
      (continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const))).add
        ((contDiff_qM (n := 0) N').continuous.comp (continuous_id.sub continuous_const))
    have hsubP : ViscFromAboveGE (fun X => X.trace + K) (Metric.ball a r) P := by
      intro x _ ψ hψ hmax
      have hq := qM_le_hessian_of_isLocalMax hψ (v a) q a N' hmax
      have htr := trace_le_trace_of_qM_le hq
      simp only
      linarith [le_max_right K₀ (-N'.trace)]
    have hsupv' : ViscFromBelowLE (fun X => X.trace - K) (Metric.ball a r) v :=
      (hsupv.mono (Set.subset_univ _)).trace_mono (le_max_left _ _)
    have hfr : ∀ x ∈ frontier (Metric.ball a r), P x - v x ≤ -(σ / 2 * r ^ 2) := fun x hx => by
      rw [frontier_ball _ hr.ne', mem_sphere_iff_norm] at hx
      have := hgap x (by rw [dist_eq_norm, hx]; exact half_lt_self hρ₁)
      rwa [hx] at this
    have hPa : P a - v a = 0 := by simp [hP, qM_zero_right]
    obtain ⟨c, r', -, hdisj, a', b, p', q', X, Y, -, hb, -, hX, hY, ⟨δ, hδ, hpsd⟩, hta', htb⟩ :=
      hSplit d _ Metric.isOpen_ball Metric.isBounded_ball K P v hPc.continuousOn
        hcont.continuousOn hsubP hsupv' _ hfr
        ⟨a, Metric.mem_ball_self hr, by
          rw [hPa]; have := mul_pos (half_pos hσ0) (pow_pos hr 2); linarith⟩ (frontier W)
        isClosed_frontier (hNull d hd W hW)
    -- `q_{N'} ≤ q_X ≤ q_Y - (δ/2)|·|²`
    have hNX : ∀ x : Rd d, qM N' x ≤ qM X x := fun x => by
      have hcd : ContDiffAt ℝ 2 (fun y => P a' + innerSL ℝ p' (y - a') + qM X (y - a')) a' :=
        (contDiff_paraboloid _ _ _ _).contDiffAt
      have h := qM_le_hessian_of_isLocalMax hcd (v a) q a N' (isLocalMax_sub_quadratic hta') x
      rwa [hessian_quadratic _ _ _ hX] at h
    have hbfr : b ∉ frontier W := fun hbW => Set.disjoint_left.1 hdisj hb hbW
    refine (hoff b hbfr q' Y hY htb σ hσ0).mono fun x => ?_
    have h1 := hNX x
    have h2 := qM_sub_ge_of_psd hpsd x
    simp only [hN', qM_sub_mat, qM_smul_one] at h1 ⊢
    nlinarith [sq_nonneg ‖x‖]
  -- the test function
  intro x _ φ hφ hmin
  refine effOp0_nonpos_of_forall fun ε hε => ?_
  have hH := hessian_isSymm_of_contDiffAt hφ
  have h := hquad x _ _ (hH.sub (Matrix.isSymm_one.smul _))
    (touch_below_of_isLocalMin hφ hmin (half_pos hε)) (ε / 2) (half_pos hε)
  refine h.mono fun y => ?_
  simp only [qM_sub_mat, qM_smul_one]
  linarith

end RandomSandpile

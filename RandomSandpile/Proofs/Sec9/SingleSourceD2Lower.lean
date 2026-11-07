import RandomSandpile.Proofs.Sec9.SingleSourceD2PS25
import RandomSandpile.Proofs.Sec9.SingleSourceD2Algebra

/-!
# Theorem 9.2 in dimension two: no positive definite lower tests

* `noPosDefLowerTest_of_peano`: the conclusion of Theorem 4.1 and a
  locally bounded weak Laplacian exclude positive definite lower tests;
* `noPosDefLowerTest_of_tendsto` (C7, Lemma 5.2): stability under locally uniform limits;
* `SourceApproximationStmt`: regularized source solutions `U_j → U`;
* `starProfile`: the starred limit `U* = v* + G` is a source profile for `F*`;
* `ssNoPosDefLowerTest_of_steps`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

/-! ### Lemma 5.1 -/

/-- The paraboloid with matrix `D²φ(a) - 2δI` lies below `u` with gap `δ|y - a|²/2` near a lower
test point `a`. -/
theorem exists_gap_paraboloid {u φ : Rd 2 → ℝ} {a : Rd 2} (hφ : ContDiffAt ℝ 2 φ a)
    (hmin : IsLocalMin (fun y => u y - φ y) a) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r₁ > 0, ∀ y, dist y a < r₁ → u a + fderiv ℝ φ a (y - a) +
      qM (hessian φ a + (-(2 * δ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - a) +
        δ / 2 * ‖y - a‖ ^ 2 ≤ u y := by
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ (half_pos hδ)
  obtain ⟨ε₁, hε₁, hloc⟩ := Metric.eventually_nhds_iff.1 hmin
  refine ⟨min ρ₁ ε₁, lt_min hρ₁ hε₁, fun y hy => ?_⟩
  have hT' := hT y (by rw [← dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_left _ _))
  have hl : u a - φ a ≤ u y - φ y := hloc (lt_of_lt_of_le hy (min_le_right _ _))
  rw [qM_add_smul_one]
  have := (abs_le.1 hT').1
  linarith

/-- A symmetric matrix with `q_X(h) ≥ c|h|²`, `c > 0`, is positive definite. -/
theorem posDef_of_qM_ge {X : Matrix (Fin 2) (Fin 2) ℝ} (hXs : X.IsSymm) {c : ℝ} (hc : 0 < c)
    (hq : ∀ h : Rd 2, c * ‖h‖ ^ 2 ≤ qM X h) : X.PosDef := by
  have h1 := posDef_of_qM_sub_le Matrix.isSymm_zero hXs (half_pos hc) (fun h => by
    have := hq h
    have h0 : qM (0 : Matrix (Fin 2) (Fin 2) ℝ) h = 0 := by simp [qM]
    have hh : 0 ≤ ‖h‖ ^ 2 := sq_nonneg _
    rw [h0]
    nlinarith)
  have h2 := posDef_add_smul_one h1 (half_pos hc).le
  have e : -((c / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) - ((0 : Matrix (Fin 2) (Fin 2) ℝ) - X) +
      (c / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = X := by abel
  rwa [e] at h2

/-- The perturbed Hessian `D²φ(a) - 2δI` stays positive definite for `δ = c/4`. -/
theorem posDef_sub_of_posDef {H : Matrix (Fin 2) (Fin 2) ℝ} (hHs : H.IsSymm) {c : ℝ} (hc : 0 < c)
    (hcq : ∀ h : Rd 2, c * ‖h‖ ^ 2 ≤ qM H h) :
    (H + (-(2 * (c / 4))) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
  refine posDef_of_qM_ge (hHs.add (Matrix.isSymm_one.smul _)) (half_pos hc) fun h => ?_
  rw [qM_add_smul_one]
  have := hcq h
  have hh : 0 ≤ ‖h‖ ^ 2 := sq_nonneg _
  nlinarith

/-- **(C6) SIMPLE-PROOF Lemma 5.1.** If `u` is continuous off the origin, has a locally bounded
weak Laplacian there, and has no positive definite Peano Hessian at positive points off the origin,
then it has no positive definite lower test there. -/
theorem noPosDefLowerTest_of_peano (hPS : PS25ParaboloidStmt) {u : Rd 2 → ℝ}
    (hu : ContinuousOn u {x | x ≠ 0}) (hW : LocWeakLaplaceBdd {x | x ≠ 0} u)
    (hpe : ∀ a : Rd 2, a ≠ 0 → 0 < u a → ∀ (p : Rd 2) (X : Matrix (Fin 2) (Fin 2) ℝ),
      X.IsSymm → HasSecondOrderTaylorAt u a p X → ¬ X.PosDef) :
    NoPosDefLowerTest u := by
  intro a ha hua φ hφ hmin hpd
  have hHs : (hessian φ a).IsSymm := hessian_isSymm_of_contDiffAt hφ
  obtain ⟨c, hc, hcq⟩ := exists_qM_ge_of_posDef hpd
  have hδ : 0 < c / 4 := div_pos hc (by norm_num)
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      X = hessian φ a + (-(2 * (c / 4))) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := ⟨_, rfl⟩
  have hXs : X.IsSymm := by rw [hXdef]; exact hHs.add (Matrix.isSymm_one.smul _)
  have hXpd : X.PosDef := by rw [hXdef]; exact posDef_sub_of_posDef hHs hc hcq
  obtain ⟨r₁, hr₁, hgap⟩ := exists_gap_paraboloid hφ hmin hδ
  rw [← hXdef] at hgap
  obtain ⟨r₀, hr₀, -, s, C, hsm, hsC, hweak⟩ := hW a ha
  have hca : ContinuousAt u a := hu.continuousAt (isOpen_compl_singleton.mem_nhds ha)
  obtain ⟨ε₂, hε₂, hpos⟩ := Metric.continuousAt_iff.1 hca (u a / 2) (half_pos hua)
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hm : 0 < min (min r₁ r₀) (min ε₂ ‖a‖) := lt_min (lt_min hr₁ hr₀) (lt_min hε₂ hna)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (min r₁ r₀) (min ε₂ ‖a‖) / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact half_pos hm
  have hrle : ∀ y, dist y a ≤ r → dist y a < r₁ ∧ dist y a < r₀ ∧ dist y a < ε₂ ∧
      dist y a < ‖a‖ := by
    intro y hy
    have h1 : min (min r₁ r₀) (min ε₂ ‖a‖) ≤ min r₁ r₀ := min_le_left _ _
    have h2 : min (min r₁ r₀) (min ε₂ ‖a‖) ≤ min ε₂ ‖a‖ := min_le_right _ _
    have h3 := min_le_left r₁ r₀
    have h4 := min_le_right r₁ r₀
    have h5 := min_le_left ε₂ ‖a‖
    have h6 := min_le_right ε₂ ‖a‖
    have h7 : r < min (min r₁ r₀) (min ε₂ ‖a‖) := by rw [hr]; linarith
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hne0 : ∀ y, dist y a < ‖a‖ → y ≠ 0 := by
    intro y hy h0
    rw [h0, dist_zero_left] at hy
    exact lt_irrefl _ hy
  have hcball : closedBall a r ⊆ {x : Rd 2 | x ≠ 0} := fun y hy =>
    hne0 y (hrle y (mem_closedBall.1 hy)).2.2.2
  have hballr : ball a r ⊆ ball a r₀ := fun y hy =>
    mem_ball.2 (hrle y (mem_ball.1 hy).le).2.1
  have hPSa := hPS u s a r C hr0 (hu.mono hcball) hsm hsC
    (isWeakSolutionLaplace_mono hweak hballr) (fderiv ℝ φ a) X hXs
    (fun y hy => by
      have hy' : dist y a = r := mem_sphere.1 hy
      have h := hgap y (hrle y hy'.le).1
      rw [← dist_eq_norm, hy'] at h
      have : 0 < c / 4 / 2 * r ^ 2 := mul_pos (half_pos hδ) (pow_pos hr0 2)
      linarith)
  obtain ⟨b, hbr, p, Y, hYs, hTb, hYX⟩ := nonempty_of_measure_ne_zero hPSa.ne'
  have hb := hrle b (mem_ball.1 hbr).le
  have hb0 : b ≠ 0 := hne0 b hb.2.2.2
  have hub : 0 < u b := by
    have h := hpos hb.2.2.1
    rw [Real.dist_eq] at h
    linarith [(abs_lt.1 h).1]
  apply hpe b hb0 hub p Y hYs hTb
  have h := hYX.add_posSemidef hXpd.posSemidef
  rwa [sub_add_cancel] at h

/-! ### Lemma 5.2 -/

/-- **(C7) SIMPLE-PROOF Lemma 5.2.** The absence of positive definite lower tests at positive points
passes to locally uniform limits off the origin. -/
theorem noPosDefLowerTest_of_tendsto {U : ℕ → Rd 2 → ℝ} {u : Rd 2 → ℝ}
    (hc : ∀ j, ContinuousOn (U j) {x | x ≠ 0}) (hu : ContinuousOn u {x | x ≠ 0})
    (hT : TendstoLocallyUniformlyOn U u atTop {x | x ≠ 0})
    (hU : ∀ j, NoPosDefLowerTest (U j)) : NoPosDefLowerTest u := by
  intro a ha hua φ hφ hmin hpd
  have hHs : (hessian φ a).IsSymm := hessian_isSymm_of_contDiffAt hφ
  obtain ⟨c, hc0, hcq⟩ := exists_qM_ge_of_posDef hpd
  have hδ : 0 < c / 4 := div_pos hc0 (by norm_num)
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      X = hessian φ a + (-(2 * (c / 4))) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := ⟨_, rfl⟩
  have hXs : X.IsSymm := by rw [hXdef]; exact hHs.add (Matrix.isSymm_one.smul _)
  have hXpd : X.PosDef := by rw [hXdef]; exact posDef_sub_of_posDef hHs hc0 hcq
  obtain ⟨r₁, hr₁, hgap⟩ := exists_gap_paraboloid hφ hmin hδ
  rw [← hXdef] at hgap
  have hca : ContinuousAt u a := hu.continuousAt (isOpen_compl_singleton.mem_nhds ha)
  obtain ⟨ε₂, hε₂, hpos⟩ := Metric.continuousAt_iff.1 hca (u a / 2) (half_pos hua)
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hm : 0 < min (min r₁ ε₂) ‖a‖ := lt_min (lt_min hr₁ hε₂) hna
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (min r₁ ε₂) ‖a‖ / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact half_pos hm
  have hrle : ∀ y, dist y a ≤ r → dist y a < r₁ ∧ dist y a < ε₂ ∧ dist y a < ‖a‖ := by
    intro y hy
    have h1 : min (min r₁ ε₂) ‖a‖ ≤ min r₁ ε₂ := min_le_left _ _
    have h2 : min (min r₁ ε₂) ‖a‖ ≤ ‖a‖ := min_le_right _ _
    have h3 := min_le_left r₁ ε₂
    have h4 := min_le_right r₁ ε₂
    have h7 : r < min (min r₁ ε₂) ‖a‖ := by rw [hr]; linarith
    refine ⟨by linarith, by linarith, by linarith⟩
  have hne0 : ∀ y, dist y a < ‖a‖ → y ≠ 0 := by
    intro y hy h0
    rw [h0, dist_zero_left] at hy
    exact lt_irrefl _ hy
  have hcball : closedBall a r ⊆ {x : Rd 2 | x ≠ 0} := fun y hy =>
    hne0 y (hrle y (mem_closedBall.1 hy)).2.2
  -- uniform closeness on the closed ball
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (c / 4 / 2 * r ^ 2 / 4) (u a / 8) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη]
    exact lt_min (div_pos (mul_pos (half_pos hδ) (pow_pos hr0 2)) (by norm_num)) (by linarith)
  have hη1 : η ≤ c / 4 / 2 * r ^ 2 / 4 := by rw [hη]; exact min_le_left _ _
  have hη2 : η ≤ u a / 8 := by rw [hη]; exact min_le_right _ _
  have hTK : TendstoUniformlyOn U u atTop (closedBall a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_compl_singleton).1 hT _ hcball
      (isCompact_closedBall a r)
  obtain ⟨j, hj⟩ := (Metric.tendstoUniformlyOn_iff.1 hTK η hη0).exists
  -- minimize `U_j - P` on the closed ball
  set P : Rd 2 → ℝ := fun y => u a + fderiv ℝ φ a (y - a) + qM X (y - a) with hP
  have hPc : Continuous P := (contDiff_paraboloid' (u a) (fderiv ℝ φ a) a X (n := 0)).continuous
  obtain ⟨b, hbK, hbmin⟩ := (isCompact_closedBall a r).exists_isMinOn
    ⟨a, mem_closedBall_self hr0.le⟩ (((hc j).mono hcball).sub hPc.continuousOn)
  have hclose : ∀ y ∈ closedBall a r, |u y - U j y| < η := fun y hy => by
    have := hj y hy; rwa [Real.dist_eq] at this
  have hPa : P a = u a := by simp [hP, qM]
  have hga : U j a - P a < η := by
    have := hclose a (mem_closedBall_self hr0.le)
    rw [hPa]; linarith [(abs_lt.1 this).1]
  have hgb : U j b - P b ≤ U j a - P a :=
    isMinOn_iff.mp hbmin a (mem_closedBall_self hr0.le)
  have hbball : b ∈ ball a r := by
    rw [mem_ball]
    refine lt_of_le_of_ne (mem_closedBall.1 hbK) fun hbr => ?_
    have h1 := hgap b (hrle b (le_of_eq hbr)).1
    have h2 := hclose b hbK
    rw [← dist_eq_norm, hbr] at h1
    have h3 : U j b - P b ≥ c / 4 / 2 * r ^ 2 - η := by
      simp only [hP]; linarith [(abs_lt.1 h2).2]
    linarith
  have hb := hrle b (mem_ball.1 hbball).le
  have hb0 : b ≠ 0 := hne0 b hb.2.2
  have hUb : 0 < U j b := by
    have h1 := hpos hb.2.1
    rw [Real.dist_eq] at h1
    have h2 := hclose b hbK
    linarith [(abs_lt.1 h1).1, (abs_lt.1 h2).2]
  have hloc : IsLocalMin (fun y => U j y - P y) b :=
    hbmin.isLocalMin (Filter.mem_of_superset (isOpen_ball.mem_nhds hbball) ball_subset_closedBall)
  have hloc' : IsLocalMin (fun y => U j y -
      ((u a + (U j b - P b)) + fderiv ℝ φ a (y - a) + qM X (y - a))) b := by
    have h := hloc
    unfold IsLocalMin IsMinFilter at h ⊢
    filter_upwards [h] with y hy
    simp only [hP] at hy ⊢
    linarith
  refine hU j b hb0 hUb _ (contDiff_paraboloid' _ (fderiv ℝ φ a) a X).contDiffAt hloc' ?_
  rw [hessian_paraboloid' _ _ _ hXs]
  exact hXpd

/-! ### Regularized source solutions -/

/-- ** Regularized source solutions**. Let `F` be degenerate elliptic with the
shift identity and trace-graph bounds `-2 ≤ f ≤ K`, `F(0) ≥ 0`, `K ≥ 1`, and let `U = v + G`
(`v` continuous) be a source profile for `F` with a locally bounded weak Laplacian off the origin
which is least among `w + G`, `w` continuous, nonnegative supersolutions off the origin. Then there
are `ε_j ∈ (0, 1)` and source profiles `U_j` of the regularized operators `F_{ε_j}`
(`regOp F K ε_j`), with locally bounded weak Laplacians off the origin, converging to `U` locally
uniformly off the origin. Inputs of the proof (§7.2): CIL Theorems 3.2 and 4.1; the comparison
principle `ShiftComparisonStmt` is available as a hypothesis. -/
def SourceApproximationStmt : Prop :=
  ShiftComparisonStmt →
  ∀ (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (K : ℝ), HasTraceShift F → DegenerateElliptic F → 1 ≤ K →
    (∀ z, -2 ≤ traceGraph F z ∧ traceGraph F z ≤ K) → 0 ≤ F 0 →
    ∀ v : Rd 2 → ℝ, Continuous v →
      IsSourceProfile F (fun x => v x + fundamentalSolution 2 x) →
      LocWeakLaplaceBdd {x | x ≠ 0} (fun x => v x + fundamentalSolution 2 x) →
      (∀ w : Rd 2 → ℝ, Continuous w →
        (∀ x : Rd 2, x ≠ 0 → 0 ≤ w x + fundamentalSolution 2 x) →
        ViscFromBelowGE F {x | x ≠ 0} (fun x => w x + fundamentalSolution 2 x) →
        ∀ x : Rd 2, x ≠ 0 → v x ≤ w x) →
      ∃ (ε : ℕ → ℝ) (U : ℕ → Rd 2 → ℝ), (∀ j, 0 < ε j ∧ ε j < 1) ∧
        (∀ j, IsSourceProfile (regOp F K (ε j)) (U j)) ∧
        (∀ j, LocWeakLaplaceBdd {x | x ≠ 0} (U j)) ∧
        TendstoLocallyUniformlyOn U (fun x => v x + fundamentalSolution 2 x) atTop {x | x ≠ 0}

/-! ### The starred limit as a source profile -/

/-- The starred limit `U* = v* + G` is a source profile for `F*`: continuity, nonnegativity and the
supersolution property from the starred obstacle set, the bounded support from the outer bound, the
divergence at the source from `G`, and the subsolution property from step. -/
theorem starProfile (hStar : SingleSourceTheoremStarD2Stmt) (hS : SSLimitSubStarD2Stmt)
    (hB : SSLimitSupportStmt) (E : RandomEnvironment 2) (hE : E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2) :
    IsSourceProfile (effOpStar E)
      (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x) := by
  obtain ⟨hleast, hae⟩ := hStar E hE
  have hv := hleast.1
  have hE1 : E.ηmax ≤ 2 * ((2 : ℕ) : ℤ) - 1 := by rw [hE]; norm_num
  obtain ⟨η, ⟨⟨-, hconv⟩, hsub⟩, hsupp⟩ :=
    ((hae.and (hS E hE)).and (hB 2 le_rfl E hE)).exists
  have hlim : IsSSSubseqLimit η
      (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x) :=
    ⟨id, strictMono_id, hconv⟩
  refine ⟨hv.1.continuousOn.add (SingleSourceMin.continuousOn_fundamentalSolution 2),
    fun x hx => by
      have := hv.2.1 x hx
      show 0 ≤ singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x
      linarith, ?_, ?_,
    (viscFromBelowMuStar_iff (by norm_num) E hE1 _ _).1 hv.2.2, hsub _ hlim⟩
  · obtain ⟨R, hR⟩ := hsupp _ hlim
    exact ⟨R + 1, fun x hx => hR x (by linarith)⟩
  · refine Filter.tendsto_atTop.2 fun T => ?_
    obtain ⟨ρ, hρ, hG⟩ := SingleSourceFstar.fundamentalSolution_large (d := 2) le_rfl
      (T - singleSourceObstacleSolutionStar E 0 + 1)
    have hc0 : ∀ᶠ x in 𝓝 (0 : Rd 2), singleSourceObstacleSolutionStar E 0 - 1 <
        singleSourceObstacleSolutionStar E x :=
      (hv.1.tendsto 0).eventually (lt_mem_nhds (by linarith))
    have hball : ∀ᶠ x in 𝓝 (0 : Rd 2), ‖x‖ ≤ ρ := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : Rd 2) hρ] with x hx
      rwa [mem_closedBall_zero_iff] at hx
    filter_upwards [nhdsWithin_le_nhds hc0, nhdsWithin_le_nhds hball, self_mem_nhdsWithin]
      with x h1 h2 h3
    have := hG x h3 h2
    linarith

/-- The weak Laplacian of the starred limit from. -/
theorem ssStarWeakLaplace_of_E1 (hStar : SingleSourceTheoremStarD2Stmt)
    (hE1 : SSLimitWeakLaplaceD2Stmt) : SSStarWeakLaplaceD2Stmt := by
  intro E hE
  obtain ⟨-, hae⟩ := hStar E hE
  obtain ⟨η, ⟨-, hconv⟩, hW⟩ := (hae.and (hE1 E hE)).exists
  exact hW _ ⟨id, strictMono_id, hconv⟩

/-! ### -/

/-- from the starred theorem, the outer bound, the comparison
principle and Pegden-Smart Proposition 2.5 (paraboloid form). -/
theorem ssNoPosDefLowerTest_of_steps (hStar : SingleSourceTheoremStarD2Stmt)
    (hS : SSLimitSubStarD2Stmt) (hOB : SSOuterBoundStmt) (hE1 : SSLimitWeakLaplaceD2Stmt)
    (hB1 : EffOpStarTraceBoundsD2Stmt) (hC5 : PlanarExclusionStmt)
    (hD7 : SourceApproximationStmt) (hCmp : ShiftComparisonStmt) (hPS : PS25ParaboloidStmt) :
    SSNoPosDefLowerTestD2Stmt := by
  intro E hE
  have hprof := starProfile hStar hS (ssLimitSupport_of_outerBound hOB) E hE
  have hW := ssStarWeakLaplace_of_E1 hStar hE1 E hE
  have hE1' : E.ηmax ≤ 2 * ((2 : ℕ) : ℤ) - 1 := by rw [hE]; norm_num
  have hshift : HasTraceShift (effOpStar E) := fun M hM t =>
    (effOpStar_add_smul_one (by norm_num) E hE1' hM t).trans (by norm_num)
  have hdeg := degenerateElliptic_effOpStar (by norm_num) E hE1'
  obtain ⟨hbd, hF0⟩ := hB1 E hE
  have hK : (1 : ℝ) ≤ ((3 - E.ηmin : ℤ) : ℝ) := by
    obtain ⟨η, h1, h2⟩ := (E.bounded 0).exists
    have hmin : E.ηmin ≤ 2 := by
      have : E.ηmax = 2 := by rw [hE]; norm_num
      omega
    have hmin' : (E.ηmin : ℝ) ≤ 2 := by exact_mod_cast hmin
    push_cast
    linarith
  have hleast := (hStar E hE).1
  obtain ⟨ε, U, hε, hprofU, hWU, hconv⟩ := hD7 hCmp (effOpStar E) _ hshift hdeg hK hbd hF0
    (singleSourceObstacleSolutionStar E) hleast.1.1 hprof hW
    (fun w hw hnn hsup x _ => (show singleSourceObstacleSolutionStar E ≤ w from hleast.2
      ⟨hw, fun y hy => by have := hnn y hy; linarith,
        (viscFromBelowMuStar_iff (by norm_num) E hE1' _ _).2 hsup⟩) x)
  refine noPosDefLowerTest_of_tendsto (fun j => (hprofU j).continuousOn) hprof.continuousOn
    hconv fun j => ?_
  refine noPosDefLowerTest_of_peano hPS (hprofU j).continuousOn (hWU j) ?_
  exact hC5 _ (regOp_hasTraceShift _ _ _)
    (regOp_degenerateElliptic hshift hdeg _ (hε j).1.le (hε j).2.le) (1 - ε j)
    (by linarith [(hε j).1]) (traceGraph_regOp_lipschitz hshift hdeg _ (hε j).2.le) _ (hprofU j)

end SingleSourceD2

end RandomSandpile

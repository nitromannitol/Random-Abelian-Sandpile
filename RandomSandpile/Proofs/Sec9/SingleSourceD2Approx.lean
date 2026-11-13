import RandomSandpile.Proofs.Sec9.SingleSourceD2Super
import RandomSandpile.Proofs.Sec9.SingleSourceD2Lower
import RandomSandpile.Proofs.Sec9.SingleSourceD2CriticalGeom
import RandomSandpile.Proofs.Sec7.LimitObstacleGamma
import RandomSandpile.Proofs.Sec7.MainTheoremLap

/-!
# Theorem 9.2 in dimension two: regularized source solutions, decomposed

`SourceApproximationStmt` from six steps (`sourceApproximation_of_steps`):
* `RegularizedFamilyStmt` (§§7.1-7.4): for every `ε ∈ (0, 1)` an `F_ε` source profile `U_ε ≤ U`,
  bounded below by `G - B` near the origin uniformly in `ε` (radial barrier, Perron on annuli,
  shrinking the source circle);
* `ViscLaplaceEquicontStmt` (§7.3): bounded functions with viscosity Laplacian bounds
  `-C ≤ Δu ≤ C` on an open set are equicontinuous on its compact subsets;
* `LocalArzelaAscoliStmt`: the Arzelà-Ascoli theorem off the origin (diagonal over compacts);
* `ViscSuperStabilityStmt` (§7.4; CIL Lemma 6.1, Remarks 6.2-6.3): locally uniform limits of
  supersolutions of uniformly converging operators are supersolutions;
* `DilationLeastStmt` (§7.5, replacing removability): a nonnegative `F`-supersolution `W` off the
  origin with `W ≥ G - B` near it lies above the source profile `U = v + G` (dilations
  `λ² W(x/λ)` and the comparison principle, as in `Proofs/Sec9/SingleSourceFstarDilation.lean`);
* `ViscLaplaceWeakStmt` (§7.3): viscosity Laplacian bounds give a locally bounded weak Laplacian.

`viscLaplace_of_profile`: a source profile of an operator with the shift identity and trace graph in
`[a, b]`, `a ≤ 0`, satisfies `Δu ≥ a` and `Δu ≤ b` in the viscosity sense off the origin (at zeros
an upper test has a local minimum).
-/

noncomputable section

open MeasureTheory Filter Topology Metric LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace SingleSourceD2

/-! ### Step statements -/

/-- ** The regularized family**. -/
def RegularizedFamilyStmt : Prop :=
  ShiftComparisonStmt →
  ∀ (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (K : ℝ), HasTraceShift F → DegenerateElliptic F → 1 ≤ K →
    (∀ z, -2 ≤ traceGraph F z ∧ traceGraph F z ≤ K) → 0 ≤ F 0 →
    ∀ v : Rd 2 → ℝ, Continuous v →
      IsSourceProfile F (fun x => v x + fundamentalSolution 2 x) →
      ∃ ρ B : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ U : Rd 2 → ℝ,
        IsSourceProfile (regOp F K ε) U ∧
        (∀ x : Rd 2, x ≠ 0 → U x ≤ v x + fundamentalSolution 2 x) ∧
        ∀ x : Rd 2, x ≠ 0 → ‖x‖ < ρ → fundamentalSolution 2 x - B ≤ U x

/-- ** Equicontinuity** from two-sided viscosity Laplacian bounds. -/
def ViscLaplaceEquicontStmt : Prop :=
  ∀ (V : Set (Rd 2)), IsOpen V → ∀ (C M : ℝ) (S : Set (Rd 2)), IsCompact S → S ⊆ V →
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ u : Rd 2 → ℝ, ContinuousOn u V →
      (∀ x ∈ V, |u x| ≤ M) → ViscFromAboveGE (fun X => X.trace + C) V u →
      ViscFromBelowLE (fun X => X.trace - C) V u →
      ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → |u x - u y| < η

/-- **Arzelà-Ascoli off the origin**: a sequence of continuous functions, uniformly bounded and
equicontinuous on every compact subset of `ℝ² ∖ {0}`, has a subsequence converging locally
uniformly there to a continuous function. -/
def LocalArzelaAscoliStmt : Prop :=
  ∀ u : ℕ → Rd 2 → ℝ, (∀ n, ContinuousOn (u n) {x | x ≠ 0}) →
    (∀ S : Set (Rd 2), IsCompact S → S ⊆ {x | x ≠ 0} → ∃ M : ℝ, ∀ n, ∀ x ∈ S, |u n x| ≤ M) →
    (∀ S : Set (Rd 2), IsCompact S → S ⊆ {x | x ≠ 0} → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → |u n x - u n y| < η) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : Rd 2 → ℝ, ContinuousOn w {x | x ≠ 0} ∧
      TendstoLocallyUniformlyOn (fun n => u (φ n)) w atTop {x | x ≠ 0}

/-- ** Stability of supersolutions** under locally uniform limits, with operators converging
uniformly on symmetric matrices (Crandall-Ishii-Lions Lemma 6.1, Remarks 6.2-6.3). -/
def ViscSuperStabilityStmt : Prop :=
  ∀ (V : Set (Rd 2)), IsOpen V → ∀ (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (Fn : ℕ → Matrix (Fin 2) (Fin 2) ℝ → ℝ) (u : ℕ → Rd 2 → ℝ) (w : Rd 2 → ℝ),
    ContinuousOn F {M | M.IsSymm} →
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm →
      |Fn n M - F M| ≤ η) →
    (∀ n, ContinuousOn (u n) V) → ContinuousOn w V → TendstoLocallyUniformlyOn u w atTop V →
    (∀ n, ViscFromBelowGE (Fn n) V (u n)) → ViscFromBelowGE F V w

/-- ** Leastness by dilation**: a nonnegative `F`-supersolution off the origin, continuous there
and bounded below by `G - B` near the origin, lies above the source profile `v + G`. -/
def DilationLeastStmt : Prop :=
  ShiftComparisonStmt → ∀ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, HasTraceShift F →
    DegenerateElliptic F → ∀ v : Rd 2 → ℝ, Continuous v →
    IsSourceProfile F (fun x => v x + fundamentalSolution 2 x) →
    ∀ W : Rd 2 → ℝ, ContinuousOn W {x | x ≠ 0} → (∀ x : Rd 2, x ≠ 0 → 0 ≤ W x) →
      ViscFromBelowGE F {x | x ≠ 0} W →
      (∃ ρ B : ℝ, 0 < ρ ∧ ∀ x : Rd 2, x ≠ 0 → ‖x‖ < ρ → fundamentalSolution 2 x - B ≤ W x) →
      ∀ x : Rd 2, x ≠ 0 → v x + fundamentalSolution 2 x ≤ W x

/-- ** Viscosity Laplacian bounds give a weak Laplacian**. -/
def ViscLaplaceWeakStmt : Prop :=
  ∀ (V : Set (Rd 2)), IsOpen V → ∀ (C : ℝ) (u : Rd 2 → ℝ), ContinuousOn u V →
    ViscFromAboveGE (fun X => X.trace + C) V u → ViscFromBelowLE (fun X => X.trace - C) V u →
    LocWeakLaplaceBdd V u

/-! ### Laplacian bounds of source profiles -/

/-- At a local minimum of a `C²` function the Laplacian is nonnegative. -/
theorem trace_hessian_nonneg_of_isLocalMin {φ : Rd 2 → ℝ} {x : Rd 2} (hφ : ContDiffAt ℝ 2 φ x)
    (hmin : IsLocalMin φ x) : 0 ≤ (hessian φ x).trace := by
  have hT := hasSecondOrderTaylorAt_of_contDiffAt hφ
  have hp := taylor_grad_eq_zero_of_isLocalMin hT hmin
  rw [hp] at hT
  have key : ∀ e : Rd 2, ‖e‖ = 1 → 0 ≤ qM (hessian φ x) e := by
    intro e he
    by_contra hneg
    have hq : qM (hessian φ x) e < 0 := not_le.mp hneg
    obtain ⟨ρ, hρ, hb⟩ := hT.bound (κ := -(qM (hessian φ x) e) / 2) (by linarith)
    obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.1 hmin
    set t := min (ρ / 2) (r / 2) with ht_def
    have ht : 0 < t := lt_min (by linarith) (by linarith)
    have htρ : t < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htr : t < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hn : ‖x + t • e - x‖ = t := by
      rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos ht]
    have h1 := hb (x + t • e) (by rw [hn]; exact htρ)
    have h2 := hr' (show dist (x + t • e) x < r by rw [dist_eq_norm, hn]; exact htr)
    rw [hn, add_sub_cancel_left, inner_zero_left, qM_smul'] at h1
    have h3 := (abs_le.1 h1).2
    have ht2 : 0 < t ^ 2 := pow_pos ht 2
    nlinarith
  have h0 := key (toE (unit (0 : Fin 2))) (MuLipschitz.norm_toE_unit 0)
  have h1 := key (toE (unit (1 : Fin 2))) (MuLipschitz.norm_toE_unit 1)
  have e0 := two_qM_toE_unit (hessian φ x) 0
  have e1 := two_qM_toE_unit (hessian φ x) 1
  rw [Matrix.trace_fin_two]
  linarith

/-- **Viscosity Laplacian bounds of a source profile**: if `G` has the shift
identity and trace graph in `[a, b]` with `a ≤ 0`, a source profile has `Δu ≥ a` (also at its
zeros) and `Δu ≤ b` off the origin. -/
theorem viscLaplace_of_profile {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hG : HasTraceShift G)
    {a b : ℝ} (hab : ∀ z, a ≤ traceGraph G z ∧ traceGraph G z ≤ b) (ha : a ≤ 0)
    {u : Rd 2 → ℝ} (hu : IsSourceProfile G u) :
    ViscFromAboveGE (fun X => X.trace - a) {x | x ≠ 0} u ∧
      ViscFromBelowLE (fun X => X.trace - b) {x | x ≠ 0} u := by
  constructor
  · intro x hx φ hφ hmax
    have hs := hessian_isSymm_of_contDiffAt hφ
    show 0 ≤ (hessian φ x).trace - a
    rcases (hu.nonneg x hx).lt_or_eq with hpos | hzero
    · have h := hu.subsolution x ⟨hx, hpos⟩ φ hφ hmax
      rw [eq_traceGraph_sub_trace hG hs] at h
      have := (hab (traceFreeCoord (hessian φ x))).1
      linarith
    · have hmin : IsLocalMin φ x := by
        filter_upwards [hmax, (isOpen_ne : IsOpen {y : Rd 2 | y ≠ 0}).mem_nhds hx] with y hy hy0
        have hy' : u y - φ y ≤ u x - φ x := hy
        have := hu.nonneg y hy0
        linarith
      have := trace_hessian_nonneg_of_isLocalMin hφ hmin
      linarith
  · intro x hx φ hφ hmin
    have hs := hessian_isSymm_of_contDiffAt hφ
    have h := hu.supersolution x hx φ hφ hmin
    rw [eq_traceGraph_sub_trace hG hs] at h
    have := (hab (traceFreeCoord (hessian φ x))).2
    show (hessian φ x).trace - b ≤ 0
    linarith

/-- The Laplacian bounds `-2 ≤ Δu ≤ K + 1` for profiles of `F_ε`, in the form `|Δu| ≤ K + 2`. -/
theorem viscLaplace_of_regProfile {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {K ε : ℝ} (hK : 1 ≤ K)
    (hTr : ∀ z, -2 ≤ traceGraph F z ∧ traceGraph F z ≤ K) (hε0 : 0 < ε) (hε1 : ε < 1)
    {u : Rd 2 → ℝ} (hu : IsSourceProfile (regOp F K ε) u) :
    ViscFromAboveGE (fun X => X.trace + (K + 2)) {x | x ≠ 0} u ∧
      ViscFromBelowLE (fun X => X.trace - (K + 2)) {x | x ≠ 0} u := by
  have hab : ∀ z, -2 ≤ traceGraph (regOp F K ε) z ∧ traceGraph (regOp F K ε) z ≤ K + 1 := by
    intro z
    rw [traceGraph_regOp]
    have h1 := (hTr z).1
    have h2 := (hTr z).2
    constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := viscLaplace_of_profile (regOp_hasTraceShift F K ε) hab (by norm_num) hu
  refine ⟨fun x hx φ hφ hmax => ?_, fun x hx φ hφ hmin => ?_⟩
  · have := h1 x hx φ hφ hmax
    show 0 ≤ (hessian φ x).trace + (K + 2)
    have h' : 0 ≤ (hessian φ x).trace - -2 := this
    linarith
  · have := h2 x hx φ hφ hmin
    show (hessian φ x).trace - (K + 2) ≤ 0
    have h' : (hessian φ x).trace - (K + 1) ≤ 0 := this
    linarith

/-! ### Compact sets off the origin -/

/-- A compact set avoiding the origin lies in an open annulus `{r < |x| < R}`, `r > 0`. -/
theorem exists_annulus {S : Set (Rd 2)} (hS : IsCompact S) (hS0 : S ⊆ {x | x ≠ 0}) :
    ∃ r R : ℝ, 0 < r ∧ S ⊆ {x | r < ‖x‖ ∧ ‖x‖ < R} := by
  have h0 : (0 : Rd 2) ∈ Sᶜ := fun h => hS0 h rfl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hS.isClosed.isOpen_compl 0 h0
  obtain ⟨R, hR⟩ := hS.isBounded.subset_ball 0
  refine ⟨r / 2, R, half_pos hr, fun x hx => ⟨?_, ?_⟩⟩
  · by_contra hle
    have : x ∈ ball (0 : Rd 2) r := by
      rw [mem_ball, dist_zero_right]; linarith [not_lt.mp hle]
    exact hball this hx
  · have := hR hx
    rwa [mem_ball, dist_zero_right] at this

theorem isOpen_annulus (r R : ℝ) : IsOpen {x : Rd 2 | r < ‖x‖ ∧ ‖x‖ < R} :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem isCompact_closedAnnulus (r R : ℝ) : IsCompact {x : Rd 2 | r ≤ ‖x‖ ∧ ‖x‖ ≤ R} := by
  refine (isCompact_closedBall (0 : Rd 2) R).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)) fun x hx => ?_
  rw [mem_closedBall, dist_zero_right]; exact hx.2

/-- A function continuous off the origin is bounded on each closed annulus `{r ≤ |x| ≤ R}`,
`r > 0`. -/
theorem exists_bound_annulus {g : Rd 2 → ℝ} (hg : ContinuousOn g {x | x ≠ 0}) {r : ℝ}
    (hr : 0 < r) (R : ℝ) : ∃ M : ℝ, ∀ x : Rd 2, r ≤ ‖x‖ → ‖x‖ ≤ R → |g x| ≤ M := by
  have hsub : {x : Rd 2 | r ≤ ‖x‖ ∧ ‖x‖ ≤ R} ⊆ {x | x ≠ 0} := fun x hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rintro rfl
    rw [norm_zero] at hx
    linarith [hx.1]
  obtain ⟨M, hM⟩ := (isCompact_closedAnnulus r R).exists_bound_of_continuousOn (hg.mono hsub)
  exact ⟨M, fun x h1 h2 => by have := hM x ⟨h1, h2⟩; rwa [Real.norm_eq_abs] at this⟩

/-! ### The reduction -/

/-- The family `U_j` is uniformly bounded and equicontinuous on compact sets off the origin. -/
theorem family_bounds (h2 : ViscLaplaceEquicontStmt) {g : Rd 2 → ℝ}
    (hg : ContinuousOn g {x | x ≠ 0}) {C : ℝ} {U : ℕ → Rd 2 → ℝ}
    (hUc : ∀ n, ContinuousOn (U n) {x | x ≠ 0})
    (hU0 : ∀ n, ∀ x : Rd 2, x ≠ 0 → 0 ≤ U n x) (hUg : ∀ n, ∀ x : Rd 2, x ≠ 0 → U n x ≤ g x)
    (hUa : ∀ n, ViscFromAboveGE (fun X => X.trace + C) {x | x ≠ 0} (U n))
    (hUb : ∀ n, ViscFromBelowLE (fun X => X.trace - C) {x | x ≠ 0} (U n))
    {S : Set (Rd 2)} (hS : IsCompact S) (hS0 : S ⊆ {x | x ≠ 0}) :
    (∃ M : ℝ, ∀ n, ∀ x ∈ S, |U n x| ≤ M) ∧
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ n, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → |U n x - U n y| < η := by
  obtain ⟨r, R, hr, hSV⟩ := exists_annulus hS hS0
  set V := {x : Rd 2 | r < ‖x‖ ∧ ‖x‖ < R} with hV
  have hV0 : V ⊆ {x | x ≠ 0} := fun x hx => by
    simp only [hV, Set.mem_ofPred_eq] at hx ⊢
    rintro rfl
    rw [norm_zero] at hx
    linarith [hx.1]
  obtain ⟨M, hM⟩ := exists_bound_annulus hg hr R
  have hUM : ∀ n, ∀ x ∈ V, |U n x| ≤ M := fun n x hx => by
    have hx0 := hV0 hx
    have h1 := hU0 n x hx0
    have h2 := hUg n x hx0
    have h3 := hM x hx.1.le hx.2.le
    rw [abs_of_nonneg h1]
    linarith [le_abs_self (g x)]
  refine ⟨⟨M, fun n x hx => hUM n x (hSV hx)⟩, fun η hη => ?_⟩
  obtain ⟨δ, hδ, hδu⟩ := h2 V (isOpen_annulus r R) C M S hS hSV η hη
  exact ⟨δ, hδ, fun n => hδu (U n) ((hUc n).mono hV0) (hUM n)
    (fun x hx => hUa n x (hV0 hx)) (fun x hx => hUb n x (hV0 hx))⟩

/-- `F` is continuous on symmetric matrices (shift identity and Lipschitz trace graph). -/
theorem continuousOn_symm {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    (hdeg : DegenerateElliptic F) : ContinuousOn F {M | M.IsSymm} := by
  have hc : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      traceGraph F (traceFreeCoord M) - M.trace := by
    have hL : LipschitzWith 1 (traceGraph F) := LipschitzWith.of_dist_le_mul fun z z' => by
      rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
      exact traceGraph_lipschitz hF hdeg z z'
    have hZ : Continuous (traceFreeCoord : Matrix (Fin 2) (Fin 2) ℝ → Rd 2) := by
      unfold traceFreeCoord
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      fin_cases i
      · show Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0 - M 1 1
        fun_prop
      · show Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => 2 * M 0 1
        fun_prop
    exact (hL.continuous.comp hZ).sub (continuous_id.matrix_trace)
  exact hc.continuousOn.congr fun M hM => eq_traceGraph_sub_trace hF hM

/-- from its steps. -/
theorem sourceApproximation_of_steps (h1 : RegularizedFamilyStmt) (h2 : ViscLaplaceEquicontStmt)
    (h3 : LocalArzelaAscoliStmt) (h4 : ViscSuperStabilityStmt) (h5 : DilationLeastStmt)
    (h6 : ViscLaplaceWeakStmt) : SourceApproximationStmt := by
  intro hSC F K hT hDE hK hTr hF0 v hv hprof _hW _hleast
  obtain ⟨ρ, B, hρ, hfam⟩ := h1 hSC F K hT hDE hK hTr hF0 v hv hprof
  set ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2) with hε_def
  have hε : ∀ j, 0 < ε j ∧ ε j < 1 := fun j => by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    refine ⟨show 0 < 1 / ((j : ℝ) + 2) by positivity, ?_⟩
    show 1 / ((j : ℝ) + 2) < 1
    rw [div_lt_one (by positivity)]
    linarith
  choose U hU using fun j => hfam (ε j) (hε j).1 (hε j).2
  have hlap := fun j => viscLaplace_of_regProfile hK hTr (hε j).1 (hε j).2 (hU j).1
  have hbd := fun S (hS : IsCompact S) (hS0 : S ⊆ {x : Rd 2 | x ≠ 0}) =>
    family_bounds h2 hprof.continuousOn (fun n => (hU n).1.continuousOn)
      (fun n => (hU n).1.nonneg) (fun n => (hU n).2.1) (fun n => (hlap n).1)
      (fun n => (hlap n).2) hS hS0
  obtain ⟨φ, hφ, w, hwc, hconv⟩ := h3 U (fun n => (hU n).1.continuousOn)
    (fun S hS hS0 => (hbd S hS hS0).1) (fun S hS hS0 => (hbd S hS hS0).2)
  -- the limit is a supersolution of `F`
  have hFn : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm →
      |regOp F K (ε (φ n)) M - F M| ≤ η := by
    intro η hη
    have hK3 : 0 < K + 3 := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((K + 3) / η)
    filter_upwards [eventually_ge_atTop N] with n hn M hM
    have hφn : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [eq_traceGraph_sub_trace hT hM]
    simp only [regOp]
    have hf := hTr (traceFreeCoord M)
    have e : (1 - ε (φ n)) * traceGraph F (traceFreeCoord M) + ε (φ n) * (K + 1) - M.trace -
        (traceGraph F (traceFreeCoord M) - M.trace) =
          ε (φ n) * (K + 1 - traceGraph F (traceFreeCoord M)) := by ring
    rw [e, abs_mul, abs_of_pos (hε (φ n)).1]
    have hb : |K + 1 - traceGraph F (traceFreeCoord M)| ≤ K + 3 := by
      rw [abs_le]; constructor <;> linarith [hf.1, hf.2]
    have hεb : ε (φ n) * (K + 3) ≤ η := by
      show 1 / ((φ n : ℝ) + 2) * (K + 3) ≤ η
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hη] at hN
      nlinarith
    calc ε (φ n) * |K + 1 - traceGraph F (traceFreeCoord M)| ≤ ε (φ n) * (K + 3) :=
          mul_le_mul_of_nonneg_left hb (hε (φ n)).1.le
      _ ≤ η := hεb
  have hwsup : ViscFromBelowGE F {x | x ≠ 0} w :=
    h4 {x | x ≠ 0} isOpen_ne F (fun n => regOp F K (ε (φ n))) (fun n => U (φ n)) w
      (continuousOn_symm hT hDE) hFn (fun n => (hU (φ n)).1.continuousOn) hwc hconv
      (fun n => (hU (φ n)).1.supersolution)
  -- pointwise bounds pass to the limit
  have hlim : ∀ x : Rd 2, x ≠ 0 → Tendsto (fun n => U (φ n) x) atTop (𝓝 (w x)) :=
    fun x hx => hconv.tendsto_at hx
  have hw0 : ∀ x : Rd 2, x ≠ 0 → 0 ≤ w x := fun x hx =>
    ge_of_tendsto (hlim x hx) (Eventually.of_forall fun n => (hU (φ n)).1.nonneg x hx)
  have hwle : ∀ x : Rd 2, x ≠ 0 → w x ≤ v x + fundamentalSolution 2 x := fun x hx =>
    le_of_tendsto (hlim x hx) (Eventually.of_forall fun n => (hU (φ n)).2.1 x hx)
  have hwB : ∀ x : Rd 2, x ≠ 0 → ‖x‖ < ρ → fundamentalSolution 2 x - B ≤ w x :=
    fun x hx hxρ => ge_of_tendsto (hlim x hx)
      (Eventually.of_forall fun n => (hU (φ n)).2.2 x hx hxρ)
  have hge := h5 hSC F hT hDE v hv hprof w hwc hw0 hwsup ⟨ρ, B, hρ, hwB⟩
  have heq : Set.EqOn w (fun x => v x + fundamentalSolution 2 x) {x | x ≠ 0} :=
    fun x hx => le_antisymm (hwle x hx) (hge x hx)
  refine ⟨fun j => ε (φ j), fun j => U (φ j), fun j => hε (φ j), fun j => (hU (φ j)).1,
    fun j => ?_, hconv.congr_right heq⟩
  exact h6 {x | x ≠ 0} isOpen_ne (K + 2) (U (φ j)) (hU (φ j)).1.continuousOn (hlap (φ j)).1
    (hlap (φ j)).2

end SingleSourceD2

end RandomSandpile

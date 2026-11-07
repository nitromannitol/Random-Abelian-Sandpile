import RandomSandpile.Proofs.Sec9.SingleSourceD2Perron

/-!
# Theorem 9.2 in dimension two: tools for shrinking the source circle

For SIMPLE-PROOF §7.4:
* the closure of the annulus `{r < |x| < L}` is `{r ≤ |x| ≤ L}` (`closure_annSet`);
* the radial clamp `x ↦ (min L (max r |x|) / |x|) x` onto the closed annulus (`clampMap`), used to
  extend the annulus solutions continuously to `ℝ² ∖ {0}`;
* Laplacian bounds for `F_ε`-solutions on an open set (`viscLaplace_of_regSol`);
* viscosity properties only depend on the function near the point (`congr_open` lemmas);
* finitely many exceptions in uniform estimates (`exists_forall_of_eventually`,
  `exists_bound_of_eventually`);
* subsolutions of `G` are supersolutions of `M ↦ -G(-M)` for `-u`, and back.
-/

noncomputable section

open Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

/-! ### The closed annulus -/

theorem closedAnnulus_subset_closure {r L : ℝ} (hr : 0 < r) (hrL : r < L) :
    {x : Rd 2 | r ≤ ‖x‖ ∧ ‖x‖ ≤ L} ⊆ closure (annSet r L) := by
  intro x hx
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le hr hx.1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (r + L) / 2 := ⟨_, rfl⟩
  have hmr : r < m := by rw [hm]; linarith
  have hmL : m < L := by rw [hm]; linarith
  have hc : Continuous fun t : ℝ => ((1 - t) + t * (m / ‖x‖)) • x := by fun_prop
  have hT : Tendsto (fun t : ℝ => ((1 - t) + t * (m / ‖x‖)) • x) (𝓝[>] 0) (𝓝 x) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [h0, h1] with t ht0 ht1
  have hcpos : 0 < (1 - t) + t * (m / ‖x‖) :=
    add_pos (by linarith) (mul_pos ht0 (div_pos (by linarith) hx0))
  have hn : ‖((1 - t) + t * (m / ‖x‖)) • x‖ = (1 - t) * ‖x‖ + t * m := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, add_mul, mul_assoc,
      div_mul_cancel₀ m hx0.ne']
  show r < ‖((1 - t) + t * (m / ‖x‖)) • x‖ ∧ ‖((1 - t) + t * (m / ‖x‖)) • x‖ < L
  rw [hn]
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith [hx.1] : (0 : ℝ) ≤ ‖x‖ - r),
      mul_pos ht0 (by linarith : (0 : ℝ) < m - r)]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith [hx.2] : (0 : ℝ) ≤ L - ‖x‖),
      mul_pos ht0 (by linarith : (0 : ℝ) < L - m)]

theorem closure_annSet {r L : ℝ} (hr : 0 < r) (hrL : r < L) :
    closure (annSet r L) = {x : Rd 2 | r ≤ ‖x‖ ∧ ‖x‖ ≤ L} :=
  Set.Subset.antisymm (closure_annSet_subset r L) (closedAnnulus_subset_closure hr hrL)

/-! ### The radial clamp -/

/-- The radial clamp onto `{r ≤ |x| ≤ L}`. -/
def clampMap (r L : ℝ) (x : Rd 2) : Rd 2 := (min L (max r ‖x‖) / ‖x‖) • x

theorem norm_clampMap {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) {x : Rd 2} (hx : x ≠ 0) :
    ‖clampMap r L x‖ = min L (max r ‖x‖) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hpos : 0 ≤ min L (max r ‖x‖) / ‖x‖ :=
    div_nonneg (le_min (by linarith) (le_max_of_le_left hr.le)) hx0.le
  rw [clampMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos, div_mul_cancel₀ _ hx0.ne']

theorem clampMap_eq {r L : ℝ} {x : Rd 2} (hx0 : x ≠ 0) (h1 : r ≤ ‖x‖) (h2 : ‖x‖ ≤ L) :
    clampMap r L x = x := by
  have hx : 0 < ‖x‖ := norm_pos_iff.2 hx0
  rw [clampMap, max_eq_right h1, min_eq_right h2, div_self hx.ne', one_smul]

theorem clampMap_mem {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) {x : Rd 2} (hx : x ≠ 0) :
    r ≤ ‖clampMap r L x‖ ∧ ‖clampMap r L x‖ ≤ L := by
  rw [norm_clampMap hr hrL hx]
  exact ⟨le_min hrL (le_max_left _ _), min_le_left _ _⟩

theorem continuousOn_clampMap (r L : ℝ) : ContinuousOn (clampMap r L) {x : Rd 2 | x ≠ 0} := by
  have h1 : ContinuousOn (fun x : Rd 2 => min L (max r ‖x‖) / ‖x‖) {x : Rd 2 | x ≠ 0} :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => norm_ne_zero_iff.2 hx
  exact h1.smul continuousOn_id

/-! ### Laplacian bounds of `F_ε` solutions on an open set -/

theorem viscLaplace_of_regSol {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {K ε : ℝ} (hK : 1 ≤ K)
    (hTr : ∀ z, -2 ≤ traceGraph F z ∧ traceGraph F z ≤ K) (hε0 : 0 < ε) (hε1 : ε < 1)
    {O : Set (Rd 2)} (hO : IsOpen O) {u : Rd 2 → ℝ} (hsup : ViscFromBelowGE (regOp F K ε) O u)
    (hsub : ViscFromAboveLE (regOp F K ε) {x | x ∈ O ∧ 0 < u x} u)
    (hnn : ∀ x ∈ O, 0 ≤ u x) :
    ViscFromAboveGE (fun X => X.trace + (K + 2)) O u ∧
      ViscFromBelowLE (fun X => X.trace - (K + 2)) O u := by
  have hab : ∀ z, -2 ≤ traceGraph (regOp F K ε) z ∧ traceGraph (regOp F K ε) z ≤ K + 1 := by
    intro z
    rw [traceGraph_regOp]
    have h1 := (hTr z).1
    have h2 := (hTr z).2
    constructor <;> nlinarith
  have hG := regOp_hasTraceShift F K ε
  constructor
  · intro x hx φ hφ hmax
    have hs := hessian_isSymm_of_contDiffAt hφ
    show 0 ≤ (hessian φ x).trace + (K + 2)
    rcases (hnn x hx).lt_or_eq with hpos | hzero
    · have h := hsub x ⟨hx, hpos⟩ φ hφ hmax
      rw [eq_traceGraph_sub_trace hG hs] at h
      have := (hab (traceFreeCoord (hessian φ x))).1
      linarith
    · have hmin : IsLocalMin φ x := by
        filter_upwards [hmax, hO.mem_nhds hx] with y hy hyO
        have hy' : u y - φ y ≤ u x - φ x := hy
        have := hnn y hyO
        linarith
      have := trace_hessian_nonneg_of_isLocalMin hφ hmin
      linarith
  · intro x hx φ hφ hmin
    have hs := hessian_isSymm_of_contDiffAt hφ
    have h := hsup x hx φ hφ hmin
    rw [eq_traceGraph_sub_trace hG hs] at h
    have := (hab (traceFreeCoord (hessian φ x))).2
    show (hessian φ x).trace - (K + 2) ≤ 0
    linarith

/-! ### Locality -/

theorem ViscFromBelowGE.congr_open {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {S O : Set (Rd 2)}
    (hO : IsOpen O) (hSO : S ⊆ O) {u w : Rd 2 → ℝ} (heq : ∀ x ∈ O, u x = w x)
    (h : ViscFromBelowGE G S u) : ViscFromBelowGE G S w := by
  intro x hx φ hφ hmin
  refine h x hx φ hφ (hmin.congr ?_)
  filter_upwards [hO.mem_nhds (hSO hx)] with y hy
  show w y - φ y = u y - φ y
  rw [heq y hy]

theorem ViscFromAboveLE.congr_open {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {S O : Set (Rd 2)}
    (hO : IsOpen O) (hSO : S ⊆ O) {u w : Rd 2 → ℝ} (heq : ∀ x ∈ O, u x = w x)
    (h : ViscFromAboveLE G S u) : ViscFromAboveLE G S w := by
  intro x hx φ hφ hmax
  refine h x hx φ hφ (hmax.congr ?_)
  filter_upwards [hO.mem_nhds (hSO hx)] with y hy
  show w y - φ y = u y - φ y
  rw [heq y hy]

/-! ### Finitely many exceptions -/

theorem exists_forall_of_eventually {P : ℕ → ℝ → Prop}
    (hmono : ∀ n δ δ', 0 < δ' → δ' ≤ δ → P n δ → P n δ') (hone : ∀ n, ∃ δ > 0, P n δ)
    (hev : ∃ N, ∃ δ > 0, ∀ n, N ≤ n → P n δ) : ∃ δ > 0, ∀ n, P n δ := by
  obtain ⟨N, hN⟩ := hev
  induction N with
  | zero =>
    obtain ⟨δ, hδ, h⟩ := hN
    exact ⟨δ, hδ, fun n => h n (Nat.zero_le n)⟩
  | succ N ih =>
    apply ih
    obtain ⟨δ, hδ, h⟩ := hN
    obtain ⟨δN, hδN, hN'⟩ := hone N
    refine ⟨min δ δN, lt_min hδ hδN, fun n hn => ?_⟩
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · exact hmono _ _ _ (lt_min hδ hδN) (min_le_right _ _) hN'
    · exact hmono _ _ _ (lt_min hδ hδN) (min_le_left _ _) (h n hlt)

theorem exists_bound_of_eventually {P : ℕ → ℝ → Prop}
    (hmono : ∀ n M M', M ≤ M' → P n M → P n M') (hone : ∀ n, ∃ M, P n M)
    (hev : ∃ N, ∃ M, ∀ n, N ≤ n → P n M) : ∃ M, ∀ n, P n M := by
  obtain ⟨N, hN⟩ := hev
  induction N with
  | zero =>
    obtain ⟨M, h⟩ := hN
    exact ⟨M, fun n => h n (Nat.zero_le n)⟩
  | succ N ih =>
    apply ih
    obtain ⟨M, h⟩ := hN
    obtain ⟨MN, hN'⟩ := hone N
    refine ⟨max M MN, fun n hn => ?_⟩
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · exact hmono _ _ _ (le_max_right _ _) hN'
    · exact hmono _ _ _ (le_max_left _ _) (h n hlt)

/-! ### Subsolutions as supersolutions -/

theorem viscFromBelowGE_neg_of_aboveLE {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {O : Set (Rd 2)}
    {u : Rd 2 → ℝ} (h : ViscFromAboveLE G O u) :
    ViscFromBelowGE (fun M => -G (-M)) O (fun x => -u x) := by
  intro x hx φ hφ hmin
  have hmax : IsLocalMax (fun y => u y - (fun y => -φ y) y) x := by
    filter_upwards [hmin] with y hy
    have hy' : -u x - φ x ≤ -u y - φ y := hy
    show u y - -φ y ≤ u x - -φ x
    linarith
  have h1 : G (hessian (fun y => -φ y) x) ≤ 0 := h x hx (fun y => -φ y) hφ.neg hmax
  rw [hessian_neg'] at h1
  show 0 ≤ -G (-hessian φ x)
  linarith

theorem viscFromAboveLE_of_neg {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {O : Set (Rd 2)}
    {w : Rd 2 → ℝ} (h : ViscFromBelowGE (fun M => -G (-M)) O (fun x => -w x)) :
    ViscFromAboveLE G O w := by
  intro x hx φ hφ hmax
  have hmin : IsLocalMin (fun y => (fun x => -w x) y - (fun y => -φ y) y) x := by
    filter_upwards [hmax] with y hy
    have hy' : w y - φ y ≤ w x - φ x := hy
    show -w x - -φ x ≤ -w y - -φ y
    linarith
  have h1 : 0 ≤ -G (-hessian (fun y => -φ y) x) := h x hx (fun y => -φ y) hφ.neg hmin
  rw [hessian_neg', neg_neg] at h1
  linarith

end SingleSourceD2

end RandomSandpile

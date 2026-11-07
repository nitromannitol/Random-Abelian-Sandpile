import RandomSandpile.Proofs.Sec9.SingleSourceD2FamilyPrep
import RandomSandpile.Proofs.Sec9.SingleSourceD2Stability
import RandomSandpile.Proofs.Sec9.SingleSourceD2Ascoli

/-!
# Theorem 9.2 in dimension two: the regularized family

`regularizedFamily : CILTheoremOfSumsStmt → CILPerronStmt → AlexandrovStmt → RegularizedFamilyStmt`.

For fixed `ε`, the annulus solutions `u_r` of `annulus_solution` (radii `r_n = r₁/(n + 2) → 0`) are
extended to `ℝ² ∖ {0}` through the radial clamp onto `{r_n ≤ |x| ≤ L}` (`ext_props`). On every
compact set off the origin they are bounded by `U` and, apart from finitely many `n`,
equicontinuous by the Laplacian bounds (`viscLaplaceEquicont`); Arzelà-Ascoli off the origin gives a
locally uniform limit `U_ε`. Stability (`viscSuperStability`, applied to tails of the sequence, and to
`-u` with `M ↦ -F_ε(-M)` on small balls where the limit is positive) makes `U_ε` an `F_ε` source
profile, with `V_1 ≤ U_ε ≤ U`; the barrier gives `U_ε ≥ G - B` near the origin uniformly in `ε`.
-/

noncomputable section

open Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

open CrandallIshiiLions

/-! ### Locally uniform convergence -/

theorem tendstoLocallyUniformlyOn_shift {F : ℕ → Rd 2 → ℝ} {f : Rd 2 → ℝ} {s : Set (Rd 2)}
    (h : TendstoLocallyUniformlyOn F f atTop s) (N : ℕ) :
    TendstoLocallyUniformlyOn (fun k => F (k + N)) f atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := h u hu x hx
  exact ⟨t, ht, (tendsto_add_atTop_nat N).eventually hev⟩

theorem tendstoLocallyUniformlyOn_neg {F : ℕ → Rd 2 → ℝ} {f : Rd 2 → ℝ} {s : Set (Rd 2)}
    (h : TendstoLocallyUniformlyOn F f atTop s) :
    TendstoLocallyUniformlyOn (fun n x => -F n x) (fun x => -f x) atTop s := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at h ⊢
  intro ε hε x hx
  obtain ⟨t, ht, hev⟩ := h ε hε x hx
  exact ⟨t, ht, hev.mono fun n hn y hy => by rw [dist_neg_neg]; exact hn y hy⟩

/-! ### Stability along the sequence -/

theorem limit_super {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hG : ContinuousOn G {M | M.IsSymm})
    {u : ℕ → Rd 2 → ℝ} {rs : ℕ → ℝ} (hrs : Tendsto rs atTop (𝓝 0)) (hanti : Antitone rs)
    (huc : ∀ n, ContinuousOn (u n) {x | x ≠ 0})
    (hsup : ∀ n, ViscFromBelowGE G {x | rs n < ‖x‖} (u n))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {w : Rd 2 → ℝ} (hwc : ContinuousOn w {x | x ≠ 0})
    (hconv : TendstoLocallyUniformlyOn (fun k => u (φ k)) w atTop {x | x ≠ 0}) :
    ViscFromBelowGE G {x | x ≠ 0} w := by
  intro x hx ψ hψ hmin
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨N, hN⟩ : ∃ N, rs N < ‖x‖ / 2 := (hrs.eventually (gt_mem_nhds (half_pos hx0))).exists
  have hVo : IsOpen {y : Rd 2 | ‖x‖ / 2 < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hV0 : {y : Rd 2 | ‖x‖ / 2 < ‖y‖} ⊆ {y | y ≠ 0} := fun y hy =>
    norm_pos_iff.1 (lt_trans (half_pos hx0) hy)
  have hrsk : ∀ k, rs (φ (k + N)) < ‖x‖ / 2 := fun k =>
    lt_of_le_of_lt (hanti (le_trans (Nat.le_add_left N k) (hφ.id_le _))) hN
  have hsupk : ∀ k, ViscFromBelowGE G {y : Rd 2 | ‖x‖ / 2 < ‖y‖} (u (φ (k + N))) :=
    fun k y hy => hsup _ y (lt_trans (hrsk k) hy)
  have hconv' : TendstoLocallyUniformlyOn (fun k => u (φ (k + N))) w atTop
      {y : Rd 2 | ‖x‖ / 2 < ‖y‖} :=
    (tendstoLocallyUniformlyOn_shift hconv N).mono hV0
  have h := viscSuperStability _ hVo G (fun _ => G) (fun k => u (φ (k + N))) w hG
    (fun η hη => Eventually.of_forall fun _ M _ => by rw [sub_self, abs_zero]; exact hη.le)
    (fun k => (huc _).mono hV0) (hwc.mono hV0) hconv' hsupk
  exact h x (half_lt_self hx0) ψ hψ hmin

theorem limit_sub {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hG : ContinuousOn G {M | M.IsSymm})
    {u : ℕ → Rd 2 → ℝ} {rs : ℕ → ℝ} (hrs : Tendsto rs atTop (𝓝 0)) (hanti : Antitone rs)
    (huc : ∀ n, ContinuousOn (u n) {x | x ≠ 0})
    (hsub : ∀ n, ViscFromAboveLE G {x | rs n < ‖x‖ ∧ 0 < u n x} (u n))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {w : Rd 2 → ℝ} (hwc : ContinuousOn w {x | x ≠ 0})
    (hconv : TendstoLocallyUniformlyOn (fun k => u (φ k)) w atTop {x | x ≠ 0}) :
    ViscFromAboveLE G {x | x ≠ 0 ∧ 0 < w x} w := by
  intro x hx ψ hψ hmax
  obtain ⟨hx0', hwx⟩ := hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx0'
  have hcont : ContinuousAt w x := (hwc x hx0').continuousAt (isOpen_ne.mem_nhds hx0')
  obtain ⟨ρ1, hρ1, hball1⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (lt_mem_nhds (half_lt_self hwx)))
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = min (‖x‖ / 4) (ρ1 / 2) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; positivity
  have hρ1' : ρ < ρ1 := by rw [hρ_def]; exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ1)
  have hρx : ρ ≤ ‖x‖ / 4 := by rw [hρ_def]; exact min_le_left _ _
  have hfar : ∀ y ∈ closedBall x ρ, ‖x‖ / 2 < ‖y‖ := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have := norm_sub_norm_le x y
    rw [norm_sub_rev] at hy
    linarith
  have hcb0 : closedBall x ρ ⊆ {y | y ≠ 0} := fun y hy =>
    norm_pos_iff.1 (lt_trans (half_pos hx0) (hfar y hy))
  have hwpos : ∀ y ∈ closedBall x ρ, w x / 2 < w y := fun y hy =>
    hball1 (lt_of_le_of_lt (mem_closedBall.1 hy) hρ1')
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ne).1 hconv
    (closedBall x ρ) hcb0 (isCompact_closedBall x ρ)
  have hev1 := Metric.tendstoUniformlyOn_iff.1 hunif (w x / 4) (by positivity)
  obtain ⟨N0, hN0⟩ : ∃ N0, rs N0 < ‖x‖ / 2 := (hrs.eventually (gt_mem_nhds (half_pos hx0))).exists
  have hev2 : ∀ᶠ k in atTop, rs (φ k) < ‖x‖ / 2 := by
    filter_upwards [eventually_ge_atTop N0] with k hk
    exact lt_of_le_of_lt (hanti (le_trans hk (hφ.id_le k))) hN0
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev1.and hev2)
  -- on the ball the tail is a positive subsolution
  have hpos : ∀ k, ∀ y ∈ ball x ρ, 0 < u (φ (k + N)) y := by
    intro k y hy
    have h1 := (hN (k + N) (Nat.le_add_left N k)).1 y (ball_subset_closedBall hy)
    have h2 := hwpos y (ball_subset_closedBall hy)
    rw [Real.dist_eq] at h1
    have := (abs_lt.1 h1).2
    linarith
  have hsubk : ∀ k, ViscFromAboveLE G (ball x ρ) (u (φ (k + N))) := by
    intro k y hy
    exact hsub _ y ⟨lt_trans (hN (k + N) (Nat.le_add_left N k)).2 (hfar y (ball_subset_closedBall hy)),
      hpos k y hy⟩
  have hG' : ContinuousOn (fun M : Matrix (Fin 2) (Fin 2) ℝ => -G (-M)) {M | M.IsSymm} :=
    (hG.comp continuousOn_neg fun M hM => Matrix.IsSymm.neg hM).neg
  have hb0 : ball x ρ ⊆ {y | y ≠ 0} := ball_subset_closedBall.trans hcb0
  have hconv' : TendstoLocallyUniformlyOn (fun k y => -u (φ (k + N)) y) (fun y => -w y) atTop
      (ball x ρ) :=
    tendstoLocallyUniformlyOn_neg ((tendstoLocallyUniformlyOn_shift hconv N).mono hb0)
  have h := viscSuperStability _ isOpen_ball (fun M => -G (-M)) (fun _ M => -G (-M))
    (fun k y => -u (φ (k + N)) y) (fun y => -w y) hG'
    (fun η hη => Eventually.of_forall fun _ M _ => by rw [sub_self, abs_zero]; exact hη.le)
    (fun k => ((huc _).mono hb0).neg) ((hwc.mono hb0).neg) hconv'
    (fun k => viscFromBelowGE_neg_of_aboveLE (hsubk k))
  exact viscFromAboveLE_of_neg h x (mem_ball_self hρ) ψ hψ hmax

/-! ### The extended annulus solutions -/

theorem ext_props {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    (hdeg : DegenerateElliptic F) {K : ℝ} (hK : 1 ≤ K) (hF0 : 0 ≤ F 0) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {U : Rd 2 → ℝ} {r L0 L : ℝ} (hr : 0 < r) (hrL0 : r < L0) (hL0L : L0 < L)
    (hU0 : ∀ x : Rd 2, L0 ≤ ‖x‖ → U x = 0) (hLR : rad2 (K + 2) 1 ≤ L ^ 2)
    {u : Rd 2 → ℝ} (huc : ContinuousOn u (closure (annSet r L)))
    (hub : ∀ x ∈ closure (annSet r L), Vbar (K + 2) 1 x ≤ u x ∧ u x ≤ U x)
    (husup : ViscFromBelowGE (regOp F K ε) (annSet r L) u)
    (husub : ViscFromAboveLE (regOp F K ε) {x | x ∈ annSet r L ∧ 0 < u x} u) :
    ContinuousOn (fun x => u (clampMap r L x)) {x | x ≠ 0} ∧
      (∀ x : Rd 2, x ≠ 0 → 0 ≤ u (clampMap r L x)) ∧
      (∀ x : Rd 2, r ≤ ‖x‖ → Vbar (K + 2) 1 x ≤ u (clampMap r L x) ∧ u (clampMap r L x) ≤ U x) ∧
      ViscFromBelowGE (regOp F K ε) {x | r < ‖x‖} (fun x => u (clampMap r L x)) ∧
      ViscFromAboveLE (regOp F K ε) {x | r < ‖x‖ ∧ 0 < u (clampMap r L x)}
        (fun x => u (clampMap r L x)) := by
  have hc : (0 : ℝ) < K + 2 := by linarith
  have hrL : r < L := by linarith
  have hcl := closure_annSet hr hrL
  have hP : ∀ x : Rd 2, x ≠ 0 → clampMap r L x ∈ closure (annSet r L) := fun x hx => by
    rw [hcl]
    exact clampMap_mem hr hrL.le hx
  have hP0 : ∀ x : Rd 2, x ≠ 0 → clampMap r L x ≠ 0 := fun x hx h => by
    have := (clampMap_mem hr hrL.le hx).1
    rw [h, norm_zero] at this
    linarith
  have hnn : ∀ x : Rd 2, x ≠ 0 → 0 ≤ u (clampMap r L x) := fun x hx =>
    (Vbar_nonneg hc one_pos (hP0 x hx)).trans (hub _ (hP x hx)).1
  have hzero : ∀ x : Rd 2, L0 ≤ ‖x‖ → u (clampMap r L x) = 0 := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      linarith
    have hL0P : L0 ≤ ‖clampMap r L x‖ := by
      rw [norm_clampMap hr hrL.le hx0]
      exact le_min hL0L.le (le_max_of_le_right hx)
    have h1 := (hub _ (hP x hx0)).2
    rw [hU0 _ hL0P] at h1
    exact le_antisymm h1 (hnn x hx0)
  have heqA : ∀ x ∈ annSet r L, u x = u (clampMap r L x) := fun x hx => by
    rw [clampMap_eq (norm_pos_iff.1 (lt_trans hr hx.1)) hx.1.le hx.2.le]
  have hOpen : IsOpen {x : Rd 2 | L0 < ‖x‖} := isOpen_lt continuous_const continuous_norm
  refine ⟨huc.comp (continuousOn_clampMap r L) fun x hx => hP x hx, hnn, fun x hx => ?_, ?_, ?_⟩
  · have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hr hx)
    by_cases hxL : ‖x‖ ≤ L
    · rw [clampMap_eq hx0 hx hxL]
      exact hub x (by rw [hcl]; exact ⟨hx, hxL⟩)
    · have hxL0 : L0 ≤ ‖x‖ := by linarith [not_le.1 hxL]
      rw [hzero x hxL0, hU0 x hxL0]
      have hsq := pow_le_pow_left₀ (by linarith) (not_le.1 hxL).le 2
      exact ⟨le_of_eq (Vbar_eq_zero hc one_pos (by linarith)), le_refl _⟩
  · intro x hx φ hφ hmin
    by_cases hxL : ‖x‖ < L
    · exact (ViscFromBelowGE.congr_open (isOpen_annSet r L) subset_rfl heqA husup) x
        ⟨hx, hxL⟩ φ hφ hmin
    · have hconst := viscFromBelowGE_regOp_const hF hdeg hK hε0.le hε1.le hF0
        {x : Rd 2 | L0 < ‖x‖} 0
      exact (ViscFromBelowGE.congr_open hOpen subset_rfl
        (fun y hy => (hzero y (le_of_lt hy)).symm) hconst) x
        (show L0 < ‖x‖ by linarith [not_lt.1 hxL]) φ hφ hmin
  · intro x hx φ hφ hmax
    have hxL0 : ‖x‖ < L0 := by
      by_contra h
      have := hzero x (not_lt.1 h)
      linarith [hx.2]
    have hxA : x ∈ annSet r L := ⟨hx.1, by linarith⟩
    have hsub' := ViscFromAboveLE.congr_open (S := {y | y ∈ annSet r L ∧ 0 < u y})
      (isOpen_annSet r L) (fun y hy => hy.1) heqA husub
    refine hsub' x ⟨hxA, ?_⟩ φ hφ hmax
    rw [heqA x hxA]
    exact hx.2

/-! ### The limit -/

/-- The radii `r₁/(n + 2)`. -/
def radSeq (r1 : ℝ) (n : ℕ) : ℝ := r1 / ((n : ℝ) + 2)

/-- The extended annulus solutions. -/
def extSeq (u : ℝ → Rd 2 → ℝ) (r1 L : ℝ) (n : ℕ) (x : Rd 2) : ℝ :=
  u (radSeq r1 n) (clampMap (radSeq r1 n) L x)

theorem radSeq_pos {r1 : ℝ} (hr1 : 0 < r1) (n : ℕ) : 0 < radSeq r1 n := by
  unfold radSeq
  positivity

theorem radSeq_lt {r1 : ℝ} (hr1 : 0 < r1) (n : ℕ) : radSeq r1 n < r1 := by
  unfold radSeq
  rw [div_lt_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem radSeq_antitone {r1 : ℝ} (hr1 : 0 < r1) : Antitone (radSeq r1) := fun m n hmn => by
  unfold radSeq
  have h : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
  exact div_le_div_of_nonneg_left hr1.le (by positivity) (by linarith)

theorem radSeq_tendsto (r1 : ℝ) : Tendsto (radSeq r1) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)

/-- **The `r → 0` limit** for fixed `ε`. -/
theorem regProfile_of_annuli (hA : AlexandrovStmt) {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hF : HasTraceShift F) (hdeg : DegenerateElliptic F) {K : ℝ} (hK : 1 ≤ K)
    (hTr : ∀ z, -2 ≤ traceGraph F z ∧ traceGraph F z ≤ K) (hF0 : 0 ≤ F 0) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {U : Rd 2 → ℝ} (hUc : ContinuousOn U {x | x ≠ 0}) {L0 : ℝ}
    (hL01 : 1 ≤ L0) (hU0 : ∀ x : Rd 2, L0 ≤ ‖x‖ → U x = 0)
    (hLR : rad2 (K + 2) 1 ≤ (L0 + 1) ^ 2) (hV : Tendsto (Vbar (K + 2) 1) (𝓝[≠] 0) atTop)
    {r1 : ℝ} (hr1 : 0 < r1) (hr11 : r1 ≤ 1)
    (hsol : ∀ r : ℝ, 0 < r → r < r1 → ∃ u : Rd 2 → ℝ,
      ContinuousOn u (closure (annSet r (L0 + 1))) ∧
      (∀ x ∈ closure (annSet r (L0 + 1)), Vbar (K + 2) 1 x ≤ u x ∧ u x ≤ U x) ∧
      ViscFromBelowGE (regOp F K ε) (annSet r (L0 + 1)) u ∧
      ViscFromAboveLE (regOp F K ε) {x | x ∈ annSet r (L0 + 1) ∧ 0 < u x} u) :
    ∃ W : Rd 2 → ℝ, IsSourceProfile (regOp F K ε) W ∧ (∀ x : Rd 2, x ≠ 0 → W x ≤ U x) ∧
      ∀ x : Rd 2, x ≠ 0 → Vbar (K + 2) 1 x ≤ W x := by
  choose! u hu using hsol
  have hrsL0 : ∀ n, radSeq r1 n < L0 := fun n => by linarith [radSeq_lt hr1 n]
  have hext : ∀ n,
      ContinuousOn (extSeq u r1 (L0 + 1) n) {x | x ≠ 0} ∧
      (∀ x : Rd 2, x ≠ 0 → 0 ≤ extSeq u r1 (L0 + 1) n x) ∧
      (∀ x : Rd 2, radSeq r1 n ≤ ‖x‖ →
        Vbar (K + 2) 1 x ≤ extSeq u r1 (L0 + 1) n x ∧ extSeq u r1 (L0 + 1) n x ≤ U x) ∧
      ViscFromBelowGE (regOp F K ε) {x | radSeq r1 n < ‖x‖} (extSeq u r1 (L0 + 1) n) ∧
      ViscFromAboveLE (regOp F K ε) {x | radSeq r1 n < ‖x‖ ∧ 0 < extSeq u r1 (L0 + 1) n x}
        (extSeq u r1 (L0 + 1) n) := fun n => by
    have h := hu (radSeq r1 n) (radSeq_pos hr1 n) (radSeq_lt hr1 n)
    exact ext_props hF hdeg hK hF0 hε0 hε1 (radSeq_pos hr1 n) (hrsL0 n) (by linarith) hU0 hLR
      h.1 h.2.1 h.2.2.1 h.2.2.2
  have hlap : ∀ n, ViscFromAboveGE (fun X => X.trace + (K + 2)) {x | radSeq r1 n < ‖x‖}
      (extSeq u r1 (L0 + 1) n) ∧ ViscFromBelowLE (fun X => X.trace - (K + 2))
      {x | radSeq r1 n < ‖x‖} (extSeq u r1 (L0 + 1) n) := fun n =>
    viscLaplace_of_regSol hK hTr hε0 hε1 (isOpen_lt continuous_const continuous_norm)
      (hext n).2.2.2.1 (hext n).2.2.2.2 fun x hx =>
        (hext n).2.1 x (norm_pos_iff.1 (lt_trans (radSeq_pos hr1 n) hx))
  -- bounds and equicontinuity on compact sets off the origin
  have hbounds : ∀ S : Set (Rd 2), IsCompact S → S ⊆ {x | x ≠ 0} →
      ∃ M : ℝ, ∀ n, ∀ x ∈ S, |extSeq u r1 (L0 + 1) n x| ≤ M := by
    intro S hS hS0
    obtain ⟨r', R', hr', hSV⟩ := exists_annulus hS hS0
    obtain ⟨MU, hMU⟩ := exists_bound_annulus hUc hr' R'
    obtain ⟨N, hN⟩ : ∃ N, radSeq r1 N < r' :=
      ((radSeq_tendsto r1).eventually (gt_mem_nhds hr')).exists
    refine exists_bound_of_eventually (P := fun n M => ∀ x ∈ S, |extSeq u r1 (L0 + 1) n x| ≤ M)
      (fun n M M' hMM' h x hx => (h x hx).trans hMM') (fun n => ?_) ⟨N, MU, fun n hn x hx => ?_⟩
    · obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn ((hext n).1.mono hS0)
      exact ⟨M, fun x hx => by have := hM x hx; rwa [Real.norm_eq_abs] at this⟩
    · have hxS := hSV hx
      have hrn : radSeq r1 n ≤ ‖x‖ :=
        ((radSeq_antitone hr1 hn).trans hN.le).trans hxS.1.le
      have h1 := ((hext n).2.2.1 x hrn).2
      have h2 := (hext n).2.1 x (hS0 hx)
      have h3 := hMU x hxS.1.le hxS.2.le
      rw [abs_of_nonneg h2]
      exact h1.trans ((le_abs_self _).trans h3)
  have hequi : ∀ S : Set (Rd 2), IsCompact S → S ⊆ {x | x ≠ 0} → ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ →
        |extSeq u r1 (L0 + 1) n x - extSeq u r1 (L0 + 1) n y| < η := by
    intro S hS hS0 η hη
    obtain ⟨r', R', hr', hSV⟩ := exists_annulus hS hS0
    have hV0 : {x : Rd 2 | r' < ‖x‖ ∧ ‖x‖ < R'} ⊆ {x | x ≠ 0} := fun x hx =>
      norm_pos_iff.1 (lt_trans hr' hx.1)
    obtain ⟨MU, hMU⟩ := exists_bound_annulus hUc hr' R'
    obtain ⟨N, hN⟩ : ∃ N, radSeq r1 N < r' :=
      ((radSeq_tendsto r1).eventually (gt_mem_nhds hr')).exists
    obtain ⟨δ, hδ, hδu⟩ := viscLaplaceEquicont hA _ (isOpen_annulus r' R') (K + 2) MU S hS hSV
      η hη
    obtain ⟨δ', hδ', h⟩ := exists_forall_of_eventually
      (P := fun n δ => ∀ x ∈ S, ∀ y ∈ S, dist x y < δ →
        |extSeq u r1 (L0 + 1) n x - extSeq u r1 (L0 + 1) n y| < η)
      (fun n δ δ' _ hδδ' h x hx y hy hxy => h x hx y hy (lt_of_lt_of_le hxy hδδ'))
      (fun n => by
        obtain ⟨δn, hδn, hn⟩ := Metric.uniformContinuousOn_iff.1
          (hS.uniformContinuousOn_of_continuous ((hext n).1.mono hS0)) η hη
        exact ⟨δn, hδn, fun x hx y hy hxy => by
          have := hn x hx y hy hxy
          rwa [Real.dist_eq] at this⟩)
      ⟨N, δ, hδ, fun n hn => by
        have hsub : {x : Rd 2 | r' < ‖x‖ ∧ ‖x‖ < R'} ⊆ {x | radSeq r1 n < ‖x‖} := fun x hx =>
          lt_of_le_of_lt ((radSeq_antitone hr1 hn).trans hN.le) hx.1
        refine hδu (extSeq u r1 (L0 + 1) n) ((hext n).1.mono hV0) (fun x hx => ?_)
          (fun x hx => (hlap n).1 x (hsub hx)) (fun x hx => (hlap n).2 x (hsub hx))
        have h1 := ((hext n).2.2.1 x (le_of_lt (hsub hx))).2
        have h2 := (hext n).2.1 x (hV0 hx)
        have h3 := hMU x hx.1.le hx.2.le
        rw [abs_of_nonneg h2]
        exact h1.trans ((le_abs_self _).trans h3)⟩
    exact ⟨δ', hδ', h⟩
  obtain ⟨φ, hφ, W, hWc, hconv⟩ := localArzelaAscoli (extSeq u r1 (L0 + 1))
    (fun n => (hext n).1) hbounds hequi
  -- pointwise bounds
  have hpt : ∀ x : Rd 2, x ≠ 0 → Vbar (K + 2) 1 x ≤ W x ∧ W x ≤ U x := by
    intro x hx
    have hlim := hconv.tendsto_at hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    obtain ⟨N, hN⟩ : ∃ N, radSeq r1 N < ‖x‖ :=
      ((radSeq_tendsto r1).eventually (gt_mem_nhds hx0)).exists
    have hev : ∀ᶠ k in atTop, Vbar (K + 2) 1 x ≤ extSeq u r1 (L0 + 1) (φ k) x ∧
        extSeq u r1 (L0 + 1) (φ k) x ≤ U x := by
      filter_upwards [eventually_ge_atTop N] with k hk
      exact (hext (φ k)).2.2.1 x
        (((radSeq_antitone hr1 (le_trans hk (hφ.id_le k))).trans hN.le))
    exact ⟨ge_of_tendsto hlim (hev.mono fun k hk => hk.1),
      le_of_tendsto hlim (hev.mono fun k hk => hk.2)⟩
  have hc : (0 : ℝ) < K + 2 := by linarith
  have hregc : ContinuousOn (regOp F K ε) {M | M.IsSymm} :=
    (continuous_regOp hF hdeg K ε).continuousOn
  refine ⟨W, ⟨hWc, fun x hx => (Vbar_nonneg hc one_pos hx).trans (hpt x hx).1,
    ⟨L0, fun x hx => ?_⟩, ?_, ?_, ?_⟩, fun x hx => (hpt x hx).2, fun x hx => (hpt x hx).1⟩
  · have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      linarith
    have h1 := (hpt x hx0).2
    rw [hU0 x hx] at h1
    exact le_antisymm h1 ((Vbar_nonneg hc one_pos hx0).trans (hpt x hx0).1)
  · exact tendsto_atTop_mono' _
      (eventually_nhdsWithin_of_forall fun x hx => (hpt x hx).1) hV
  · exact limit_super hregc (radSeq_tendsto r1) (radSeq_antitone hr1) (fun n => (hext n).1)
      (fun n => (hext n).2.2.2.1) hφ hWc hconv
  · exact limit_sub hregc (radSeq_tendsto r1) (radSeq_antitone hr1) (fun n => (hext n).1)
      (fun n => (hext n).2.2.2.2) hφ hWc hconv

/-! ### The family -/

/-- `V_1 → ∞` at the origin. -/
theorem tendsto_Vbar_one {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {K : ℝ}
    (hK : 1 ≤ K) {v : Rd 2 → ℝ} (hv : Continuous v)
    (hU : IsSourceProfile F (fun x => v x + fundamentalSolution 2 x)) :
    Tendsto (Vbar (K + 2) 1) (𝓝[≠] 0) atTop := by
  have hc : (0 : ℝ) < K + 2 := by linarith
  have hR := rad2_pos hc one_pos
  obtain ⟨Mv, hMv⟩ := (isCompact_closedBall (0 : Rd 2) 1).exists_bound_of_continuousOn
    hv.continuousOn
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (K + 2) / 4 * rad2 (K + 2) 1 -
      1 / (4 * Real.pi) * Real.log (rad2 (K + 2) 1) := ⟨_, rfl⟩
  have hlim : Tendsto (fun x => v x + fundamentalSolution 2 x + -(Mv + B)) (𝓝[≠] 0) atTop :=
    tendsto_atTop_add_const_right _ _ hU.tendsto_atTop
  have hρ : 0 < min 1 (Real.sqrt (rad2 (K + 2) 1)) := lt_min one_pos (Real.sqrt_pos.2 hR)
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : Rd 2) hρ)] with x hx hxb
  have hx0 : x ≠ 0 := hx
  rw [mem_ball, dist_zero_right] at hxb
  have hx1 : ‖x‖ ≤ 1 := (lt_of_lt_of_le hxb (min_le_left _ _)).le
  have hxR : ‖x‖ ^ 2 ≤ rad2 (K + 2) 1 :=
    ((Real.lt_sqrt (norm_nonneg x)).1 (lt_of_lt_of_le hxb (min_le_right _ _))).le
  have h1 := fundamentalSolution_sub_le hc hx0 hxR
  have h2 := hMv x (by rw [mem_closedBall, dist_zero_right]; exact hx1)
  rw [Real.norm_eq_abs] at h2
  have h3 := le_abs_self (v x)
  rw [← hB] at h1
  linarith

/-- ** The regularized family**, from Crandall-Ishii-Lions
Theorems 3.2 and 4.1 and Alexandrov's theorem. -/
theorem regularizedFamily (hTS : CILTheoremOfSumsStmt) (hP : CILPerronStmt)
    (hA : AlexandrovStmt) : RegularizedFamilyStmt := by
  intro _ F K hT hDE hK hTr hF0 v hv hprof
  have hTrK : ∀ z, traceGraph F z ≤ K := fun z => (hTr z).2
  have hc : (0 : ℝ) < K + 2 := by linarith
  have hR := rad2_pos hc one_pos
  have hsq := Real.sqrt_pos.2 hR
  refine ⟨Real.sqrt (rad2 (K + 2) 1),
    (K + 2) / 4 * rad2 (K + 2) 1 - 1 / (4 * Real.pi) * Real.log (rad2 (K + 2) 1), hsq,
    fun ε hε0 hε1 => ?_⟩
  obtain ⟨R0, hR0⟩ := hprof.eventually_zero
  obtain ⟨L0, hL0⟩ : ∃ L0 : ℝ, L0 = max (max R0 (Real.sqrt (rad2 (K + 2) 1))) 1 := ⟨_, rfl⟩
  have hL01 : 1 ≤ L0 := by rw [hL0]; exact le_max_right _ _
  have hL0R : R0 ≤ L0 := by rw [hL0]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hL0s : Real.sqrt (rad2 (K + 2) 1) ≤ L0 := by
    rw [hL0]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hU0 : ∀ x : Rd 2, L0 ≤ ‖x‖ → v x + fundamentalSolution 2 x = 0 := fun x hx =>
    hR0 x (hL0R.trans hx)
  have hLR : rad2 (K + 2) 1 ≤ (L0 + 1) ^ 2 := by
    have h1 : Real.sqrt (rad2 (K + 2) 1) ≤ L0 + 1 := by linarith
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt hR.le] at h2
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = min 1 (Real.sqrt (rad2 (K + 2) 1)) := ⟨_, rfl⟩
  have hr1pos : 0 < r1 := by rw [hr1]; exact lt_min one_pos hsq
  have hr11 : r1 ≤ 1 := by rw [hr1]; exact min_le_left _ _
  have hsol : ∀ r : ℝ, 0 < r → r < r1 → ∃ u : Rd 2 → ℝ,
      ContinuousOn u (closure (annSet r (L0 + 1))) ∧
      (∀ x ∈ closure (annSet r (L0 + 1)),
        Vbar (K + 2) 1 x ≤ u x ∧ u x ≤ v x + fundamentalSolution 2 x) ∧
      ViscFromBelowGE (regOp F K ε) (annSet r (L0 + 1)) u ∧
      ViscFromAboveLE (regOp F K ε) {x | x ∈ annSet r (L0 + 1) ∧ 0 < u x} u := by
    intro r hr hrr1
    have hrs : r < Real.sqrt (rad2 (K + 2) 1) :=
      lt_of_lt_of_le hrr1 (by rw [hr1]; exact min_le_right _ _)
    have hrR : r ^ 2 < rad2 (K + 2) 1 := (Real.lt_sqrt hr.le).1 hrs
    exact annulus_solution hTS hP hT hDE hK hTrK hF0 hv hprof hε0 hε1
      (fun x hx => hU0 x (by linarith)) hLR hr hrR
  obtain ⟨W, hW, hWU, hVW⟩ := regProfile_of_annuli hA hT hDE hK hTr hF0 hε0 hε1
    (U := fun x => v x + fundamentalSolution 2 x) hprof.continuousOn hL01 hU0 hLR
    (tendsto_Vbar_one hK hv hprof) hr1pos hr11 hsol
  refine ⟨W, hW, hWU, fun x hx hxρ => ?_⟩
  have hxR : ‖x‖ ^ 2 ≤ rad2 (K + 2) 1 := ((Real.lt_sqrt (norm_nonneg x)).1 hxρ).le
  exact (fundamentalSolution_sub_le hc hx hxR).trans (hVW x hx)

end SingleSourceD2

end RandomSandpile

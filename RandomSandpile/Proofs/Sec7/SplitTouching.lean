import RandomSandpile.Proofs.Sec7.SplitTouchingJensen
import RandomSandpile.Proofs.Sec7.LimitObstacle

/-! # `SplitTouchingStmt` from Alexandrov's theorem

`splitTouching_of_alexandrov : AlexandrovStmt → SplitTouchingStmt` (Jensen's lemma for sup- and
inf-convolutions, Crandall-Ishii-Lions, *User's guide*, Section 5 and Lemma A.3), following the
route of the docstring of `SplitTouchingStmt` (`Proofs/Sec7/LimitObstacle.lean`) and the proof of
`shiftComparison_of_alexandrov` (`Proofs/Sec9/OpenBoundaryComparison.lean`).

Let `γ = u(x₀) - w(x₀) - m > 0`. With `u^δ` the sup-convolution of `u` and `(-w)^δ` that of `-w`
over `Ū`, `Z = u^δ + (-w)^δ + (ε/2)|·|²` is semiconvex; for `|p| ≤ r` the maxima of `Z - p·(·)` over
`Ū` lie in the compact `A = {u - w ≥ m + γ/4} ⊆ U`. At a maximum point `x` where `u^δ` and
`(-w)^δ` have second-order expansions `X₁`, `X₂` (Alexandrov, off a null set), the viscosity
inequalities at the maximizers give `tr X₁, tr X₂ ≥ -K`, and `X₁ + X₂ + εI ≤ 0`; so
`|det D²Z(x)| ≤ d! (2|K|)^d`, and the quantitative Jensen lemma (`SplitJensen.jensen_volume`)
bounds the measure of the maximum points below, uniformly in `δ`. Since `N` is closed and null, its
`t`-neighbourhood has small measure for small `t`; choosing `δ` with maximizer displacement `< t`,
some maximum point `x` has `B_t(x) ∩ N = ∅`, and `a = ŷ₁`, `b = ŷ₂` (the maximizers), `X = X₁ + (ε/4)I`,
`Y = -(X₂ + (ε/4)I)` satisfy the conclusion with `Y - X ⪰ (ε/4) I`. -/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Matrix

namespace RandomSandpile

open OpenComparison

namespace SplitTouchingProof

variable {d : ℕ}

/-- A viscosity inequality `F(D²u) ≥ 0` tested from above, at a touching paraboloid. -/
theorem ge_of_touchAbove {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U : Set (Rd d)} {u : Rd d → ℝ}
    (h : ViscFromAboveGE F U u) {y : Rd d} (hy : y ∈ U) {X : Matrix (Fin d) (Fin d) ℝ}
    (hX : X.IsSymm) (ht : TouchAbove u y X) : 0 ≤ F X := by
  obtain ⟨q, hq⟩ := ht
  have := h y hy _ ((contDiff_paraboloid (u y) q y X (n := 2)).contDiffAt) hq
  rwa [hessian_quadratic _ _ _ hX] at this

/-- `TouchAbove` in the explicit form of `SplitTouchingStmt`. -/
theorem touch_above_explicit {u : Rd d → ℝ} {y : Rd d} {X : Matrix (Fin d) (Fin d) ℝ}
    (ht : TouchAbove u y X) : ∃ q : Rd d, ∀ᶠ z in 𝓝 y, u z ≤ u y + inner ℝ q (z - y) + qM X (z - y) := by
  obtain ⟨q, hq⟩ := ht
  refine ⟨q, ?_⟩
  filter_upwards [hq] with z hz
  simp only [innerSL_apply_apply, sub_self, inner_zero_right, qM_zero', add_zero] at hz
  linarith

/-- `TouchAbove (-w)` is touching `w` from below with the opposite matrix. -/
theorem touch_below_explicit {w : Rd d → ℝ} {y : Rd d} {X : Matrix (Fin d) (Fin d) ℝ}
    (ht : TouchAbove (fun z => -w z) y X) :
    ∃ q : Rd d, ∀ᶠ z in 𝓝 y, w y + inner ℝ q (z - y) + qM (-X) (z - y) ≤ w z := by
  obtain ⟨q, hq⟩ := touch_above_explicit ht
  refine ⟨-q, ?_⟩
  filter_upwards [hq] with z hz
  rw [inner_neg_left, qM_neg']
  linarith

end SplitTouchingProof

set_option maxHeartbeats 400000 in
open SplitTouchingProof SplitJensen in
/-- **`SplitTouchingStmt`** from Alexandrov's theorem. -/
theorem splitTouching_of_alexandrov (hA : AlexandrovStmt) : SplitTouchingStmt := by
  intro d U hU hUb K u w hu hw hsub hsup m hbd hex N hNcl hN0
  obtain ⟨x₀, hx₀U, hx₀m⟩ := hex
  set S := closure U with hSdef
  have hS : IsCompact S := hUb.isCompact_closure
  have hx₀ : x₀ ∈ S := subset_closure hx₀U
  have hfront : ∀ y ∈ S, y ∉ U → y ∈ frontier U := fun y hy hyU => by
    rw [frontier, hU.interior_eq]; exact ⟨hy, hyU⟩
  set γ := u x₀ - w x₀ - m with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  set R₁ := |R| + 1 with hR₁
  have hR₁0 : 0 < R₁ := by positivity
  have hRS : ∀ y ∈ S, ‖y‖ ≤ R₁ := fun y hy => by
    have := hR y hy; have := le_abs_self R; linarith
  set ε := γ / (8 * R₁ ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  have hεS : ∀ y ∈ S, ε / 2 * ‖y‖ ^ 2 ≤ γ / 16 := by
    intro y hy
    have h1 : ‖y‖ ^ 2 ≤ R₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hRS y hy) 2
    have h2 : ε / 2 * R₁ ^ 2 = γ / 16 := by rw [hε]; field_simp; ring
    have h3 : ε / 2 * ‖y‖ ^ 2 ≤ ε / 2 * R₁ ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  set r := γ / (16 * R₁) with hr
  have hr0 : 0 < r := by positivity
  have hpS : ∀ p ∈ closedBall (0 : Rd d) r, ∀ y ∈ S, |inner ℝ p y| ≤ γ / 16 := by
    intro p hp y hy
    have h1 := abs_real_inner_le_norm p y
    have h2 : ‖p‖ ≤ r := mem_closedBall_zero_iff.1 hp
    have h3 := hRS y hy
    have h4 : r * R₁ = γ / 16 := by rw [hr]; field_simp
    have h5 : ‖p‖ * ‖y‖ ≤ r * R₁ := mul_le_mul h2 h3 (norm_nonneg _) hr0.le
    linarith
  -- the compact set `A` and its distance to `∂U`
  have hwneg : ContinuousOn (fun z => -w z) S := hw.neg
  set A : Set (Rd d) := S ∩ (fun y => u y - w y) ⁻¹' Ici (m + γ / 4) with hAdef
  have hAcl : IsClosed A := (hu.sub hw).preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
  have hAc : IsCompact A := hS.of_isClosed_subset hAcl inter_subset_left
  have hAU : A ⊆ U := by
    intro y hy
    by_contra hyU
    have h1 := hbd y (hfront y hy.1 hyU)
    have h2 : m + γ / 4 ≤ u y - w y := hy.2
    linarith
  obtain ⟨ρ, hρ, hthick⟩ := hAc.exists_thickening_subset_open hU hAU
  have hballU : ∀ y ∈ A, ball y ρ ⊆ U := fun y hy =>
    (ball_subset_thickening hy ρ).trans hthick
  have hballS : ∀ y ∈ A, ball y ρ ⊆ S := fun y hy => (hballU y hy).trans subset_closure
  -- the determinant bound and the lower bound on the measure of the maximum points
  set T : ℝ := 2 * |K| with hT
  set B : ℝ := (d.factorial : ℝ) * T ^ d + 1 with hB
  have hB0 : 0 < B := by positivity
  set V₀ := volume (ball (0 : Rd d) r) with hV₀
  have hV₀pos : 0 < V₀ := measure_ball_pos volume _ hr0
  set c₁ := V₀ / ENNReal.ofReal B with hc₁
  have hc₁pos : 0 < c₁ := ENNReal.div_pos_iff.2 ⟨hV₀pos.ne', ENNReal.ofReal_ne_top⟩
  -- the closed null set near `A`
  set N' := N ∩ cthickening 1 A with hN'
  have hN'cl : IsClosed N' := hNcl.inter isClosed_cthickening
  have hN'0 : volume N' = 0 := measure_mono_null inter_subset_left hN0
  have hN'b : Bornology.IsBounded (thickening 1 N') :=
    ((hAc.isBounded.cthickening (δ := 1)).subset inter_subset_right).thickening
  have hlim := tendsto_measure_thickening_of_isClosed (μ := volume)
    ⟨1, one_pos, hN'b.measure_lt_top.ne⟩ hN'cl
  rw [hN'0] at hlim
  obtain ⟨t₁, ht₁, hsmall⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (hlim.eventually (gt_mem_nhds hc₁pos)))
  set t := min (t₁ / 2) (min 1 ρ) with ht
  have ht0 : 0 < t := lt_min (by positivity) (lt_min one_pos hρ)
  have htN : volume (thickening t N') < c₁ :=
    hsmall (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
               have := min_le_left (t₁ / 2) (min 1 ρ); linarith) ht0
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have htρ : t ≤ ρ := (min_le_right _ _).trans (min_le_right _ _)
  -- the sup-convolutions
  obtain ⟨δu, hδu, hUu⟩ := supConv_uniform hS hu (show 0 < γ / 16 by positivity) ht0
  obtain ⟨δw, hδw, hUw⟩ := supConv_uniform hS hwneg (show 0 < γ / 16 by positivity) ht0
  set δ := min δu δw with hδ
  have hδ0 : 0 < δ := lt_min hδu hδw
  have hSne : S.Nonempty := ⟨x₀, hx₀⟩
  set su := supConv S δ u with hsu
  set sw := supConv S δ (fun z => -w z) with hsw
  have hsu_ge : ∀ y ∈ S, u y ≤ su y := fun y hy => le_supConv hS hu hy
  have hsw_ge : ∀ y ∈ S, -w y ≤ sw y := fun y hy => le_supConv hS hwneg hy
  have hsu_le : ∀ y ∈ S, su y ≤ u y + γ / 16 := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := (supConv_spec hS hSne δ hu y).2
    have h := (hUu δ hδ0 (min_le_left _ _) y hy z hz hyz).2
    rw [hsu, hyz]
    have : 0 ≤ ‖y - z‖ ^ 2 / (2 * δ) := by positivity
    linarith
  have hsw_le : ∀ y ∈ S, sw y ≤ -w y + γ / 16 := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := (supConv_spec hS hSne δ hwneg y).2
    have h := (hUw δ hδ0 (min_le_right _ _) y hy z hz hyz).2
    rw [hsw, hyz]
    have : 0 ≤ ‖y - z‖ ^ 2 / (2 * δ) := by positivity
    linarith
  set Z : Rd d → ℝ := fun z => su z + sw z + ε / 2 * ‖z‖ ^ 2 with hZ
  have hZc : Continuous Z :=
    ((continuous_supConv hS hu δ).add (continuous_supConv hS hwneg δ)).add
      (continuous_const.mul (continuous_norm.pow 2))
  have hconv : ConvexOn ℝ univ (fun z => Z z + 1 / δ * ‖z‖ ^ 2) := by
    have h := ((convexOn_supConv_add hS hSne hδ0 hu).add
      (convexOn_supConv_add hS hSne hδ0 hwneg)).add (convexOn_sq_norm (d := d) (by positivity :
        (0 : ℝ) ≤ ε / 2))
    refine h.congr fun z _ => ?_
    simp only [Pi.add_apply, Z, su, sw]
    ring
  -- maxima of `Z - p·(·)` lie in `A`
  have hmaxA : ∀ p ∈ closedBall (0 : Rd d) r, ∀ y ∈ S, IsMaxSlope Z S y p → y ∈ A := by
    intro p hp y hyS hy
    refine ⟨hyS, ?_⟩
    have h0 := hy x₀ hx₀
    have a1 := hsu_ge x₀ hx₀; have a2 := hsw_ge x₀ hx₀
    have a3 : 0 ≤ ε / 2 * ‖x₀‖ ^ 2 := by positivity
    have a4 := abs_le.1 (hpS p hp x₀ hx₀)
    have b1 := hsu_le y hyS; have b2 := hsw_le y hyS; have b3 := hεS y hyS
    have b4 := abs_le.1 (hpS p hp y hyS)
    show m + γ / 4 ≤ u y - w y
    simp only [Z] at h0
    linarith
  have hmax : ∀ p ∈ closedBall (0 : Rd d) r, ∃ y ∈ A, IsMaxSlope Z S y p := by
    intro p hp
    have hc : ContinuousOn (fun y => Z y - inner ℝ p y) S :=
      (hZc.sub (continuous_const.inner continuous_id)).continuousOn
    obtain ⟨y, hyS, hy⟩ := hS.exists_isMaxOn hSne hc
    have hym : IsMaxSlope Z S y p := fun z hz => hy hz
    exact ⟨y, hmaxA p hp y hyS hym, hym⟩
  -- Alexandrov's theorem for the two semiconvex functions
  set G₁ : Rd d → ℝ := fun z => su z + ‖z‖ ^ 2 / (2 * δ) with hG₁
  set G₂ : Rd d → ℝ := fun z => sw z + ‖z‖ ^ 2 / (2 * δ) with hG₂
  have hA₁ := hA d G₁ (convexOn_supConv_add hS hSne hδ0 hu)
  have hA₂ := hA d G₂ (convexOn_supConv_add hS hSne hδ0 hwneg)
  rw [ae_iff] at hA₁ hA₂
  set Bad := {a | ¬∃ p X, X.IsSymm ∧ HasSecondOrderTaylorAt G₁ a p X} ∪
    {a | ¬∃ p X, X.IsSymm ∧ HasSecondOrderTaylorAt G₂ a p X} with hBad
  have hBad0 : volume Bad = 0 := measure_union_null hA₁ hA₂
  -- the data at a good maximum point
  set c₀ : ℝ := -(1 / (2 * δ)) with hc₀
  set η := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  have hdata : ∀ x ∈ A, x ∉ Bad → ∀ p, IsMaxSlope Z S x p →
      ∃ (X₁ X₂ : Matrix (Fin d) (Fin d) ℝ) (q₁ q₂ : Rd d), X₁.IsSymm ∧ X₂.IsSymm ∧
        HasSecondOrderTaylorAt su x q₁ X₁ ∧ HasSecondOrderTaylorAt sw x q₂ X₂ ∧
        (∀ h : Rd d, qM X₁ h + qM X₂ h + ε / 2 * ‖h‖ ^ 2 ≤ 0) ∧
        ∃ y₁ ∈ U, ∃ y₂ ∈ U, ‖x - y₁‖ < t ∧ ‖x - y₂‖ < t ∧
          su x = u y₁ - ‖x - y₁‖ ^ 2 / (2 * δ) ∧ sw x = -w y₂ - ‖x - y₂‖ ^ 2 / (2 * δ) ∧
          TouchAbove u y₁ (X₁ + η • 1) ∧ TouchAbove (fun z => -w z) y₂ (X₂ + η • 1) := by
    intro x hxA hxN p hxp
    rw [mem_union, not_or] at hxN
    obtain ⟨hxN₁, hxN₂⟩ := hxN
    simp only [mem_ofPred_eq, not_not] at hxN₁ hxN₂
    obtain ⟨q₁, Y₁, hY₁, hT₁⟩ := hxN₁
    obtain ⟨q₂, Y₂, hY₂, hT₂⟩ := hxN₂
    set X₁ := Y₁ + (2 * c₀) • (1 : Matrix (Fin d) (Fin d) ℝ) with hX₁
    set X₂ := Y₂ + (2 * c₀) • (1 : Matrix (Fin d) (Fin d) ℝ) with hX₂
    have hX₁s : X₁.IsSymm := hY₁.add (Matrix.isSymm_one.smul _)
    have hX₂s : X₂.IsSymm := hY₂.add (Matrix.isSymm_one.smul _)
    have hTu : HasSecondOrderTaylorAt su x (q₁ + (2 * c₀) • x) X₁ :=
      taylor_congr (taylor_add hT₁ (taylor_sq c₀ x)) fun z => by
        simp only [G₁, c₀]; ring
    have hTw : HasSecondOrderTaylorAt sw x (q₂ + (2 * c₀) • x) X₂ :=
      taylor_congr (taylor_add hT₂ (taylor_sq c₀ x)) fun z => by
        simp only [G₂, c₀]; ring
    have hTZ := taylor_add (taylor_add hTu hTw) (taylor_sq (ε / 2) x)
    have hloc : IsLocalMax (fun y => Z y - inner ℝ p y) x := by
      filter_upwards [ball_mem_nhds x hρ] with y hy
      exact hxp y (hballS x hxA hy)
    have hneg : ∀ h : Rd d, qM X₁ h + qM X₂ h + ε / 2 * ‖h‖ ^ 2 ≤ 0 := by
      intro h
      have := qM_nonpos_of_isLocalMax (taylor_congr hTZ fun z => rfl) hloc h
      rw [qM_add', qM_add', qM_smul_one'] at this
      linarith
    obtain ⟨y₁, hy₁S, hy₁⟩ := (supConv_spec hS hSne δ hu x).2
    obtain ⟨y₂, hy₂S, hy₂⟩ := (supConv_spec hS hSne δ hwneg x).2
    have hxS : x ∈ S := hballS x hxA (mem_ball_self hρ)
    have hd₁ := (hUu δ hδ0 (min_le_left _ _) x hxS y₁ hy₁S hy₁).1
    have hd₂ := (hUw δ hδ0 (min_le_right _ _) x hxS y₂ hy₂S hy₂).1
    have hy₁U : y₁ ∈ U := hballU x hxA (by
      rw [mem_ball, dist_comm, dist_eq_norm]; linarith)
    have hy₂U : y₂ ∈ U := hballU x hxA (by
      rw [mem_ball, dist_comm, dist_eq_norm]; linarith)
    exact ⟨X₁, X₂, _, _, hX₁s, hX₂s, hTu, hTw, hneg, y₁, hy₁U, y₂, hy₂U, hd₁, hd₂, hy₁, hy₂,
      touch_supConv hS hU subset_closure hu hy₁U hy₁ (touch_of_taylor hTu hη0),
      touch_supConv hS hU subset_closure hwneg hy₂U hy₂ (touch_of_taylor hTw hη0)⟩
  have hdpos : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- the trace and determinant bounds at good maximum points
  have hgood : ∀ x ∈ A, x ∉ Bad → ∀ p, IsMaxSlope Z S x p →
      ∃ (P : Rd d) (H : Matrix (Fin d) (Fin d) ℝ), H.IsSymm ∧ HasSecondOrderTaylorAt Z x P H ∧
        |H.det| ≤ B := by
    intro x hxA hxN p hxp
    obtain ⟨X₁, X₂, q₁, q₂, hX₁s, hX₂s, hTu, hTw, hneg, y₁, hy₁U, y₂, hy₂U, -, -, -, -,
      ht₁, ht₂⟩ := hdata x hxA hxN p hxp
    have hη1 : (X₁ + η • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := hX₁s.add (Matrix.isSymm_one.smul _)
    have hη2 : (X₂ + η • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := hX₂s.add (Matrix.isSymm_one.smul _)
    have htr₁ := ge_of_touchAbove hsub hy₁U hη1 ht₁
    obtain ⟨q', hq'⟩ := touch_below_explicit ht₂
    have htr₂ := ViscFromBelowLE.le_of_touch hsup hη2.neg hy₂U hq'
    simp only [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul] at htr₁ htr₂
    set H := X₁ + X₂ + (2 * (ε / 2)) • (1 : Matrix (Fin d) (Fin d) ℝ) with hH
    have hHs : H.IsSymm := (hX₁s.add hX₂s).add (Matrix.isSymm_one.smul _)
    have hTZ : HasSecondOrderTaylorAt Z x _ H := taylor_add (taylor_add hTu hTw) (taylor_sq (ε / 2) x)
    have hHneg : ∀ h : Rd d, qM H h ≤ 0 := by
      intro h
      rw [hH, qM_add', qM_add', qM_smul_one']
      have := hneg h
      linarith
    have hHtr : -T ≤ H.trace := by
      simp only [hH, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
        smul_eq_mul]
      have hK : K ≤ |K| := le_abs_self K
      have e1 : (d : ℝ) * η = d * ε / 4 := by rw [hη]; ring
      have e2 : 0 ≤ (d : ℝ) * ε := by positivity
      rw [hT]; linarith
    have hdet := abs_det_le_of_nonpos hHs hHneg hHtr
    exact ⟨_, H, hHs, hTZ, by rw [hB]; linarith⟩
  -- the lower bound on the measure of the maximum points
  have hvol := jensen_volume hZc (by positivity : (0 : ℝ) ≤ 1 / δ) hρ hconv hAc hballS hmax
    hBad0 hgood
  set Kset := {x | x ∈ A ∧ ∃ p ∈ closedBall (0 : Rd d) r, IsMaxSlope Z S x p} with hKset
  have hKvol : c₁ ≤ volume Kset := by
    rw [hc₁]; exact ENNReal.div_le_of_le_mul (by rw [mul_comm]; exact hvol)
  -- a good maximum point far from `N`
  have hex : ∃ x ∈ Kset, x ∉ thickening t N' ∧ x ∉ Bad := by
    by_contra hcon
    push Not at hcon
    have hsub : Kset ⊆ thickening t N' ∪ Bad := fun x hx => by
      by_cases h : x ∈ thickening t N'
      · exact Or.inl h
      · exact Or.inr (hcon x hx h)
    have := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
    rw [hBad0, add_zero] at this
    exact absurd (hKvol.trans this) (not_le.2 htN)
  obtain ⟨x, ⟨hxA, p, hp, hxp⟩, hxN, hxB⟩ := hex
  obtain ⟨X₁, X₂, q₁, q₂, hX₁s, hX₂s, -, -, hneg, y₁, hy₁U, y₂, hy₂U, hd₁, hd₂, hy₁, hy₂,
    ht₁, ht₂⟩ := hdata x hxA hxB p hxp
  obtain ⟨qa, hqa⟩ := touch_above_explicit ht₁
  obtain ⟨qb, hqb⟩ := touch_below_explicit ht₂
  set X := X₁ + η • (1 : Matrix (Fin d) (Fin d) ℝ) with hXdef
  set Y := -(X₂ + η • (1 : Matrix (Fin d) (Fin d) ℝ)) with hYdef
  have hXs : X.IsSymm := hX₁s.add (Matrix.isSymm_one.smul _)
  have hYs : Y.IsSymm := (hX₂s.add (Matrix.isSymm_one.smul _)).neg
  refine ⟨x, t, ?_, ?_, y₁, y₂, qa, qb, X, Y, ?_, ?_, ?_, hXs, hYs, ⟨η, hη0, ?_⟩, hqa, hqb⟩
  · exact (ball_subset_ball htρ).trans (hballU x hxA)
  · rw [Set.disjoint_left]
    intro y hy hyN
    apply hxN
    rw [mem_thickening_iff]
    refine ⟨y, ⟨hyN, ?_⟩, by rw [dist_comm]; exact hy⟩
    exact Metric.mem_cthickening_of_dist_le y x 1 A hxA (by linarith [mem_ball.1 hy])
  · rw [mem_ball, dist_comm, dist_eq_norm]; exact hd₁
  · rw [mem_ball, dist_comm, dist_eq_norm]; exact hd₂
  · -- `u(y₁) - w(y₂) ≥ u^δ(x) + (-w)^δ(x) > m`
    have hxS : x ∈ S := hballS x hxA (mem_ball_self hρ)
    have h0 := hxp x₀ hx₀
    have a1 := hsu_ge x₀ hx₀; have a2 := hsw_ge x₀ hx₀
    have a3 : 0 ≤ ε / 2 * ‖x₀‖ ^ 2 := by positivity
    have a4 := abs_le.1 (hpS p hp x₀ hx₀)
    have b3 := hεS x hxS
    have b4 := abs_le.1 (hpS p hp x hxS)
    have c1 : 0 ≤ ‖x - y₁‖ ^ 2 / (2 * δ) := by positivity
    have c2 : 0 ≤ ‖x - y₂‖ ^ 2 / (2 * δ) := by positivity
    simp only [Z] at h0
    linarith
  · refine posSemidef_of_qM_nonneg' ((hYs.sub hXs).sub (Matrix.isSymm_one.smul _)) fun h => ?_
    rw [hXdef, hYdef]
    simp only [qM_sub', qM_add', qM_neg', qM_smul_one']
    have hsq : 0 ≤ ε * ‖h‖ ^ 2 := by positivity
    have := hneg h
    rw [hη]
    linarith

end RandomSandpile

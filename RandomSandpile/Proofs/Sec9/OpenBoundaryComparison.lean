import RandomSandpile.Proofs.Sec9.OpenBoundaryComparisonJensen
import RandomSandpile.Steps.Sec9.OpenBoundary
import RandomSandpile.Inputs.Alexandrov

/-! # Theorem 9.1, step: the Crandall-Ishii-Lions comparison principle

`shiftComparison_of_alexandrov : AlexandrovStmt → ShiftComparisonStmt`. This is Jensen's proof
(Crandall-Ishii-Lions, *User's guide*, Section 5.A; Caffarelli-Cabré, Theorem 5.3), with
Alexandrov's theorem as the only literature input.

Suppose `u > w` somewhere in `Ū` and let `m = u(x) - w(x) > 0`.
* `A = {u - w ≥ m/4} ⊆ U` is compact; `ρ` is its distance to `∂U`.
* Let `u^δ` be the sup-convolution of `u` and `v_δ` that of `-w`. They are uniformly close to
  `u` and `-w` on `Ū`, and their maximizers lie within `ρ` (`supConv_uniform`).
* `Z = u^δ + v_δ + (ε/2)|·|²` is semiconvex. For small slopes `p`, `Z - p·(·)` attains its maximum
  over `Ū` in `A`.
* Jensen's lemma (`jensen_exists`) and Alexandrov's theorem give a maximum point `x̂` where `u^δ`
  and `v_δ` have second-order expansions with matrices `X₁`, `X₂`. The second-order condition
  gives `X₁ + X₂ + εI ≤ 0`.
* Testing `u` and `w` at the maximizers with the paraboloids of `X₁ + (ε/4)I` and
  `-(X₂ + (ε/4)I)` gives `F(X₁ + (ε/4)I) ≤ 0 ≤ F(-(X₂ + (ε/4)I))`.
* Degenerate ellipticity and the shift `F(M - (ε/2)I) = F(M) + dε/2` give `dε/2 ≤ 0`, a
  contradiction. -/

noncomputable section

open MeasureTheory Filter Topology Metric Set

namespace RandomSandpile

namespace OpenComparison

variable {d : ℕ}

theorem continuous_supConv {S : Set (Rd d)} (hS : IsCompact S) {f : Rd d → ℝ}
    (hf : ContinuousOn f S) (δ : ℝ) : Continuous (supConv S δ f) := by
  have hK : IsCompact (univ : Set S) := isCompact_iff_isCompact_univ.1 hS
  have h1 : Continuous (fun y : S => f y) := hf.domRestrict
  have hcont : Continuous (fun q : Rd d × S => f q.2 - ‖q.1 - q.2‖ ^ 2 / (2 * δ)) :=
    (h1.comp continuous_snd).sub
      (((continuous_fst.sub (continuous_subtype_val.comp continuous_snd)).norm.pow 2).div_const _)
  have := hK.continuous_sSup (f := fun (x : Rd d) (y : S) => f y - ‖x - (y : Rd d)‖ ^ 2 / (2 * δ))
    (by exact hcont)
  convert this using 1
  funext x
  rw [Set.image_univ, sSup_range]
  rfl

theorem supConv_dist_sq {S : Set (Rd d)} (hS : IsCompact S) {f : Rd d → ℝ}
    (hf : ContinuousOn f S) {δ : ℝ} (hδ : 0 < δ) {x y : Rd d} (hx : x ∈ S)
    (hy : supConv S δ f x = f y - ‖x - y‖ ^ 2 / (2 * δ)) :
    ‖x - y‖ ^ 2 ≤ 2 * δ * (f y - f x) := by
  have h := (supConv_spec hS ⟨x, hx⟩ δ hf x).1 x hx
  rw [sub_self, norm_zero, hy] at h
  have h2 : ‖x - y‖ ^ 2 / (2 * δ) ≤ f y - f x := by
    have : (0 : ℝ) ^ 2 / (2 * δ) = 0 := by simp
    linarith
  rwa [div_le_iff₀ (by positivity), mul_comm] at h2

/-- For small `δ`, maximizers of the sup-convolution are `ρ`-close and nearly maximal. -/
theorem supConv_uniform {S : Set (Rd d)} (hS : IsCompact S) {f : Rd d → ℝ}
    (hf : ContinuousOn f S) {θ ρ : ℝ} (hθ : 0 < θ) (hρ : 0 < ρ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ x ∈ S, ∀ y ∈ S,
      supConv S δ f x = f y - ‖x - y‖ ^ 2 / (2 * δ) → ‖x - y‖ < ρ ∧ f y < f x + θ := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hf
  obtain ⟨κ, hκ, hUC⟩ :=
    Metric.uniformContinuousOn_iff.1 (hS.uniformContinuousOn_of_continuous hf) θ hθ
  set κ' := min κ ρ with hκ'
  have hκ'0 : 0 < κ' := lt_min hκ hρ
  refine ⟨κ' ^ 2 / (4 * (|B| + 1)), by positivity, fun δ hδ hδ₀ x hx y hy hxy => ?_⟩
  have hsq := supConv_dist_sq hS hf hδ hx hxy
  have hfy : f y - f x ≤ 2 * |B| := by
    have h1 := hB y hy; have h2 := hB x hx
    rw [Real.norm_eq_abs] at h1 h2
    have := abs_le.1 h1; have := abs_le.1 h2
    have : B ≤ |B| := le_abs_self B
    linarith
  have hlt : ‖x - y‖ ^ 2 < κ' ^ 2 := by
    have e : 4 * (|B| + 1) * (κ' ^ 2 / (4 * (|B| + 1))) = κ' ^ 2 := by field_simp
    have h4 : 2 * δ * (f y - f x) ≤ 4 * δ * |B| := by nlinarith
    have h5 : 4 * δ * |B| < 4 * (|B| + 1) * (κ' ^ 2 / (4 * (|B| + 1))) := by
      have : 4 * δ * |B| ≤ 4 * (κ' ^ 2 / (4 * (|B| + 1))) * |B| := by
        have := abs_nonneg B
        nlinarith
      have h6 : 0 < κ' ^ 2 / (4 * (|B| + 1)) := by positivity
      nlinarith
    linarith
  have hd : ‖x - y‖ < κ' := lt_of_pow_lt_pow_left₀ 2 hκ'0.le hlt
  refine ⟨lt_of_lt_of_le hd (min_le_right _ _), ?_⟩
  have := hUC x hx y hy (by rw [dist_eq_norm]; exact lt_of_lt_of_le hd (min_le_left _ _))
  rw [Real.dist_eq] at this
  linarith [(abs_lt.1 this).1]

theorem convexOn_sq_norm {c : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ univ (fun z : Rd d => c * ‖z‖ ^ 2) := by
  have h := ConvexOn.smul hc ((convexOn_norm (E := Rd d) convex_univ).pow (fun (x : Rd d) _ => norm_nonneg x) 2)
  simpa [smul_eq_mul] using h

theorem qM_sub' (A B : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) :
    qM (A - B) x = qM A x - qM B x := by
  rw [sub_eq_add_neg, qM_add', qM_neg']; ring

end OpenComparison

open OpenComparison in
/-- **Step** (`ShiftComparisonStmt`) from Alexandrov's theorem. -/
theorem shiftComparison_of_alexandrov (hA : AlexandrovStmt) : ShiftComparisonStmt := by
  intro d hd F hF hshift U hU hUb u w hu hw hsub hsup hbd x₀ hx₀
  by_contra hlt
  rw [not_le] at hlt
  set S := closure U with hSdef
  have hS : IsCompact S := hUb.isCompact_closure
  have hfront : ∀ y ∈ S, y ∉ U → y ∈ frontier U := fun y hy hyU => by
    rw [frontier, hU.interior_eq]; exact ⟨hy, hyU⟩
  have hx₀U : x₀ ∈ U := by
    by_contra h
    exact absurd (hbd x₀ (hfront x₀ hx₀ h)) (not_le.2 hlt)
  set m := u x₀ - w x₀ with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  set R₁ := |R| + 1 with hR₁
  have hR₁0 : 0 < R₁ := by positivity
  have hRS : ∀ y ∈ S, ‖y‖ ≤ R₁ := fun y hy => by
    have := hR y hy; have := le_abs_self R; linarith
  set ε := m / (8 * R₁ ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  have hεS : ∀ y ∈ S, ε / 2 * ‖y‖ ^ 2 ≤ m / 16 := by
    intro y hy
    have h1 : ‖y‖ ^ 2 ≤ R₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hRS y hy) 2
    have h2 : ε / 2 * R₁ ^ 2 = m / 16 := by rw [hε]; field_simp; ring
    nlinarith
  set r := m / (16 * R₁) with hr
  have hr0 : 0 < r := by positivity
  have hpS : ∀ p ∈ ball (0 : Rd d) r, ∀ y ∈ S, |inner ℝ p y| ≤ m / 16 := by
    intro p hp y hy
    have h1 := abs_real_inner_le_norm p y
    have h2 : ‖p‖ < r := mem_ball_zero_iff.1 hp
    have h3 := hRS y hy
    have h4 : r * R₁ = m / 16 := by rw [hr]; field_simp
    nlinarith [norm_nonneg p, norm_nonneg y]
  -- the compact set `A` and its distance to `∂U`
  have hwneg : ContinuousOn (fun z => -w z) S := hw.neg
  set A : Set (Rd d) := S ∩ (fun y => u y - w y) ⁻¹' Ici (m / 4) with hAdef
  have hAcl : IsClosed A := (hu.sub hw).preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
  have hAc : IsCompact A := hS.of_isClosed_subset hAcl inter_subset_left
  have hAU : A ⊆ U := by
    intro y hy
    by_contra hyU
    have h1 := hbd y (hfront y hy.1 hyU)
    have h2 : m / 4 ≤ u y - w y := hy.2
    linarith
  obtain ⟨ρ, hρ, hthick⟩ := hAc.exists_thickening_subset_open hU hAU
  have hballU : ∀ y ∈ A, ball y ρ ⊆ U := fun y hy =>
    (ball_subset_thickening hy ρ).trans hthick
  have hballS : ∀ y ∈ A, ball y ρ ⊆ S := fun y hy => (hballU y hy).trans subset_closure
  -- the sup-convolutions
  obtain ⟨δu, hδu, hUu⟩ := supConv_uniform hS hu (show 0 < m / 16 by positivity) hρ
  obtain ⟨δw, hδw, hUw⟩ := supConv_uniform hS hwneg (show 0 < m / 16 by positivity) hρ
  set δ := min δu δw with hδ
  have hδ0 : 0 < δ := lt_min hδu hδw
  have hSne : S.Nonempty := ⟨x₀, hx₀⟩
  set su := supConv S δ u with hsu
  set sw := supConv S δ (fun z => -w z) with hsw
  have hsu_ge : ∀ y ∈ S, u y ≤ su y := fun y hy => le_supConv hS hu hy
  have hsw_ge : ∀ y ∈ S, -w y ≤ sw y := fun y hy => le_supConv hS hwneg hy
  have hsu_le : ∀ y ∈ S, su y ≤ u y + m / 16 := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := (supConv_spec hS hSne δ hu y).2
    have h := (hUu δ hδ0 (min_le_left _ _) y hy z hz hyz).2
    rw [hsu, hyz]
    have : 0 ≤ ‖y - z‖ ^ 2 / (2 * δ) := by positivity
    linarith
  have hsw_le : ∀ y ∈ S, sw y ≤ -w y + m / 16 := by
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
  -- semiconvexity
  have hconv : ConvexOn ℝ univ (fun z => Z z + 1 / δ * ‖z‖ ^ 2) := by
    have h := ((convexOn_supConv_add hS hSne hδ0 hu).add
      (convexOn_supConv_add hS hSne hδ0 hwneg)).add (convexOn_sq_norm (d := d) (by positivity :
        (0 : ℝ) ≤ ε / 2))
    refine h.congr fun z _ => ?_
    simp only [Pi.add_apply, Z, su, sw]
    ring
  -- maxima of `Z - p·(·)` lie in `A`
  have hmax : ∀ p ∈ ball (0 : Rd d) r, ∃ y ∈ A, IsMaxSlope Z S y p := by
    intro p hp
    have hc : ContinuousOn (fun y => Z y - inner ℝ p y) S :=
      (hZc.sub (continuous_const.inner continuous_id)).continuousOn
    obtain ⟨y, hyS, hy⟩ := hS.exists_isMaxOn hSne hc
    refine ⟨y, ⟨hyS, ?_⟩, fun z hz => hy hz⟩
    have h0 := hy hx₀
    simp only [mem_ofPred_eq] at h0
    have a1 := hsu_ge x₀ hx₀; have a2 := hsw_ge x₀ hx₀
    have a3 : 0 ≤ ε / 2 * ‖x₀‖ ^ 2 := by positivity
    have a4 := abs_le.1 (hpS p hp x₀ hx₀)
    have b1 := hsu_le y hyS; have b2 := hsw_le y hyS; have b3 := hεS y hyS
    have b4 := abs_le.1 (hpS p hp y hyS)
    show m / 4 ≤ u y - w y
    simp only [Z] at h0
    linarith
  -- Alexandrov's theorem for the two semiconvex functions
  set G₁ : Rd d → ℝ := fun z => su z + ‖z‖ ^ 2 / (2 * δ) with hG₁
  set G₂ : Rd d → ℝ := fun z => sw z + ‖z‖ ^ 2 / (2 * δ) with hG₂
  have hA₁ := hA d G₁ (convexOn_supConv_add hS hSne hδ0 hu)
  have hA₂ := hA d G₂ (convexOn_supConv_add hS hSne hδ0 hwneg)
  rw [ae_iff] at hA₁ hA₂
  obtain ⟨xh, hxA, hxN, p, hxp⟩ := jensen_exists (by positivity : (0 : ℝ) ≤ 1 / δ) hρ hr0
    hconv hballS hmax (measure_union_null hA₁ hA₂)
  rw [mem_union, not_or] at hxN
  obtain ⟨hxN₁, hxN₂⟩ := hxN
  simp only [mem_ofPred_eq, not_not] at hxN₁ hxN₂
  obtain ⟨q₁, Y₁, hY₁, hT₁⟩ := hxN₁
  obtain ⟨q₂, Y₂, hY₂, hT₂⟩ := hxN₂
  -- expansions of `su`, `sw`, `Z` at `xh`
  set c₀ : ℝ := -(1 / (2 * δ)) with hc₀
  set X₁ := Y₁ + (2 * c₀) • (1 : Matrix (Fin d) (Fin d) ℝ) with hX₁
  set X₂ := Y₂ + (2 * c₀) • (1 : Matrix (Fin d) (Fin d) ℝ) with hX₂
  have hX₁s : X₁.IsSymm := hY₁.add (Matrix.isSymm_one.smul _)
  have hX₂s : X₂.IsSymm := hY₂.add (Matrix.isSymm_one.smul _)
  have hTu : HasSecondOrderTaylorAt su xh (q₁ + (2 * c₀) • xh) X₁ :=
    taylor_congr (taylor_add hT₁ (taylor_sq c₀ xh)) fun z => by
      simp only [G₁, c₀]; ring
  have hTw : HasSecondOrderTaylorAt sw xh (q₂ + (2 * c₀) • xh) X₂ :=
    taylor_congr (taylor_add hT₂ (taylor_sq c₀ xh)) fun z => by
      simp only [G₂, c₀]; ring
  have hTZ := taylor_add (taylor_add hTu hTw) (taylor_sq (ε / 2) xh)
  have hloc : IsLocalMax (fun y => Z y - inner ℝ p y) xh := by
    filter_upwards [ball_mem_nhds xh hρ] with y hy
    exact hxp y (hballS xh hxA hy)
  have hneg : ∀ h : Rd d, qM X₁ h + qM X₂ h + ε / 2 * ‖h‖ ^ 2 ≤ 0 := by
    intro h
    have := qM_nonpos_of_isLocalMax (taylor_congr hTZ fun z => rfl) hloc h
    rw [qM_add', qM_add', qM_smul_one'] at this
    linarith
  -- the viscosity inequalities at the maximizers
  set η := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨y₁, hy₁S, hy₁⟩ := (supConv_spec hS hSne δ hu xh).2
  obtain ⟨y₂, hy₂S, hy₂⟩ := (supConv_spec hS hSne δ hwneg xh).2
  have hy₁U : y₁ ∈ U := hballU xh hxA (by
    rw [mem_ball, dist_comm, dist_eq_norm]
    exact (hUu δ hδ0 (min_le_left _ _) xh (hballS xh hxA (mem_ball_self hρ)) y₁ hy₁S hy₁).1)
  have hy₂U : y₂ ∈ U := hballU xh hxA (by
    rw [mem_ball, dist_comm, dist_eq_norm]
    exact (hUw δ hδ0 (min_le_right _ _) xh (hballS xh hxA (mem_ball_self hρ)) y₂ hy₂S hy₂).1)
  have hF1 : F (X₁ + η • 1) ≤ 0 :=
    le_zero_of_touch hsub hy₁U (hX₁s.add (Matrix.isSymm_one.smul _))
      (touch_supConv hS hU subset_closure hu hy₁U hy₁ (touch_of_taylor hTu hη0))
  have hF2 : 0 ≤ F (-(X₂ + η • 1)) :=
    nonneg_of_touch_neg hsup hy₂U (hX₂s.add (Matrix.isSymm_one.smul _))
      (touch_supConv hS hU subset_closure hwneg hy₂U hy₂ (touch_of_taylor hTw hη0))
  -- degenerate ellipticity and the shift
  set P₁ := X₁ + η • (1 : Matrix (Fin d) (Fin d) ℝ) with hP₁
  set P₂ := -(X₂ + η • (1 : Matrix (Fin d) (Fin d) ℝ)) with hP₂
  have hP₁s : P₁.IsSymm := hX₁s.add (Matrix.isSymm_one.smul _)
  have hP₂s : P₂.IsSymm := (hX₂s.add (Matrix.isSymm_one.smul _)).neg
  have hQs : (P₂ + (-(ε / 2)) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    hP₂s.add (Matrix.isSymm_one.smul _)
  have hpsd : (P₂ + (-(ε / 2)) • (1 : Matrix (Fin d) (Fin d) ℝ) - P₁).PosSemidef := by
    refine posSemidef_of_qM_nonneg' (hQs.sub hP₁s) fun h => ?_
    rw [hP₂, hP₁]
    simp only [qM_sub', qM_add', qM_neg', qM_smul_one']
    have := hneg h
    nlinarith [sq_nonneg ‖h‖]
  have hle := hF P₁ _ hP₁s hQs hpsd
  rw [hshift P₂ hP₂s (-(ε / 2))] at hle
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have : 0 < (d : ℝ) * (ε / 2) := by positivity
  linarith

end RandomSandpile

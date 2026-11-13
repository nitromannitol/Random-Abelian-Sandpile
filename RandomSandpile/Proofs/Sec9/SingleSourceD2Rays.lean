import RandomSandpile.Proofs.Sec9.SingleSourceD2Winding

/-!
# Theorem 9.2 in dimension two: the alternating-rays lemma

`alternatingRays : AlternatingRaysStmt`, by winding numbers instead of the
polygonal parity argument of SIMPLE-PROOF §3. In complex coordinates `L` with `L(a) = 0`, `L(v) = 1`,
`L(w) = i`: if a path `γ` in `P` joined `a + rv` to `a - rv`, then with the segment `S` from `a - rv`
to `a + rv` it forms a loop; `W(q) = Δ_γ(q) + Δ_S(q)` (changes of continuous logarithms of `γ - q`
and `S - q`) lies in `2πiℤ` and is constant along a path in `N` from `a + τw` to `a - τw`, while
`Im W(τi) - Im W(-τi) = 2π + o(1)` as `τ → 0` (explicit principal logarithms along `S`, continuity
of `Δ_γ` at `0`).
-/

noncomputable section

open Filter Topology Set Metric

namespace RandomSandpile

namespace SingleSourceD2

/-- Complex coordinates with respect to a basis `(v, w)` of the plane. -/
theorem exists_complex_coord {v w : Rd 2} (hli : LinearIndependent ℝ ![v, w]) :
    ∃ L : Rd 2 → ℂ, Continuous L ∧ Function.Injective L ∧ (∀ x y, L (x - y) = L x - L y) ∧
      (∀ (s : ℝ) (x : Rd 2), L (s • x) = s * L x) ∧ L v = 1 ∧ L w = Complex.I := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (Rd 2) := by simp
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = ![v, w] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hv : b 0 = v := by rw [hb]; rfl
  have hw : b 1 = w := by rw [hb]; rfl
  have hc0 : Continuous (b.coord 0) := LinearMap.continuous_of_finiteDimensional _
  have hc1 : Continuous (b.coord 1) := LinearMap.continuous_of_finiteDimensional _
  refine ⟨fun x => ((b.coord 0 x : ℝ) : ℂ) + ((b.coord 1 x : ℝ) : ℂ) * Complex.I, by fun_prop,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have h0 : b.coord 0 x = b.coord 0 y := by
      have := congrArg Complex.re hxy
      simpa using this
    have h1 : b.coord 1 x = b.coord 1 y := by
      have := congrArg Complex.im hxy
      simpa using this
    rw [Module.Basis.coord_apply, Module.Basis.coord_apply] at h0 h1
    refine b.ext_elem fun i => ?_
    fin_cases i
    · exact h0
    · exact h1
  · intro x y
    simp only [map_sub, Complex.ofReal_sub]
    ring
  · intro s x
    simp only [map_smul, smul_eq_mul, Complex.ofReal_mul]
    ring
  · rw [← hv]
    show (((b.coord 0 (b 0) : ℝ)) : ℂ) + ((b.coord 1 (b 0) : ℝ) : ℂ) * Complex.I = 1
    rw [Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, Finsupp.single_apply, ite_eq_right (by decide)]
    simp
  · rw [← hw]
    show (((b.coord 0 (b 1) : ℝ)) : ℂ) + ((b.coord 1 (b 1) : ℝ) : ℂ) * Complex.I = Complex.I
    rw [Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, Finsupp.single_apply, ite_eq_right (by decide)]
    simp

/-- The straight path `t ↦ (2t - 1) r` from `-r` to `r`. -/
def segPath (r : ℝ) (t : unitInterval) : ℂ := (((2 * (t : ℝ) - 1) * r : ℝ) : ℂ)

theorem continuous_segPath (r : ℝ) : Continuous (segPath r) := by
  unfold segPath
  fun_prop

theorem segPath_one (r : ℝ) : segPath r 1 = r := by norm_num [segPath]

theorem segPath_zero (r : ℝ) : segPath r 0 = -r := by norm_num [segPath]

/-- Off the real axis, the lift change along the segment is a difference of principal logarithms. -/
theorem liftChange_segPath {r y : ℝ} (hy : y ≠ 0) :
    liftChange (segPath r) (y * Complex.I) =
      Complex.log (r - y * Complex.I) - Complex.log (-r - y * Complex.I) := by
  have him : ∀ t, (segPath r t - y * Complex.I).im = -y := fun t => by simp [segPath]
  have hne : ∀ t, segPath r t ≠ y * Complex.I := fun t h => by
    have := him t
    rw [h, sub_self, Complex.zero_im] at this
    exact hy (by linarith)
  have hslit : ∀ t, segPath r t - y * Complex.I ∈ Complex.slitPlane := fun t =>
    Complex.mem_slitPlane_iff.2 (Or.inr (by rw [him t]; exact neg_ne_zero.2 hy))
  have hL : Continuous fun t => Complex.log (segPath r t - y * Complex.I) :=
    continuous_iff_continuousAt.2 fun t =>
      ContinuousAt.comp (g := Complex.log) (f := fun t => segPath r t - (y : ℂ) * Complex.I)
        (continuousAt_clog (hslit t)) ((continuous_segPath r).sub continuous_const).continuousAt
  have hs1 : segPath r 1 = r := by norm_num [segPath]
  have hs0 : segPath r 0 = -r := by norm_num [segPath]
  rw [liftChange_eq (continuous_segPath r) hne hL fun t =>
    Complex.exp_log (sub_ne_zero.2 (hne t)), hs1, hs0]

/-- The jump of the imaginary part of the segment's lift change across the real axis. -/
theorem im_liftChange_segPath_jump {r τ : ℝ} (hτ : 0 < τ)
    (h1 : |Complex.arg (r + τ * Complex.I)| < Real.pi / 8)
    (h2 : |Complex.arg (r - τ * Complex.I)| < Real.pi / 8) :
    3 * Real.pi / 2 ≤ (liftChange (segPath r) (τ * Complex.I)).im -
      (liftChange (segPath r) ((-τ : ℝ) * Complex.I)).im := by
  rw [liftChange_segPath hτ.ne', liftChange_segPath (neg_ne_zero.2 hτ.ne')]
  simp only [Complex.sub_im, Complex.log_im]
  have e1 : (-(r : ℂ) - τ * Complex.I) = -(r + τ * Complex.I) := by ring
  have e2 : (-(r : ℂ) - ((-τ : ℝ) : ℂ) * Complex.I) = -(r - τ * Complex.I) := by push_cast; ring
  have e3 : ((r : ℂ) - ((-τ : ℝ) : ℂ) * Complex.I) = r + τ * Complex.I := by push_cast; ring
  have hi1 : 0 < ((r : ℂ) + τ * Complex.I).im := by simp [hτ]
  have hi2 : ((r : ℂ) - τ * Complex.I).im < 0 := by simp [hτ]
  rw [e1, e2, e3, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi1,
    Complex.arg_neg_eq_arg_add_pi_of_im_neg hi2]
  have := abs_lt.1 h1
  have := abs_lt.1 h2
  linarith [Real.pi_pos]

/-- `exp z = 1` forces `Im z ∈ 2πℤ`. -/
theorem im_div_two_pi_int {z : ℂ} (hz : Complex.exp z = 1) :
    ∃ k : ℤ, z.im / (2 * Real.pi) = k := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hz
  refine ⟨n, ?_⟩
  rw [hn]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
    Complex.im_ofNat]
  field_simp
  ring

/-- **(C3) SIMPLE-PROOF Lemma 3.1 (alternating rays).** -/
theorem alternatingRays : AlternatingRaysStmt := by
  intro P N a v w r hP hN hPN hNc haP haN hli hr hrays hmem
  obtain ⟨L, hLc, hLi, hLsub, hLsmul, hLv, hLw⟩ := exists_complex_coord hli
  have hpr := (hrays r hr le_rfl).1
  -- a path `γ` in `P` from `a + r v` to `a - r v`
  have hKo : IsOpen (connectedComponentIn P (a + r • v)) := hP.connectedComponentIn
  have hKc : IsConnected (connectedComponentIn P (a + r • v)) :=
    isConnected_connectedComponentIn_iff.2 hpr
  have hj := ((hKo.isConnected_iff_isPathConnected).1 hKc).joinedIn _
    (mem_connectedComponentIn hpr) _ hmem
  set γ := hj.somePath
  have hγP : ∀ t, γ t ∈ P := fun t => connectedComponentIn_subset _ _ (hj.somePath_mem t)
  -- `γ` stays away from `a`
  obtain ⟨t₀, -, ht₀⟩ := (isCompact_univ (X := unitInterval)).exists_isMinOn univ_nonempty
    (by fun_prop : Continuous fun t => ‖γ t - a‖).continuousOn
  set δ := ‖γ t₀ - a‖
  have hδ : 0 < δ := norm_pos_iff.2 (sub_ne_zero.2 fun h => haP (h ▸ hγP t₀))
  have hγδ : ∀ t, δ ≤ ‖γ t - a‖ := fun t => isMinOn_iff.mp ht₀ t (mem_univ t)
  -- complex coordinates of `γ` and of the segment
  have hLa : ∀ x, L x - L a = L (x - a) := fun x => (hLsub x a).symm
  set c₁ : unitInterval → ℂ := fun t => L (γ t) - L a
  have hc₁ : Continuous c₁ := (hLc.comp γ.continuous).sub continuous_const
  have hc₁0 : c₁ 0 = r := by
    show L (γ 0) - L a = r
    rw [γ.source, hLa, add_sub_cancel_left, hLsmul, hLv, mul_one]
  have hc₁1 : c₁ 1 = -r := by
    show L (γ 1) - L a = -r
    rw [γ.target, hLa, sub_sub_cancel_left, ← neg_smul, hLsmul, hLv, mul_one,
      Complex.ofReal_neg]
  have hseg : ∀ t, segPath r t = L (a + ((2 * (t : ℝ) - 1) * r) • v) - L a := fun t => by
    rw [hLa, add_sub_cancel_left, hLsmul, hLv, mul_one]
    rfl
  have hsegP : ∀ s : ℝ, |s| ≤ r → s ≠ 0 → a + s • v ∈ P := fun s hs hs0 => by
    rcases lt_or_gt_of_ne hs0 with hneg | hpos
    · have h := (hrays (-s) (by linarith) (by rw [abs_of_neg hneg] at hs; linarith)).2.1
      have e : a - (-s) • v = a + s • v := by rw [neg_smul, sub_neg_eq_add]
      rwa [e] at h
    · exact (hrays s hpos (by rw [abs_of_pos hpos] at hs; exact hs)).1
  -- points of `N` avoid both curves
  have havoid₁ : ∀ x ∈ N, ∀ t, c₁ t ≠ L x - L a := fun x hx t h =>
    Set.disjoint_left.1 hPN (hγP t) (hLi (sub_left_inj.1 h) ▸ hx)
  have havoid₂ : ∀ x ∈ N, ∀ t, segPath r t ≠ L x - L a := fun x hx t h => by
    rw [hseg] at h
    have hx' := hLi (sub_left_inj.1 h)
    by_cases hs0 : (2 * (t : ℝ) - 1) * r = 0
    · rw [hs0, zero_smul, add_zero] at hx'
      exact haN (hx' ▸ hx)
    · have ht1 : |2 * (t : ℝ) - 1| ≤ 1 := abs_le.2 ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
      have hs : |(2 * (t : ℝ) - 1) * r| ≤ r := by
        rw [abs_mul, abs_of_pos hr]
        exact mul_le_of_le_one_left hr.le ht1
      exact Set.disjoint_left.1 hPN (hsegP _ hs hs0) (hx' ▸ hx)
  -- a vertical path near `0` avoiding `γ`
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℝ, τ₀ = min r (δ / (2 * (‖w‖ + 1))) := ⟨_, rfl⟩
  have hτ₀pos : 0 < τ₀ := by rw [hτ₀]; exact lt_min hr (by positivity)
  have hτ₀δ : τ₀ * ‖w‖ < δ := by
    have h1 : τ₀ ≤ δ / (2 * (‖w‖ + 1)) := by rw [hτ₀]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg w]
  set σv : unitInterval → ℂ := fun s => (((2 * (s : ℝ) - 1) * τ₀ : ℝ) : ℂ) * Complex.I
  have hσv : Continuous σv := by fun_prop
  have havoidv : ∀ s t, c₁ t ≠ σv s := fun s t h => by
    have hy : |(2 * (s : ℝ) - 1) * τ₀| ≤ τ₀ := by
      rw [abs_mul, abs_of_pos hτ₀pos]
      exact mul_le_of_le_one_left hτ₀pos.le
        (abs_le.2 ⟨by linarith [s.2.1], by linarith [s.2.2]⟩)
    have hL' : L (γ t - a) = L (((2 * (s : ℝ) - 1) * τ₀) • w) := by
      rw [← hLa, hLsmul, hLw]
      exact h
    have h2 := hγδ t
    rw [hLi hL', norm_smul, Real.norm_eq_abs] at h2
    nlinarith [mul_le_mul_of_nonneg_right hy (norm_nonneg w)]
  have hlc := continuous_liftChange_comp hc₁ hσv havoidv
  obtain ⟨η₂, hη₂, hη₂c⟩ := Metric.continuousAt_iff.1
    (hlc.continuousAt (x := ⟨1 / 2, by norm_num, by norm_num⟩)) (Real.pi / 4) (by positivity)
  -- continuity of `arg` at `r`
  have harg : ContinuousAt (fun y : ℝ => Complex.arg ((r : ℂ) + (y : ℂ) * Complex.I)) 0 := by
    have h1 : ContinuousAt Complex.arg ((r : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) :=
      Complex.continuousAt_arg (by simp [Complex.mem_slitPlane_iff, hr])
    exact ContinuousAt.comp (g := Complex.arg) h1 (by fun_prop)
  have harg0 : Complex.arg ((r : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = 0 := by
    simp [Complex.arg_ofReal_of_nonneg hr.le]
  obtain ⟨η₁, hη₁, hη₁c⟩ := Metric.continuousAt_iff.1 harg (Real.pi / 8) (by positivity)
  -- the parameter `τ`
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = min (min (τ₀ / 2) (τ₀ * η₂)) (η₁ / 2) := ⟨_, rfl⟩
  have hτ : 0 < τ := by
    rw [hτdef]
    exact lt_min (lt_min (half_pos hτ₀pos) (mul_pos hτ₀pos hη₂)) (half_pos hη₁)
  have hτ1 : τ ≤ τ₀ / 2 := by rw [hτdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hτ2 : τ ≤ τ₀ * η₂ := by rw [hτdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hτ3 : τ ≤ η₁ / 2 := by rw [hτdef]; exact min_le_right _ _
  have hτr : τ ≤ r := hτ1.trans ((half_le_self hτ₀pos.le).trans (by rw [hτ₀]; exact min_le_left _ _))
  -- `|arg (r ± τ i)| < π/8`
  have hargp : |Complex.arg ((r : ℂ) + τ * Complex.I)| < Real.pi / 8 := by
    have h := hη₁c (x := τ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hτ]; linarith)
    rwa [harg0, Real.dist_eq, sub_zero] at h
  have hargm : |Complex.arg ((r : ℂ) - τ * Complex.I)| < Real.pi / 8 := by
    have h := hη₁c (x := -τ) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hτ]; linarith)
    rw [harg0, Real.dist_eq, sub_zero] at h
    have e : (r : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I = (r : ℂ) - τ * Complex.I := by push_cast; ring
    rwa [e] at h
  -- `Δ_γ(τ i) ≈ Δ_γ(-τ i)`
  have hq : τ / (2 * τ₀) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hq0 : 0 < τ / (2 * τ₀) := by positivity
  have hqη : τ / (2 * τ₀) < η₂ := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  set sp : unitInterval := ⟨1 / 2 + τ / (2 * τ₀), by linarith, by linarith⟩
  set sm : unitInterval := ⟨1 / 2 - τ / (2 * τ₀), by linarith, by linarith⟩
  have hσp : σv sp = (τ : ℂ) * Complex.I := by
    show ((((2 * (1 / 2 + τ / (2 * τ₀)) - 1) * τ₀ : ℝ)) : ℂ) * Complex.I = _
    congr 2
    field_simp
    ring
  have hσm : σv sm = ((-τ : ℝ) : ℂ) * Complex.I := by
    show ((((2 * (1 / 2 - τ / (2 * τ₀)) - 1) * τ₀ : ℝ)) : ℂ) * Complex.I = _
    congr 2
    field_simp
    ring
  have hdp := hη₂c (x := sp) (by
    rw [Subtype.dist_eq, Real.dist_eq]
    show |1 / 2 + τ / (2 * τ₀) - 1 / 2| < η₂
    rw [add_sub_cancel_left, abs_of_pos hq0]; exact hqη)
  have hdm := hη₂c (x := sm) (by
    rw [Subtype.dist_eq, Real.dist_eq]
    show |1 / 2 - τ / (2 * τ₀) - 1 / 2| < η₂
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos hq0]; exact hqη)
  rw [hσp, Complex.dist_eq] at hdp
  rw [hσm, Complex.dist_eq] at hdm
  have hγjump : |(liftChange c₁ ((τ : ℂ) * Complex.I)).im -
      (liftChange c₁ (((-τ : ℝ) : ℂ) * Complex.I)).im| < Real.pi / 2 := by
    have h1 := Complex.abs_im_le_norm (liftChange c₁ ((τ : ℂ) * Complex.I) -
      liftChange c₁ (σv ⟨1 / 2, by norm_num, by norm_num⟩))
    have h2 := Complex.abs_im_le_norm (liftChange c₁ (((-τ : ℝ) : ℂ) * Complex.I) -
      liftChange c₁ (σv ⟨1 / 2, by norm_num, by norm_num⟩))
    rw [Complex.sub_im] at h1 h2
    rw [abs_lt]
    constructor <;> linarith [(abs_lt.1 (h1.trans_lt hdp)).1, (abs_lt.1 (h1.trans_lt hdp)).2,
      (abs_lt.1 (h2.trans_lt hdm)).1, (abs_lt.1 (h2.trans_lt hdm)).2]
  -- a path in `N` from `a + τ w` to `a - τ w`
  obtain ⟨-, -, hNp, hNm⟩ := hrays τ hτ hτr
  have hNconn : IsConnected N := ⟨⟨_, hNp⟩, hNc⟩
  have hjN := ((hN.isConnected_iff_isPathConnected).1 hNconn).joinedIn _ hNp _ hNm
  set σN := hjN.somePath
  set σc : unitInterval → ℂ := fun s => L (σN s) - L a
  have hσc : Continuous σc := (hLc.comp σN.continuous).sub continuous_const
  have hav1 : ∀ s t, c₁ t ≠ σc s := fun s t => havoid₁ _ (hjN.somePath_mem s) t
  have hav2 : ∀ s t, segPath r t ≠ σc s := fun s t => havoid₂ _ (hjN.somePath_mem s) t
  have hWc : Continuous fun s => liftChange c₁ (σc s) + liftChange (segPath r) (σc s) :=
    (continuous_liftChange_comp hc₁ hσc hav1).add
      (continuous_liftChange_comp (continuous_segPath r) hσc hav2)
  have hWint : ∀ s, ∃ k : ℤ,
      (liftChange c₁ (σc s) + liftChange (segPath r) (σc s)).im / (2 * Real.pi) = k := by
    intro s
    refine im_div_two_pi_int ?_
    have h1 : (r : ℂ) - σc s ≠ 0 := sub_ne_zero.2 (by rw [← hc₁0]; exact hav1 s 0)
    have h2 : -(r : ℂ) - σc s ≠ 0 := sub_ne_zero.2 (by rw [← hc₁1]; exact hav1 s 1)
    rw [Complex.exp_add, exp_liftChange hc₁ (fun t => hav1 s t),
      exp_liftChange (continuous_segPath r) (fun t => hav2 s t), hc₁0, hc₁1, segPath_one,
      segPath_zero, div_mul_div_comm, mul_comm (-(r : ℂ) - σc s), div_self (mul_ne_zero h1 h2)]
  have hWeq := int_valued_endpoints ((Complex.continuous_im.comp hWc).div_const _) hWint
  have hσ0 : σc 0 = (τ : ℂ) * Complex.I := by
    show L (σN 0) - L a = _
    rw [σN.source, hLa, add_sub_cancel_left, hLsmul, hLw]
  have hσ1 : σc 1 = ((-τ : ℝ) : ℂ) * Complex.I := by
    show L (σN 1) - L a = _
    rw [σN.target, hLa, sub_sub_cancel_left, ← neg_smul, hLsmul, hLw]
  simp only [Function.comp_apply, hσ0, hσ1, Complex.add_im] at hWeq
  have hjump := im_liftChange_segPath_jump (r := r) hτ hargp hargm
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [div_left_inj' hpi.ne'] at hWeq
  linarith [(abs_lt.1 hγjump).1, (abs_lt.1 hγjump).2, Real.pi_pos]

end SingleSourceD2

end RandomSandpile

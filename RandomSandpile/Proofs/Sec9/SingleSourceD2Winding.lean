import RandomSandpile.Proofs.Sec9.SingleSourceD2Label

/-!
# Theorem 9.2 in dimension two: lift changes of logarithms

Winding-number infrastructure for the alternating-rays lemma, built on
Mathlib's covering-space lifting for `Complex.exp` (`Complex.isCoveringMap_exp`,
`IsCoveringMap.liftHomotopy`).
* `exists_log_homotopy`: a nonvanishing continuous map on `I × A` has a continuous logarithm
  extending a given one on `{0} × A`;
* `exists_log_path`: continuous logarithms along paths;
* `log_change_unique`: two continuous logarithms of one map on `I` have the same change;
* `liftChange c q`: the change of a continuous logarithm of `t ↦ c t - q` along `[0, 1]`,
  `exp_liftChange`, and `continuous_liftChange_comp`: continuity along paths avoiding `c`.
-/

noncomputable section

open Filter Topology Set

namespace RandomSandpile

namespace SingleSourceD2

/-- A continuous logarithm on `I × A` of a nonvanishing map, extending one on `{0} × A`. -/
theorem exists_log_homotopy {A : Type*} [TopologicalSpace A] (g : unitInterval × A → ℂ)
    (hg : Continuous g) (hg0 : ∀ x, g x ≠ 0) (f : A → ℂ) (hf : Continuous f)
    (hf0 : ∀ a, Complex.exp (f a) = g (0, a)) :
    ∃ L : unitInterval × A → ℂ, Continuous L ∧ (∀ x, Complex.exp (L x) = g x) ∧
      ∀ a, L (0, a) = f a := by
  have cov : IsCoveringMap (fun z : ℂ =>
      (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) := Complex.isCoveringMap_exp
  let H : C(unitInterval × A, {w : ℂ // w ≠ 0}) := ⟨fun x => ⟨g x, hg0 x⟩, hg.subtype_mk _⟩
  let f' : C(A, ℂ) := ⟨f, hf⟩
  have H0 : ∀ a, H (0, a) = (fun z : ℂ =>
      (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) (f' a) :=
    fun a => Subtype.ext (hf0 a).symm
  refine ⟨cov.liftHomotopy H f' H0, (cov.liftHomotopy H f' H0).continuous, fun x => ?_,
    fun a => cov.liftHomotopy_zero H f' H0 a⟩
  have := congrFun (cov.liftHomotopy_lifts H f' H0) x
  exact congrArg Subtype.val this

/-- A continuous logarithm along a path. -/
theorem exists_log_path (c : unitInterval → ℂ) (hc : Continuous c) (hc0 : ∀ t, c t ≠ 0) :
    ∃ L : unitInterval → ℂ, Continuous L ∧ ∀ t, Complex.exp (L t) = c t := by
  obtain ⟨L, hL, hLe, -⟩ := exists_log_homotopy (A := Unit) (fun x => c x.1)
    (hc.comp continuous_fst) (fun x => hc0 x.1) (fun _ => Complex.log (c 0)) continuous_const
    (fun _ => Complex.exp_log (hc0 0))
  exact ⟨fun t => L (t, ()), hL.comp (continuous_id.prodMk continuous_const),
    fun t => hLe (t, ())⟩

theorem int_cast_ne_half (m : ℤ) : (m : ℝ) ≠ 1 / 2 := by
  intro h
  rcases le_or_gt m 0 with hm | hm
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    linarith
  · have h1 : (1 : ℤ) ≤ m := by omega
    have : (1 : ℝ) ≤ m := by exact_mod_cast h1
    linarith

/-- A continuous integer-valued function on `I` has equal endpoint values. -/
theorem int_valued_endpoints {φ : unitInterval → ℝ} (hφ : Continuous φ)
    (hint : ∀ t, ∃ k : ℤ, φ t = k) : φ 1 = φ 0 := by
  by_contra hne
  obtain ⟨k₀, hk₀⟩ := hint 0
  obtain ⟨k₁, hk₁⟩ := hint 1
  have hI : IsPreconnected (univ : Set unitInterval) := isPreconnected_univ
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hk : k₁ < k₀ := by
      rw [hk₀, hk₁] at hlt; exact_mod_cast hlt
    have hk' : (k₁ : ℝ) + 1 ≤ k₀ := by exact_mod_cast hk
    have hm : (k₁ : ℝ) + 1 / 2 ∈ Icc (φ 1) (φ 0) :=
      ⟨by rw [hk₁]; linarith, by rw [hk₀]; linarith⟩
    obtain ⟨t, -, ht⟩ := hI.intermediate_value (mem_univ 1) (mem_univ 0) hφ.continuousOn hm
    obtain ⟨k, hk2⟩ := hint t
    rw [hk2] at ht
    exact int_cast_ne_half (k - k₁) (by push_cast; linarith)
  · have hk : k₀ < k₁ := by
      rw [hk₀, hk₁] at hlt; exact_mod_cast hlt
    have hk' : (k₀ : ℝ) + 1 ≤ k₁ := by exact_mod_cast hk
    have hm : (k₀ : ℝ) + 1 / 2 ∈ Icc (φ 0) (φ 1) :=
      ⟨by rw [hk₀]; linarith, by rw [hk₁]; linarith⟩
    obtain ⟨t, -, ht⟩ := hI.intermediate_value (mem_univ 0) (mem_univ 1) hφ.continuousOn hm
    obtain ⟨k, hk2⟩ := hint t
    rw [hk2] at ht
    exact int_cast_ne_half (k - k₀) (by push_cast; linarith)

/-- Two continuous logarithms of the same map on `I` have the same change. -/
theorem log_change_unique {L₁ L₂ : unitInterval → ℂ} (h₁ : Continuous L₁) (h₂ : Continuous L₂)
    (h : ∀ t, Complex.exp (L₁ t) = Complex.exp (L₂ t)) : L₁ 1 - L₁ 0 = L₂ 1 - L₂ 0 := by
  have hn : ∀ t, ∃ n : ℤ, L₁ t = L₂ t + n * (2 * Real.pi * Complex.I) := fun t =>
    Complex.exp_eq_exp_iff_exists_int.1 (h t)
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have him : ∀ t, ∃ k : ℤ, (L₁ t - L₂ t).im / (2 * Real.pi) = k := fun t => by
    obtain ⟨n, hn'⟩ := hn t
    refine ⟨n, ?_⟩
    rw [hn', add_sub_cancel_left]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]
    field_simp
    ring
  have hc : Continuous fun t => (L₁ t - L₂ t).im / (2 * Real.pi) :=
    (Complex.continuous_im.comp (h₁.sub h₂)).div_const _
  have heq := int_valued_endpoints hc him
  obtain ⟨n₀, hn₀⟩ := hn 0
  obtain ⟨n₁, hn₁⟩ := hn 1
  have e0 : (L₁ 0 - L₂ 0).im / (2 * Real.pi) = n₀ := by
    rw [hn₀, add_sub_cancel_left]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]
    field_simp
    ring
  have e1 : (L₁ 1 - L₂ 1).im / (2 * Real.pi) = n₁ := by
    rw [hn₁, add_sub_cancel_left]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]
    field_simp
    ring
  have hnn : n₁ = n₀ := by
    have : (n₁ : ℝ) = n₀ := by rw [← e0, ← e1]; exact heq
    exact_mod_cast this
  rw [hn₀, hn₁, hnn]
  ring

open Classical in
/-- The change of a continuous logarithm of `t ↦ c t - q` along `[0, 1]` (junk `0` if `c` is not
continuous or meets `q`). -/
def liftChange (c : unitInterval → ℂ) (q : ℂ) : ℂ :=
  if h : Continuous c ∧ ∀ t, c t ≠ q then
    Classical.choose (exists_log_path (fun t => c t - q) (h.1.sub continuous_const)
        (fun t => sub_ne_zero.2 (h.2 t))) 1 -
      Classical.choose (exists_log_path (fun t => c t - q) (h.1.sub continuous_const)
        (fun t => sub_ne_zero.2 (h.2 t))) 0
  else 0

theorem liftChange_eq {c : unitInterval → ℂ} {q : ℂ} (hc : Continuous c) (hq : ∀ t, c t ≠ q)
    {L : unitInterval → ℂ} (hL : Continuous L) (hLe : ∀ t, Complex.exp (L t) = c t - q) :
    liftChange c q = L 1 - L 0 := by
  rw [liftChange, dite_eq_left ⟨hc, hq⟩]
  have hs := Classical.choose_spec (exists_log_path (fun t => c t - q) (hc.sub continuous_const)
    (fun t => sub_ne_zero.2 (hq t)))
  exact log_change_unique hs.1 hL fun t => (hs.2 t).trans (hLe t).symm

theorem exp_liftChange {c : unitInterval → ℂ} {q : ℂ} (hc : Continuous c) (hq : ∀ t, c t ≠ q) :
    Complex.exp (liftChange c q) = (c 1 - q) / (c 0 - q) := by
  obtain ⟨L, hL, hLe⟩ := exists_log_path (fun t => c t - q) (hc.sub continuous_const)
    (fun t => sub_ne_zero.2 (hq t))
  rw [liftChange_eq hc hq hL hLe, Complex.exp_sub, hLe, hLe]

/-- Continuity of the lift change along a path `σ` avoiding `c`. -/
theorem continuous_liftChange_comp {c σ : unitInterval → ℂ} (hc : Continuous c)
    (hσ : Continuous σ) (hav : ∀ s t, c t ≠ σ s) :
    Continuous fun s => liftChange c (σ s) := by
  obtain ⟨f, hf, hfe⟩ := exists_log_path (fun t => c t - σ 0) (hc.sub continuous_const)
    (fun t => sub_ne_zero.2 (hav 0 t))
  obtain ⟨L, hL, hLe, -⟩ := exists_log_homotopy (A := unitInterval) (fun x => c x.2 - σ x.1)
    ((hc.comp continuous_snd).sub (hσ.comp continuous_fst)) (fun x => sub_ne_zero.2 (hav x.1 x.2))
    f hf hfe
  have e : (fun s => liftChange c (σ s)) = fun s => L (s, 1) - L (s, 0) := by
    funext s
    exact liftChange_eq hc (hav s) (hL.comp (Continuous.prodMk_right s)) fun t => hLe (s, t)
  rw [e]
  exact (hL.comp (continuous_id.prodMk continuous_const)).sub
    (hL.comp (continuous_id.prodMk continuous_const))

end SingleSourceD2

end RandomSandpile

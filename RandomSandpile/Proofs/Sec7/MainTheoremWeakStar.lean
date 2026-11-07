import RandomSandpile.Proofs.Sec7.MainTheoremSandpile

/-!
# Theorem 1.1, step: weak-* limits in `L^∞`

`weakStarRepresentation : WeakStarRepresentationStmt`. A sequence `f_n` of measurable functions
with `|f_n| ≤ C`, eventually vanishing off a bounded set `B`, whose integrals against every test
function `φ ∈ C_c^∞(ℝ^d)` converge, converges weakly-* (against `L¹`) to some `s ∈ L^∞(ℝ^d)`.

Route.
1. The limit functional `T g = lim ∫ f_n g` exists for every `g ∈ L¹`: `C_c^∞` is dense in `L¹`
   (`MemLp.exist_eLpNorm_sub_le`) and `|∫ f_n (g - φ)| ≤ C ‖g - φ‖₁`; `T` is linear,
   `|T g| ≤ C ‖g‖₁`, and `T g = T (𝟙_U g)` for a ball `U ⊇ B`.
2. On the Hilbert space `L²(U)` (`U` has finite measure), `F ↦ T(𝟙_U F)` is a continuous linear
   functional (`‖F‖₁ ≤ |U|^{1/2} ‖F‖₂`); the Riesz representation theorem
   (`InnerProductSpace.toDual`) gives `S ∈ L²(U)` with `T(𝟙_A) = ∫_{A ∩ U} S` for every measurable
   `A` of finite measure (tested against `indicatorConstLp`).
3. `s = 𝟙_U S` satisfies `|∫_A s| ≤ C |A|`, hence `|s| ≤ C` a.e., and `∫ s g = T g` on all of
   `L¹` by `Integrable.induction` (both sides are `C`-Lipschitz on `L¹`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace RandomSandpile

variable {d : ℕ}

/-! ### The limit functional on `L¹` -/

theorem integrable_mul_of_abs_le {f : Rd d → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) {g : Rd d → ℝ} (hg : Integrable g volume) :
    Integrable (fun x => f x * g x) volume :=
  hg.bdd_mul hf.aestronglyMeasurable (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem abs_integral_mul_le_of_abs_le {f : Rd d → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) {g : Rd d → ℝ} (hg : Integrable g volume) :
    |∫ x, f x * g x| ≤ C * ∫ x, |g x| := by
  calc |∫ x, f x * g x| ≤ ∫ x, |f x * g x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, C * |g x| := integral_mono (integrable_mul_of_abs_le hf hC hg).abs
        (hg.abs.const_mul C) fun x => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
    _ = C * ∫ x, |g x| := integral_const_mul _ _

/-- Convergence against `C_c^∞` extends to `L¹` for uniformly bounded sequences. -/
theorem exists_tendsto_integral_mul_of_testFn {f : ℕ → Rd d → ℝ}
    (hmeas : ∀ n, Measurable (f n)) {C : ℝ} (hC : ∀ n x, |f n x| ≤ C)
    (hconv : ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∃ L : ℝ, Tendsto (fun n => ∫ x, f n x * φ x) atTop (𝓝 L))
    {g : Rd d → ℝ} (hg : Integrable g volume) :
    ∃ L : ℝ, Tendsto (fun n => ∫ x, f n x * g x) atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  set δ := ε / (4 * (C + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨φ, hφc, hφs, hφn⟩ :=
    (memLp_one_iff_integrable.2 hg).exist_eLpNorm_sub_le ENNReal.one_ne_top le_rfl hδpos
  have hφi : Integrable φ volume := hφs.continuous.integrable_of_hasCompactSupport hφc
  have hgφ : ∫ x, |g x - φ x| ≤ δ := by
    have h1 : ∫ x, ‖(g - φ) x‖ = (eLpNorm (g - φ) 1 volume).toReal := by
      rw [integral_norm_eq_lintegral_enorm (hg.sub hφi).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm]
    have h2 : (eLpNorm (g - φ) 1 volume).toReal ≤ δ :=
      ENNReal.toReal_le_of_le_ofReal hδpos.le hφn
    simpa [Real.norm_eq_abs] using h1.trans_le h2
  obtain ⟨L, hL⟩ := hconv φ hφs hφc
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hL.cauchySeq (ε / 2) (half_pos hε)
  have hgφi : Integrable (fun x => g x - φ x) volume := hg.sub hφi
  have hsplit : ∀ k, ∫ x, f k x * g x = (∫ x, f k x * φ x) + ∫ x, f k x * (g x - φ x) :=
    fun k => by
    rw [← integral_add (integrable_mul_of_abs_le (hmeas k) (hC k) hφi)
      (integrable_mul_of_abs_le (hmeas k) (hC k) hgφi)]
    congr 1; funext x; ring
  have herr : ∀ k, |∫ x, f k x * (g x - φ x)| ≤ C * δ := fun k =>
    (abs_integral_mul_le_of_abs_le (hmeas k) (hC k) hgφi).trans
      (mul_le_mul_of_nonneg_left hgφ hC0)
  have hCδ : C * δ ≤ ε / 4 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := abs_lt.1 (by simpa [Real.dist_eq] using hN m hm n hn)
  rw [Real.dist_eq, hsplit m, hsplit n, abs_lt]
  have hm' := abs_le.1 (herr m)
  have hn' := abs_le.1 (herr n)
  constructor <;> linarith [hm'.1, hm'.2, hn'.1, hn'.2, h1.1, h1.2]

theorem integral_abs_indicator_one {A : Set (Rd d)} (hA : MeasurableSet A) :
    ∫ x, |A.indicator (fun _ => (1 : ℝ)) x| = volume.real A := by
  have : (fun x => |A.indicator (fun _ => (1 : ℝ)) x|) = A.indicator 1 := by
    funext x; by_cases hx : x ∈ A <;> simp [hx]
  rw [this, integral_indicator_one hA]

/-! ### The step -/

/-- **Step** of Theorem 1.1: weak-* limits in `L^∞`. -/
theorem weakStarRepresentation : WeakStarRepresentationStmt := by
  intro d f C B hB hmeas hC hsupp hconv
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0)
  obtain ⟨ρ, hρ⟩ := hB.subset_ball (0 : Rd d)
  set U : Set (Rd d) := Metric.ball 0 ρ with hU
  have hUm : MeasurableSet U := measurableSet_ball
  have hUfin : volume U < ⊤ := measure_ball_lt_top
  haveI : Fact (volume U < ⊤) := ⟨hUfin⟩
  have hint : ∀ n {g : Rd d → ℝ}, Integrable g volume →
      Integrable (fun x => f n x * g x) volume :=
    fun n _ hg => integrable_mul_of_abs_le (hmeas n) (hC n) hg
  -- 1. the limit functional
  set T : (Rd d → ℝ) → ℝ := fun g => limUnder atTop fun n => ∫ x, f n x * g x with hT
  have hTt : ∀ {g : Rd d → ℝ}, Integrable g volume →
      Tendsto (fun n => ∫ x, f n x * g x) atTop (𝓝 (T g)) := fun hg =>
    tendsto_nhds_limUnder (exists_tendsto_integral_mul_of_testFn hmeas hC hconv hg)
  have hTadd : ∀ {g h : Rd d → ℝ}, Integrable g volume → Integrable h volume →
      T (fun x => g x + h x) = T g + T h := by
    intro g h hg hh
    refine tendsto_nhds_unique (hTt (hg.add hh)) (((hTt hg).add (hTt hh)).congr fun n => ?_)
    rw [← integral_add (hint n hg) (hint n hh)]
    congr 1; funext x; ring
  have hTsmul : ∀ (c : ℝ) {g : Rd d → ℝ}, Integrable g volume →
      T (fun x => c * g x) = c * T g := by
    intro c g hg
    refine tendsto_nhds_unique (hTt (hg.const_mul c)) (((hTt hg).const_mul c).congr fun n => ?_)
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have hTae : ∀ {g g' : Rd d → ℝ}, g =ᵐ[volume] g' → T g = T g' := by
    intro g g' h
    show limUnder atTop (fun n => ∫ x, f n x * g x) =
      limUnder atTop (fun n => ∫ x, f n x * g' x)
    congr 1; funext n
    exact integral_congr_ae (h.mono fun x hx => by simp only [hx])
  have hTsub : ∀ {g h : Rd d → ℝ}, Integrable g volume → Integrable h volume →
      T (fun x => g x - h x) = T g - T h := by
    intro g h hg hh
    have e1 := hTadd hg (hh.const_mul (-1))
    rw [hTsmul (-1) hh] at e1
    calc T (fun x => g x - h x) = T (fun x => g x + -1 * h x) :=
          hTae (ae_of_all _ fun x => by ring)
      _ = T g - T h := by rw [e1]; ring
  have hTbd : ∀ {g : Rd d → ℝ}, Integrable g volume → |T g| ≤ C * ∫ x, |g x| := fun hg =>
    le_of_tendsto (hTt hg).abs (Eventually.of_forall fun n =>
      abs_integral_mul_le_of_abs_le (hmeas n) (hC n) hg)
  have hTU : ∀ {g : Rd d → ℝ}, Integrable g volume → T g = T (U.indicator g) := by
    intro g hg
    refine tendsto_nhds_unique (hTt hg) ((hTt (hg.indicator hUm)).congr' ?_)
    filter_upwards [hsupp] with n hn
    congr 1; funext x
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, hn x fun hxB => hx (hρ hxB)]
  -- 2. the Riesz representation on `L²(U)`
  have hLint : ∀ F : Lp ℝ 2 (volume.restrict U), Integrable (U.indicator ⇑F) volume := fun F =>
    (integrable_indicator_iff hUm).2 ((Lp.memLp F).integrable one_le_two)
  have hind_ae : ∀ {g h : Rd d → ℝ}, g =ᵐ[volume.restrict U] h →
      U.indicator g =ᵐ[volume] U.indicator h := by
    intro g h hgh
    filter_upwards [(ae_restrict_iff' hUm).1 hgh] with x hx
    by_cases hxU : x ∈ U
    · simp [Set.indicator_of_mem hxU, hx hxU]
    · simp [Set.indicator_of_notMem hxU]
  have hΛadd : ∀ F G : Lp ℝ 2 (volume.restrict U),
      T (U.indicator ⇑(F + G)) = T (U.indicator ⇑F) + T (U.indicator ⇑G) := by
    intro F G
    rw [hTae (hind_ae (Lp.coeFn_add F G)), ← hTadd (hLint F) (hLint G)]
    refine hTae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ U <;> simp [hx]
  have hΛsmul : ∀ (c : ℝ) (F : Lp ℝ 2 (volume.restrict U)),
      T (U.indicator ⇑(c • F)) = c * T (U.indicator ⇑F) := by
    intro c F
    rw [hTae (hind_ae (Lp.coeFn_smul c F)), ← hTsmul c (hLint F)]
    refine hTae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ U <;> simp [hx]
  set K : ℝ := ((volume.restrict U) Set.univ ^
    (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal with hK
  have hKbd : ∀ F : Lp ℝ 2 (volume.restrict U), ∫ x, |U.indicator (⇑F) x| ≤ ‖F‖ * K := by
    intro F
    have h1 : ∫ x, |U.indicator (⇑F) x| = ∫ x, ‖F x‖ ∂(volume.restrict U) := by
      rw [← integral_indicator hUm]
      congr 1; funext x
      by_cases hx : x ∈ U <;> simp [hx, Real.norm_eq_abs]
    have h2 : ∫ x, ‖F x‖ ∂(volume.restrict U) = (eLpNorm F 1 (volume.restrict U)).toReal := by
      rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable F),
        eLpNorm_one_eq_lintegral_enorm]
    have h3 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict U)
      (p := 1) (q := 2) one_le_two (Lp.aestronglyMeasurable F)
    have hfin : (volume.restrict U) Set.univ ^
        (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
    rw [h1, h2, Lp.norm_def, hK, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top F) hfin) h3
  let Λlin : Lp ℝ 2 (volume.restrict U) →ₗ[ℝ] ℝ :=
    { toFun := fun F => T (U.indicator ⇑F)
      map_add' := hΛadd
      map_smul' := fun c F => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact hΛsmul c F }
  let Λ : StrongDual ℝ (Lp ℝ 2 (volume.restrict U)) := Λlin.mkContinuous (C * K) fun F => by
    show ‖T (U.indicator ⇑F)‖ ≤ C * K * ‖F‖
    rw [Real.norm_eq_abs]
    calc |T (U.indicator ⇑F)| ≤ C * ∫ x, |U.indicator (⇑F) x| := hTbd (hLint F)
      _ ≤ C * (‖F‖ * K) := mul_le_mul_of_nonneg_left (hKbd F) hC0
      _ = C * K * ‖F‖ := by ring
  set S : Lp ℝ 2 (volume.restrict U) :=
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume.restrict U))).symm Λ with hS_def
  have hS : ∀ F : Lp ℝ 2 (volume.restrict U), ⟪S, F⟫_ℝ = T (U.indicator ⇑F) := fun F =>
    InnerProductSpace.toDual_symm_apply
  set s : Rd d → ℝ := U.indicator ⇑S with hs_def
  have hsi : Integrable s volume := hLint S
  have hset : ∀ A : Set (Rd d), MeasurableSet A → volume A < ⊤ →
      ∫ x in A, s x = T (A.indicator fun _ => (1 : ℝ)) := by
    intro A hA hAfin
    have hμA : (volume.restrict U) A ≠ ⊤ :=
      ((Measure.restrict_apply_le (μ := (volume : Measure (Rd d))) U A).trans_lt hAfin).ne
    have e1 := hS (indicatorConstLp 2 hA hμA (1 : ℝ))
    rw [real_inner_comm, L2.inner_indicatorConstLp_one, Measure.restrict_restrict hA] at e1
    rw [hs_def, setIntegral_indicator hUm, e1, hTU (integrable_indicator_one hA hAfin)]
    have hcoe : ⇑(indicatorConstLp 2 hA hμA (1 : ℝ)) =ᵐ[volume.restrict U]
        A.indicator fun _ => (1 : ℝ) := indicatorConstLp_coeFn
    exact hTae (hind_ae hcoe)
  -- 3. bounds and the representation on `L¹`
  have hsA : ∀ A : Set (Rd d), MeasurableSet A → volume A < ⊤ →
      |∫ x in A, s x| ≤ C * volume.real A := fun A hA hAfin => by
    rw [hset A hA hAfin, ← integral_abs_indicator_one hA]
    exact hTbd (integrable_indicator_one hA hAfin)
  have hup : 0 ≤ᵐ[volume] fun x => C - s x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun A _ hAfin => (integrableOn_const (C := C) hAfin.ne).sub hsi.integrableOn)
      fun A hA hAfin => ?_
    rw [integral_sub (integrableOn_const (C := C) hAfin.ne) hsi.integrableOn, setIntegral_const,
      smul_eq_mul]
    linarith [(abs_le.1 (hsA A hA hAfin)).2]
  have hlo : 0 ≤ᵐ[volume] fun x => C + s x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun A _ hAfin => (integrableOn_const (C := C) hAfin.ne).add hsi.integrableOn)
      fun A hA hAfin => ?_
    rw [integral_add (integrableOn_const (C := C) hAfin.ne) hsi.integrableOn, setIntegral_const,
      smul_eq_mul]
    linarith [(abs_le.1 (hsA A hA hAfin)).1]
  have hsbd : ∀ᵐ x ∂volume, ‖s x‖ ≤ C := by
    filter_upwards [hup, hlo] with x h1 h2
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.zero_apply] at h1 h2
    constructor <;> linarith
  have hsmul_int : ∀ {u : Rd d → ℝ}, Integrable u volume →
      Integrable (fun x => s x * u x) volume := fun hu =>
    hu.bdd_mul hsi.aestronglyMeasurable hsbd
  have habs_s : ∀ {u : Rd d → ℝ}, Integrable u volume → |∫ x, s x * u x| ≤ C * ∫ x, |u x| := by
    intro u hu
    calc |∫ x, s x * u x| ≤ ∫ x, |s x * u x| := abs_integral_le_integral_abs
      _ ≤ ∫ x, C * |u x| := integral_mono_ae (hsmul_int hu).abs (hu.abs.const_mul C) (by
          filter_upwards [hsbd] with x hx
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hx) (abs_nonneg _))
      _ = C * ∫ x, |u x| := integral_const_mul _ _
  have hdistL1 : ∀ F G : Rd d →₁[volume] ℝ, ∫ x, |(⇑F) x - (⇑G) x| = dist F G := by
    intro F G
    rw [dist_eq_norm, L1.norm_eq_integral_norm]
    refine integral_congr_ae ((Lp.coeFn_sub F G).mono fun x hx => ?_)
    simp only [hx, Pi.sub_apply, Real.norm_eq_abs]
  have hrep : ∀ ⦃g : Rd d → ℝ⦄, Integrable g volume → ∫ x, s x * g x = T g := by
    refine Integrable.induction (μ := volume) (fun g => ∫ x, s x * g x = T g) ?_ ?_ ?_ ?_
    · intro c A hA hAfin
      have e1 : (fun x => s x * A.indicator (fun _ => c) x) =
          A.indicator fun x => c * s x := by
        funext x; by_cases hx : x ∈ A <;> simp [hx, mul_comm]
      have e2 : (A.indicator fun _ => c) = fun x => c * A.indicator (fun _ => (1 : ℝ)) x := by
        funext x; by_cases hx : x ∈ A <;> simp [hx]
      rw [e1, integral_indicator hA, integral_const_mul, hset A hA hAfin, e2,
        hTsmul c (integrable_indicator_one hA hAfin)]
    · intro g h _ hg hh hPg hPh
      show ∫ x, s x * (g x + h x) = T (fun x => g x + h x)
      rw [hTadd hg hh, ← hPg, ← hPh, ← integral_add (hsmul_int hg) (hsmul_int hh)]
      congr 1; funext x; ring
    · have hc1 : Continuous fun F : Rd d →₁[volume] ℝ => ∫ x, s x * F x := by
        refine (LipschitzWith.of_dist_le_mul (K := ⟨C, hC0⟩) fun F G => ?_).continuous
        rw [Real.dist_eq, ← integral_sub (hsmul_int (L1.integrable_coeFn F))
          (hsmul_int (L1.integrable_coeFn G)), ← hdistL1]
        change _ ≤ C * _
        calc |∫ x, (s x * F x - s x * G x)| = |∫ x, s x * (F x - G x)| := by
              congr 1; congr 1; funext x; ring
          _ ≤ C * ∫ x, |F x - G x| :=
              habs_s ((L1.integrable_coeFn F).sub (L1.integrable_coeFn G))
      have hc2 : Continuous fun F : Rd d →₁[volume] ℝ => T F := by
        refine (LipschitzWith.of_dist_le_mul (K := ⟨C, hC0⟩) fun F G => ?_).continuous
        rw [Real.dist_eq, ← hTsub (L1.integrable_coeFn F) (L1.integrable_coeFn G), ← hdistL1]
        change _ ≤ C * _
        exact hTbd ((L1.integrable_coeFn F).sub (L1.integrable_coeFn G))
      exact isClosed_eq hc1 hc2
    · intro g h hgh _ hPg
      show ∫ x, s x * h x = T h
      rw [← hTae hgh, ← hPg]
      exact integral_congr_ae (hgh.mono fun x hx => by rw [hx]) |>.symm
  refine ⟨s, memLp_top_of_bound hsi.aestronglyMeasurable C hsbd, fun g hg => ?_⟩
  rw [hrep hg]
  exact hTt hg

end RandomSandpile

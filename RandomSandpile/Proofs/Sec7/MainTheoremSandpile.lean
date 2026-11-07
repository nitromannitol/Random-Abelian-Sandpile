import RandomSandpile.Steps.Sec7.MainTheorem
import RandomSandpile.Steps.Sec7.Compactness

/-!
# Theorem 1.1: the sandpile claims from their sub-steps

`sandpileLimit_of_steps` derives `SandpileLimitStmt` from the bounds of the proof of
Lemma 7.2 (`FreeOdometerUpperBoundStmt`, `FreeOdometerLapBoundStmt`), the ergodic theorem
(`EnvWeakStarStmt`), summation by parts (`RescaledLapWeakStmt`), the representation of weak-*
limits in `L^∞` (`WeakStarRepresentationStmt`) and the support radius (`SandpileSupportStmt`).

Elementary ingredients proved here: measurability of the rescalings; weak-* limits inherit almost
everywhere upper bounds and vanishing (tested against indicators of sets of finite measure); the
weak-* limit is determined by its integrals against `C_c^∞` (so `s` does not depend on `η`); and
`∫ s = |W| E η(0)`, from the weak equation tested against a bump function equal to `1` on a ball
containing `B_R(W)` and the support of `v̄` (where the Hessian of the bump vanishes).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-! ### Measurability -/

theorem measurable_latticeRound : Measurable (latticeRound (d := d)) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact Int.measurable_floor.comp (PiLp.continuous_apply 2 _ i).measurable

theorem measurable_rescaleSandpile (s : Site d → ℤ) (n : ℕ) :
    Measurable (rescaleSandpile s n) :=
  (measurable_of_countable fun z : Site d => (s z : ℝ)).comp
    (measurable_latticeRound.comp (measurable_const_smul _))

/-! ### Weak-* limits tested against indicators -/

theorem integrable_indicator_one {A : Set (Rd d)} (hA : MeasurableSet A) (hfin : volume A < ⊤) :
    Integrable (A.indicator fun _ => (1 : ℝ)) volume :=
  (integrable_indicator_iff hA).2 (integrableOn_const hfin.ne)

theorem integral_mul_indicator_one (f : Rd d → ℝ) {A : Set (Rd d)} (hA : MeasurableSet A) :
    ∫ x, f x * A.indicator (fun _ => (1 : ℝ)) x = ∫ x in A, f x := by
  rw [← integral_indicator hA]
  congr 1
  funext x
  by_cases hx : x ∈ A <;> simp [hx]

theorem WeakStarTendsto.tendsto_setIntegral {f : ℕ → Rd d → ℝ} {s : Rd d → ℝ}
    (hf : WeakStarTendsto f s) {A : Set (Rd d)} (hA : MeasurableSet A) (hfin : volume A < ⊤) :
    Tendsto (fun n => ∫ x in A, f n x) atTop (𝓝 (∫ x in A, s x)) := by
  have := hf _ (integrable_indicator_one hA hfin)
  simpa only [integral_mul_indicator_one _ hA] using this

theorem memLp_top_integrableOn {s : Rd d → ℝ} (hs : MemLp s ⊤ volume) {A : Set (Rd d)}
    (hfin : volume A < ⊤) : IntegrableOn s A volume := by
  haveI : Fact (volume A < ⊤) := ⟨hfin⟩
  exact (hs.restrict A).integrable le_top

theorem integrableOn_of_abs_le {f : Rd d → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    {A : Set (Rd d)} (hfin : volume A < ⊤) : IntegrableOn f A volume :=
  Integrable.mono' (integrableOn_const (C := C) hfin.ne) hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- A weak-* limit in `L^∞` of functions eventually bounded above by `c` is bounded by `c`
almost everywhere. -/
theorem WeakStarTendsto.ae_le {f : ℕ → Rd d → ℝ} {s : Rd d → ℝ} (hf : WeakStarTendsto f s)
    (hs : MemLp s ⊤ volume) (hmeas : ∀ n, Measurable (f n)) {C c : ℝ}
    (hC : ∀ n x, |f n x| ≤ C) (hc : ∀ᶠ n in atTop, ∀ x, f n x ≤ c) :
    ∀ᵐ x ∂volume, s x ≤ c := by
  have h0 : 0 ≤ᵐ[volume] fun x => c - s x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun A _ hfin => (integrableOn_const (C := c) hfin.ne).sub (memLp_top_integrableOn hs hfin))
      fun A hA hfin => ?_
    have hlim := hf.tendsto_setIntegral hA hfin
    have hle : ∫ x in A, s x ≤ ∫ x in A, c := by
      refine le_of_tendsto hlim ?_
      filter_upwards [hc] with n hn
      exact setIntegral_mono (integrableOn_of_abs_le (hmeas n) (hC n) hfin)
        (integrableOn_const (C := c) hfin.ne) (hn)
    rw [integral_sub (integrableOn_const (C := c) hfin.ne) (memLp_top_integrableOn hs hfin)]
    linarith
  filter_upwards [h0] with x hx
  simpa using hx

/-- A weak-* limit of functions eventually vanishing off `T` vanishes almost everywhere off `T`. -/
theorem WeakStarTendsto.ae_eq_zero_of_compl {f : ℕ → Rd d → ℝ} {s : Rd d → ℝ}
    (hf : WeakStarTendsto f s) (hs : MemLp s ⊤ volume) {T : Set (Rd d)} (hT : MeasurableSet T)
    (hv : ∀ᶠ n in atTop, ∀ x, x ∉ T → f n x = 0) : ∀ᵐ x ∂volume, x ∉ T → s x = 0 := by
  have h0 : Tᶜ.indicator s =ᵐ[volume] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
      (fun A _ hfin => (memLp_top_integrableOn hs hfin).indicator hT.compl) fun A hA hfin => ?_
    rw [setIntegral_indicator hT.compl]
    have hfin' : volume (A ∩ Tᶜ) < ⊤ := (measure_mono Set.inter_subset_left).trans_lt hfin
    have hlim := hf.tendsto_setIntegral (hA.inter hT.compl) hfin'
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
    filter_upwards [hv] with n hn
    rw [setIntegral_eq_zero_of_forall_eq_zero fun x hx => hn x hx.2]
  filter_upwards [h0] with x hx hxT
  rw [Pi.zero_apply, Set.indicator_of_mem (Set.mem_compl hxT)] at hx
  exact hx

/-- Two `L^∞` functions with the same integrals against all test functions agree a.e. -/
theorem ae_eq_of_integral_testFn_eq {s s' : Rd d → ℝ} (hs : MemLp s ⊤ volume)
    (hs' : MemLp s' ⊤ volume)
    (h : ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, s x * φ x = ∫ x, s' x * φ x) : ∀ᵐ x ∂volume, s x = s' x := by
  refine ae_eq_of_integral_contDiff_smul_eq (hs.locallyIntegrable le_top)
    (hs'.locallyIntegrable le_top) fun g hg hgc => ?_
  simp only [smul_eq_mul]
  rw [show (fun x => g x * s x) = fun x => s x * g x from funext fun x => mul_comm _ _,
    show (fun x => g x * s' x) = fun x => s' x * g x from funext fun x => mul_comm _ _]
  exact h g hg hgc

/-! ### The bump function and the Hessian -/

theorem hessian_eq_zero_of_eventuallyEq_const {φ : Rd d → ℝ} {x : Rd d} {c : ℝ}
    (h : φ =ᶠ[𝓝 x] fun _ => c) : hessian φ x = 0 := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    rw [hy.fderiv_eq]
    exact fderiv_const_apply c
  ext i j
  simp [hessian, h1.fderiv_eq]

theorem integral_indicator_const_mul (W : Set (Rd d)) (hW : MeasurableSet W) (c : ℝ)
    (φ : Rd d → ℝ) : ∫ x, W.indicator (fun _ => c) x * φ x = c * ∫ x in W, φ x := by
  rw [← integral_const_mul, ← integral_indicator hW]
  congr 1
  funext x
  by_cases hx : x ∈ W <;> simp [hx]

/-! ### The reduction -/

/-- The sandpile claims for one environment `E` and one support radius `R` (the core of the argument,
shared by `sandpileLimit_of_steps` and the law-radius variant `sandpileLimitLaw_of_steps`,
`Proofs/Sec7/SandpileSupport.lean`). -/
theorem sandpileLimit_core (hUB : FreeOdometerUpperBoundStmt)
    (hLap : FreeOdometerLapBoundStmt) (hEnv : EnvWeakStarStmt) (hRL : RescaledLapWeakStmt)
    (hRep : WeakStarRepresentationStmt) (hd : 2 ≤ d) {W : Set (Rd d)} (hW : IsLipschitzDomain W)
    (E : RandomEnvironment d) {R : ℝ} (hR : 0 < R)
    (hSR : ∀ᵐ η ∂E.P, ∀ᶠ n : ℕ in atTop, ∀ x : Rd d, x ∉ Metric.thickening R W →
      rescaleSandpile (freeSandpile η (discretize W n)) n x = 0)
    (vbar : Rd d → ℝ) (hvc : Continuous vbar)
    (hae : ∀ᵐ η ∂E.P, TendstoUniformly
      (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n) vbar atTop) :
    ∃ s : Rd d → ℝ, MemLp s ⊤ volume ∧
      (∀ᵐ η ∂E.P,
        WeakStarTendsto (fun n : ℕ => rescaleSandpile (freeSandpile η (discretize W n)) n) s) ∧
      ∫ x, s x = (volume W).toReal * meanEta E.P ∧
      (∀ᵐ x ∂volume, s x ≤ 2 * (d : ℝ) - 1) ∧
      (∀ᵐ x ∂volume, x ∉ Metric.thickening R W → s x = 0) ∧
      ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, s x * φ x =
          (∫ x, vbar x * Matrix.trace (hessian φ x)) + meanEta E.P * ∫ x in W, φ x := by
  have hWm : MeasurableSet W := hW.2.1.measurableSet
  set T := Metric.thickening R W with hT_def
  have hTm : MeasurableSet T := Metric.isOpen_thickening.measurableSet
  have hTb : Bornology.IsBounded T := hW.1.thickening
  obtain ⟨C₀, R₀, hUB'⟩ := hUB d hd W hW.1 E.ηmax
  set K : ℝ := 2 * d + 2 * (|(E.ηmin : ℝ)| + |(E.ηmax : ℝ)|) with hK
  -- notation
  set sb : (Site d → ℤ) → ℕ → Rd d → ℝ :=
    fun η n => rescaleSandpile (freeSandpile η (discretize W n)) n with hsb
  set Tφ : (Rd d → ℝ) → ℝ := fun φ =>
    (∫ x, vbar x * Matrix.trace (hessian φ x)) + meanEta E.P * ∫ x in W, φ x with hTφ
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  -- the sandpile is bounded
  have hsbB : ∀ η : Site d → ℤ, (∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax) → ∀ n x, |sb η n x| ≤ K := by
    intro η hη n x
    have hne := (hUB' η (fun x => (hη x).2) n).1
    have hl := hLap d E.ηmin E.ηmax η (discretize W n) hη hne (latticeRound ((n : ℝ) • x))
    have hl' : |(lap (freeOdometer η (discretize W n)) (latticeRound ((n : ℝ) • x)) : ℝ)| ≤
        2 * d + |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| := by
      have := (Int.cast_le (R := ℝ)).2 hl
      push_cast at this
      exact this
    have hi : |(((discretize W n).indicator η (latticeRound ((n : ℝ) • x)) : ℤ) : ℝ)| ≤
        |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| := by
      by_cases hy : latticeRound ((n : ℝ) • x) ∈ discretize W n
      · rw [Set.indicator_of_mem hy]
        have h1 := (hη (latticeRound ((n : ℝ) • x))).1
        have h2 := (hη (latticeRound ((n : ℝ) • x))).2
        have h1' : (E.ηmin : ℝ) ≤ η (latticeRound ((n : ℝ) • x)) := by exact_mod_cast h1
        have h2' : (η (latticeRound ((n : ℝ) • x)) : ℝ) ≤ E.ηmax := by exact_mod_cast h2
        rw [abs_le]
        constructor <;> linarith [neg_abs_le (E.ηmin : ℝ), le_abs_self (E.ηmax : ℝ),
          abs_nonneg (E.ηmin : ℝ), abs_nonneg (E.ηmax : ℝ)]
      · rw [Set.indicator_of_notMem hy]; simp; positivity
    simp only [hsb, rescaleSandpile, freeSandpile, Int.cast_add]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hi hl'
      _ = K := by rw [hK]; ring
  -- convergence against test functions
  have hTest : ∀ η : Site d → ℤ, (∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax) →
      TendstoUniformly (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n) vbar atTop →
      WeakStarTendsto (fun n : ℕ => rescaleSandpile ((discretize W n).indicator η) n)
        (W.indicator fun _ => meanEta E.P) →
      ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        Tendsto (fun n => ∫ x, sb η n x * φ x) atTop (𝓝 (Tφ φ)) := by
    intro η hη hconv henv φ hφ hφc
    have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hlap := hRL d R₀ (fun n => freeOdometer η (discretize W n)) vbar
      (fun n x hx => (hUB' η (fun x => (hη x).2) n).2.2 x hx) hvc hconv φ hφ hφc
    have hen := henv φ hφi
    rw [integral_indicator_const_mul W hWm] at hen
    have hsum := hen.add hlap
    rw [add_comm] at hsum
    simp only [hTφ]
    refine Tendsto.congr (fun n => ?_) hsum
    have hi1 : Integrable (fun x => rescaleSandpile ((discretize W n).indicator η) n x * φ x)
        volume := by
      refine hφi.bdd_mul (c := |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| + 0)
        (measurable_rescaleSandpile _ n).aestronglyMeasurable (ae_of_all _ fun x => ?_)
      · rw [Real.norm_eq_abs]
        have := hsbB η hη n x
        simp only [hsb, rescaleSandpile, freeSandpile] at this ⊢
        by_cases hy : latticeRound ((n : ℝ) • x) ∈ discretize W n
        · rw [Set.indicator_of_mem hy]
          have h1 : (E.ηmin : ℝ) ≤ η (latticeRound ((n : ℝ) • x)) := by
            exact_mod_cast (hη _).1
          have h2 : (η (latticeRound ((n : ℝ) • x)) : ℝ) ≤ E.ηmax := by
            exact_mod_cast (hη _).2
          rw [abs_le]
          constructor <;> linarith [neg_abs_le (E.ηmin : ℝ), le_abs_self (E.ηmax : ℝ),
            abs_nonneg (E.ηmin : ℝ), abs_nonneg (E.ηmax : ℝ)]
        · rw [Set.indicator_of_notMem hy]; simp; positivity
    have hi2 : Integrable
        (fun x => rescaleSandpile (lap (freeOdometer η (discretize W n))) n x * φ x) volume := by
      refine hφi.bdd_mul (c := 2 * d + |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)|)
        (measurable_rescaleSandpile _ n).aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs]
      have hne := (hUB' η (fun x => (hη x).2) n).1
      have hl := hLap d E.ηmin E.ηmax η (discretize W n) hη hne (latticeRound ((n : ℝ) • x))
      have := (Int.cast_le (R := ℝ)).2 hl
      push_cast at this
      exact this
    rw [← integral_add hi1 hi2]
    congr 1
    funext x
    simp only [hsb, rescaleSandpile, freeSandpile, Int.cast_add]
    ring
  -- the good event
  have hG : ∀ᵐ η ∂E.P, (∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax) ∧
      TendstoUniformly (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n) vbar
        atTop ∧
      WeakStarTendsto (fun n : ℕ => rescaleSandpile ((discretize W n).indicator η) n)
        (W.indicator fun _ => meanEta E.P) ∧
      (∀ᶠ n : ℕ in atTop, ∀ x : Rd d, x ∉ T → sb η n x = 0) := by
    filter_upwards [hbdd, hae, hEnv d hd E W hW, hSR] with η h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  -- for every good `η`, a weak-* limit exists
  have hlimη : ∀ η : Site d → ℤ, (∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax) ∧
      TendstoUniformly (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n) vbar
        atTop ∧
      WeakStarTendsto (fun n : ℕ => rescaleSandpile ((discretize W n).indicator η) n)
        (W.indicator fun _ => meanEta E.P) ∧
      (∀ᶠ n : ℕ in atTop, ∀ x : Rd d, x ∉ T → sb η n x = 0) →
      ∃ s : Rd d → ℝ, MemLp s ⊤ volume ∧ WeakStarTendsto (sb η) s ∧
        ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ x, s x * φ x = Tφ φ := by
    rintro η ⟨h1, h2, h3, h4⟩
    obtain ⟨s, hs, hws⟩ := hRep d (sb η) K T hTb (fun n => measurable_rescaleSandpile _ n)
      (hsbB η h1) h4 fun φ hφ hφc => ⟨_, hTest η h1 h2 h3 φ hφ hφc⟩
    refine ⟨s, hs, hws, fun φ hφ hφc => tendsto_nhds_unique
      (hws φ (hφ.continuous.integrable_of_hasCompactSupport hφc)) (hTest η h1 h2 h3 φ hφ hφc)⟩
  obtain ⟨η₀, hη₀⟩ := hG.exists
  obtain ⟨s, hs, hws₀, hsT⟩ := hlimη η₀ hη₀
  -- the limit does not depend on `η`
  have hws : ∀ᵐ η ∂E.P, WeakStarTendsto (sb η) s := by
    filter_upwards [hG] with η hη
    obtain ⟨s', hs', hws', hs'T⟩ := hlimη η hη
    have heq : ∀ᵐ x ∂volume, s' x = s x := ae_eq_of_integral_testFn_eq hs' hs
      fun φ hφ hφc => (hs'T φ hφ hφc).trans (hsT φ hφ hφc).symm
    intro g hg
    have := hws' g hg
    rwa [integral_congr_ae (show (fun x => s' x * g x) =ᵐ[volume] fun x => s x * g x by
      filter_upwards [heq] with x hx; rw [hx])] at this
  -- `s ≤ 2d - 1`
  have hle : ∀ᵐ x ∂volume, s x ≤ 2 * (d : ℝ) - 1 := by
    refine hws₀.ae_le hs (fun n => measurable_rescaleSandpile _ n) (hsbB η₀ hη₀.1)
      (Eventually.of_forall fun n x => ?_)
    have hne := (hUB' η₀ (fun x => (hη₀.1 x).2) n).1
    have hst := (isLeast_freeOdometer hne).1.2 (latticeRound ((n : ℝ) • x)) (Set.mem_univ _)
    simp only [hsb, rescaleSandpile, freeSandpile]
    have : (discretize W n).indicator η₀ (latticeRound ((n : ℝ) • x)) +
        lap (freeOdometer η₀ (discretize W n)) (latticeRound ((n : ℝ) • x)) ≤
        2 * (d : ℤ) - 1 := by linarith
    exact_mod_cast this
  -- `s = 0` off `B_R(W)`
  have hzero : ∀ᵐ x ∂volume, x ∉ T → s x = 0 := hws₀.ae_eq_zero_of_compl hs hTm hη₀.2.2.2
  -- `v̄` vanishes far away
  have hvsupp : ∀ x : Rd d, (d : ℝ) * (2 * R₀ + 1) < ‖x‖ → vbar x = 0 := by
    intro x hx
    refine tendsto_nhds_unique (hη₀.2.1.tendsto_at x) (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨i, hi⟩ := exists_le_abs_latticeRound hn R₀ hx
    simp only [rescaleOdo]
    rw [(hUB' η₀ (fun x => (hη₀.1 x).2) n).2.2 _ ⟨i, hi⟩]
    simp
  -- the bump function
  obtain ⟨ρ₁, hρ₁⟩ := hTb.subset_closedBall (0 : Rd d)
  set r₀ : ℝ := (d : ℝ) * (2 * R₀ + 1) + |ρ₁| + 1 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  let φb : ContDiffBump (0 : Rd d) := ⟨r₀, r₀ + 1, hr₀pos, by linarith⟩
  have hφ1 : ∀ x : Rd d, ‖x‖ ≤ r₀ → φb x = 1 := fun x hx =>
    φb.one_of_mem_closedBall (by simpa using hx)
  have hTφb : ∀ x ∈ T, φb x = 1 := fun x hx => hφ1 x (by
    have := hρ₁ hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    have hd0 : 0 ≤ (d : ℝ) * (2 * R₀ + 1) := by positivity
    linarith [le_abs_self ρ₁, abs_nonneg ρ₁])
  have hhess : ∀ x : Rd d, vbar x * Matrix.trace (hessian φb x) = 0 := by
    intro x
    by_cases hx : ‖x‖ < r₀
    · have hev : (φb : Rd d → ℝ) =ᶠ[𝓝 x] fun _ => 1 :=
        Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds
          (show x ∈ Metric.ball (0 : Rd d) r₀ by rw [Metric.mem_ball, dist_zero_right]; exact hx))
          fun y hy => hφ1 y (by rw [Metric.mem_ball, dist_zero_right] at hy; exact hy.le)
      rw [hessian_eq_zero_of_eventuallyEq_const hev]
      simp
    · rw [hvsupp x (by linarith [abs_nonneg ρ₁, not_lt.1 hx, hr₀])]
      simp
  have hWT : W ⊆ T := Metric.self_subset_thickening hR W
  have hmass : ∫ x, s x = (volume W).toReal * meanEta E.P := by
    have h1 := hsT φb φb.contDiff φb.hasCompactSupport
    have h2 : ∫ x, s x * φb x = ∫ x, s x := by
      refine integral_congr_ae ?_
      filter_upwards [hzero] with x hx
      by_cases hxT : x ∈ T
      · rw [hTφb x hxT, mul_one]
      · rw [hx hxT, zero_mul]
    have h3 : ∫ x in W, φb x = (volume W).toReal := by
      rw [setIntegral_congr_fun hWm (fun x hx => hTφb x (hWT hx)), setIntegral_const]
      simp [Measure.real]
    simp only [hTφ, hhess, integral_zero, zero_add, h3] at h1
    rw [← h2, h1, mul_comm]
  refine ⟨s, hs, hws, hmass, hle, hzero, fun φ hφ hφc => ?_⟩
  exact hsT φ hφ hφc

/-- **Step** of Theorem 1.1 from its sub-steps. -/
theorem sandpileLimit_of_steps (hUB : FreeOdometerUpperBoundStmt)
    (hLap : FreeOdometerLapBoundStmt) (hEnv : EnvWeakStarStmt) (hRL : RescaledLapWeakStmt)
    (hRep : WeakStarRepresentationStmt) (hSupp : SandpileSupportStmt) : SandpileLimitStmt := by
  intro d hd W hW m
  obtain ⟨R, hR, hSR⟩ := hSupp d hd W hW m
  exact ⟨R, hR, fun E hHD hm vbar hvc hae =>
    sandpileLimit_core hUB hLap hEnv hRL hRep hd hW E hR (hSR E hHD hm) vbar hvc hae⟩

end RandomSandpile

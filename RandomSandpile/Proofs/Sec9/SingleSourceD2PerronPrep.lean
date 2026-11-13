import RandomSandpile.Proofs.Sec9.SingleSourceD2BarrierLe
import RandomSandpile.Proofs.Sec9.SingleSourceD2ObsCompare

/-!
# Theorem 9.2 in dimension two: ingredients of Perron's method on annuli

For SIMPLE-PROOF §7.2:
* `regOp F K ε` is continuous on all matrices, and so is the shifted operator
  `shOp F K ε κ X = F_ε(X + 2κI)` (the equation for `u - g`, `g = a + κ|x|²`), which keeps the shift
  identity and degenerate ellipticity;
* the obstacle operator `min{s + g(x), A(X)}` is proper and continuous (CIL (0.1));
* a supersolution of `F` is one of `F_ε` (`viscFromBelowGE_regOp`), and constants
  are supersolutions of `F_ε` when `F(0) ≥ 0` (`viscFromBelowGE_regOp_const`);
* `κ` is decreasing on `(0, R²]` for `m = 1` (`kap_antitone`), so `V_1 ≤ V_1(r)` outside `B_r`;
* subjets are monotone (`mem_subJet2_of_le`); continuous barriers vanishing on the boundary satisfy
  the envelope conditions of CIL Theorem 4.1 (`envelopes_of_continuousWithinAt`);
* the annulus `{r < |x| < L}`, its closure and its frontier.
-/

noncomputable section

open Filter Topology Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

open CrandallIshiiLions

/-! ### Operators -/

theorem continuous_traceFreeCoord :
    Continuous (traceFreeCoord : Matrix (Fin 2) (Fin 2) ℝ → Rd 2) := by
  unfold traceFreeCoord
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · show Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0 - M 1 1
    fun_prop
  · show Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => 2 * M 0 1
    fun_prop

theorem continuous_regOp {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    (hdeg : DegenerateElliptic F) (K ε : ℝ) : Continuous (regOp F K ε) := by
  have hL : LipschitzWith 1 (traceGraph F) := LipschitzWith.of_dist_le_mul fun z z' => by
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    exact traceGraph_lipschitz hF hdeg z z'
  show Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ =>
    (1 - ε) * traceGraph F (traceFreeCoord M) + ε * (K + 1) - M.trace
  exact ((continuous_const.mul (hL.continuous.comp continuous_traceFreeCoord)).add
    continuous_const).sub continuous_id.matrix_trace

/-- The shifted operator `F_ε(X + 2κI)`. -/
def shOp (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (K ε κ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  regOp F K ε (X + (2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))

theorem shOp_hasTraceShift (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (K ε κ : ℝ) :
    HasTraceShift (shOp F K ε κ) := by
  intro M hM t
  show regOp F K ε (M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (2 * κ) • 1) =
    regOp F K ε (M + (2 * κ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) - 2 * t
  rw [add_right_comm]
  exact regOp_hasTraceShift F K ε _ (hM.add (Matrix.isSymm_one.smul _)) t

theorem shOp_degenerateElliptic {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    (hdeg : DegenerateElliptic F) (K : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (κ : ℝ) :
    DegenerateElliptic (shOp F K ε κ) := by
  intro X Y hX hY hXY
  exact regOp_degenerateElliptic hF hdeg K hε0 hε1 _ _ (hX.add (Matrix.isSymm_one.smul _))
    (hY.add (Matrix.isSymm_one.smul _)) (by rwa [add_sub_add_right_eq_sub])

theorem continuous_shOp {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    (hdeg : DegenerateElliptic F) (K ε κ : ℝ) : Continuous (shOp F K ε κ) :=
  (continuous_regOp hF hdeg K ε).comp (continuous_id.add continuous_const)

theorem isProper_obsOp {g : Rd 2 → ℝ} {A : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hA : DegenerateElliptic A) : IsProper (obsOp g A) := by
  intro x r s p X Y hX hY hrs hXY
  show min (r + g x) (A X) ≤ min (s + g x) (A Y)
  exact min_le_min (by linarith) (hA Y X hY hX hXY)

theorem continuous_obsOp {g : Rd 2 → ℝ} (hg : Continuous g) {A : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hA : Continuous A) :
    Continuous (fun w : Rd 2 × ℝ × Rd 2 × Matrix (Fin 2) (Fin 2) ℝ =>
      obsOp g A w.1 w.2.1 w.2.2.1 w.2.2.2) := by
  show Continuous fun w : Rd 2 × ℝ × Rd 2 × Matrix (Fin 2) (Fin 2) ℝ =>
    min (w.2.1 + g w.1) (A w.2.2.2)
  exact (continuous_snd.fst.add (hg.comp continuous_fst)).min (hA.comp continuous_snd.snd.snd)

/-! ### Supersolutions of `F_ε` -/

/-- A supersolution of `F` is a supersolution of `F_ε`. -/
theorem viscFromBelowGE_regOp {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    {K ε : ℝ} (hε0 : 0 ≤ ε) (hTr : ∀ z, traceGraph F z ≤ K) {V : Set (Rd 2)} {u : Rd 2 → ℝ}
    (hu : ViscFromBelowGE F V u) : ViscFromBelowGE (regOp F K ε) V u := by
  intro x hx φ hφ hmin
  have h := hu x hx φ hφ hmin
  rw [eq_traceGraph_sub_trace hF (hessian_isSymm_of_contDiffAt hφ)] at h
  have hf := hTr (traceFreeCoord (hessian φ x))
  have hp := mul_nonneg hε0
    (by linarith : (0 : ℝ) ≤ K + 1 - traceGraph F (traceFreeCoord (hessian φ x)))
  show 0 ≤ (1 - ε) * traceGraph F (traceFreeCoord (hessian φ x)) + ε * (K + 1) -
    (hessian φ x).trace
  linarith

/-- At a local maximum of a `C²` function, `-D²φ` is positive semidefinite. -/
theorem posSemidef_neg_hessian_of_isLocalMax {φ : Rd 2 → ℝ} {x : Rd 2}
    (hφ : ContDiffAt ℝ 2 φ x) (hmax : IsLocalMax φ x) : (0 - hessian φ x).PosSemidef := by
  have hq : ∀ h : Rd 2, qM (hessian φ x) h ≤ 0 := by
    intro h
    have hm : IsLocalMax (fun y => (0 + inner ℝ (0 : Rd 2) (y - x) +
        qM (0 : Matrix (Fin 2) (Fin 2) ℝ) (y - x)) - -φ y) x := by
      filter_upwards [hmax] with y hy
      simpa [qM] using hy
    have h1 := qM_le_hessian_of_isLocalMax hφ.neg 0 0 x 0 hm h
    rw [hessian_neg', qM_neg_mat] at h1
    have h0 : qM (0 : Matrix (Fin 2) (Fin 2) ℝ) h = 0 := by simp [qM]
    linarith
  refine posSemidef_of_bilin_le (hessian_isSymm_of_contDiffAt hφ) Matrix.isSymm_zero
    fun ξ => ?_
  have h1 := hq ξ
  rw [qM_eq_matrixBilin] at h1
  have h0 : matrixBilin (0 : Matrix (Fin 2) (Fin 2) ℝ) ξ ξ = 0 := by simp [matrixBilin_apply]
  linarith

/-- Constants are supersolutions of `F_ε` when `F(0) ≥ 0`. -/
theorem viscFromBelowGE_regOp_const {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    (hdeg : DegenerateElliptic F) {K ε : ℝ} (hK : 1 ≤ K) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hF0 : 0 ≤ F 0) (V : Set (Rd 2)) (k : ℝ) :
    ViscFromBelowGE (regOp F K ε) V (fun _ => k) := by
  intro x _ φ hφ hmin
  have hmax : IsLocalMax φ x := by
    filter_upwards [hmin] with y hy
    have hy' : k - φ x ≤ k - φ y := hy
    linarith
  have h1 := regOp_degenerateElliptic hF hdeg K hε0 hε1 (hessian φ x) 0
    (hessian_isSymm_of_contDiffAt hφ) Matrix.isSymm_zero
    (posSemidef_neg_hessian_of_isLocalMax hφ hmax)
  have he := eq_traceGraph_sub_trace hF (Matrix.isSymm_zero (n := Fin 2) (α := ℝ))
  rw [Matrix.trace_zero, sub_zero] at he
  have h0 : 0 ≤ regOp F K ε 0 := by
    simp only [regOp, Matrix.trace_zero, sub_zero]
    rw [← he]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) hF0,
      mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ K + 1)]
  linarith

/-! ### Monotonicity of the profile -/

/-- `κ` (mass `1`) is decreasing on `(0, R²]`. -/
theorem kap_antitone {c : ℝ} (hc : 0 < c) {s t : ℝ} (ht : 0 < t) (hts : t ≤ s)
    (hs : s ≤ rad2 c 1) : kap c 1 s ≤ kap c 1 t := by
  have hR := rad2_pos hc one_pos
  have hs0 : 0 < s := lt_of_lt_of_le ht hts
  have hπ := Real.pi_pos
  have hlog : Real.log (t / s) ≤ t / s - 1 := Real.log_le_sub_one_of_pos (div_pos ht hs0)
  have hsplit : Real.log (s / rad2 c 1) = Real.log (t / rad2 c 1) + -Real.log (t / s) := by
    rw [Real.log_div hs0.ne' hR.ne', Real.log_div ht.ne' hR.ne', Real.log_div ht.ne' hs0.ne']
    ring
  have hcs : Real.pi * c * s ≤ 1 := by
    have h := hs
    unfold rad2 at h
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have h1 : (s - t) / s = 1 - t / s := by rw [sub_div, div_self hs0.ne']
  have h2 : Real.pi * c * (s - t) ≤ (s - t) / s := by
    rw [le_div_iff₀ hs0]
    nlinarith [mul_nonneg (sub_nonneg.2 hts) (by linarith : 0 ≤ 1 - Real.pi * c * s)]
  have h3 : Real.pi * c * (s - t) ≤ -Real.log (t / s) := by linarith
  have h4 : 1 / (4 * Real.pi) * (Real.pi * c * (s - t)) = c / 4 * (s - t) := by
    field_simp
  have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.pi))
  unfold kap
  rw [hsplit]
  nlinarith

/-! ### Jets and envelopes -/

/-- Subjets are monotone: if `f ≤ h` with equality at `x`, a subjet of `f` is one of `h`. -/
theorem mem_subJet2_of_le {O : Set (Rd 2)} {f h : Rd 2 → ℝ} {x : Rd 2} (hle : ∀ y, f y ≤ h y)
    (heq : f x = h x) {pX : Rd 2 × Matrix (Fin 2) (Fin 2) ℝ} (hj : pX ∈ subJet2 O f x) :
    pX ∈ subJet2 O h x := by
  simp only [subJet2, Set.mem_ofPred_eq] at hj ⊢
  refine ⟨hj.1, fun ε hε => ?_⟩
  filter_upwards [hj.2 ε hε] with y hy
  rw [← heq]
  linarith [hle y]

/-- A function continuous on `Ω̄` and vanishing at a boundary point has both semicontinuous
envelopes zero there (the boundary condition of CIL Theorem 4.1). -/
theorem envelopes_of_continuousWithinAt {Ω : Set (Rd 2)} {f : Rd 2 → ℝ} {x : Rd 2}
    (hx : x ∈ closure Ω) (hf : ContinuousWithinAt f (closure Ω) x) (h0 : f x = 0) :
    LowerEnvelopeZeroAt Ω f x ∧ UpperEnvelopeZeroAt Ω f x := by
  have hne : (𝓝[closure Ω] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hx)
  have hT : Tendsto f (𝓝[closure Ω] x) (𝓝 0) := by
    rw [← h0]
    exact hf.tendsto
  have hlo : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝[closure Ω] x, -ε < f y := fun ε hε =>
    hT.eventually (lt_mem_nhds (by linarith))
  have hhi : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝[closure Ω] x, f y < ε := fun ε hε =>
    hT.eventually (gt_mem_nhds hε)
  refine ⟨?_, ?_⟩
  · exact And.intro hlo fun ε hε => (hhi ε hε).frequently
  · exact And.intro hhi fun ε hε => (hlo ε hε).frequently

/-! ### The annulus -/

/-- The annulus `{r < |x| < L}`. -/
def annSet (r L : ℝ) : Set (Rd 2) := {x | r < ‖x‖ ∧ ‖x‖ < L}

theorem isOpen_annSet (r L : ℝ) : IsOpen (annSet r L) := isOpen_annulus r L

theorem isBounded_annSet (r L : ℝ) : Bornology.IsBounded (annSet r L) :=
  (isBounded_closedBall (x := (0 : Rd 2)) (r := L)).subset fun _ hx => by
    rw [mem_closedBall, dist_zero_right]
    exact hx.2.le

theorem closure_annSet_subset (r L : ℝ) :
    closure (annSet r L) ⊆ {x : Rd 2 | r ≤ ‖x‖ ∧ ‖x‖ ≤ L} :=
  closure_minimal (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))

theorem norm_of_mem_frontier_annSet {r L : ℝ} {x : Rd 2} (hx : x ∈ frontier (annSet r L)) :
    ‖x‖ = r ∨ ‖x‖ = L := by
  rw [(isOpen_annSet r L).frontier_eq] at hx
  obtain ⟨h1, h2⟩ := hx
  have h3 := closure_annSet_subset r L h1
  by_cases ha : ‖x‖ = r
  · exact Or.inl ha
  · by_cases hb : ‖x‖ = L
    · exact Or.inr hb
    · exact absurd ⟨lt_of_le_of_ne h3.1 (Ne.symm ha), lt_of_le_of_ne h3.2 hb⟩ h2

theorem ne_zero_of_mem_closure_annSet {r L : ℝ} (hr : 0 < r) {x : Rd 2}
    (hx : x ∈ closure (annSet r L)) : x ≠ 0 := by
  intro h
  have h1 := (closure_annSet_subset r L hx).1
  rw [h, norm_zero] at h1
  linarith

end SingleSourceD2

end RandomSandpile

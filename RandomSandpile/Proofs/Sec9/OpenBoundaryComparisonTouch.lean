import RandomSandpile.Infra.SupConvolution
import RandomSandpile.Infra.Touching

/-! # Comparison principle (Theorem 9.1): touching by paraboloids

Elementary tools for the Jensen proof of `ShiftComparisonStmt`. The proof only tests with
paraboloids `z ↦ f(x) + p·(z - x) + q_X(z - x)`.
* `TouchAbove f x X`: such a paraboloid touches `f` from above at `x` (a local maximum of the
  difference);
* `le_zero_of_touch`, `nonneg_of_touch_neg`: the viscosity inequalities for paraboloids;
* `touch_of_taylor`: a second-order Peano expansion with matrix `X` gives touching with `X + ηI`;
* `touch_supConv`: touching passes from a sup-convolution `f^δ` at `x` to `f` at the maximizer;
* `qM_nonpos_of_isLocalMax`: the second-order condition at a local maximum;
* Taylor expansions of sums and of `c|x|²`, `posSemidef_of_qM_nonneg`.
-/

noncomputable section

open Filter Topology Asymptotics Metric

namespace RandomSandpile

namespace OpenComparison

variable {d : ℕ}

/-- A paraboloid with matrix `X` touches `f` from above at `x`. -/
def TouchAbove (f : Rd d → ℝ) (x : Rd d) (X : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ p : Rd d, IsLocalMax (fun z => f z - (f x + innerSL ℝ p (z - x) + qM X (z - x))) x

theorem qM_zero' (M : Matrix (Fin d) (Fin d) ℝ) : qM M (0 : Rd d) = 0 := by simp [qM]

theorem qM_add' (A B : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) :
    qM (A + B) x = qM A x + qM B x := by
  simp only [qM, Matrix.add_mulVec, dotProduct_add]; ring

theorem qM_neg' (A : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) : qM (-A) x = -qM A x := by
  simp only [qM, Matrix.neg_mulVec, dotProduct_neg]; ring

theorem qM_smul_one' (c : ℝ) (x : Rd d) :
    qM (c • (1 : Matrix (Fin d) (Fin d) ℝ)) x = c / 2 * ‖x‖ ^ 2 := by
  have h := qM_add_smul_one (0 : Matrix (Fin d) (Fin d) ℝ) c x
  rw [zero_add] at h
  rw [h]; simp [qM]

/-- Viscosity subsolution inequality for a touching paraboloid. -/
theorem le_zero_of_touch {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U : Set (Rd d)} {u : Rd d → ℝ}
    (hu : ViscFromAboveLE F U u) {x : Rd d} (hx : x ∈ U) {X : Matrix (Fin d) (Fin d) ℝ}
    (hX : X.IsSymm) (ht : TouchAbove u x X) : F X ≤ 0 := by
  obtain ⟨p, hp⟩ := ht
  have h := hu x hx _ (contDiff_paraboloid (u x) p x X).contDiffAt hp
  rwa [hessian_paraboloid, hessian_qM_of_isSymm hX] at h

/-- Viscosity supersolution inequality: a paraboloid with matrix `X` touching `-w` from above is
`-` a paraboloid with matrix `-X` touching `w` from below. -/
theorem nonneg_of_touch_neg {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U : Set (Rd d)} {w : Rd d → ℝ}
    (hw : ViscFromBelowGE F U w) {x : Rd d} (hx : x ∈ U) {X : Matrix (Fin d) (Fin d) ℝ}
    (hX : X.IsSymm) (ht : TouchAbove (fun z => -w z) x X) : 0 ≤ F (-X) := by
  obtain ⟨p, hp⟩ := ht
  have hmin : IsLocalMin
      (fun z => w z - (w x + innerSL ℝ (-p) (z - x) + qM (-X) (z - x))) x := by
    have h := hp.neg
    have heq : (fun z => -((fun z => -w z) z - ((fun z => -w z) x + innerSL ℝ p (z - x) +
        qM X (z - x)))) = fun z => w z - (w x + innerSL ℝ (-p) (z - x) + qM (-X) (z - x)) := by
      funext z
      simp only [innerSL_apply_apply, inner_neg_left, qM_neg']
      ring
    rw [← heq]; exact h
  have h := hw x hx _ (contDiff_paraboloid (w x) (-p) x (-X)).contDiffAt hmin
  rwa [hessian_paraboloid, hessian_qM_of_isSymm hX.neg] at h

/-- A second-order Peano expansion with matrix `X` gives a touching paraboloid with `X + ηI`. -/
theorem touch_of_taylor {f : Rd d → ℝ} {x p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ}
    (hf : HasSecondOrderTaylorAt f x p X) {η : ℝ} (hη : 0 < η) :
    TouchAbove f x (X + η • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  refine ⟨p, ?_⟩
  have hb := hf.bound (half_pos hη)
  filter_upwards [hb] with z hz
  simp only [sub_self, innerSL_apply_apply, inner_zero_right, qM_zero', add_zero]
  rw [qM_add_smul_one]
  rw [Real.norm_eq_abs, norm_pow, norm_norm] at hz
  have h1 := (abs_le.1 hz).2
  have h2 : 0 ≤ ‖z - x‖ ^ 2 := sq_nonneg _
  nlinarith

/-- **Touching passes to the maximizer of a sup-convolution.** -/
theorem touch_supConv {S U : Set (Rd d)} (hS : IsCompact S) (hU : IsOpen U) (hUS : U ⊆ S)
    {δ : ℝ} {f : Rd d → ℝ} (hf : ContinuousOn f S) {x y : Rd d} (hyU : y ∈ U)
    (hy : supConv S δ f x = f y - ‖x - y‖ ^ 2 / (2 * δ)) {X : Matrix (Fin d) (Fin d) ℝ}
    (ht : TouchAbove (supConv S δ f) x X) : TouchAbove f y X := by
  obtain ⟨p, hp⟩ := ht
  refine ⟨p, ?_⟩
  have hxy : y + (x - y) = x := by abel
  have hT : Tendsto (fun z => z + (x - y)) (𝓝 y) (𝓝 x) := by
    have : Continuous (fun z : Rd d => z + (x - y)) := by fun_prop
    simpa [hxy] using this.tendsto y
  filter_upwards [hT.eventually hp, hU.mem_nhds hyU] with z h1 h2
  have hb := (supConv_spec hS ⟨y, hUS hyU⟩ δ hf (z + (x - y))).1 z (hUS h2)
  have he : z + (x - y) - z = x - y := by abel
  have he2 : z + (x - y) - x = z - y := by abel
  rw [he] at hb
  simp only [he2, sub_self, innerSL_apply_apply, inner_zero_right, qM_zero', add_zero] at h1 ⊢
  linarith

theorem taylor_add {f g : Rd d → ℝ} {x p q : Rd d} {X Y : Matrix (Fin d) (Fin d) ℝ}
    (hf : HasSecondOrderTaylorAt f x p X) (hg : HasSecondOrderTaylorAt g x q Y) :
    HasSecondOrderTaylorAt (fun z => f z + g z) x (p + q) (X + Y) := by
  unfold HasSecondOrderTaylorAt at *
  refine (hf.add hg).congr_left fun z => ?_
  simp only [inner_add_left, qM_add']
  ring

/-- `c |z|²` has the exact expansion with gradient `2c x` and matrix `2c I`. -/
theorem taylor_sq (c : ℝ) (x : Rd d) :
    HasSecondOrderTaylorAt (fun z => c * ‖z‖ ^ 2) x ((2 * c) • x)
      ((2 * c) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  unfold HasSecondOrderTaylorAt
  have h0 : (fun z : Rd d => c * ‖z‖ ^ 2 - c * ‖x‖ ^ 2 - inner ℝ ((2 * c) • x) (z - x) -
      qM ((2 * c) • (1 : Matrix (Fin d) (Fin d) ℝ)) (z - x)) = fun _ => 0 := by
    funext z
    rw [qM_smul_one', real_inner_smul_left]
    have : ‖z‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (z - x) + ‖z - x‖ ^ 2 := by
      have h := norm_add_sq_real x (z - x)
      rw [add_sub_cancel] at h
      exact h
    rw [this]; ring
  rw [h0]
  exact isLittleO_zero _ _

theorem taylor_congr {f g : Rd d → ℝ} {x p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ}
    (hf : HasSecondOrderTaylorAt f x p X) (hfg : ∀ z, f z = g z) :
    HasSecondOrderTaylorAt g x p X := by
  have : f = g := funext hfg
  rwa [← this]

/-- **Second-order condition** at a local maximum of `Z - p·(·)`. -/
theorem qM_nonpos_of_isLocalMax {Z : Rd d → ℝ} {x P p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ}
    (hT : HasSecondOrderTaylorAt Z x P X) (hmax : IsLocalMax (fun y => Z y - inner ℝ p y) x)
    (h : Rd d) : qM X h ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  set a := qM X h with ha
  have hh : h ≠ 0 := by
    rintro rfl; rw [qM_zero'] at ha; linarith
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  obtain ⟨r₁, hr₁, H₁⟩ := Metric.eventually_nhds_iff.1 hmax
  obtain ⟨r₂, hr₂, H₂⟩ := Metric.eventually_nhds_iff.1
    (hT.bound (show 0 < a / (2 * ‖h‖ ^ 2) by positivity))
  set t := min r₁ r₂ / (2 * (‖h‖ + 1)) with ht
  have ht0 : 0 < t := by positivity
  have hdist : ∀ s : ℝ, |s| = t → dist (x + s • h) x < min r₁ r₂ := by
    intro s hs
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hs, ht]
    have hm : 0 < min r₁ r₂ := lt_min hr₁ hr₂
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have key : ∀ s : ℝ, |s| = t →
      Z (x + s • h) ≤ Z x + inner ℝ p (s • h) ∧
        Z x + s * inner ℝ P h + s ^ 2 * a - a / 2 * s ^ 2 ≤ Z (x + s • h) := by
    intro s hs
    have hd := hdist s hs
    have h1 := H₁ (lt_of_lt_of_le hd (min_le_left _ _))
    have h2 := H₂ (lt_of_lt_of_le hd (min_le_right _ _))
    simp only at h1
    rw [inner_add_right] at h1
    refine ⟨by linarith, ?_⟩
    rw [add_sub_cancel_left, Real.norm_eq_abs, norm_pow, norm_norm, norm_smul, Real.norm_eq_abs,
      qM_smul, real_inner_smul_right, mul_pow, sq_abs] at h2
    have h3 := (abs_le.1 h2).1
    have h4 : a / (2 * ‖h‖ ^ 2) * (s ^ 2 * ‖h‖ ^ 2) = a / 2 * s ^ 2 := by
      field_simp
    rw [h4] at h3
    linarith
  obtain ⟨hp1, hq1⟩ := key t (abs_of_pos ht0)
  obtain ⟨hp2, hq2⟩ := key (-t) (by rw [abs_neg, abs_of_pos ht0])
  rw [real_inner_smul_right] at hp1 hp2
  have : 0 < t ^ 2 * a := by positivity
  nlinarith

/-- A symmetric matrix with nonnegative quadratic form is positive semidefinite. -/
theorem posSemidef_of_qM_nonneg' {N : Matrix (Fin d) (Fin d) ℝ} (hN : N.IsSymm)
    (h : ∀ v : Rd d, 0 ≤ qM N v) : N.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨Matrix.isHermitian_iff_isSymm.2 hN,
    fun x => ?_⟩
  have := h (WithLp.toLp 2 x)
  simp only [qM] at this
  rw [star_trivial]
  linarith

end OpenComparison

end RandomSandpile

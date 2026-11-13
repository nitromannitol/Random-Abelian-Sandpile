import RandomSandpile.Defs.Viscosity
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Sup-convolutions (Jensen; Crandall-Ishii-Lions, *User's guide*, §5)

For `S ⊆ ℝ^d` compact, `u ∈ C(S)` and `ε > 0`, the sup-convolution
`u^ε(x) = sup_{y ∈ S} (u(y) - |x - y|²/(2ε))` (`supConv S ε u`) is defined on all of `ℝ^d`.

* `supConv_spec`: the supremum is attained at some `ŷ ∈ S`, and bounds every competitor;
* `le_supConv`: `u ≤ u^ε` on `S`;
* `convexOn_supConv_add`: `u^ε + |x|²/(2ε)` is convex on `ℝ^d` (semiconvexity), so
  Alexandrov's theorem applies to it;
* `ViscFromAboveGE.supConv_at`: if `u` is a viscosity subsolution of `-Δu - K = 0` in the open
  set `U ⊆ S` (Crandall-Ishii-Lions), so is `u^ε` at every `x` whose maximizer `ŷ` lies in `U`
  (test functions are translated by `x - ŷ`);
* `trace_add_nonneg_of_taylor`: at a point where a function with that pointwise viscosity property
  has a second-order Peano expansion with symmetric matrix `X`, `tr X + K ≥ 0`.

Inf-convolutions are `-(-v)^ε`.
-/

noncomputable section

open Filter Topology Asymptotics

namespace RandomSandpile

variable {d : ℕ}

/-- The sup-convolution `u^ε(x) = sup_{y ∈ S} (u(y) - |x - y|²/(2ε))`. -/
def supConv (S : Set (Rd d)) (ε : ℝ) (u : Rd d → ℝ) (x : Rd d) : ℝ :=
  ⨆ y : S, (u y - ‖x - y‖ ^ 2 / (2 * ε))

/-- The sup in `supConv` is attained, and bounds every competitor (`S` compact, nonempty). -/
theorem supConv_spec {S : Set (Rd d)} (hS : IsCompact S) (hne : S.Nonempty) (ε : ℝ)
    {u : Rd d → ℝ} (hu : ContinuousOn u S) (x : Rd d) :
    (∀ y ∈ S, u y - ‖x - y‖ ^ 2 / (2 * ε) ≤ supConv S ε u x) ∧
      ∃ y ∈ S, supConv S ε u x = u y - ‖x - y‖ ^ 2 / (2 * ε) := by
  have hg : ContinuousOn (fun y => u y - ‖x - y‖ ^ 2 / (2 * ε)) S :=
    hu.sub ((continuous_const.sub continuous_id).norm.pow 2 |>.div_const _).continuousOn
  obtain ⟨y₀, hy₀, hmax⟩ := hS.exists_isMaxOn hne hg
  have hbdd : BddAbove (Set.range fun y : S => u y - ‖x - y‖ ^ 2 / (2 * ε)) :=
    ⟨u y₀ - ‖x - y₀‖ ^ 2 / (2 * ε), by rintro _ ⟨y, rfl⟩; exact hmax y.2⟩
  have hle : ∀ y ∈ S, u y - ‖x - y‖ ^ 2 / (2 * ε) ≤ supConv S ε u x := fun y hy =>
    le_ciSup hbdd (⟨y, hy⟩ : S)
  refine ⟨hle, y₀, hy₀, le_antisymm ?_ (hle y₀ hy₀)⟩
  have : Nonempty S := ⟨⟨y₀, hy₀⟩⟩
  exact ciSup_le fun y => hmax y.2

/-- `u ≤ u^ε` on `S`. -/
theorem le_supConv {S : Set (Rd d)} (hS : IsCompact S) {ε : ℝ} {u : Rd d → ℝ}
    (hu : ContinuousOn u S) {x : Rd d} (hx : x ∈ S) : u x ≤ supConv S ε u x := by
  have := (supConv_spec hS ⟨x, hx⟩ ε hu x).1 x hx
  simpa using this

/-- **Semiconvexity**: `u^ε + |x|²/(2ε)` is convex on `ℝ^d` (a supremum of affine functions). -/
theorem convexOn_supConv_add {S : Set (Rd d)} (hS : IsCompact S) (hne : S.Nonempty) {ε : ℝ}
    (hε : 0 < ε) {u : Rd d → ℝ} (hu : ContinuousOn u S) :
    ConvexOn ℝ Set.univ (fun x => supConv S ε u x + ‖x‖ ^ 2 / (2 * ε)) := by
  have hid : ∀ x w : Rd d, u w - ‖x - w‖ ^ 2 / (2 * ε) + ‖x‖ ^ 2 / (2 * ε) =
      (u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ x w / ε := by
    intro x w
    rw [norm_sub_sq_real]
    field_simp
    ring
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨hle, w, hw, hzw⟩ := supConv_spec hS hne ε hu (a • x + b • y)
  have hx := (supConv_spec hS hne ε hu x).1 w hw
  have hy := (supConv_spec hS hne ε hu y).1 w hw
  have hx' : (u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ x w / ε ≤
      supConv S ε u x + ‖x‖ ^ 2 / (2 * ε) := by rw [← hid]; linarith
  have hy' : (u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ y w / ε ≤
      supConv S ε u y + ‖y‖ ^ 2 / (2 * ε) := by rw [← hid]; linarith
  have hz : supConv S ε u (a • x + b • y) + ‖a • x + b • y‖ ^ 2 / (2 * ε) =
      (u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ (a • x + b • y) w / ε := by rw [hzw, hid]
  simp only [smul_eq_mul]
  rw [hz, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h1 := mul_le_mul_of_nonneg_left hx' ha
  have h2 := mul_le_mul_of_nonneg_left hy' hb
  have e : (u w - ‖w‖ ^ 2 / (2 * ε)) + (a * inner ℝ x w + b * inner ℝ y w) / ε =
      a * ((u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ x w / ε) +
        b * ((u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ y w / ε) := by
    rw [show a * ((u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ x w / ε) +
        b * ((u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ y w / ε) =
        (a + b) * (u w - ‖w‖ ^ 2 / (2 * ε)) + (a * inner ℝ x w + b * inner ℝ y w) / ε by ring,
      hab, one_mul]
  rw [e]
  linarith

/-! ### Hessians of translates and of paraboloids -/

theorem fderiv_comp_add_right_funext (φ : Rd d → ℝ) (c : Rd d) :
    fderiv ℝ (fun z => φ (z + c)) = fun z => fderiv ℝ φ (z + c) :=
  funext fun _ => fderiv_comp_add_right (f := φ) c

/-- The Hessian of a translate is the translated Hessian. -/
theorem hessian_comp_add_right (φ : Rd d → ℝ) (c y : Rd d) :
    hessian (fun z => φ (z + c)) y = hessian φ (y + c) := by
  ext i j
  simp only [hessian_apply, fderiv_comp_add_right_funext]
  rw [fderiv_comp_add_right (f := fderiv ℝ φ) c]

theorem ContDiffAt.comp_add_right' {φ : Rd d → ℝ} {c y : Rd d} {n : WithTop ℕ∞}
    (hφ : ContDiffAt ℝ n φ (y + c)) : ContDiffAt ℝ n (fun z => φ (z + c)) y :=
  hφ.comp y (contDiffAt_id.add contDiffAt_const)

/-- The paraboloid `z ↦ c + p·(z - x) + q_M(z - x)` has the Hessian of `q_M`. -/
theorem hessian_paraboloid (c : ℝ) (p x : Rd d) (M : Matrix (Fin d) (Fin d) ℝ) (y : Rd d) :
    hessian (fun z => c + innerSL ℝ p (z - x) + qM M (z - x)) y = hessian (qM M) y := by
  have h1 : fderiv ℝ (fun z => c + innerSL ℝ p (z - x) + qM M (z - x)) =
      fun z => innerSL ℝ p + qMDeriv M (z - x) := by
    funext z
    have hsub : HasFDerivAt (fun z : Rd d => z - x) (ContinuousLinearMap.id ℝ (Rd d)) z :=
      (hasFDerivAt_id z).sub_const x
    have := ((hasFDerivAt_const c z).add ((innerSL ℝ p).hasFDerivAt.comp z hsub)).add
      ((hasFDerivAt_qM M (z - x)).comp z hsub)
    exact (this.congr_fderiv (by ext; simp)).fderiv
  have h2 : fderiv ℝ (fun z => innerSL ℝ p + qMDeriv M (z - x)) y = qMDeriv M := by
    have hsub : HasFDerivAt (fun z : Rd d => z - x) (ContinuousLinearMap.id ℝ (Rd d)) y :=
      (hasFDerivAt_id y).sub_const x
    have := (hasFDerivAt_const (innerSL ℝ p) y).add ((qMDeriv M).hasFDerivAt.comp y hsub)
    exact (this.congr_fderiv (by ext; simp)).fderiv
  have h3 : fderiv ℝ (fderiv ℝ (qM M)) y = qMDeriv M := by
    rw [fderiv_qM]; exact (qMDeriv M).fderiv
  ext i j
  rw [hessian_apply, hessian_apply, h1, h2, h3]

theorem contDiff_paraboloid (c : ℝ) (p x : Rd d) (M : Matrix (Fin d) (Fin d) ℝ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (fun z => c + innerSL ℝ p (z - x) + qM M (z - x)) :=
  (contDiff_const.add ((innerSL ℝ p).contDiff.comp (contDiff_id.sub contDiff_const))).add
    ((contDiff_qM M).comp (contDiff_id.sub contDiff_const))

theorem qM_add_smul_one (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (h : Rd d) :
    qM (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) h = qM M h + t / 2 * ‖h‖ ^ 2 := by
  have hn : ‖h‖ ^ 2 = WithLp.ofLp h ⬝ᵥ WithLp.ofLp h := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  rw [hn]
  simp only [qM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  ring

/-! ### Viscosity inequalities at points of second-order expansion -/

/-- If every `C²` function touching `f` from above at `x` has `tr D²φ(x) + K ≥ 0` and `f` has a
second-order Peano expansion at `x` with symmetric matrix `X`, then `tr X + K ≥ 0`. -/
theorem trace_add_nonneg_of_taylor {f : Rd d → ℝ} {x p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ}
    {K : ℝ} (hX : X.IsSymm) (hT : HasSecondOrderTaylorAt f x p X)
    (hv : ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMax (fun z => f z - φ z) x →
      0 ≤ (hessian φ x).trace + K) :
    0 ≤ X.trace + K := by
  have key : ∀ η > 0, 0 ≤ X.trace + K + 2 * η * d := by
    intro η hη
    set M := X + (2 * η) • (1 : Matrix (Fin d) (Fin d) ℝ) with hM
    have hMs : M.IsSymm := hX.add (Matrix.isSymm_one.smul _)
    set φ : Rd d → ℝ := fun z => f x + innerSL ℝ p (z - x) + qM M (z - x) with hφ
    have hmax : IsLocalMax (fun z => f z - φ z) x := by
      filter_upwards [hT.def hη] with z hz
      have hq : qM M (z - x) = qM X (z - x) + 2 * η / 2 * ‖z - x‖ ^ 2 :=
        qM_add_smul_one X (2 * η) (z - x)
      have h0 : qM M 0 = 0 := by simp [qM]
      simp only [hφ, innerSL_apply_apply, sub_self, inner_zero_right, add_zero] at hz ⊢
      try rw [h0]
      rw [hq]
      rw [Real.norm_eq_abs, abs_le] at hz
      simp only [norm_pow, norm_norm] at hz
      nlinarith [hz.2]
    have h := hv φ (contDiff_paraboloid _ _ _ _).contDiffAt hmax
    rw [hφ, hessian_paraboloid, hessian_qM_of_isSymm hMs, hM, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_one] at h
    simp only [Fintype.card_fin, smul_eq_mul] at h
    linarith
  by_contra hneg
  push Not at hneg
  have := key (-(X.trace + K) / (4 * (d + 1))) (by
    apply div_pos (by linarith); positivity)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : 2 * (-(X.trace + K) / (4 * (d + 1))) * d < -(X.trace + K) := by
    rw [mul_div_assoc', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Sup-convolution keeps viscosity subsolutions** of `-Δu - K = 0` (Crandall-Ishii-Lions),
at every `x` whose maximizer `ŷ` lies in the open set `U ⊆ S` where `u` is a subsolution: a test
function touching `u^ε` from above at `x`, translated by `ŷ - x`, touches `u` from above at `ŷ`. -/
theorem ViscFromAboveGE.supConv_at {S U : Set (Rd d)} (hS : IsCompact S) (hU : IsOpen U)
    (hUS : U ⊆ S) {ε K : ℝ} {u : Rd d → ℝ} (hu : ContinuousOn u S)
    (hvisc : ViscFromAboveGE (fun X => X.trace + K) U u) {x y : Rd d} (hyU : y ∈ U)
    (hy : supConv S ε u x = u y - ‖x - y‖ ^ 2 / (2 * ε)) (φ : Rd d → ℝ)
    (hφ : ContDiffAt ℝ 2 φ x) (hmax : IsLocalMax (fun z => supConv S ε u z - φ z) x) :
    0 ≤ (hessian φ x).trace + K := by
  have hxy : y + (x - y) = x := by abel
  have hψ : ContDiffAt ℝ 2 (fun z => φ (z + (x - y))) y := by
    apply ContDiffAt.comp_add_right'; rw [hxy]; exact hφ
  have hT : Tendsto (fun z => z + (x - y)) (𝓝 y) (𝓝 x) := by
    have : Continuous (fun z : Rd d => z + (x - y)) := by fun_prop
    simpa [hxy] using this.tendsto y
  have hloc : IsLocalMax (fun z => u z - φ (z + (x - y))) y := by
    filter_upwards [hT.eventually hmax, hU.mem_nhds hyU] with z h1 h2
    have hb := (supConv_spec hS ⟨y, hUS hyU⟩ ε hu (z + (x - y))).1 z (hUS h2)
    have he : z + (x - y) - z = x - y := by abel
    rw [he] at hb
    simp only [hxy] at h1 ⊢
    linarith
  have h := hvisc y hyU _ hψ hloc
  simpa [hessian_comp_add_right, hxy] using h

end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceD2Super
import RandomSandpile.Proofs.Sec7.PegdenSmartAdapter

/-!
# Pegden-Smart Proposition 2.5 on a ball, paraboloid form

`ps25Paraboloid_of_ps25 : PegdenSmartProp25Stmt → PS25ParaboloidStmt`. Given `u` with bounded weak
Laplacian on `B_r(a)` and a paraboloid `P` touching `u` at `a` and strictly below it on `∂B_r(a)`,
Pegden-Smart Proposition 2.5 applied to `H(y) = (P - u)(a + r y)` on `B_1` gives a positive-measure set of
Peano points of `u` with Hessian `> D²P`.

Ingredients (proved here):
* `integral_mul_trace_hessian_eq`: Green's identity `∫ f Δψ = ∫ Δf ψ` for `f ∈ C²`, `ψ ∈ C²_c`
  (two integrations by parts per coordinate, `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`);
* `isWeakSolutionLaplace_paraboloid`: `ΔP = tr X` weakly;
* `isWeakSolutionLaplace_rescale`: weak solutions under `y ↦ a + r y`;
* `hasSecondOrderTaylorAt_of_contDiffAt`: `C²` functions have Peano expansions.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

/-! ### Peano expansion of `C²` functions -/

/-- A function `C²` near `b` has the second-order Peano expansion with gradient the Riesz
representative of `Dφ(b)` and matrix `D²φ(b)`. -/
theorem hasSecondOrderTaylorAt_of_contDiffAt {φ : Rd 2 → ℝ} {b : Rd 2} (hφ : ContDiffAt ℝ 2 φ b) :
    HasSecondOrderTaylorAt φ b ((InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ b))
      (hessian φ b) := by
  unfold HasSecondOrderTaylorAt
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨ρ, hρ, hT⟩ := ContDiffAt.taylor_two hφ hc
  filter_upwards [Metric.ball_mem_nhds b hρ] with y hy
  rw [InnerProductSpace.toDual_symm_apply, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖y - b‖)]
  exact hT y (by rwa [mem_ball, dist_eq_norm] at hy)

/-! ### Green's identity -/

/-- `∂_v (∂_v φ) = D²φ(v, v)` for `φ ∈ C²`. -/
theorem fderiv_apply_fderiv {φ : Rd 2 → ℝ} (hφ : ContDiff ℝ 2 φ) (v x : Rd 2) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x v = fderiv ℝ (fderiv ℝ φ) x v v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have h : HasFDerivAt (fun y => fderiv ℝ φ y v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ φ) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hd.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- `x ↦ Dφ(x) v` is `C¹` for `φ ∈ C²`. -/
theorem contDiff_fderiv_apply {φ : Rd 2 → ℝ} (hφ : ContDiff ℝ 2 φ) (v : Rd 2) :
    ContDiff ℝ 1 (fun y => fderiv ℝ φ y v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp (hφ.fderiv_right (m := 1) (by norm_num))

/-- One integration by parts in the direction `v`, for `f, g ∈ C¹`, `g` compactly supported. -/
theorem integral_mul_fderiv_apply {f g : Rd 2 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : Rd 2) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  have hfc' : Continuous fun x => fderiv ℝ f x v :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgc' : Continuous fun x => fderiv ℝ g x v :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsupp : HasCompactSupport fun x => fderiv ℝ g x v :=
    (hgc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Rd 2 →L[ℝ] ℝ => L v) rfl
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) ?_ ?_ ?_
    (fun x _ => (hf.differentiable (by norm_num)) x) (fun x _ => (hg.differentiable (by norm_num)) x)
  · exact (hfc'.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  · exact (hf.continuous.mul hgc').integrable_of_hasCompactSupport hsupp.mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left

/-- Integrability of `x ↦ D²f(v,v)(x) ψ(x)` (`f ∈ C²`, `ψ ∈ C²_c`) in the form produced by the
integrations by parts. -/
theorem integrable_fderiv_apply_mul {f ψ : Rd 2 → ℝ} (hf : ContDiff ℝ 1 f) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (v : Rd 2) :
    Integrable fun x => fderiv ℝ f x v * ψ x :=
  (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hψ)
    |>.integrable_of_hasCompactSupport hψc.mul_left

/-- **Green's identity** `∫ f Δψ = ∫ Δf ψ` for `f ∈ C²(ℝ²)` and `ψ ∈ C²_c(ℝ²)`, `Δ = tr D²`. -/
theorem integral_mul_trace_hessian_eq {f ψ : Rd 2 → ℝ} (hf : ContDiff ℝ 2 f)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, f x * (hessian ψ x).trace = ∫ x, (hessian f x).trace * ψ x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  -- one coordinate
  have key : ∀ i : Fin 2,
      (Integrable fun x => f x * hessian ψ x i i) ∧ (Integrable fun x => hessian f x i i * ψ x) ∧
      ∫ x, f x * hessian ψ x i i = ∫ x, hessian f x i i * ψ x := by
    intro i
    set e : Rd 2 := EuclideanSpace.single i 1
    have hgψ : ContDiff ℝ 1 (fun y => fderiv ℝ ψ y e) := contDiff_fderiv_apply hψ e
    have hgf : ContDiff ℝ 1 (fun y => fderiv ℝ f y e) := contDiff_fderiv_apply hf e
    have hgψc : HasCompactSupport (fun y => fderiv ℝ ψ y e) :=
      (hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Rd 2 →L[ℝ] ℝ => L e) rfl
    have eψ : ∀ x, hessian ψ x i i = fderiv ℝ (fun y => fderiv ℝ ψ y e) x e := fun x => by
      rw [fderiv_apply_fderiv hψ e x]; rfl
    have ef : ∀ x, hessian f x i i = fderiv ℝ (fun y => fderiv ℝ f y e) x e := fun x => by
      rw [fderiv_apply_fderiv hf e x]; rfl
    simp only [eψ, ef]
    refine ⟨?_, integrable_fderiv_apply_mul hgf hψ.continuous hψc e, ?_⟩
    · have hc : Continuous fun x => fderiv ℝ (fun y => fderiv ℝ ψ y e) x e :=
        (hgψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
      have hs : HasCompactSupport fun x => fderiv ℝ (fun y => fderiv ℝ ψ y e) x e :=
        (hgψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Rd 2 →L[ℝ] ℝ => L e) rfl
      exact (hf.continuous.mul hc).integrable_of_hasCompactSupport hs.mul_left
    · rw [integral_mul_fderiv_apply hf1 hgψ hgψc e, integral_mul_fderiv_apply hgf hψ1 hψc e,
        neg_neg]
  have htr : ∀ (M : Rd 2 → Matrix (Fin 2) (Fin 2) ℝ) (x : Rd 2),
      (M x).trace = ∑ i : Fin 2, M x i i := fun M x => rfl
  simp only [htr, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => (key i).1), integral_finsetSum _ (fun i _ => (key i).2.1)]
  exact Finset.sum_congr rfl fun i _ => (key i).2.2

/-! ### Weak Laplacian of a paraboloid -/

theorem paraboloid_eq_innerSL (c : ℝ) (L : Rd 2 →L[ℝ] ℝ) (a : Rd 2) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    (fun x => c + L (x - a) + qM X (x - a)) = fun x =>
      c + innerSL ℝ ((InnerProductSpace.toDual ℝ (Rd 2)).symm L) (x - a) + qM X (x - a) := by
  funext x
  rw [innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]

theorem contDiff_paraboloid' (c : ℝ) (L : Rd 2 →L[ℝ] ℝ) (a : Rd 2) (X : Matrix (Fin 2) (Fin 2) ℝ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (fun x => c + L (x - a) + qM X (x - a)) := by
  rw [paraboloid_eq_innerSL]
  exact contDiff_paraboloid _ _ _ _

theorem hessian_paraboloid' (c : ℝ) (L : Rd 2 →L[ℝ] ℝ) (a : Rd 2) {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : X.IsSymm) (y : Rd 2) : hessian (fun x => c + L (x - a) + qM X (x - a)) y = X := by
  rw [paraboloid_eq_innerSL, hessian_paraboloid, hessian_qM_of_isSymm hX]

/-- The paraboloid `P(x) = c + L(x - a) + ½(x - a)ᵀX(x - a)` is a weak solution of `ΔP = tr X`. -/
theorem isWeakSolutionLaplace_paraboloid (U : Set (Rd 2)) (c : ℝ) (L : Rd 2 →L[ℝ] ℝ) (a : Rd 2)
    {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : X.IsSymm) :
    IsWeakSolutionLaplace U (fun x => c + L (x - a) + qM X (x - a)) (fun _ => X.trace) := by
  intro ψ hψ hψc _
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (WithTop.coe_le_coe.2 le_top)
  rw [integral_mul_trace_hessian_eq (contDiff_paraboloid' c L a X) hψ2 hψc]
  congr 1
  funext x
  rw [hessian_paraboloid' c L a hX x]

/-! ### Rescaling -/

/-- `∫ F(a + r y) dy = r⁻² ∫ F` on `ℝ²`, `r > 0`. -/
theorem integral_comp_affine_two (F : Rd 2 → ℝ) (a : Rd 2) {r : ℝ} (hr : 0 < r) :
    ∫ y, F (a + r • y) = (r ^ 2)⁻¹ * ∫ x, F x := by
  have h1 := Measure.integral_comp_smul_of_nonneg volume (fun x => F (a + x)) r (hR := hr.le)
  rw [h1, integral_add_left_eq_self, finrank_euclideanSpace_fin, smul_eq_mul]

/-- Weak solutions under the affine change `y ↦ a + r y`. -/
theorem isWeakSolutionLaplace_rescale {h s : Rd 2 → ℝ} {a : Rd 2} {r : ℝ} (hr : 0 < r)
    (hw : IsWeakSolutionLaplace (ball a r) h s) :
    IsWeakSolutionLaplace (ball (0 : Rd 2) 1) (fun y => h (a + r • y))
      (fun y => r ^ 2 * s (a + r • y)) := by
  intro ψ hψ hψc hψs
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨φ, hφdef⟩ : ∃ φ : Rd 2 → ℝ, φ = fun x => 1 * ψ (r⁻¹ • x + -(r⁻¹ • a)) := ⟨_, rfl⟩
  have hpt : ∀ y : Rd 2, r⁻¹ • (a + r • y) + -(r⁻¹ • a) = y := fun y => by
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    abel
  have hinv : ∀ x : Rd 2, a + r • (r⁻¹ • x + -(r⁻¹ • a)) = x := fun x => by
    simp only [smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hφy : ∀ y, φ (a + r • y) = ψ y := fun y => by rw [hφdef]; simp only [hpt, one_mul]
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := by
    rw [hφdef]
    exact contDiff_const.mul (hψ.comp ((contDiff_id.const_smul r⁻¹).add contDiff_const))
  obtain ⟨K, hKdef⟩ : ∃ K : Set (Rd 2), K = (fun y => a + r • y) '' tsupport ψ := ⟨_, rfl⟩
  have hK : IsCompact K := by
    rw [hKdef]; exact hψc.isCompact.image (by fun_prop)
  have hzero : ∀ x, x ∉ K → φ x = 0 := by
    intro x hx
    have hnot : r⁻¹ • x + -(r⁻¹ • a) ∉ tsupport ψ := by
      intro hin
      apply hx
      rw [hKdef]
      exact ⟨_, hin, hinv x⟩
    rw [hφdef]
    simp only [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  have hφc : HasCompactSupport φ := HasCompactSupport.intro hK hzero
  have hφK : tsupport φ ⊆ K := closure_minimal (fun x hx => by
    by_contra hxK
    exact hx (hzero x hxK)) hK.isClosed
  have hKb : K ⊆ ball a r := by
    rw [hKdef]
    rintro _ ⟨y, hy, rfl⟩
    have hy1 := hψs hy
    rw [mem_ball_zero_iff] at hy1
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hmain := hw φ hφs hφc (hφK.trans hKb)
  have hhess : ∀ y, (hessian ψ y).trace = r ^ 2 * (hessian φ (a + r • y)).trace := by
    intro y
    obtain ⟨-, h2, -⟩ := PegdenSmartAdapter.affine_test (x₁ := a) hr (hψ2.contDiffAt (x := y))
    rw [hφdef, h2, Matrix.trace_smul, smul_eq_mul, inv_pow]
    field_simp
  have hr2 : (r ^ 2) ≠ 0 := pow_ne_zero 2 hr.ne'
  calc ∫ y, h (a + r • y) * (hessian ψ y).trace
      = ∫ y, r ^ 2 * (h (a + r • y) * (hessian φ (a + r • y)).trace) := by
        congr 1; funext y; rw [hhess]; ring
    _ = r ^ 2 * ∫ y, h (a + r • y) * (hessian φ (a + r • y)).trace := integral_const_mul _ _
    _ = r ^ 2 * ((r ^ 2)⁻¹ * ∫ x, h x * (hessian φ x).trace) := by
        rw [integral_comp_affine_two (fun x => h x * (hessian φ x).trace) a hr]
    _ = ∫ x, s x * φ x := by rw [← mul_assoc, mul_inv_cancel₀ hr2, one_mul, hmain]
    _ = r ^ 2 * ((r ^ 2)⁻¹ * ∫ x, s x * φ x) := by rw [← mul_assoc, mul_inv_cancel₀ hr2, one_mul]
    _ = r ^ 2 * ∫ y, s (a + r • y) * φ (a + r • y) := by
        rw [integral_comp_affine_two (fun x => s x * φ x) a hr]
    _ = ∫ y, r ^ 2 * s (a + r • y) * ψ y := by
        rw [← integral_const_mul]; congr 1; funext y; rw [hφy]; ring

/-! ### Pegden-Smart Proposition 2.5 on a ball -/

/-- **`PS25ParaboloidStmt` from Pegden-Smart Proposition 2.5.** -/
theorem ps25Paraboloid_of_ps25 (h25 : PegdenSmartProp25Stmt) : PS25ParaboloidStmt := by
  intro u s a r C hr hu hs hC hw L X hX hsph
  obtain ⟨P, hPdef⟩ : ∃ P : Rd 2 → ℝ, P = fun x => u a + L (x - a) + qM X (x - a) := ⟨_, rfl⟩
  have hPc : ContDiff ℝ 2 P := by rw [hPdef]; exact contDiff_paraboloid' _ _ _ _
  have hPw : IsWeakSolutionLaplace (ball a r) P (fun _ => X.trace) := by
    rw [hPdef]; exact isWeakSolutionLaplace_paraboloid _ _ _ _ hX
  have hcu : ContinuousOn u (ball a r) := hu.mono ball_subset_closedBall
  have hw' : IsWeakSolutionLaplace (ball a r) (fun x => P x - u x) (fun x => X.trace - s x) :=
    PegdenSmartAdapter.isWeakSolutionLaplace_sub isOpen_ball hPc.continuous.continuousOn hcu
      measurable_const hs (C := max |X.trace| C) (fun _ => le_max_left _ _)
      (fun x => (hC x).trans (le_max_right _ _)) hPw hw
  have hres := isWeakSolutionLaplace_rescale hr hw'
  -- the rescaled function
  have haff : ∀ y : Rd 2, y ∈ closedBall (0 : Rd 2) 1 → a + r • y ∈ closedBall a r := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
    nlinarith
  have hHc : ContinuousOn (fun y => P (a + r • y) - u (a + r • y)) (closedBall 0 1) := by
    refine ContinuousOn.sub (hPc.continuous.comp (by fun_prop)).continuousOn ?_
    exact hu.comp (by fun_prop : Continuous fun y : Rd 2 => a + r • y).continuousOn haff
  have hSm : MemLp (fun y => r ^ 2 * (X.trace - s (a + r • y))) ⊤
      (volume.restrict (ball (0 : Rd 2) 1)) := by
    have hmeas : Measurable fun y : Rd 2 => r ^ 2 * (X.trace - s (a + r • y)) := by fun_prop
    refine memLp_top_of_bound hmeas.aestronglyMeasurable (r ^ 2 * (|X.trace| + C))
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r)]
    have h1 := abs_sub X.trace (s (a + r • y))
    have h2 := hC (a + r • y)
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg r)
  -- boundary and centre values
  have hsph' : ∀ y ∈ sphere (0 : Rd 2) 1, P (a + r • y) - u (a + r • y) < 0 := by
    intro y hy
    rw [mem_sphere_zero_iff_norm] at hy
    have hmem : a + r • y ∈ sphere a r := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, hy, mul_one]
    have := hsph _ hmem
    rw [hPdef]
    linarith
  have hH0 : P (a + r • (0 : Rd 2)) - u (a + r • (0 : Rd 2)) = 0 := by
    rw [hPdef]
    simp [qM]
  have hsup : sSup ((fun y => P (a + r • y) - u (a + r • y)) '' sphere (0 : Rd 2) 1) <
      sSup ((fun y => P (a + r • y) - u (a + r • y)) '' ball (0 : Rd 2) 1) := by
    have hcs : IsCompact ((fun y => P (a + r • y) - u (a + r • y)) '' sphere (0 : Rd 2) 1) :=
      (isCompact_sphere 0 1).image_of_continuousOn (hHc.mono sphere_subset_closedBall)
    have hne : ((fun y => P (a + r • y) - u (a + r • y)) '' sphere (0 : Rd 2) 1).Nonempty :=
      ⟨_, EuclideanSpace.single 0 1, by simp, rfl⟩
    obtain ⟨y₀, hy₀, hy₀eq⟩ := hcs.sSup_mem hne
    have hbdd : BddAbove ((fun y => P (a + r • y) - u (a + r • y)) '' ball (0 : Rd 2) 1) :=
      ((isCompact_closedBall 0 1).image_of_continuousOn hHc).bddAbove.mono
        (Set.image_mono ball_subset_closedBall)
    have hle := le_csSup hbdd ⟨0, mem_ball_self one_pos, rfl⟩
    rw [← hy₀eq]
    have := hsph' y₀ hy₀
    simp only at hle
    linarith
  have hpos := h25 2 le_rfl _ _ hSm hHc hres hsup
  -- back to `u`
  refine PegdenSmartAdapter.volume_pos_of_preimage (x₁ := a) hr hpos
    (Filter.Eventually.of_forall fun y hy => ?_)
  obtain ⟨hy1, -, p', X', hX's, hT, hneg⟩ := hy
  have hb : a + r • y ∈ ball a r := by
    rw [mem_ball_zero_iff] at hy1
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  refine ⟨hb, ?_⟩
  have hpt : -(r⁻¹ • a) + r⁻¹ • (a + r • y) = y := by
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    abel
  have hT' : HasSecondOrderTaylorAt (fun y => P (a + r • y) - u (a + r • y))
      (-(r⁻¹ • a) + r⁻¹ • (a + r • y)) p' X' := by rw [hpt]; exact hT
  have hTH := PegdenSmartAdapter.taylor_comp_affine hT'
  have hTP := hasSecondOrderTaylorAt_of_contDiffAt (hPc.contDiffAt (x := a + r • y))
  have hTu := PegdenSmartAdapter.taylor_sub hTP hTH
  have hfun : (fun z => P z - (fun y => P (a + r • y) - u (a + r • y))
      (-(r⁻¹ • a) + r⁻¹ • z)) = u := by
    funext z
    have hz : a + r • (-(r⁻¹ • a) + r⁻¹ • z) = z := by
      simp only [smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    simp only [hz]
    ring
  rw [hfun] at hTu
  have hHP : hessian P (a + r • y) = X := by rw [hPdef]; exact hessian_paraboloid' _ _ _ hX _
  rw [hHP] at hTu
  refine ⟨_, _, hX.sub (hX's.smul _), hTu, ?_⟩
  have e : X - (r⁻¹ ^ 2) • X' - X = (r⁻¹ ^ 2) • (-X') := by
    rw [smul_neg]; abel
  rw [e]
  exact hneg.smul (by positivity)

end SingleSourceD2

end RandomSandpile

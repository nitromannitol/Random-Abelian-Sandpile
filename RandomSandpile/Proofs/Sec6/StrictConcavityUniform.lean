import RandomSandpile.Proofs.Sec6.StrictConcavityUniformGrad
import RandomSandpile.Proofs.Sec6.StrictConcavityUniformLinAlg
import RandomSandpile.Proofs.Sec6.StrictConcavityUniformDet
import RandomSandpile.Proofs.Sec6.StrictConcavityUniformSegment

/-! # Step L2-C (`ConcaveUniformConcavityStmt`): uniform concavity of the limit

`concaveUniformConcavity` proves `ConcaveUniformConcavityStmt` with `κ = 1 / (2Λ + 1)^{d-1}`, without
literature inputs. Fix `X, Y ∈ B_1` and `δ < 1` with `X, Y ∈ B_δ`, and write `g = ∇V`, `L = 2Λ + 1`.
* `g` is `2Λ`-Lipschitz on `B̄_δ`, and touching slopes are `g` (`StrictConcavityUniformGrad`).
* At differentiability points `Dg` is symmetric with quadratic form in `[-L|w|², 0]`, so
  `|det Dg| ≤ L^d`; the slope mass gives `|g(K)| ≥ α |K|`, hence `|det Dg| ≥ α` a.e.
  (`StrictConcavityUniformDet`), and then `⟪Dg w, w⟫ ≤ -(α/L^{d-1}) |w|²` a.e.
  (`StrictConcavityUniformLinAlg`).
* `g` is strongly monotone (`StrictConcavityUniformSegment`), and the mean value theorem along
  `[X, Y]` gives `V(Y) ≤ V(X) + ⟪g(X), Y - X⟫ - (κα/2)|Y - X|²`. -/

open MeasureTheory Filter Metric Set
open scoped Topology NNReal ENNReal

namespace RandomSandpile

open UniformConcavity

/-- **Step L2-C** (`ConcaveUniformConcavityStmt`), with `κ = 1 / (2Λ + 1)^{d-1}`. -/
theorem concaveUniformConcavity : ConcaveUniformConcavityStmt := by
  intro d hd Λ hΛ
  set L : ℝ := 2 * Λ + 1 with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  refine ⟨1 / L ^ (d - 1), by positivity, fun α hα V hconc hA hB X hX q hq Y hY => ?_⟩
  have hA' : Semiconvex V Λ := hA
  have hB' : SlopeMass V α := hB
  have hTg := fun Z (hZ : Z ∈ ball (0 : Rd d) 1) => touch_gradient hα hconc hA' hB' hZ
  have hT : ∀ Z ∈ ball (0 : Rd d) 1, Touch V Z (gradient V Z) := fun Z hZ => (hTg Z hZ).1
  have hD : ∀ Z ∈ ball (0 : Rd d) 1, HasFDerivAt V (innerSL ℝ (gradient V Z)) Z :=
    fun Z hZ => (hTg Z hZ).2.1
  have hq' : q = gradient V X := (hTg X hX).2.2 q hq
  have hmax : max ‖X‖ ‖Y‖ < 1 := max_lt (mem_ball_zero_iff.1 hX) (mem_ball_zero_iff.1 hY)
  set δ := (max ‖X‖ ‖Y‖ + 1) / 2 with hδ
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  have hXδ : X ∈ ball (0 : Rd d) δ :=
    mem_ball_zero_iff.2 (by rw [hδ]; linarith [le_max_left ‖X‖ ‖Y‖])
  have hYδ : Y ∈ ball (0 : Rd d) δ :=
    mem_ball_zero_iff.2 (by rw [hδ]; linarith [le_max_right ‖X‖ ‖Y‖])
  have hδB : ball (0 : Rd d) δ ⊆ ball 0 1 := ball_subset_ball hδ1.le
  have hlip : LipschitzOnWith (2 * Λ).toNNReal (gradient V) (closedBall (0 : Rd d) δ) :=
    lipschitzOnWith_gradient hΛ hA' hT hδ1
  -- the derivative of `∇V` at differentiability points
  have hquad : ∀ x ∈ ball (0 : Rd d) δ, DifferentiableAt ℝ (gradient V) x →
      (fderiv ℝ (gradient V) x : Rd d →ₗ[ℝ] Rd d).IsSymmetric ∧
      (∀ w, -L * ‖w‖ ^ 2 ≤ inner ℝ ((fderiv ℝ (gradient V) x : Rd d →ₗ[ℝ] Rd d) w) w) ∧
      (∀ w, inner ℝ ((fderiv ℝ (gradient V) x : Rd d →ₗ[ℝ] Rd d) w) w ≤ 0) := by
    intro x hx hdx
    have hxB := hδB hx
    have hAx := hdx.hasFDerivAt
    refine ⟨fun v w => inner_fderiv_gradient_comm hD hxB hAx v w, fun w => ?_,
      fun w => inner_fderiv_gradient_nonpos hT hxB hAx w⟩
    have h1 := neg_le_inner_fderiv_gradient hΛ hlip hx hAx w
    have h2 : -L * ‖w‖ ^ 2 ≤ -(2 * Λ) * ‖w‖ ^ 2 := by
      rw [hL]; nlinarith [sq_nonneg ‖w‖]
    exact h2.trans h1
  have hfin : Module.finrank ℝ (Rd d) = d := finrank_euclideanSpace_fin
  -- the image of closed balls under `∇V` carries the slope mass
  have hmass : ∀ (c : Rd d) (r : ℝ), 0 < r → closedBall c r ⊆ ball (0 : Rd d) δ →
      ENNReal.ofReal α * volume (closedBall c r) ≤ volume (gradient V '' closedBall c r) := by
    intro c r hr hsub
    refine (hB' c r hr (hsub.trans hδB)).trans (measure_mono ?_)
    rintro p ⟨Z, hZ, hpZ⟩
    exact ⟨Z, hZ, ((hTg Z (hδB (hsub hZ))).2.2 p hpZ).symm⟩
  have hdetae := ae_le_abs_det (B := L ^ d) hα (hlip.mono ball_subset_closedBall) hmass
    (fun x hx hdx => by
      obtain ⟨hs, hlo, hhi⟩ := hquad x hx hdx
      exact abs_det_le hfin hs hlo hhi)
  set c := α / L ^ (d - 1) with hc
  have hgood : ∀ᵐ x, x ∈ ball (0 : Rd d) δ → DifferentiableAt ℝ (gradient V) x ∧
      ∀ w, inner ℝ (fderiv ℝ (gradient V) x w) w ≤ -c * ‖w‖ ^ 2 := by
    filter_upwards [hdetae] with x hx hxδ
    obtain ⟨hdx, hdet⟩ := hx hxδ
    obtain ⟨hs, hlo, hhi⟩ := hquad x hxδ hdx
    exact ⟨hdx, fun w => inner_le_of_abs_det hfin hs hL0 hlo hhi hdet w⟩
  -- the mean value theorem along `[X, Y]`
  set v := Y - X with hv
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, X + t • v ∈ ball (0 : Rd d) δ := fun t ht =>
    (convex_ball (0 : Rd d) δ).add_smul_sub_mem hXδ hYδ ht
  set χ : ℝ → ℝ := fun t => V (X + t • v) + c / 2 * t ^ 2 * ‖v‖ ^ 2 with hχdef
  set χ' : ℝ → ℝ := fun t => inner ℝ (gradient V (X + t • v)) v + c * t * ‖v‖ ^ 2 with hχ'def
  have hχ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt χ (χ' t) t := by
    intro t ht
    have hline : HasDerivAt (fun s : ℝ => X + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add X
    have h1 : HasDerivAt (fun s => V (X + s • v)) (inner ℝ (gradient V (X + t • v)) v) t := by
      have := (hD _ (hδB (hseg t ht))).comp_hasDerivAt t hline
      simp only [Function.comp_def, innerSL_apply_apply] at this
      exact this
    have h2 : HasDerivAt (fun s : ℝ => c / 2 * s ^ 2 * ‖v‖ ^ 2) (c * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (c / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      ring
    exact h1.add h2
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope χ χ' zero_lt_one
    (fun t ht => (hχ t ht).continuousAt.continuousWithinAt)
    (fun t ht => hχ t (Ioo_subset_Icc_self ht))
  have hχ'0 : χ' 0 = inner ℝ (gradient V X) v := by
    simp only [hχ'def, zero_smul, add_zero, mul_zero, zero_mul]
  have hχ0 : χ 0 = V X := by
    simp only [hχdef, zero_smul, add_zero]; ring
  have hXY : X + (1 : ℝ) • v = Y := by rw [one_smul, hv]; abel
  have hχ1 : χ 1 = V Y + c / 2 * ‖v‖ ^ 2 := by
    simp only [hχdef]; rw [hXY]; ring
  have hξle : χ' ξ ≤ χ' 0 := by
    have hm := inner_sub_le_of_ae hlip hgood hXδ (hseg ξ (Ioo_subset_Icc_self hξ))
    rw [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hξ.1,
      inner_sub_left, mul_pow] at hm
    have e : ξ * (χ' ξ - χ' 0) = ξ * (inner ℝ (gradient V (X + ξ • v)) v -
        inner ℝ (gradient V X) v) + c * ξ ^ 2 * ‖v‖ ^ 2 := by
      rw [hχ'0]; simp only [hχ'def]; ring
    have h0 : ξ * (χ' ξ - χ' 0) ≤ ξ * 0 := by rw [e, mul_zero]; nlinarith
    have := le_of_mul_le_mul_left h0 hξ.1
    linarith
  rw [hχ1, hχ0, sub_zero, div_one] at hξeq
  have hfinal : V Y + c / 2 * ‖v‖ ^ 2 - V X ≤ inner ℝ (gradient V X) v := by
    rw [← hξeq, ← hχ'0]; exact hξle
  have hκ : 1 / L ^ (d - 1) * α / 2 = c / 2 := by rw [hc]; ring
  rw [hq', hκ]
  linarith

end RandomSandpile

import RandomSandpile.Proofs.PegdenSmart
import LatticeProb.Analysis.ViscositySubharmonic
import LatticeProb.Analysis.ViscositySubMean
import LatticeProb.Analysis.SubMeanValueDistribution
import LatticeProb.Analysis.BoundedLaplacianDensity
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Viscosity solutions of `|Δu| ≤ K` are weak solutions of `Δu = s` with `|s| ≤ K`

This file proves `ViscosityWeakLaplaceStmt`. Let `u` be continuous on an open set `U ⊆ ℝ^d`,
`d ≥ 2`, with `Δu ≥ -K` and `Δu ≤ K` in the viscosity sense.

* The functions `u + K ‖x‖² / 2d` and `-u + K ‖x‖² / 2d` are viscosity subharmonic
  (`LatticeProb.Ishii.isViscSubharmonic_add_sq`).
* A continuous viscosity subharmonic function lies below every harmonic function on a ball that
  dominates it on the sphere (`le_of_le_on_sphere_of_isViscSubharmonic`). With the Poisson integral
  on balls this gives the ball sub-mean-value property
  (`LatticeProb.Ishii.le_ballAverage_of_comparison`).
* A continuous function with the ball sub-mean-value property has a nonnegative distributional
  Laplacian (`LatticeProb.Ishii.integral_mul_laplacian_nonneg_of_le_ballAverage`). Integrating by
  parts against `‖x‖²` gives `-K ∫ φ ≤ ∫ u Δφ ≤ K ∫ φ` for every nonnegative test function `φ`.
* Testing with a bump function shows `0 ≤ K` (the domain is nonempty), and the two-sided bound
  yields a measurable density `s` with `|s| ≤ K`
  (`LatticeProb.PegdenSmart.exists_density_of_two_sided`).
-/

open MeasureTheory Metric
open scoped InnerProductSpace Laplacian ContDiff

namespace RandomSandpile

open LatticeProb.Ishii

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A continuous viscosity subharmonic function is bounded above on a ball by a harmonic function
that bounds it above on the sphere. -/
theorem le_of_le_on_sphere_of_isViscSubharmonic [Nontrivial E] {U : Set E} {v : E → ℝ}
    (hv : ContinuousOn v U) (hvisc : IsViscSubharmonic U v)
    {a : E} {r : ℝ} (hball : closedBall a r ⊆ U) {h : E → ℝ}
    (hhc : ContinuousOn h (closedBall a r)) (hh : InnerProductSpace.HarmonicOnNhd h (ball a r))
    (hboundary : ∀ x ∈ sphere a r, v x ≤ h x) :
    ∀ x ∈ ball a r, v x ≤ h x := by
  intro x hx
  by_contra hn
  have hm : 0 < v x - h x := sub_pos.mpr (lt_of_not_ge hn)
  have hx' : x ∈ closedBall a r := ball_subset_closedBall hx
  have hc : IsCompact (closedBall a r) := isCompact_closedBall a r
  obtain ⟨y, _, hymax⟩ := hc.exists_isMaxOn ⟨x, hx'⟩
    ((continuous_norm.pow 2).continuousOn : ContinuousOn (fun z : E => ‖z‖ ^ 2) _)
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt hm (‖y‖ ^ 2)
  let F : E → ℝ := fun z => v z - h z + ε * ‖z‖ ^ 2
  have hFc : ContinuousOn F (closedBall a r) :=
    ((hv.mono hball).sub hhc).add ((continuous_norm.pow 2).const_mul ε).continuousOn
  obtain ⟨z, hz, hzmax⟩ := hc.exists_isMaxOn ⟨x, hx'⟩ hFc
  have hFx : v x - h x ≤ F x := by
    dsimp [F]
    nlinarith [sq_nonneg ‖x‖]
  have hFz : v x - h x ≤ F z := hFx.trans (hzmax hx')
  have hzball : z ∈ ball a r := by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    by_contra hznot
    have hzs : z ∈ sphere a r := mem_sphere.mpr (le_antisymm hz (le_of_not_gt hznot))
    have hq : ‖z‖ ^ 2 ≤ ‖y‖ ^ 2 := hymax hz
    have hb := hboundary z hzs
    dsimp [F] at hFz
    nlinarith [mul_le_mul_of_nonneg_left hq hε.le]
  have hlocal : IsLocalMax F z := hzmax.isLocalMax
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hzball) ball_subset_closedBall)
  have hh' := hh z hzball
  have hq : ContDiffAt ℝ 2 (ε • fun w : E => ‖w‖ ^ 2) z :=
    ((contDiff_norm_sq ℝ (n := 2)).const_smul ε).contDiffAt
  have hmax : IsLocalMax (fun w => v w - (h - ε • fun w : E => ‖w‖ ^ 2) w) z := by
    have heq : (fun w => v w - (h - ε • fun w : E => ‖w‖ ^ 2) w) = F := by
      funext w
      simp only [F, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact hlocal
  have hvineq := hvisc z (hball hz) (h - ε • fun w : E => ‖w‖ ^ 2) (hh'.1.sub hq) hmax
  rw [hh'.1.laplacian_sub hq, laplacian_smul_norm_sq, hh'.2.self_of_nhds, Pi.zero_apply] at hvineq
  have hdim : (0 : ℝ) < Module.finrank ℝ E := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  nlinarith

end Comparison

variable {d : ℕ}

/-- A continuous viscosity subharmonic function on an open set of `ℝ^d`, `d ≥ 1`, satisfies the
sub-mean-value property on every closed ball contained in the set. -/
theorem le_ballAverage_of_isViscSubharmonic (hd : 1 ≤ d) {U : Set (Rd d)} {v : Rd d → ℝ}
    (hv : ContinuousOn v U) (hvisc : IsViscSubharmonic U v) {a : Rd d} {r : ℝ} (hr : 0 < r)
    (hball : closedBall a r ⊆ U) :
    v a ≤ ⨍ y in ball a r, v y := by
  have : Nontrivial (Rd d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  exact le_ballAverage_of_comparison hr (hv.mono hball) fun ρ _ hρr h hh hhc hbd =>
    le_of_le_on_sphere_of_isViscSubharmonic hv hvisc
      ((closedBall_subset_closedBall hρr).trans hball) hhc hh hbd

/-- If `Δu ≥ -K` in the viscosity sense on an open set `U ⊆ ℝ^d`, `d ≥ 1`, then
`-K ∫ φ ≤ ∫ u Δφ` for every nonnegative smooth `φ` with compact support in `U`. -/
theorem neg_mul_integral_le_integral_mul_laplacian (hd : 1 ≤ d) {U : Set (Rd d)} (hU : IsOpen U)
    {K : ℝ} {u : Rd d → ℝ} (hu : ContinuousOn u U)
    (h : ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMax (fun y => u y - φ y) x →
      -K ≤ Δ φ x)
    {φ : Rd d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    -K * ∫ x, φ x ≤ ∫ x, u x * Δ φ x := by
  set c : ℝ := K / (2 * Module.finrank ℝ (Rd d)) with hc_def
  have hvisc : IsViscSubharmonic U fun x => u x + c * ‖x‖ ^ 2 := isViscSubharmonic_add_sq h
  have hsq : ContinuousOn (fun x : Rd d => ‖x‖ ^ 2) U := (continuous_norm.pow 2).continuousOn
  have hvc : ContinuousOn (fun x => u x + c * ‖x‖ ^ 2) U := hu.add (continuousOn_const.mul hsq)
  have h0 : 0 ≤ ∫ x, (u x + c * ‖x‖ ^ 2) * Δ φ x :=
    integral_mul_laplacian_nonneg_of_le_ballAverage hU hvc
      (fun a ha r hr hball => le_ballAverage_of_isViscSubharmonic hd hvc hvisc hr hball)
      hφ hc hφU hφ0
  have hsplit : (fun x => (u x + c * ‖x‖ ^ 2) * Δ φ x) =
      fun x => u x * Δ φ x + c * (‖x‖ ^ 2 * Δ φ x) := by
    funext x
    ring
  rw [hsplit, integral_add (LatticeProb.PegdenSmart.integrable_mul_laplacian hu hφ hc hφU)
    ((LatticeProb.PegdenSmart.integrable_mul_laplacian hsq hφ hc hφU).const_mul c),
    integral_const_mul, integral_mul_laplacian_eq (contDiff_norm_sq ℝ (n := ∞)) hφ hc] at h0
  simp_rw [laplacian_norm_sq] at h0
  rw [integral_const_mul, finrank_euclideanSpace_fin] at h0
  rw [finrank_euclideanSpace_fin] at hc_def
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hcK : c * (2 * d) = K := by
    rw [hc_def]
    field_simp
  rw [← mul_assoc, hcK] at h0
  linarith

/-- **Viscosity solutions of `|Δu| ≤ K` are weak solutions of `Δu = s` with `|s| ≤ K`.** -/
theorem viscosityWeakLaplace : ViscosityWeakLaplaceStmt := by
  intro d hd U hU hne K u hu hA hB
  have hd1 : 1 ≤ d := by omega
  have hsub : ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x →
      IsLocalMax (fun y => u y - φ y) x → -K ≤ Δ φ x := by
    intro x hx φ hφ hmax
    have : 0 ≤ (hessian φ x).trace + K := hA x hx φ hφ hmax
    rw [trace_hessian_eq_laplacian] at this
    linarith
  have hsup : ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x →
      IsLocalMax (fun y => -u y - φ y) x → -K ≤ Δ φ x := by
    intro x hx φ hφ hmax
    have hmin : IsLocalMin (fun y => u y - (-φ) y) x := by
      have heq : (fun y => u y - (-φ) y) = fun y => -(-u y - φ y) := by
        funext y
        simp only [Pi.neg_apply]
        ring
      rw [heq]
      exact hmax.neg
    have : (hessian (-φ) x).trace - K ≤ 0 := hB x hx (-φ) hφ.neg hmin
    rw [trace_hessian_eq_laplacian, InnerProductSpace.laplacian_neg, Pi.neg_apply] at this
    linarith
  have hlow : ∀ φ : Rd d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x) → -K * ∫ x, φ x ≤ ∫ x, u x * Δ φ x :=
    fun φ hφ hc hφU hφ0 =>
      neg_mul_integral_le_integral_mul_laplacian hd1 hU hu hsub hφ hc hφU hφ0
  have hupp : ∀ φ : Rd d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x) → ∫ x, u x * Δ φ x ≤ K * ∫ x, φ x := by
    intro φ hφ hc hφU hφ0
    have := neg_mul_integral_le_integral_mul_laplacian hd1 hU hu.neg hsup hφ hc hφU hφ0
    simp only [Pi.neg_apply, neg_mul, integral_neg] at this
    linarith
  have hK : 0 ≤ K := by
    obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
    let b : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
    have hbU : tsupport b ⊆ U := by
      rw [b.tsupport_eq]
      exact (closedBall_subset_ball (by simp [b]; linarith)).trans hεU
    have h1 := hlow b b.contDiff b.hasCompactSupport hbU fun x => b.nonneg
    have h2 := hupp b b.contDiff b.hasCompactSupport hbU fun x => b.nonneg
    have hpos : 0 < ∫ x, b x := b.integral_pos
    nlinarith
  obtain ⟨s, hs, hsK, hweak⟩ :=
    LatticeProb.PegdenSmart.exists_density_of_two_sided (μ := volume) hU hu hK
      fun φ hφ hc hφU hφ0 => abs_le.mpr ⟨by linarith [hlow φ hφ hc hφU hφ0],
        hupp φ hφ hc hφU hφ0⟩
  exact ⟨s, hs, hsK, (isWeakSolutionLaplace_iff U u s).2 hweak⟩

end RandomSandpile

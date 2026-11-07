import RandomSandpile.Proofs.Sec5.MuConvergenceBall

/-!
# Open balls are bounded Lipschitz domains

The bounded-Lipschitz-domain property is invariant under the maps `x ↦ z + r • x` (`r > 0`):
these are homeomorphisms, and the Lipschitz graph `γ` is replaced by `v ↦ r * γ (r⁻¹ • v)`, with
the same Lipschitz constant. Combined with `unitBallLipschitz` (the unit ball is a bounded
Lipschitz domain), every open ball `B_r(z)`, `r > 0`, is a bounded Lipschitz domain.
-/

open MeasureTheory LatticeProb Metric
noncomputable section
namespace RandomSandpile
namespace StrictConcavityBall

/-- Affine invariance: if `W` is a bounded Lipschitz domain, so is `z + r • W` for `r > 0`. -/
theorem isLipschitzDomain_affine {d : ℕ} {W : Set (Rd d)} (hW : IsLipschitzDomain W) (z : Rd d)
    {r : ℝ} (hr : 0 < r) : IsLipschitzDomain ((fun x => z + r • x) '' W) := by
  obtain ⟨hb, ho, hc, hf⟩ := hW
  have hr0 : r ≠ 0 := hr.ne'
  let h : Rd d ≃ₜ Rd d := (Homeomorph.smulOfNeZero r hr0).trans (Homeomorph.addLeft z)
  have hcoe : ∀ x, h x = z + r • x := fun x => rfl
  have himg : (fun x => z + r • x) '' W = h '' W := rfl
  rw [himg]
  have hL : LipschitzWith r.toNNReal h := LipschitzWith.of_dist_le' (fun x y => by
    rw [hcoe, hcoe, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr])
  refine ⟨hL.isBounded_image hb, h.isOpen_image.2 ho, hc.image h h.continuous.continuousOn, ?_⟩
  intro x' hx'
  rw [← h.image_frontier] at hx'
  obtain ⟨x₀, hx₀, rfl⟩ := hx'
  obtain ⟨ρ, hρ, e, he, L, γ, hγ, hmem⟩ := hf x₀ hx₀
  refine ⟨r * ρ, mul_pos hr hρ, e, he, L, fun v => r * γ (r⁻¹ • v), ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul (fun v w => ?_)
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hr, ← Real.dist_eq]
    calc r * dist (γ (r⁻¹ • v)) (γ (r⁻¹ • w))
        ≤ r * (L * dist (r⁻¹ • v) (r⁻¹ • w)) :=
          mul_le_mul_of_nonneg_left (hγ.dist_le_mul _ _) hr.le
      _ = L * dist v w := by
          rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
          field_simp
  · intro y' hy'
    obtain ⟨y, rfl⟩ : ∃ y, h y = y' := ⟨h.symm y', h.apply_symm_apply _⟩
    have hdist : dist (h y) (h x₀) = r * dist y x₀ := by
      rw [hcoe, hcoe, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr]
    have hyb : y ∈ Metric.ball x₀ ρ := by
      rw [Metric.mem_ball] at hy' ⊢
      rw [hdist] at hy'
      exact lt_of_mul_lt_mul_left hy' hr.le
    rw [h.injective.mem_set_image, hmem y hyb]
    have hsub : h y - h x₀ = r • (y - x₀) := by
      rw [hcoe, hcoe, add_sub_add_left_eq_sub, smul_sub]
    have hin : inner ℝ (h y - h x₀) e = r * inner ℝ (y - x₀) e := by
      rw [hsub, real_inner_smul_left]
    have hproj : (h y - h x₀) - inner ℝ (h y - h x₀) e • e
        = r • ((y - x₀) - inner ℝ (y - x₀) e • e) := by
      rw [hin, hsub, mul_smul, ← smul_sub]
    rw [hproj, hin]
    beta_reduce
    rw [inv_smul_smul₀ hr0]
    exact (mul_lt_mul_iff_right₀ hr).symm

/-- Every open ball `B_r(z)`, `r > 0`, is a bounded Lipschitz domain. -/
theorem isLipschitzDomain_ball {d : ℕ} (z : Rd d) {r : ℝ} (hr : 0 < r) :
    IsLipschitzDomain (ball z r) := by
  have himg : (fun x => z + r • x) '' ball (0 : Rd d) 1 = ball z r := by
    ext p
    simp only [Set.mem_image, Metric.mem_ball, dist_eq_norm, sub_zero]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      calc r * ‖x‖ < r * 1 := mul_lt_mul_of_pos_left hx hr
        _ = r := mul_one r
    · intro hp
      refine ⟨r⁻¹ • (p - z), ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
        calc r⁻¹ * ‖p - z‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hp (inv_pos.2 hr)
          _ = 1 := inv_mul_cancel₀ hr.ne'
      · rw [smul_inv_smul₀ hr.ne', add_sub_cancel]
  rw [← himg]
  exact isLipschitzDomain_affine (unitBallLipschitz d) z hr

end StrictConcavityBall
end RandomSandpile

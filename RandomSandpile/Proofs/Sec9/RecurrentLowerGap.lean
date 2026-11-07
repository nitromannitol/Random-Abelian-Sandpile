import RandomSandpile.Proofs.Sec6.StrictConcavitySemiconvex
import RandomSandpile.Steps.Sec6.StrictConcavity

/-! Quadratic growth above a lower contact. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- A bounded discrete Laplacian controls the gap above a lower supporting
plane quadratically in an interior ball. -/
theorem lower_contact_gap_le_quadratic {w : Site d → ℝ} {K C R : ℝ} {n : ℕ}
    (hHarn : ∀ (R : ℝ) (f : Site d → ℝ), (∀ x, 0 ≤ f x) → f 0 = 0 →
      (∀ x ∈ ballZ0 R, |lapR f x| ≤ K) → ∀ x ∈ ballZ0 (1 / 2 * R), f x ≤ C * ‖toE x‖ ^ 2)
    (hlap : ∀ y ∈ ballZ0 (d := d) (n : ℝ), |lapR w y| ≤ K) {x : Site d} {p : Rd d}
    (hp : p ∈ subGrad w x (ballZ0 (n : ℝ)))
    (hR : ∀ y : Site d, ‖toE y - toE x‖ < R → y ∈ ballZ0 (d := d) (n : ℝ))
    {y : Site d} (hy : ‖toE y - toE x‖ < 1 / 2 * R) :
    w y - (w x + inner ℝ p (toE y - toE x)) ≤ C * ‖toE y - toE x‖ ^ 2 := by
  have hp' : -p ∈ supGrad (fun z => -w z) x (ballZ0 (n : ℝ)) := by
    rw [NearMaxBending.mem_supGrad_neg_iff, neg_neg]
    exact hp
  have hlap' : ∀ z ∈ ballZ0 (d := d) (n : ℝ), |lapR (fun z => -w z) z| ≤ K := by
    intro z hz
    rw [NearMaxBending.lapR_neg, abs_neg]
    exact hlap z hz
  have h := LimitSemiconvex.gap_le_quadratic hHarn hlap' hp' hR hy
  simp only [inner_neg_left] at h
  linarith

end RandomSandpile

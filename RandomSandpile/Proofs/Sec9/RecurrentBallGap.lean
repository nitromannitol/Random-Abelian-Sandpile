import RandomSandpile.Proofs.Sec9.RecurrentLowerGap
import RandomSandpile.Proofs.Sec9.RecurrentBallComparison

/-! Lower contact gaps between nearby central lattice sites. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- The lower contact gap between two sites in a small central ball is
quadratic in the radius of that ball. -/
theorem recurrent_central_lower_gap {w : Site d → ℝ} {K C β : ℝ} {n : ℕ}
    (hHarn : ∀ (R : ℝ) (f : Site d → ℝ), (∀ x, 0 ≤ f x) → f 0 = 0 →
      (∀ x ∈ ballZ0 R, |lapR f x| ≤ K) → ∀ x ∈ ballZ0 (1 / 2 * R), f x ≤ C * ‖toE x‖ ^ 2)
    (hC : 0 ≤ C) (_hβ : 0 ≤ β) (hβsmall : β < 1 / 8) (hn : 0 < n)
    (hlap : ∀ y ∈ ballZ0 (d := d) (n : ℝ), |lapR w y| ≤ K)
    {x z : Site d} (hx : x ∈ ballZ0 (d := d) (β * n))
    (hz : z ∈ ballZ0 (d := d) (β * n)) {t : Rd d}
    (hp : t ∈ subGrad w z (ballZ0 (n : ℝ))) :
    w x - (w z + inner ℝ t (toE x - toE z)) ≤ C * (2 * β * n) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx' := MuLipschitz.mem_ballZ0.1 hx
  have hz' := MuLipschitz.mem_ballZ0.1 hz
  have hdist : ‖toE x - toE z‖ < 2 * β * n := by
    have := norm_sub_le (toE x) (toE z)
    linarith
  have hR : ∀ y : Site d, ‖toE y - toE z‖ < (n : ℝ) / 2 →
      y ∈ ballZ0 (d := d) (n : ℝ) := by
    intro y hy
    apply MuLipschitz.mem_ballZ0.2
    have h := norm_sub_le (toE y - toE z) (-toE z)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at h
    nlinarith
  have hsmall : ‖toE x - toE z‖ < 1 / 2 * ((n : ℝ) / 2) := by nlinarith
  have h := lower_contact_gap_le_quadratic hHarn hlap hp hR hsmall
  have hsq : ‖toE x - toE z‖ ^ 2 ≤ (2 * β * n) ^ 2 := by
    nlinarith [norm_nonneg (toE x - toE z)]
  exact h.trans (mul_le_mul_of_nonneg_left hsq hC)

end RandomSandpile

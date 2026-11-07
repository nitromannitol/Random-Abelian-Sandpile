import RandomSandpile.Proofs.Sec9.RecurrentContactComparison
import RandomSandpile.Steps.Sec7.Flat

/-! Quantitative recurrent comparison on lattice balls. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- A bent upper competitor and a lower supporting plane on a lattice ball
force a quadratic boundary drop to be bounded by the interior lower gap and
the affine rounding error. -/
theorem recurrent_ball_bending_le_gap {η r s : Site d → ℤ} {n : ℕ} {β ca : ℝ}
    (hr : IsRecurrentFunction η (ballZ0 (n : ℝ)) r)
    (hs : ∀ x ∈ ballZ0 (n : ℝ), lap s x + η x ≤ 2 * (d : ℤ) - 1)
    (hβ : β ≤ 1 / 2) (hca : 0 ≤ ca) (q : Site d → ℝ)
    {x z : Site d} (hx : x ∈ ballZ0 (d := d) (β * n)) (p t : Rd d) (G : ℝ)
    (hbend : ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
      (r y : ℝ) - q y ≤ ((r x : ℝ) - q x) + inner ℝ p (toE y - toE x) -
        ca * ((1 - β) * n) * ‖toE y - toE x‖)
    (hp : t ∈ subGrad (fun y => (s y : ℝ) - q y) z (ballZ0 (n : ℝ)))
    (hgap : (s x : ℝ) - q x - (((s z : ℝ) - q z) + inner ℝ t (toE x - toE z)) ≤ G) :
    ca * (n : ℝ) ^ 2 / 4 ≤ G + ((d : ℝ) + 1) * (2 * n + 1) + 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hxn := MuLipschitz.mem_ballZ0.1 hx
  have hxnorm : ‖toE x‖ ≤ (n : ℝ) := by nlinarith
  have hxA : x ∈ ballZ0 (d := d) (n : ℝ) := MuLipschitz.mem_ballZ0.2 (by nlinarith)
  have hupper : ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)), (r y : ℝ) - q y ≤
      ((r x : ℝ) - q x) + inner ℝ p (toE y - toE x) - ca * (n : ℝ) ^ 2 / 4 := by
    intro y hy
    have h1 := hbend y hy
    have h2 := mul_le_mul_of_nonneg_left (Flat.quarter_le_bend hβ hx hy) hca
    nlinarith
  have hlower : ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
      ((s z : ℝ) - q z) + inner ℝ t (toE y - toE z) ≤ (s y : ℝ) - q y := by
    intro y hy
    exact hp y (by rw [dClosure_eq]; exact Or.inr hy)
  obtain ⟨y, hy, h⟩ := recurrent_bending_le_lower_gap (MuLipschitz.ballZ0_finite _)
    hr hs q hxA p t (ca * (n : ℝ) ^ 2 / 4) G hupper hlower hgap
  have hyn := MuLipschitz.norm_lt_of_mem_bdry_ballZ0 hy
  have hd0 : 0 ≤ (d : ℝ) + 1 := by positivity
  have he := mul_le_mul_of_nonneg_left (show ‖toE x‖ + ‖toE y‖ ≤ 2 * n + 1 by linarith) hd0
  nlinarith

end RandomSandpile

import RandomSandpile.Proofs.Sec9.RecurrentBallGap

/-! Finite-volume estimate for separation of recurrent curvature densities. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- Two recurrent competitors with central upper and lower contacts obey a
quantitative separation estimate. -/
theorem recurrent_separation_finite {η r s : Site d → ℤ} {n : ℕ} {β ca K C : ℝ}
    (hHarn : ∀ (R : ℝ) (f : Site d → ℝ), (∀ x, 0 ≤ f x) → f 0 = 0 →
      (∀ x ∈ ballZ0 R, |lapR f x| ≤ K) → ∀ x ∈ ballZ0 (1 / 2 * R), f x ≤ C * ‖toE x‖ ^ 2)
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (hβsmall : β < 1 / 8) (hn : 0 < n) (hca : 0 ≤ ca)
    (hr : IsRecurrentFunction η (ballZ0 (n : ℝ)) r)
    (hs : IsRecurrentFunction η (ballZ0 (n : ℝ)) s)
    (q : Site d → ℝ)
    (hlap : ∀ y ∈ ballZ0 (d := d) (n : ℝ),
      |lapR (fun z => (s z : ℝ) - q z) y| ≤ K)
    {x z : Site d} (hx : x ∈ ballZ0 (d := d) (β * n))
    (hz : z ∈ ballZ0 (d := d) (β * n)) (p t : Rd d)
    (hbend : ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
      (r y : ℝ) - q y ≤ ((r x : ℝ) - q x) + inner ℝ p (toE y - toE x) -
        ca * ((1 - β) * n) * ‖toE y - toE x‖)
    (hp : t ∈ subGrad (fun y => (s y : ℝ) - q y) z (ballZ0 (n : ℝ))) :
    ca * (n : ℝ) ^ 2 / 4 ≤ C * (2 * β * n) ^ 2 + ((d : ℝ) + 1) * (2 * n + 1) + 2 := by
  have hgap := recurrent_central_lower_gap hHarn hC hβ hβsmall hn hlap hx hz hp
  exact recurrent_ball_bending_le_gap hr hs.1 (by linarith) hca q hx p t _ hbend hp hgap

end RandomSandpile

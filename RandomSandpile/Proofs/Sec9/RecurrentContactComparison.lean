import RandomSandpile.Proofs.Sec9.RecurrentAffineComparison

/-! Comparison of bent upper and lower supporting planes. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- Recurrent comparison bounds upper bending by the lower contact gap and
integer affine rounding errors. -/
theorem recurrent_bending_le_lower_gap {η r s : Site d → ℤ} {A : Set (Site d)}
    (hA : A.Finite) (hr : IsRecurrentFunction η A r)
    (hs : ∀ x ∈ A, lap s x + η x ≤ 2 * (d : ℤ) - 1)
    (q : Site d → ℝ) {x z : Site d} (hx : x ∈ A) (p t : Rd d) (D G : ℝ)
    (hupper : ∀ y ∈ bdry A, (r y : ℝ) - q y ≤
      ((r x : ℝ) - q x) + inner ℝ p (toE y - toE x) - D)
    (hlower : ∀ y ∈ bdry A, ((s z : ℝ) - q z) + inner ℝ t (toE y - toE z) ≤
      (s y : ℝ) - q y)
    (hgap : (s x : ℝ) - q x - (((s z : ℝ) - q z) + inner ℝ t (toE x - toE z)) ≤ G) :
    ∃ y ∈ bdry A, D ≤ G + (((d : ℝ) + 1) * ‖toE x‖ + 1) +
      (((d : ℝ) + 1) * ‖toE y‖ + 1) := by
  let c : ℝ := ((r x : ℝ) - q x) - inner ℝ p (toE x) -
    (((s z : ℝ) - q z) - inner ℝ t (toE z))
  obtain ⟨y, hy, hcmp⟩ := recurrent_compare_real_affine hA hr hs (p - t) c hx
  have hu := hupper y hy
  have hl := hlower y hy
  simp only [inner_sub_left, inner_sub_right] at hcmp hu hl hgap
  dsimp [c] at hcmp
  refine ⟨y, hy, ?_⟩
  linarith

end RandomSandpile

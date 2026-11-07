import RandomSandpile.Proofs.Sec9.RecurrentShift
import RandomSandpile.Proofs.Sec9.SingleSourceFstarLattice

/-! Recurrent comparison after rounding a real affine function. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- Recurrent comparison is stable under subtracting a real affine function,
with an explicit error from rounding it to an integer harmonic function. -/
theorem recurrent_compare_real_affine {η r s : Site d → ℤ} {A : Set (Site d)}
    (hA : A.Finite) (hr : IsRecurrentFunction η A r)
    (hs : ∀ x ∈ A, lap s x + η x ≤ 2 * (d : ℤ) - 1)
    (g : Rd d) (c : ℝ) {x : Site d} (hx : x ∈ A) :
    ∃ y ∈ bdry A,
      (r x : ℝ) - s x - (c + inner ℝ g (toE x)) ≤
        (r y : ℝ) - s y - (c + inner ℝ g (toE y)) +
          (((d : ℝ) + 1) * ‖toE x‖ + 1) +
          (((d : ℝ) + 1) * ‖toE y‖ + 1) := by
  obtain ⟨h, hh, happrox⟩ := SingleSourceFstar.exists_int_affine (-g) (-c) 0
  have hrec := hr.add_harmonic (fun z _ => hh z)
  obtain ⟨y, hy, hxy⟩ := hrec.2 A hA ⟨x, hx⟩ (Set.Subset.rfl) s hs x hx
  have hxy' : ((r x + h x - s x : ℤ) : ℝ) ≤ (r y + h y - s y : ℤ) := by
    exact_mod_cast hxy
  have hex := happrox x
  have hey := happrox y
  simp only [inner_neg_left, sub_zero] at hex hey
  rw [abs_le] at hex hey
  push_cast at hxy'
  refine ⟨y, hy, ?_⟩
  linarith [hex.1, hey.2]

end RandomSandpile

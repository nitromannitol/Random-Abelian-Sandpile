import RandomSandpile.Defs.Recurrent
import RandomSandpile.Steps.Sec3.Burning
import RandomSandpile.Proofs.Sec3.Burning

/-! Recurrent comparison is invariant under adding an integer harmonic function. -/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- Adding a function harmonic on the domain preserves recurrent comparison. -/
theorem IsRecurrentFunction.add_harmonic {η r h : Site d → ℤ} {A : Set (Site d)}
    (hr : IsRecurrentFunction η A r) (hh : ∀ x ∈ A, lap h x = 0) :
    IsRecurrentFunction η A (r + h) := by
  constructor
  · intro x hx
    change lap (fun y => r y + h y) x + η x ≤ _
    rw [Burning.lap_add_apply', hh x hx, add_zero]
    exact hr.1 x hx
  · intro E hfin hne hEA w hw x hx
    have hw' : ∀ z ∈ E, lap (w - h) z + η z ≤ 2 * (d : ℤ) - 1 := by
      intro z hz
      change lap (fun y => w y - h y) z + η z ≤ _
      rw [Burning.lap_sub_apply', hh z (hEA hz), sub_zero]
      exact hw z hz
    obtain ⟨y, hy, hxy⟩ := hr.2 E hfin hne hEA (w - h) hw' x hx
    refine ⟨y, hy, ?_⟩
    simp only [Pi.add_apply, Pi.sub_apply] at *
    omega

/-- Constant shifts preserve recurrent comparison. -/
theorem IsRecurrentFunction.add_const {η r : Site d → ℤ} {A : Set (Site d)}
    (hr : IsRecurrentFunction η A r) (c : ℤ) :
    IsRecurrentFunction η A (fun x => r x + c) := by
  exact hr.add_harmonic (fun x _ => Burning.lap_const_apply c x)

/-- On a finite set, a constant shift makes a recurrent function nonnegative. -/
theorem IsRecurrentFunction.exists_nonnegative_shift {η r : Site d → ℤ}
    {A S : Set (Site d)} (hr : IsRecurrentFunction η A r) (hS : S.Finite) :
    ∃ c : ℤ, IsRecurrentFunction η A (fun x => r x + c) ∧
      ∀ x ∈ S, 0 ≤ r x + c := by
  obtain ⟨b, hb⟩ := (hS.image r).bddBelow
  refine ⟨-b, hr.add_const (-b), ?_⟩
  intro x hx
  have h := hb (Set.mem_image_of_mem r hx)
  omega

end RandomSandpile

import RandomSandpile.Proofs.Sec9.RecurrentSubadditive
import RandomSandpile.Proofs.Sec5.MuConvergenceStationary

/-! Translation stationarity of the recurrent upper gradient measure. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal Pointwise Matrix
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- Translation preserves the local recurrent comparison property. -/
theorem isRecurrentFunction_transl {A : Set (Site d)} {η r : Site d → ℤ}
    (y : Site d) (hr : IsRecurrentFunction (shift y η) A r) :
    IsRecurrentFunction η (y +ᵥ A) (transl y r) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [lap_transl]
    simpa [add_comm] using hr.1 (x - y) (mem_vadd_set_sub.1 hx)
  · intro E hE hne hEA w hw x hx
    let F : Set (Site d) := (-y) +ᵥ E
    have hF : F.Finite := by
      change ((fun z : Site d => (-y) + z) '' E).Finite
      exact hE.image _
    have hneF : F.Nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨z - y, mem_vadd_set_sub.2 (by simpa using hz)⟩
    have hFA : F ⊆ A := by
      intro z hz
      have hz' : z + y ∈ E := by simpa [F] using (mem_vadd_set_sub.1 hz)
      have := mem_vadd_set_sub.1 (hEA hz')
      simpa using this
    have hwF : ∀ z ∈ F, lap (transl (-y) w) z + shift y η z ≤ 2 * (d : ℤ) - 1 := by
      intro z hz
      have hz' : z + y ∈ E := by simpa [F] using (mem_vadd_set_sub.1 hz)
      rw [lap_transl]
      simpa [shift, sub_neg_eq_add, add_comm] using hw (z + y) hz'
    have hxF : x - y ∈ F := mem_vadd_set_sub.2 (by simpa using hx)
    obtain ⟨z, hz, hcomp⟩ := hr.2 F hF hneF hFA (transl (-y) w) hwF (x - y) hxF
    refine ⟨z + y, ?_, ?_⟩
    · have : z ∈ bdry ((-y) +ᵥ E) := hz
      have := mem_bdry_vadd.1 this
      simpa using this
    · simpa [transl, sub_neg_eq_add] using hcomp

/-- The recurrent upper measure is translation covariant. -/
theorem muRecurrent_shift_le (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (y : Site d) (A : Set (Site d)) :
    muRecurrent A (shift y η) l M ≤ muRecurrent (y +ᵥ A) η l M := by
  refine iSup₂_le fun w hw => ?_
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨p₀, c, hp⟩ := parabola_transl l M y
  have hmem : (fun z => ((transl y u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)) ∈
      recurrentPerturbed (y +ᵥ A) η l M := ⟨_, isRecurrentFunction_transl y hu, rfl⟩
  have hw' : ∀ z, (fun z => ((transl y u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)) (z + y) =
      (fun x => (u x : ℝ) - (qlZ l x + qMZ M x)) z + inner ℝ (-p₀) (toE z) + (-c) := by
    intro z
    simp only [transl_apply, add_sub_cancel_right, inner_neg_left, hp z]
    ring
  rw [← volume_supGradSet_vadd (w := fun x => ((u x : ℤ) : ℝ) - (qlZ l x + qMZ M x))
    (w' := fun z => ((transl y u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)) (y := y) hw']
  exact le_iSup₂_of_le _ hmem le_rfl

/-- Stationarity under simultaneous translation of domain and background. -/
theorem muRecurrent_shift_eq (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (y : Site d) (A : Set (Site d)) :
    muRecurrent A (shift y η) l M = muRecurrent (y +ᵥ A) η l M := by
  refine le_antisymm (muRecurrent_shift_le η l M y A) ?_
  have h := muRecurrent_shift_le (shift y η) l M (-y) (y +ᵥ A)
  rwa [← shift_add, neg_add_cancel, shift_zero, id_eq, vadd_vadd, neg_add_cancel, zero_vadd] at h

end RandomSandpile

import RandomSandpile.Proofs.Sec9.RecurrentLeast

/-! The pointwise infimum of bounded-below signed stabilizers is a least stabilizer. -/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- Pointwise lower bounds yield the least signed stabilizer with prescribed boundary. -/
theorem exists_least_stabilizer_of_pointwise_bdd {η v : Site d → ℤ} {A : Set (Site d)}
    (hv : ∀ x ∈ A, lap v x + η x ≤ 2 * (d : ℤ) - 1)
    (hbound : ∀ x ∈ A, ∃ b : ℤ, ∀ w : Site d → ℤ,
      (∀ y ∈ bdry A, w y = v y) →
      (∀ y ∈ A, lap w y + η y ≤ 2 * (d : ℤ) - 1) → b ≤ w x) :
    ∃ r : Site d → ℤ,
      (∀ x ∈ A, lap r x + η x ≤ 2 * (d : ℤ) - 1) ∧
      (∀ y ∈ bdry A, r y = v y) ∧
      ∀ w : Site d → ℤ, (∀ y ∈ bdry A, w y = v y) →
        (∀ y ∈ A, lap w y + η y ≤ 2 * (d : ℤ) - 1) → ∀ x ∈ A, r x ≤ w x := by
  classical
  let S : Set (Site d → ℤ) := {w | (∀ y ∈ bdry A, w y = v y) ∧
    (∀ y ∈ A, lap w y + η y ≤ 2 * (d : ℤ) - 1)}
  have hvS : v ∈ S := ⟨fun _ _ => rfl, hv⟩
  let values (x : Site d) : Set ℤ := {n | ∃ w ∈ S, w x = n}
  have hne : ∀ x, (values x).Nonempty := fun x => ⟨v x, v, hvS, rfl⟩
  have hbdd : ∀ x ∈ A, BddBelow (values x) := by
    intro x hx
    obtain ⟨b, hb⟩ := hbound x hx
    refine ⟨b, ?_⟩
    rintro n ⟨w, hw, rfl⟩
    exact hb w hw.1 hw.2
  let r : Site d → ℤ := fun x => if x ∈ A then sInf (values x) else v x
  have hrle : ∀ x ∈ A, ∀ w ∈ S, r x ≤ w x := by
    intro x hx w hw
    simp only [r, ite_eq_left hx]
    exact csInf_le (hbdd x hx) ⟨w, hw, rfl⟩
  have hrbd : ∀ y ∈ bdry A, r y = v y := by
    intro y hy
    simp [r, (mem_bdry.mp hy).1]
  have hcontact : ∀ x ∈ A, ∃ w ∈ S, r x = w x := by
    intro x hx
    obtain ⟨w, hw, heq⟩ := Int.csInf_mem (hne x) (hbdd x hx)
    exact ⟨w, hw, by simpa [r, hx] using heq.symm⟩
  have hcmp : ∀ w ∈ S, ∀ z ∈ dClosure A, r z ≤ w z := by
    intro w hw z hz
    rw [dClosure_eq] at hz
    rcases hz with hz | hz
    · exact hrle z hz w hw
    · rw [hrbd z hz, hw.1 z hz]
  refine ⟨r, ?_, hrbd, ?_⟩
  · intro x hx
    obtain ⟨w, hw, heq⟩ := hcontact x hx
    have hl := PegdenSmartRegularity.lap_le_lap_of_nbr heq fun i =>
      ⟨hcmp w hw _ (by simpa [dClosure_eq] using Burning.add_unit_mem hx i),
       hcmp w hw _ (by simpa [dClosure_eq] using Burning.sub_unit_mem hx i)⟩
    linarith [hw.2 x hx]
  · intro w hbd hw x hx
    exact hrle x hx w ⟨hbd, hw⟩

end RandomSandpile

import RandomSandpile.Proofs.Sec9.RecurrentMuStar
import RandomSandpile.Proofs.Sec6.StrictConcavityNearMax
import RandomSandpile.Proofs.Sec5.StabilizingLegal

/-! Recurrent perturbations are represented by locally legal topplings. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- A constant shift of a recurrent function agrees on the finite closure with a
locally legal stabilizing toppling function. -/
theorem IsRecurrentFunction.exists_locLegal_shift {A : Set (Site d)} (hd : 0 < d)
    (hA : A.Finite) {η r : Site d → ℤ} (hr : IsRecurrentFunction η A r) :
    ∃ (c : ℤ) (u : Site d → ℤ), u ∈ locLegal η A ∧
      ∀ x ∈ dClosure A, u x = r x + c := by
  classical
  obtain ⟨c, hrc, hnn⟩ := hr.exists_nonnegative_shift (dClosure_finite hA)
  let v : Site d → ℤ := (dClosure A).indicator (fun x => r x + c)
  have hv : v ∈ stabilizing η A := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x
      by_cases hx : x ∈ dClosure A
      · simpa [v, hx] using hnn x hx
      · simp [v, hx]
    · intro x hx
      simp [v, hx]
    · intro x hx
      change lap ((dClosure A).indicator (fun x => r x + c)) x + η x ≤ _
      rw [SingleSourceH0.lap_indicator_dClosure _ hx, PegdenSmartRegularity.lap_add_const]
      exact hr.1 x hx
  obtain ⟨u, ⟨hu, hus⟩, hub⟩ := NearMaxSequence.exists_locLegal_stabilizing hd hA η hv.1
  have huv : u ≤ v := locLegalLeStabilizing d A η u v hu hv (fun x hx => (hub x hx).symm)
  have hvu : ∀ x ∈ A, v x ≤ u x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hrc.2 A hA ⟨x, hx⟩ (Set.Subset.refl A) u hus.2 x hx
    have h1 : v x = r x + c := by simp [v, subset_dClosure A hx]
    have h2 : v y = r y + c := by simp [v, bdry_subset_dClosure A hy]
    have h3 := hub y hy
    dsimp only at hxy
    omega
  refine ⟨c, u, hu, ?_⟩
  intro x hx
  rw [dClosure_eq] at hx
  rcases hx with hx | hx
  · have h := le_antisymm (huv x) (hvu x hx)
    simpa [v, subset_dClosure A hx] using h
  · rw [hub x hx]
    simp [v, bdry_subset_dClosure A hx]

/-- The recurrent upper gradient measure is bounded by the original upper measure. -/
theorem recurrentMuLe : RecurrentMuLeStmt := by
  intro d hd A hA η l M
  unfold muRecurrent mu
  refine iSup₂_le fun f hf => ?_
  obtain ⟨r, hr, rfl⟩ := hf
  obtain ⟨c, u, hu, heq⟩ := hr.exists_locLegal_shift (by omega) hA
  let g : Site d → ℝ := fun x => (u x : ℝ) - (qlZ l x + qMZ M x)
  have hg : g ∈ perturbedSub A η l M := ⟨u, hu, rfl⟩
  have hgrad : supGradSet g A = supGradSet
      (fun x => (r x : ℝ) - (qlZ l x + qMZ M x)) A := by
    unfold supGradSet
    apply Set.iUnion₂_congr
    intro x hx
    ext p
    simp only [supGrad, Set.mem_setOf_eq]
    constructor <;> intro h y hy
    · have hh := h y hy
      dsimp [g] at hh
      rw [heq x (subset_dClosure A hx), heq y hy] at hh
      push_cast at hh
      linarith
    · dsimp [g]
      rw [heq x (subset_dClosure A hx), heq y hy]
      push_cast
      have hh := h y hy
      linarith
  rw [← hgrad]
  exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)

end RandomSandpile

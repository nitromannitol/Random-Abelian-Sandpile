import RandomSandpile.Proofs.Sec9.RecurrentNoForbidden
import RandomSandpile.Proofs.Sec9.RecurrentSubadditive

/-! # Recurrent comparison after legal topplings -/

open Filter LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- A stabilizing locally legal toppling function is recurrent on any subset
whose sites have all toppled. -/
theorem isRecurrentFunction_of_toppled_locLegal {d : ℕ} {η u : Site d → ℤ}
    {A W : Set (Site d)} (hAW : A ⊆ W) (hu : u ∈ locLegal η W)
    (hpos : ∀ x ∈ A, 1 ≤ u x)
    (hstable : ∀ x ∈ A, lap u x + η x ≤ 2 * (d : ℤ) - 1) :
    IsRecurrentFunction η A u := by
  apply isRecurrentFunction_of_noForbidden hstable
  have hnf := toppledNoForbidden d A W η u hAW hu hpos
  simpa only [add_comm] using hnf

/-- Away from a point source, the recurrent comparison property applies to
the original background as well as to the source-augmented background. -/
theorem singleSource_recurrent_of_toppled_locLegal {d : ℕ} {η u : Site d → ℤ}
    {A W : Set (Site d)} (n : ℕ) (hAW : A ⊆ W)
    (hzero : ∀ x ∈ A, x ≠ 0)
    (hu : u ∈ locLegal (fun x => η x + (n : ℤ) * dirac 0 x) W)
    (hpos : ∀ x ∈ A, 1 ≤ u x)
    (hstable : ∀ x ∈ A,
      lap u x + (η x + (n : ℤ) * dirac 0 x) ≤ 2 * (d : ℤ) - 1) :
    IsRecurrentFunction η A u := by
  have hr := isRecurrentFunction_of_toppled_locLegal hAW hu hpos hstable
  apply (isRecurrentFunction_congr_background (η := fun x => η x + (n : ℤ) * dirac 0 x)
    (η' := η) (A := A) (r := u) ?_).1 hr
  intro x hx
  simp [dirac, hzero x hx]

/-- Pointwise eventual limits of locally legal toppling functions retain
recurrent comparison on stabilized sites where the limit has toppled. -/
theorem isRecurrentFunction_of_eventually_toppled {d : ℕ}
    {η u : Site d → ℤ} {A W : Set (Site d)} (hAW : A ⊆ W)
    (v : ℕ → Site d → ℤ) (hv : ∀ t, v t ∈ locLegal η W)
    (hlim : ∀ x, ∀ᶠ t in atTop, v t x = u x)
    (hpos : ∀ x ∈ A, 1 ≤ u x)
    (hstable : ∀ x ∈ A, lap u x + η x ≤ 2 * (d : ℤ) - 1) :
    IsRecurrentFunction η A u := by
  apply isRecurrentFunction_of_noForbidden hstable
  intro E hEA hE hne
  have hevent : ∀ᶠ t in atTop, ∀ x ∈ dClosure E, v t x = u x :=
    (eventually_all_finite (dClosure_finite hE)).2 (fun x _ => hlim x)
  obtain ⟨t, ht⟩ := hevent.exists
  have hEpos : ∀ x ∈ E, 1 ≤ v t x := by
    intro x hx
    rw [ht x (mem_dClosure_of_mem hx)]
    exact hpos x (hEA hx)
  have hnf := toppledNoForbidden d E W η (v t) (hEA.trans hAW) (hv t) hEpos
  obtain ⟨x, hx, hxnf⟩ := hnf E (Set.Subset.rfl) hE hne
  refine ⟨x, hx, ?_⟩
  have hlap : lap (v t) x = lap u x := by
    simp only [lap, nbrSumZ, ht x (mem_dClosure_of_mem hx),
      ht _ (add_unit_mem_dClosure hx _), ht _ (sub_unit_mem_dClosure hx _)]
  simpa [hlap, add_comm] using hxnf

end RandomSandpile

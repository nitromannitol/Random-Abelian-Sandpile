import RandomSandpile.Proofs.Sec9.SingleSourceD2Critical
import RandomSandpile.Proofs.Sec3.RecurrentOfToppled
import RandomSandpile.Proofs.Sec5.StabilizingLegal

/-!
# Theorem 9.2 in dimension two: the recurrent minimum principle

D2-PROOF (1.5)-(1.6). If `s` is recurrent in a finite connected `A` and `D : ℤ² → ℤ` is any integer
function with `s + ΔD ≤ 3` in `A` (no sign condition), then `min_A D ≥ min_{∂A} D`
(`recurrent_minPrinciple`). Proof: shift `D` to be nonnegative on `Ā`; the legal stabilizing
function `u` with the same boundary values lies below it (least action,
`locLegalLeStabilizing`) and above its boundary minimum (Proposition 3.3, `burning`, recurrent
case).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter

namespace RandomSandpile

namespace SingleSourceD2

/-- **Recurrent minimum principle**. -/
theorem recurrent_minPrinciple {A : Set (Site 2)} (hA : A.Finite)
    (hconn : ((lattice 2).induce A).Connected) {s : Site 2 → ℤ} (hrec : IsRecurrentOn s A)
    {D : Site 2 → ℤ} (hD : ∀ x ∈ A, lap D x + s x ≤ 2 * (2 : ℤ) - 1) :
    ∀ x ∈ A, ∃ y ∈ bdry A, D y ≤ D x := by
  have hfinD : (dClosure A).Finite := dClosure_finite hA
  obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ y ∈ dClosure A, c ≤ D y := by
    obtain ⟨c, hc⟩ := (hfinD.image D).bddBelow
    exact ⟨c, fun y hy => hc ⟨y, hy, rfl⟩⟩
  obtain ⟨D', hD'def⟩ : ∃ D' : Site 2 → ℤ, D' = (dClosure A).indicator fun y => D y - c :=
    ⟨_, rfl⟩
  have hv : ∀ y ∈ dClosure A, D' y = D y - c := fun y hy => by
    rw [hD'def, Set.indicator_of_mem hy]
  have hD'T : IsTopplingFn A D' := by
    refine ⟨fun y => ?_, fun y hy => by rw [hD'def, Set.indicator_of_notMem hy]⟩
    by_cases hy : y ∈ dClosure A
    · rw [hv y hy]; linarith [hc y hy]
    · rw [hD'def, Set.indicator_of_notMem hy]
  have hD'lap : ∀ x ∈ A, lap D' x = lap D x := by
    intro x hx
    have hnb := fun i => Flat.mem_dClosure_of_nbr hx i
    simp only [lap, nbrSumZ, Fin.sum_univ_two]
    rw [hv _ (hnb 0).1, hv _ (hnb 0).2, hv _ (hnb 1).1, hv _ (hnb 1).2,
      hv _ (mem_dClosure_of_mem hx)]
    ring
  have hD'S : D' ∈ stabilizing s A := ⟨hD'T, fun x hx => by rw [hD'lap x hx]; exact hD x hx⟩
  obtain ⟨u, ⟨hL, hS⟩, hbd⟩ :=
    NearMaxSequence.exists_locLegal_stabilizing (by norm_num) hA s hD'T
  have hle : u ≤ D' := locLegalLeStabilizing 2 A s u D' hL hD'S fun x hx => (hbd x hx).symm
  have hb := (burning 2 le_rfl A hA hconn D' s u (fun y _ => hD'T.1 y) ⟨hL, hS⟩ hbd).2.1 hrec
  intro x hx
  obtain ⟨y, hy, hyle⟩ := hb x hx
  refine ⟨y, hy, ?_⟩
  have h1 : u x ≤ D' x := hle x
  have h2 := hv y (bdry_subset_dClosure A hy)
  have h3 := hv x (mem_dClosure_of_mem hx)
  omega

end SingleSourceD2

end RandomSandpile

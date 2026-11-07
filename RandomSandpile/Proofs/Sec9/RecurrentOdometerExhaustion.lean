import RandomSandpile.Proofs.Sec9.RecurrentToppledComparison
import RandomSandpile.Proofs.Sec9.OpenBoundaryMaxPrinciple
import LatticeProb.Sandpile.RadiusConsequences
import Mathlib.Data.Set.FiniteExhaustion

/-! # Legal exhaustion of a globally stabilizing odometer -/

open Filter LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

theorem IsLegal.mono_domain {d : ℕ} {η u : Site d → ℤ}
    {A B : Set (Site d)} (hu : IsLegal η A u) (hAB : A ⊆ B) : IsLegal η B u := by
  obtain ⟨n, xs, hx, hlegal, hsum⟩ := hu
  exact ⟨n, xs, fun i => hAB (hx i), hlegal, hsum⟩

/-- Open odometers increase when their finite domain increases. -/
theorem openOdometer_mono_domain {d : ℕ} (hd : 0 < d) (η : Site d → ℤ)
    {A B : Set (Site d)} (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B) :
    openOdometer η A ≤ openOdometer η B :=
  legalLeStabilizing d B η _ _
    ((OpenMaxPrinciple.openOdometer_isLegal hd hA η).mono_domain hAB)
    (OpenMaxPrinciple.openOdometer_mem_stabilizing hd hB η)

/-- Finite-volume legal odometers converge pointwise eventually to the global least
stabilizing toppling function. -/
theorem openOdometer_eventually_eq_of_isLeast {d : ℕ} (hd : 0 < d)
    {η u : Site d → ℤ} (hu : IsLeast (stabilizing η Set.univ) u)
    (W : Set.FiniteExhaustion (Set.univ : Set (Site d))) :
    ∀ x, ∀ᶠ n in atTop, openOdometer η (W n) x = u x := by
  classical
  let v : ℕ → Site d → ℤ := fun n => openOdometer η (W n)
  have hlegal : ∀ n, IsLegal η Set.univ (v n) := fun n =>
    (OpenMaxPrinciple.openOdometer_isLegal hd (W.finite n) η).mono_domain (Set.subset_univ _)
  have hle : ∀ n, v n ≤ u := fun n => legalLeStabilizing d Set.univ η _ _ (hlegal n) hu.1
  have hmono : ∀ x, Monotone (fun n => v n x) := fun x _ _ hmn =>
    openOdometer_mono_domain hd η (W.finite _) (W.finite _) (W.mono hmn) x
  have hconst : ∀ x, ∃ k, ∀ n, k ≤ n → v n x = v k x := fun x =>
    eventually_const_of_monotone_le (fun n => v n x) (hmono x) (u x) (fun n => hle n x)
  choose K hK using hconst
  let w : Site d → ℤ := fun x => v (K x) x
  have hlim : ∀ x, ∀ᶠ n in atTop, v n x = w x := fun x =>
    eventually_atTop.2 ⟨K x, fun n hn => hK x n hn⟩
  have hwle : w ≤ u := fun x => hle (K x) x
  have hwstab : w ∈ stabilizing η Set.univ := by
    apply mem_stabilizing_univ.2
    refine ⟨fun x => (hlegal (K x)).isTopplingFn.1 x, fun x => ?_⟩
    have he : ∀ᶠ n in atTop, ∀ z ∈ dClosure ({x} : Set (Site d)), v n z = w z :=
      (eventually_all_finite (dClosure_finite (Set.finite_singleton x))).2 (fun z _ => hlim z)
    have hx : ∃ n, x ∈ W n := Set.mem_iUnion.1 (W.iUnion_eq.symm ▸ Set.mem_univ x)
    obtain ⟨j, hj⟩ := hx
    have hew : ∀ᶠ n in atTop, x ∈ W n :=
      eventually_atTop.2 ⟨j, fun n hn => W.mono hn hj⟩
    obtain ⟨n, hn, hnx⟩ := (he.and hew).exists
    have hlap : lap (v n) x = lap w x := by
      have hmem : x ∈ ({x} : Set (Site d)) := Set.mem_singleton x
      simp only [lap, nbrSumZ, hn x (mem_dClosure_of_mem hmem),
        hn _ (add_unit_mem_dClosure hmem _), hn _ (sub_unit_mem_dClosure hmem _)]
    have hs := (OpenMaxPrinciple.openOdometer_mem_stabilizing hd (W.finite n) η).2 x hnx
    change lap (v n) x + η x ≤ 2 * (d : ℤ) - 1 at hs
    simpa only [hlap] using hs
  have hwu : w = u := le_antisymm hwle (hu.2 hwstab)
  simpa only [← hwu] using hlim

/-- A global least stabilizing toppling is recurrent on stabilized sites that toppled. -/
theorem isRecurrentFunction_of_isLeast_toppled {d : ℕ} (hd : 0 < d)
    {η u : Site d → ℤ} {A : Set (Site d)}
    (hu : IsLeast (stabilizing η Set.univ) u)
    (hpos : ∀ x ∈ A, 1 ≤ u x) : IsRecurrentFunction η A u := by
  let W := (Set.to_countable (Set.univ : Set (Site d))).finiteExhaustion
  apply isRecurrentFunction_of_eventually_toppled (Set.subset_univ A)
    (fun n => openOdometer η (W n))
  · intro n
    apply mem_locLegal_of_isLegal
    exact (OpenMaxPrinciple.openOdometer_isLegal hd (W.finite n) η).mono_domain
      (Set.subset_univ _)
  · exact openOdometer_eventually_eq_of_isLeast hd hu W
  · exact hpos
  · intro x hx
    exact (mem_stabilizing_univ.1 hu.1).2 x

/-- The single-source odometer is recurrent for the original background away
from the source, wherever it has toppled. -/
theorem singleSourceOdometer_recurrent_of_toppled {d : ℕ} (hd : 0 < d)
    {η : Site d → ℤ} (n : ℕ) {A : Set (Site d)}
    (hne : (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty)
    (hzero : ∀ x ∈ A, x ≠ 0)
    (hpos : ∀ x ∈ A, 1 ≤ singleSourceOdometer η n x) :
    IsRecurrentFunction η A (singleSourceOdometer η n) := by
  have hr := isRecurrentFunction_of_isLeast_toppled hd (isLeast_singleSourceOdometer hne) hpos
  apply (isRecurrentFunction_congr_background
    (η := fun x => η x + (n : ℤ) * dirac 0 x) (η' := η)
    (A := A) (r := singleSourceOdometer η n) ?_).1 hr
  intro x hx
  simp [dirac, hzero x hx]

end RandomSandpile

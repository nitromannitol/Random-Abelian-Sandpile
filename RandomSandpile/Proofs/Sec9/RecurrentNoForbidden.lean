import RandomSandpile.Proofs.Sec9.RecurrentMuEquality

/-! Recurrent comparison and forbidden subconfigurations. -/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- Recurrent comparison rules out forbidden subconfigurations in the final sandpile. -/
theorem IsRecurrentFunction.noForbiddenSubconfig {η r : Site d → ℤ} {A : Set (Site d)}
    (hr : IsRecurrentFunction η A r) :
    NoForbiddenSubconfig (fun x => η x + lap r x) A := by
  classical
  intro E hEA hE hne
  by_contra hbad
  push Not at hbad
  let i : Site d → ℤ := E.indicator fun _ => 1
  let w : Site d → ℤ := fun z => r z - i z
  have hw : ∀ z ∈ E, lap w z + η z ≤ 2 * (d : ℤ) - 1 := by
    intro z hz
    dsimp [w]
    rw [Burning.lap_sub_apply']
    have h := hbad z hz
    change η z + lap r z - lap i z < 2 * (d : ℤ) at h
    omega
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hxy⟩ := hr.2 E hE ⟨x, hx⟩ hEA w hw x hx
  have hix : i x = 1 := by simp [i, hx]
  have hiy : i y = 0 := by simp [i, (mem_bdry.mp hy).1]
  dsimp [w] at hxy
  omega

/-- The absence of forbidden subconfigurations also implies recurrent comparison
for a stabilizing function. -/
theorem isRecurrentFunction_of_noForbidden {η r : Site d → ℤ} {A : Set (Site d)}
    (hr : ∀ x ∈ A, lap r x + η x ≤ 2 * (d : ℤ) - 1)
    (hnf : NoForbiddenSubconfig (fun x => η x + lap r x) A) :
    IsRecurrentFunction η A r := by
  refine ⟨hr, ?_⟩
  intro E hE hne hEA w hw x hx
  have hs : ∀ z ∈ E, lap (fun y => w y - r y) z +
      (η z + lap r z) ≤ 2 * (d : ℤ) - 1 := by
    intro z hz
    rw [Burning.lap_sub_apply']
    linarith [hw z hz]
  obtain ⟨y, hy, hxy⟩ := supersolutionMinPrinciple d E hE
    (fun z => η z + lap r z) (fun z => w z - r z) (hnf.subset hEA) hs x hx
  exact ⟨y, hy, by omega⟩

/-- A recurrent stabilized configuration has nonnegative height. -/
theorem IsRecurrentFunction.height_nonneg {η r : Site d → ℤ} {A : Set (Site d)}
    (hr : IsRecurrentFunction η A r) {x : Site d} (hx : x ∈ A) :
    0 ≤ η x + lap r x := by
  have hnf := hr.noForbiddenSubconfig
  have hset : ({x} : Set (Site d)) ⊆ A := by simpa using hx
  obtain ⟨z, hz, h⟩ := hnf {x} hset (Set.finite_singleton x) (Set.singleton_nonempty x)
  have hzx : z = x := Set.mem_singleton_iff.mp hz
  subst z
  have hi : ({x} : Set (Site d)).indicator (fun _ => (1 : ℤ)) = dirac x := by
    funext y
    by_cases hy : y = x <;> simp [hy, dirac]
  rw [hi] at h
  have hplus (i : Fin d) : x + unit i ≠ x := (Burning.self_ne_add_unit x i).symm
  have hminus (i : Fin d) : x - unit i ≠ x := by
    intro heq
    have hu : unit i = 0 := by
      have := congrArg (fun z : Site d => z - x) heq
      simpa using this
    exact unit_ne_zero i hu
  have hlap : lap (dirac x) x = -(2 * (d : ℤ)) := by
    simp [lap, nbrSumZ, dirac_of_ne (hplus _), dirac_of_ne (hminus _)]
  rw [hlap] at h
  dsimp only at h
  omega

end RandomSandpile

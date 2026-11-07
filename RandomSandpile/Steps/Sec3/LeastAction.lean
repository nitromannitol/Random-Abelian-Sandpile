import RandomSandpile.Draft.Section3

/-!
# Steps of Proposition 3.1 (least action principle)

Carving of `RandomSandpile.LeastActionStmt` (Proposition 3.1, `paper/random_piles-corrected.tex`) into two steps, and the reduction `leastAction_of_steps`.

* `LegalLeStabilizingStmt` (the least action principle of Fey-Levine-Peres, sequential form): a
  legal toppling function for `η` in `A` lies below every stabilizing toppling function for `η` in
  `A`. Lattice-Probability's `LatticeProb.Sandpile.le_of_isLegalToppling` is the parallel-time,
  whole-space version.
* `ExistsLegalStabilizingStmt`: for finite `A` (and `d ≥ 1`) some toppling function is both legal
  and stabilizing for `η` in `A` ("topple unstable sites of `A` until stable").

Assembly (`leastAction_of_steps`): a locally legal toppling function vanishing on `∂A` is legal
for `η` in `A` (`isLegal_of_mem_locLegal`), and a legal one is locally legal and vanishes on `∂A`
(`mem_locLegal_of_isLegal`, `IsLegal.eq_zero_of_notMem`). The legal stabilizing `v` of the second
step is then the greatest element of the first set and the least element of the second set of
Proposition 3.1, by the first step, and the unique legal stabilizing toppling function vanishing on
`∂A` by antisymmetry. Connectedness of `A` is not used.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Step 1 of Proposition 3.1, the least action principle: if `u` is legal for `η`
in `A` and `v ∈ 𝓢(η, A)` is stabilizing for `η` in `A`, then `u ≤ v`. No finiteness of `A` is
needed. -/
def LegalLeStabilizingStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)) (η u v : Site d → ℤ), IsLegal η A u → v ∈ stabilizing η A → u ≤ v

/-- Step 2 of Proposition 3.1: for `d ≥ 1` and finite `A`, some toppling function `v` is legal and
stabilizing for `η` in `A`. -/
def ExistsLegalStabilizingStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (A : Set (Site d)), A.Finite → ∀ η : Site d → ℤ,
    ∃ v : Site d → ℤ, IsLegal η A v ∧ v ∈ stabilizing η A

variable {d : ℕ}

/-- The Laplacian of the zero function vanishes. -/
theorem lap_zero_apply (x : Site d) : lap (0 : Site d → ℤ) x = 0 := by
  simp [lap, nbrSumZ]

/-- A legal toppling function for `η` in `A` vanishes off `A`. -/
theorem IsLegal.eq_zero_of_notMem {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (hu : IsLegal η A u) {x : Site d} (hx : x ∉ A) : u x = 0 := by
  obtain ⟨n, xs, hA, -, rfl⟩ := hu
  exact Finset.sum_eq_zero fun i _ => dirac_of_ne fun h => hx (h ▸ hA i)

/-- A legal toppling function for `η` in `A` is locally legal for `η` in `A` (with `w = 0`). -/
theorem mem_locLegal_of_isLegal {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (hu : IsLegal η A u) : u ∈ locLegal η A := by
  have hη : (fun y => lap (0 : Site d → ℤ) y + η y) = η := funext fun y => by
    simp [lap_zero_apply]
  refine ⟨0, u, ⟨fun _ => le_rfl, fun _ _ => rfl⟩, hu.isTopplingFn, (zero_add u).symm,
    fun _ _ => rfl, fun y hy => hu.eq_zero_of_notMem (Set.disjoint_right.1 (bdry_disjoint A) hy),
    ?_⟩
  rw [hη]; exact hu

/-- A locally legal toppling function for `η` in `A` vanishing on `∂A` is legal for `η` in `A`:
its boundary part `w` vanishes on `Ā`, hence everywhere. -/
theorem isLegal_of_mem_locLegal {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (hu : u ∈ locLegal η A) (hb : ∀ y ∈ bdry A, u y = 0) : IsLegal η A u := by
  obtain ⟨w, uh, hw, -, rfl, hwA, huhB, hleg⟩ := hu
  have hw0 : w = 0 := by
    funext x
    by_cases hxA : x ∈ A
    · exact hwA x hxA
    by_cases hxB : x ∈ bdry A
    · have h := hb x hxB
      simp only [Pi.add_apply, huhB x hxB, add_zero] at h
      exact h
    · exact hw.2 x fun h => (Set.mem_union _ _ _).1 h |>.elim hxA hxB
  subst hw0
  have hη : (fun y => lap (0 : Site d → ℤ) y + η y) = η := funext fun y => by
    simp [lap_zero_apply]
  rw [hη] at hleg
  rwa [zero_add]

/-- **Reduction of Proposition 3.1** to its two steps. -/
theorem leastAction_of_steps (h1 : LegalLeStabilizingStmt) (h2 : ExistsLegalStabilizingStmt) :
    LeastActionStmt := by
  intro d hd A hA _ η
  obtain ⟨v, hvL, hvS⟩ := h2 d (by omega) A hA η
  have hvB : ∀ y ∈ bdry A, v y = 0 := fun y hy =>
    hvL.eq_zero_of_notMem (Set.disjoint_right.1 (bdry_disjoint A) hy)
  have hvLoc : v ∈ locLegal η A := mem_locLegal_of_isLegal hvL
  -- every locally legal `w` vanishing on `∂A` is below `v`
  have hle : ∀ w, w ∈ locLegal η A → (∀ y ∈ bdry A, w y = 0) → w ≤ v := fun w hw hwB =>
    h1 d A η w v (isLegal_of_mem_locLegal hw hwB) hvS
  -- `v` is below every stabilizing `u`
  have hge : ∀ u, u ∈ stabilizing η A → v ≤ u := fun u hu => h1 d A η v u hvL hu
  refine ⟨v, ⟨⟨hvLoc, hvB⟩, fun w hw => hle w hw.1 hw.2⟩, ⟨⟨hvS, hvB⟩, fun u hu => hge u hu.1⟩,
    ⟨⟨hvLoc, hvS⟩, hvB⟩, fun v' hv' hv'B => le_antisymm (hle v' hv'.1 hv'B) (hge v' hv'.2)⟩

end RandomSandpile

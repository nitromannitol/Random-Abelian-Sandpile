import RandomSandpile.Steps.Sec5.MuConvergence

/-!
# Lemma 5.5, Steps 1a, 1b and 3: restriction and locality of `𝓛(η, A)` and `𝓢(η, A)`

* `locLegalRestrict` (Step 1a): for `B ⊆ A` and `u = w + û ∈ 𝓛(η, A)`, the
  restriction of `u` to `B̄` decomposes as `w_B + û_B` with `w_B = u` on `∂B` (boundary topplings of
  `B`, performed first) and `û_B = û` on `B`. The legal topplings of `û` at sites of `B`, in their
  original order, stay legal for `Δ_{ℤ^d} w_B + η`: at such a site the configuration has the same
  number of topplings, the neighbours in `B` have toppled as often, and the neighbours on `∂B` have
  already received all of their topplings (`legal_restrict`).
* `stabilizingRestrict` (Step 1b): the Laplacian at a site of `B` only sees `B̄`.
* `locLegalLocal` (Step 3): legality is only tested at sites of `A`.
-/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

private theorem dirac_nonneg_aux (z x : Site d) : 0 ≤ dirac z x := by
  unfold dirac; split_ifs <;> norm_num

/-- The Laplacian at `x` is monotone in the values at the `2d` neighbours of `x`, among functions
that agree at `x`. -/
theorem lap_le_lap_of_le_nbr {u v : Site d → ℤ} {x : Site d} (hx : u x = v x)
    (h : ∀ i, u (x + unit i) ≤ v (x + unit i) ∧ u (x - unit i) ≤ v (x - unit i)) :
    lap u x ≤ lap v x := by
  rw [lap, lap, nbrSumZ, nbrSumZ, hx]
  linarith [Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => add_le_add (h i).1 (h i).2]

/-- The Laplacian at a site `x ∈ B` only depends on the values on `B̄`. -/
theorem lap_eq_of_eqOn_dClosure {u v : Site d → ℤ} {B : Set (Site d)}
    (h : ∀ y ∈ dClosure B, u y = v y) {x : Site d} (hx : x ∈ B) : lap u x = lap v x :=
  le_antisymm
    (lap_le_lap_of_le_nbr (h x (subset_dClosure B hx)) fun i =>
      ⟨(h _ (add_unit_mem_dClosure hx i)).le, (h _ (sub_unit_mem_dClosure hx i)).le⟩)
    (lap_le_lap_of_le_nbr (h x (subset_dClosure B hx)).symm fun i =>
      ⟨(h _ (add_unit_mem_dClosure hx i)).ge, (h _ (sub_unit_mem_dClosure hx i)).ge⟩)

/-- A neighbour of a site of `B` lies in `B` or in `∂B`. -/
theorem mem_or_mem_bdry_of_mem_dClosure {B : Set (Site d)} {y : Site d} (hy : y ∈ dClosure B) :
    y ∈ B ∨ y ∈ bdry B := by
  rwa [dClosure_eq] at hy

/-- The core of Step 1a. Let `B ⊆ A`, let `w` vanish on `A` and let `v` be legal for
`Δ_{ℤ^d} w + η` in `A`. For every nonnegative `g` vanishing on `B` with `g ≥ w + v` on `∂B`, the
restriction `1_B v` is legal for `Δ_{ℤ^d} g + η` in `B`. -/
theorem legal_restrict {η : Site d → ℤ} {A B : Set (Site d)} (hBA : B ⊆ A) {w : Site d → ℤ}
    (hw : ∀ x ∈ A, w x = 0) {v : Site d → ℤ} (hv : IsLegal (fun y => lap w y + η y) A v) :
    ∀ g : Site d → ℤ, (∀ y, 0 ≤ g y) → (∀ y ∈ B, g y = 0) → (∀ y ∈ bdry B, w y + v y ≤ g y) →
      IsLegal (fun y => lap g y + η y) B (B.indicator v) := by
  refine IsLegal.induction (fun v => ∀ g : Site d → ℤ, (∀ y, 0 ≤ g y) → (∀ y ∈ B, g y = 0) →
      (∀ y ∈ bdry B, w y + v y ≤ g y) → IsLegal (fun y => lap g y + η y) B (B.indicator v))
    (fun g _ _ _ => by simpa using IsLegal.zero _ B) ?_ hv
  intro v x hvleg ih hxA hx g hg0 hgB hgbd
  have hv0 : ∀ y, 0 ≤ v y := hvleg.isTopplingFn.1
  have hIH := ih g hg0 hgB fun y hy =>
    (le_add_of_nonneg_right (dirac_nonneg_aux x y)).trans (by simpa [add_assoc] using hgbd y hy)
  by_cases hxB : x ∈ B
  · have hind : B.indicator (v + dirac x) = B.indicator v + dirac x := by
      funext z
      by_cases hz : z ∈ B
      · simp [Set.indicator_of_mem hz]
      · have hzx : z ≠ x := fun h => hz (h ▸ hxB)
        simp [Set.indicator_of_notMem hz, dirac_of_ne hzx]
    rw [hind]
    refine hIH.snoc hxB ?_
    -- compare `v + w` with `1_B v + g` around `x`
    have hcmp : lap (v + w) x ≤ lap (B.indicator v + g) x := by
      have hnb : ∀ y ∈ dClosure B, (v + w) y ≤ (B.indicator v + g) y := by
        intro y hy
        rcases mem_or_mem_bdry_of_mem_dClosure hy with hyB | hyB
        · simp [Set.indicator_of_mem hyB, hw y (hBA hyB), hgB y hyB]
        · have := hgbd y hyB
          simp only [Pi.add_apply] at this
          simp only [Pi.add_apply, Set.indicator_of_notMem hyB.1, zero_add]
          linarith [dirac_nonneg_aux x y]
      refine lap_le_lap_of_le_nbr ?_ fun i =>
        ⟨hnb _ (add_unit_mem_dClosure hxB i), hnb _ (sub_unit_mem_dClosure hxB i)⟩
      simp [Set.indicator_of_mem hxB, hw x hxA, hgB x hxB]
    rw [lap_add', lap_add'] at hcmp
    beta_reduce at hx ⊢
    linarith
  · have hind : B.indicator (v + dirac x) = B.indicator v := by
      funext z
      by_cases hz : z ∈ B
      · have hzx : z ≠ x := fun h => hxB (h ▸ hz)
        simp [Set.indicator_of_mem hz, dirac_of_ne hzx]
      · simp [Set.indicator_of_notMem hz]
    rw [hind]
    exact hIH

/-- **Step 1a**: restriction of a locally legal toppling to a subdomain. -/
theorem locLegalRestrict : LocLegalRestrictStmt := by
  intro d η A B u hBA hu
  obtain ⟨w, uh, hwT, huhT, rfl, hwA, huhbd, hleg⟩ := hu
  have hu0 : ∀ y, 0 ≤ (w + uh) y := fun y => add_nonneg (hwT.1 y) (huhT.1 y)
  refine ⟨(bdry B).indicator (w + uh), B.indicator uh, ⟨fun y => ?_, fun y hy => ?_⟩,
    ⟨fun y => ?_, fun y hy => ?_⟩, ?_, fun y hy => ?_, fun y hy => ?_, ?_⟩
  · exact Set.indicator_nonneg (fun z _ => hu0 z) y
  · exact Set.indicator_of_notMem (fun h => hy (bdry_subset_dClosure B h)) _
  · exact Set.indicator_nonneg (fun z _ => huhT.1 z) y
  · exact Set.indicator_of_notMem (fun h => hy (subset_dClosure B h)) _
  · funext z
    by_cases hzB : z ∈ B
    · have hzbd : z ∉ bdry B := fun h => h.1 hzB
      simp [Set.indicator_of_mem (subset_dClosure B hzB), Set.indicator_of_mem hzB,
        Set.indicator_of_notMem hzbd, hwA z (hBA hzB)]
    · by_cases hzbd : z ∈ bdry B
      · simp [Set.indicator_of_mem (bdry_subset_dClosure B hzbd), Set.indicator_of_mem hzbd,
          Set.indicator_of_notMem hzB]
      · have hzc : z ∉ dClosure B := by
          rw [dClosure_eq]; exact fun h => h.elim hzB hzbd
        simp [Set.indicator_of_notMem hzc, Set.indicator_of_notMem hzB,
          Set.indicator_of_notMem hzbd]
  · exact Set.indicator_of_notMem (fun h => h.1 hy) _
  · exact Set.indicator_of_notMem hy.1 _
  · refine legal_restrict hBA hwA hleg _ (Set.indicator_nonneg fun z _ => hu0 z)
      (fun y hy => Set.indicator_of_notMem (fun h => h.1 hy) _) fun y hy => ?_
    simp [Set.indicator_of_mem hy]

/-- **Step 1b**: restriction of a stabilizing toppling to a subdomain. -/
theorem stabilizingRestrict : StabilizingRestrictStmt := by
  intro d η A B v hBA hv
  refine ⟨⟨fun y => Set.indicator_nonneg (fun z _ => hv.1.1 z) y,
    fun y hy => Set.indicator_of_notMem hy _⟩, fun x hx => ?_⟩
  rw [lap_eq_of_eqOn_dClosure (v := v) (fun y hy => Set.indicator_of_mem hy _) hx]
  exact hv.2 x (hBA hx)

/-- Legality in `A` only tests the configuration at sites of `A`. -/
theorem IsLegal.congr_config {ξ ξ' : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (h : ∀ x ∈ A, ξ x = ξ' x) (hu : IsLegal ξ A u) : IsLegal ξ' A u := by
  obtain ⟨n, xs, hA, hleg, rfl⟩ := hu
  exact ⟨n, xs, hA, fun i => (h _ (hA i)) ▸ hleg i, rfl⟩

/-- **Step 3** (locality): `𝓛(η, A)` and `𝓢(η, A)` only depend on `η` restricted to `A`. -/
theorem locLegalLocal : LocLegalLocalStmt := by
  have key : ∀ (d : ℕ) (η η' : Site d → ℤ) (A : Set (Site d)), (∀ x ∈ A, η x = η' x) →
      locLegal η A ⊆ locLegal η' A ∧ stabilizing η A ⊆ stabilizing η' A := by
    intro d η η' A h
    refine ⟨fun u ⟨w, uh, h1, h2, h3, h4, h5, h6⟩ => ⟨w, uh, h1, h2, h3, h4, h5,
      h6.congr_config fun x hx => by simp only [h x hx]⟩, fun v ⟨h1, h2⟩ =>
      ⟨h1, fun x hx => h x hx ▸ h2 x hx⟩⟩
  intro d η η' A h
  have h' : ∀ x ∈ A, η' x = η x := fun x hx => (h x hx).symm
  exact ⟨(key d η η' A h).1.antisymm (key d η' η A h').1,
    (key d η η' A h).2.antisymm (key d η' η A h').2⟩

end RandomSandpile

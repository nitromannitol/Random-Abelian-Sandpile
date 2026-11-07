import RandomSandpile.Proofs.Sec9.RecurrentShift
import RandomSandpile.Infra.ConcaveEnvelope
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTranslates

/-! A least signed fixed-boundary stabilizer satisfies recurrent comparison. -/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

noncomputable def patchMin (E : Set (Site d)) (r w : Site d → ℤ) : Site d → ℤ := by
  classical
  exact fun z => if z ∈ E then min (r z) (w z) else r z

/-- Patching a smaller stabilizer across a boundary where it dominates preserves stability. -/
theorem stabilizing_patch_min {η r w : Site d → ℤ} {A E : Set (Site d)}
    (hr : ∀ x ∈ A, lap r x + η x ≤ 2 * (d : ℤ) - 1)
    (hw : ∀ x ∈ E, lap w x + η x ≤ 2 * (d : ℤ) - 1)
    (hbd : ∀ y ∈ bdry E, r y ≤ w y) :
    ∀ x ∈ A, lap (patchMin E r w) x + η x ≤
      2 * (d : ℤ) - 1 := by
  classical
  let p : Site d → ℤ := patchMin E r w
  have hpr : ∀ z, p z ≤ r z := by
    intro z
    dsimp [p, patchMin]
    split_ifs <;> simp
  have hpw : ∀ z ∈ dClosure E, p z ≤ w z := by
    intro z hz
    rw [dClosure_eq] at hz
    by_cases hzE : z ∈ E
    · simp [p, patchMin, hzE]
    · have hzb : z ∈ bdry E := hz.resolve_left hzE
      simpa [p, patchMin, hzE] using hbd z hzb
  intro x hx
  change lap p x + η x ≤ _
  by_cases hxE : x ∈ E
  · by_cases h : w x ≤ r x
    · have hpx : p x = w x := by simp [p, patchMin, hxE, min_eq_right h]
      have hl := PegdenSmartRegularity.lap_le_lap_of_nbr hpx fun i =>
        ⟨hpw _ (by simpa [dClosure_eq] using Burning.add_unit_mem hxE i),
         hpw _ (by simpa [dClosure_eq] using Burning.sub_unit_mem hxE i)⟩
      linarith [hw x hxE]
    · have hpx : p x = r x := by simp [p, patchMin, hxE, min_eq_left (not_le.mp h).le]
      have hl := lap_le_lap_of_le hpr hpx
      linarith [hr x hx]
  · have hpx : p x = r x := by simp [p, patchMin, hxE]
    have hl := lap_le_lap_of_le hpr hpx
    linarith [hr x hx]

/-- The least signed stabilizer with prescribed boundary values is recurrent. -/
theorem recurrent_of_least_fixed_boundary (hd : 0 < d) {η r : Site d → ℤ}
    {A : Set (Site d)}
    (hr : ∀ x ∈ A, lap r x + η x ≤ 2 * (d : ℤ) - 1)
    (hleast : ∀ w : Site d → ℤ, (∀ y ∈ bdry A, w y = r y) →
      (∀ x ∈ A, lap w x + η x ≤ 2 * (d : ℤ) - 1) → ∀ x ∈ A, r x ≤ w x) :
    IsRecurrentFunction η A r := by
  classical
  refine ⟨hr, ?_⟩
  intro E hE hne hEA w hw x hx
  have hfin : (bdry E).Finite := (dClosure_finite hE).subset (bdry_subset_dClosure E)
  obtain ⟨y, hy, hymax⟩ := Set.exists_max_image (bdry E) (fun z => r z - w z)
    hfin (Burning.bdry_nonempty hd hE hne)
  let c : ℤ := r y - w y
  let w' : Site d → ℤ := fun z => w z + c
  have hbd : ∀ z ∈ bdry E, r z ≤ w' z := by
    intro z hz
    have h := hymax z hz
    dsimp [w', c]
    omega
  have hw' : ∀ z ∈ E, lap w' z + η z ≤ 2 * (d : ℤ) - 1 := by
    intro z hz
    dsimp [w']
    rw [PegdenSmartRegularity.lap_add_const]
    exact hw z hz
  let p : Site d → ℤ := patchMin E r w'
  have hpbd : ∀ z ∈ bdry A, p z = r z := by
    intro z hz
    have hzE : z ∉ E := fun hzE => (mem_bdry.mp hz).1 (hEA hzE)
    simp [p, patchMin, hzE]
  have hp : ∀ z ∈ A, lap p z + η z ≤ 2 * (d : ℤ) - 1 :=
    stabilizing_patch_min hr hw' hbd
  have hle := hleast p hpbd hp x (hEA hx)
  have hpx : p x ≤ w' x := by simp [p, patchMin, hx]
  refine ⟨y, hy, ?_⟩
  dsimp [w', c] at hpx
  omega

end RandomSandpile

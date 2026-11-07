import RandomSandpile.Proofs.Sec9.RecurrentInf
import RandomSandpile.Proofs.Sec3.RecurrentOfToppled
import RandomSandpile.Proofs.Sec7.OdometerLowerBound
import RandomSandpile.Steps.Sec9.RecurrentHomogenization

/-! Finite-domain lower bounds and fixed-boundary recurrentization. -/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- The finite-domain barrier bounds signed fixed-boundary stabilizers below. -/
theorem fixed_boundary_stabilizers_bdd (hd : 0 < d) {η v : Site d → ℤ}
    {A : Set (Site d)} (hA : A.Finite) :
    ∀ x ∈ A, ∃ b : ℤ, ∀ w : Site d → ℤ,
      (∀ y ∈ bdry A, w y = v y) →
      (∀ y ∈ A, lap w y + η y ≤ 2 * (d : ℤ) - 1) → b ≤ w x := by
  have hbdFin : (bdry A).Finite := (dClosure_finite hA).subset (bdry_subset_dClosure A)
  obtain ⟨m, hm⟩ := (hA.image η).bddBelow
  obtain ⟨k, hk⟩ := (hbdFin.image v).bddBelow
  let C : ℤ := max 0 (2 * (d : ℤ) - 1 - m)
  have hC : 0 ≤ C := le_max_left _ _
  obtain ⟨φ, _, hφoff, hφlap⟩ := superharmonicBarrier d hd A hA C hC
  intro x hx
  refine ⟨k - φ x, ?_⟩
  intro w hwbd hw
  have hsuper : ∀ z ∈ A, lapR (fun z => ((w z + φ z : ℤ) : ℝ)) z ≤ 0 := by
    intro z hz
    rw [lapR_intCast, Burning.lap_add_apply']
    have hη := hm (Set.mem_image_of_mem η hz)
    have hcomp := le_max_right 0 (2 * (d : ℤ) - 1 - m)
    have hl := hφlap z hz
    have hs := hw z hz
    have hi : lap w z + lap φ z ≤ 0 := by dsimp [C] at *; omega
    exact_mod_cast hi
  obtain ⟨y, hy, hxy⟩ := superharmonicMinPrinciple d hd A hA
    (fun z => ((w z + φ z : ℤ) : ℝ)) hsuper x hx
  have hφy : φ y = 0 := hφoff y ((mem_bdry.mp hy).1)
  have hky := hk (Set.mem_image_of_mem v hy)
  rw [hwbd y hy, hφy, add_zero] at hxy
  have hxy' : v y ≤ w x + φ x := by exact_mod_cast hxy
  omega

/-- Fixed-boundary recurrentization on every finite lattice domain. -/
theorem recurrentizeFixedBoundary : RecurrentizeFixedBoundaryStmt := by
  intro d hd A hA η v hv
  obtain ⟨r, hrs, hrbd, hrleast⟩ :=
    exists_least_stabilizer_of_pointwise_bdd hv (fixed_boundary_stabilizers_bdd (by omega) hA)
  have hrr : IsRecurrentFunction η A r := by
    apply recurrent_of_least_fixed_boundary (by omega) hrs
    intro w hwbd hw x hx
    apply hrleast w ?_ hw x hx
    intro y hy
    rw [hwbd y hy, hrbd y hy]
  exact ⟨r, hrr, hrbd, hrleast⟩

end RandomSandpile

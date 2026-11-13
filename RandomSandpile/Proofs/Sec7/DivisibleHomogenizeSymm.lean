import RandomSandpile.Defs.Green

/-!
# Symmetry of the killed Green's function and the Poisson equation in the second variable

For finite `A ⊂ ℤ^d`, `d ≥ 1`: `g_A(x, y) = g_A(y, x)` (Lattice-Probability's
`Network.killedGreenReal_symm`), hence `Δ_{ℤ^d} g_A(x, ·)(w) = -1{w = x}` for `w ∈ A`. Used for
the (difference) estimate of Lemma 7.3 (`paper/random_piles-corrected.tex`), where
`g_n(x, ·)` is harmonic on balls avoiding `x` and `∂B_n`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

variable {d : ℕ}

namespace DivisibleHomogenize

/-- The killed Green's function of a finite set is symmetric. -/
theorem greenKilled_symm (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) (x y : Site d) :
    greenKilled A x y = greenKilled A y x := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨B, rfl⟩ := hA.exists_finset_coe
  obtain ⟨q, hq⟩ := exists_not_mem_finset hd B
  exact Network.killedGreenReal_symm (Graph.Zd.latticeConnected d) B hq x y

/-- **The Poisson equation in the second variable**: `Δ_{ℤ^d} g_A(x, ·)(w) = -1{w = x}` for
`w ∈ A`. -/
theorem lapR_greenKilled_right (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) (x : Site d)
    {w : Site d} (hw : w ∈ A) :
    lapR (fun z => greenKilled A x z) w = -(if w = x then 1 else 0) := by
  have h : (fun z => greenKilled A x z) = fun z => greenKilled A z x :=
    funext fun z => greenKilled_symm hd hA x z
  rw [h]
  exact lapR_greenKilled hd hA hw x

end DivisibleHomogenize

end RandomSandpile

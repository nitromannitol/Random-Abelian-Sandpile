import RandomSandpile.Steps.Sec3.Abelian
import RandomSandpile.Proofs.Sec3.Burning

/-!
# Proof of Proposition 3.2 (Abelian decomposition)

Proofs of the steps of `RandomSandpile/Steps/Sec3/Abelian.lean` and of
`RandomSandpile.AbelianDecompositionStmt`. All proofs are by induction on legal toppling functions
(`IsLegal.induction`, appending one toppling at a time), so no reordering of toppling sequences is
needed.

* `legalMono`: appending a toppling at `x` keeps it legal for `η'`, as `η x ≤ η' x` at a toppled
  site `x`.
* `IsLegal.sub_dirac` (front removal): if `c` is legal for `η`, `y` is unstable in `η` and `c`
  topples `y`, then `c - 1_y` is legal for `η + Δ_{ℤ^d} 1_y`. If the last toppling `x` of `c` is
  not the only toppling at `y`, append `x` to the induction hypothesis; otherwise `x = y` and the
  remaining topplings avoid `y`, where `Δ_{ℤ^d} 1_y ≥ 0`, so `legalMono` applies.
* `abelianProperty`: induction on `a`, removing its topplings from the front of `b` one by one.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- **Step 1 of Proposition 3.2**: adding chips at the toppled sites preserves legality. -/
theorem legalMono : LegalMonoStmt := by
  intro d A η η' u hu
  refine IsLegal.induction (fun u => (∀ x ∈ A, 1 ≤ u x → η x ≤ η' x) → IsLegal η' A u)
    (fun _ => IsLegal.zero η' A) ?_ hu
  intro u x hu' ih hxA hx h
  have hu0 : ∀ y, 0 ≤ u y := hu'.isTopplingFn.1
  have ih' := ih fun y hy h1 => h y hy (by
    have := Burning.dirac_nonneg' x y
    simp only [Pi.add_apply]; linarith)
  refine ih'.snoc hxA ?_
  have := h x hxA (by simp only [Pi.add_apply, dirac_self]; linarith [hu0 x])
  linarith

/-- Front removal of a toppling: if `c` is legal for `η` in `A`, the site `y` is unstable in `η`
and `c` topples `y`, then `c - 1_y` is legal for `η + Δ_{ℤ^d} 1_y` in `A`. -/
theorem IsLegal.sub_dirac {η : Site d → ℤ} {A : Set (Site d)} {c : Site d → ℤ} {y : Site d}
    (hc : IsLegal η A c) (hy : 2 * (d : ℤ) ≤ η y) (h1 : 1 ≤ c y) :
    IsLegal (fun x => η x + lap (dirac y) x) A (c - dirac y) := by
  revert h1
  refine IsLegal.induction
    (fun c => 1 ≤ c y → IsLegal (fun x => η x + lap (dirac y) x) A (c - dirac y))
    (fun h => absurd h (by simp)) ?_ hc
  intro c x hc' ih hxA hx h1
  have hc0 : ∀ z, 0 ≤ c z := hc'.isTopplingFn.1
  by_cases hcy : 1 ≤ c y
  · have h := (ih hcy).snoc hxA (x := x) (by
      show 2 * (d : ℤ) ≤ lap (c - dirac y) x + (η x + lap (dirac y) x)
      rw [Abelian.lap_pi_sub_apply]
      linarith)
    convert h using 1
    funext z
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · have hxy : x = y := by
      by_contra hne
      simp only [Pi.add_apply, dirac_of_ne (Ne.symm hne)] at h1
      omega
    subst hxy
    have hcx : c x = 0 := by have := hc0 x; omega
    have he : c + dirac x - dirac x = c := by funext z; simp
    rw [he]
    refine legalMono d A η _ c hc' fun z _ hz1 => ?_
    have hzx : z ≠ x := fun h => by subst h; omega
    have h0 := lap_le_lap_of_le (u := 0) (w := dirac x) (fun y => Burning.dirac_nonneg' x y)
      (x := z) (by simp [dirac_of_ne hzx])
    rw [lap_zero_apply] at h0
    show η z ≤ η z + lap (dirac x) z
    linarith

/-- **Step 2 of Proposition 3.2**, the Abelian property: if `a ≤ b` are legal for `η` in `A`, then
`b - a` is legal for `η + Δ_{ℤ^d} a` in `A`. -/
theorem abelianProperty : AbelianPropertyStmt := by
  intro d A η a b ha
  revert b
  refine IsLegal.induction
    (fun a => ∀ b, IsLegal η A b → a ≤ b → IsLegal (fun x => η x + lap a x) A (b - a)) ?_ ?_ ha
  · intro b hb _
    have he : (fun x => η x + lap (0 : Site d → ℤ) x) = η := funext fun x => by
      simp [lap_zero_apply]
    rw [he, sub_zero]
    exact hb
  · intro a y _ ih hyA hy b hb hab
    have hab' : a ≤ b := fun z => le_trans
      (by simp only [Pi.add_apply]; linarith [Burning.dirac_nonneg' y z]) (hab z)
    have h := (ih b hb hab').sub_dirac (y := y)
      (by show 2 * (d : ℤ) ≤ η y + lap a y; linarith)
      (by
        have := hab y
        simp only [Pi.add_apply, Pi.sub_apply, dirac_self] at this ⊢
        linarith)
    convert h using 1
    · funext x
      rw [Burning.lap_pi_add_apply]
      ring
    · funext x
      simp only [Pi.sub_apply, Pi.add_apply]
      ring

/-- **Proposition 3.2** (Abelian). -/
theorem abelianDecomposition : AbelianDecompositionStmt :=
  abelianDecomposition_of_steps leastAction legalLeStabilizing legalMono abelianProperty

end RandomSandpile

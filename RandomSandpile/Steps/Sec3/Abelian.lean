import RandomSandpile.Steps.Sec3.Burning
import LatticeProb.Sandpile.LeastAction

/-!
# Steps of Proposition 3.2 (Abelian decomposition)

Carving of `RandomSandpile.AbelianDecompositionStmt` (Proposition 3.2,
`paper/random_piles-corrected.tex`) into two steps on legal toppling functions, and the
reduction `abelianDecomposition_of_steps`. No proof is printed (: "a consequence of the
Abelian property"); the reduction follows the natural proof of .

1. Write `v = w + v̂` as in the definition of `𝓛(η, A)`: `w` topples only `∂A`, and
   `v̂` is legal for `η' := Δ_{ℤ^d} w + η` in `A`; `Δ_{ℤ^d} w ≥ 0` in `A`.
2. Let `v₁` be the odometer of `η` in `A` (Proposition 3.1, `LeastActionStmt`). It is legal for `η`
   in `A`, hence legal for `η' ≥ η` (`LegalMonoStmt`: adding chips preserves legality).
3. `v̂` is stabilizing for `η'` in `A`, since `Δ_{ℤ^d} v̂ + η' = Δ_{ℤ^d} v + η`; so `v₁ ≤ v̂` by the
   least action principle (`LegalLeStabilizingStmt`).
4. By the Abelian property (`AbelianPropertyStmt`), `v̂ - v₁` is legal for `η' + Δ_{ℤ^d} v₁`.
   Hence `v₂ := w + (v̂ - v₁) = v - v₁` lies in `𝓛(η + Δ_{ℤ^d} v₁, A) ∩ 𝒮(η + Δ_{ℤ^d} v₁, A)`, with
   boundary part `w`, and `v₂ = v = f` on `∂A`.

The hypothesis `f ≥ 0` on `∂A` is not used, and connectedness of `A` and `d ≥ 2` are used only
through Proposition 3.1.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Step 1 of Proposition 3.2 (adding chips preserves legality; : a legal
toppling function `u` for `η` in `A` stays legal for every `η'` with `η ≤ η'` at the sites of `A`
that `u` topples. -/
def LegalMonoStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)) (η η' u : Site d → ℤ), IsLegal η A u →
    (∀ x ∈ A, 1 ≤ u x → η x ≤ η' x) → IsLegal η' A u

/-- Step 2 of Proposition 3.2, the Abelian property of legal toppling (Dhar; Diaconis-Fulton): if
`a ≤ b` are legal toppling functions for `η` in `A`, then `b - a` is legal for `η + Δ_{ℤ^d} a` in
`A`, that is, the topplings of `b` can be performed after those of `a`. -/
def AbelianPropertyStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)) (η a b : Site d → ℤ), IsLegal η A a → IsLegal η A b → a ≤ b →
    IsLegal (fun x => η x + lap a x) A (b - a)

namespace Abelian

variable {d : ℕ}

/-- The integer Laplacian commutes with pointwise differences `f - g`. -/
theorem lap_pi_sub_apply (f g : Site d → ℤ) (x : Site d) :
    lap (f - g) x = lap f x - lap g x :=
  Burning.lap_sub_apply' f g x

/-- A nonnegative function vanishing at `x` has a nonnegative Laplacian at `x`; in particular
`Δ_{ℤ^d} w ≥ 0` in `A` for a boundary toppling `w` (`w ≥ 0`, `w = 0` in `A`). -/
theorem lap_nonneg_of_nonneg_of_eq_zero {w : Site d → ℤ} (hw : ∀ y, 0 ≤ w y) {x : Site d}
    (hx : w x = 0) : 0 ≤ lap w x := by
  have h := lap_le_lap_of_le (u := 0) (w := w) hw (x := x) (by simp [hx])
  rwa [lap_zero_apply] at h

end Abelian

/-- Reduction of Proposition 3.2 to Proposition 3.1 (existence of the odometer `v₁`), the least
action principle, and Steps 1-2. -/
theorem abelianDecomposition_of_steps (hLA : LeastActionStmt) (hLS : LegalLeStabilizingStmt)
    (hmono : LegalMonoStmt) (hab : AbelianPropertyStmt) : AbelianDecompositionStmt := by
  intro d hd A hA hconn η v f hv hvf _
  obtain ⟨v₁, -, -, ⟨⟨hv₁L, hv₁S⟩, hv₁b⟩, -⟩ := hLA d hd A hA hconn η
  have hv₁ : IsLegal η A v₁ := isLegal_of_mem_locLegal hv₁L hv₁b
  obtain ⟨⟨w, uh, hw, huh, rfl, hwA, huhB, hleg⟩, hvS⟩ := hv
  have hlapw : ∀ x ∈ A, 0 ≤ lap w x := fun x hx =>
    Abelian.lap_nonneg_of_nonneg_of_eq_zero hw.1 (hwA x hx)
  -- `v₁` stays legal for `η' = Δ w + η ≥ η`
  have hv₁' : IsLegal (fun y => lap w y + η y) A v₁ :=
    hmono d A η _ v₁ hv₁ fun x hx _ => by
      show η x ≤ lap w x + η x
      linarith [hlapw x hx]
  -- `v̂` is stabilizing for `η'`
  have huhS : uh ∈ stabilizing (fun y => lap w y + η y) A := ⟨huh, fun x hx => by
    have h := hvS.2 x hx
    rw [Burning.lap_pi_add_apply] at h
    show lap uh x + (lap w x + η x) ≤ 2 * (d : ℤ) - 1
    linarith⟩
  have hle : v₁ ≤ uh := hLS d A _ v₁ uh hv₁' huhS
  have hab' := hab d A _ v₁ uh hv₁' hleg hle
  refine ⟨v₁, w + (uh - v₁), ?_, ⟨⟨hv₁L, hv₁S⟩, hv₁b⟩, ⟨⟨w, uh - v₁, hw,
    ⟨fun x => ?_, fun x hx => ?_⟩, rfl, hwA, fun x hx => ?_, ?_⟩,
    ⟨⟨fun x => ?_, fun x hx => ?_⟩, fun x hx => ?_⟩⟩, fun y hy => ?_⟩
  · funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  · exact sub_nonneg.2 (hle x)
  · simp [huh.2 x hx, hv₁S.1.2 x hx]
  · simp [huhB x hx, hv₁b x hx]
  · convert hab' using 1
    funext y
    ring
  · simp only [Pi.add_apply, Pi.sub_apply]
    linarith [hw.1 x, hle x]
  · simp [hw.2 x hx, huh.2 x hx, hv₁S.1.2 x hx]
  · have h := hvS.2 x hx
    rw [Burning.lap_pi_add_apply] at h
    rw [Burning.lap_pi_add_apply, Abelian.lap_pi_sub_apply]
    linarith
  · have h := hvf y hy
    simp only [Pi.add_apply, Pi.sub_apply] at h ⊢
    rw [hv₁b y hy]
    linarith

end RandomSandpile

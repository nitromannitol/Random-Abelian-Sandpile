import RandomSandpile.Draft.Section7

/-!
# Steps of Lemma 7.1 (one-dimensional toppling)

Carving of `RandomSandpile.OneDimTopplingStmt` (Lemma 7.1, `paper/random_piles-corrected.tex`, with the proposed correction [C5]: the bound is `g ≤ C_r (ℓ + 1)²`) into four steps
about an explicit solution, and the reduction `oneDimToppling_of_steps`.

**Explicit formula.** Since `R_k = 2r`, the source term is
`f = -(2r + 2) 𝟙_{|x| ≤ ℓ} + 𝟙_{|x| ≤ ℓ(r+1)} + 𝟙_{|x| ≤ ℓ(r+1)+r}`. The ramp potential
`rampPotential m x = ∑_{|y| ≤ m} (y - x)⁺` has second difference `𝟙_{|x| ≤ m}` (the second
difference of `t ↦ t⁺` is the Dirac mass at `0`), so
`oneDimOdometer r ℓ = Q_{ℓ(r+1)} + Q_{ℓ(r+1)+r} - (2r + 2) Q_ℓ` solves `Δ g = f`; it is
`∑_y (y - x)⁺ f(y)`, the compactly supported solution `½ ∑_y |x - y| f(y)` of the [C5] note
(the two agree because `∑ f = 0` and `∑ y f(y) = 0`). It is integer-valued by construction.

* `OneDimSecondDiffStmt`: `Δ g = f` (one-dimensional second difference);
* `OneDimSupportStmt`: `g` vanishes for `|x| ≥ ℓ(r+1) + r`, i.e. off `I`;
* `OneDimNonnegStmt`: `g ≥ 0`, so `g` takes values in `ℕ`;
* `OneDimBoundStmt`: `g ≤ ((r + 1)(ℓ + 1))²`, the bound `g ≤ C_r (ℓ + 1)²` with `C_r = (r + 1)²`.
-/

noncomputable section

open Finset

namespace RandomSandpile

/-- The ramp potential of the indicator of `[-m, m] ∩ ℤ`: `Q_m(x) = ∑_{|y| ≤ m} (y - x)⁺`. Its
second difference is `𝟙_{|x| ≤ m}`, it vanishes for `x ≥ m` and is affine for `x ≤ -m`. -/
def rampPotential (m : ℕ) (x : ℤ) : ℤ :=
  ∑ y ∈ Icc (-(m : ℤ)) m, max (y - x) 0

/-- The explicit solution of Lemma 7.1 for `R_k = 2r`:
`g = Q_{ℓ(r+1)} + Q_{ℓ(r+1)+r} - (2r + 2) Q_ℓ`, i.e. `g(x) = ∑_y (y - x)⁺ f(y)`. -/
def oneDimOdometer (r ℓ : ℕ) (x : ℤ) : ℤ :=
  rampPotential (ℓ * (r + 1)) x + rampPotential (ℓ * (r + 1) + r) x -
    (2 * r + 2) * rampPotential ℓ x

/-- Step 1 of Lemma 7.1: `Δ g = f`, where `Δ g (x) = g(x+1) + g(x-1) - 2 g(x)` and `f` is the source
term with `R_k = 2r`. -/
def OneDimSecondDiffStmt : Prop :=
  ∀ (r ℓ : ℕ) (x : ℤ),
    oneDimOdometer r ℓ (x + 1) + oneDimOdometer r ℓ (x - 1) - 2 * oneDimOdometer r ℓ x =
      if |x| ≤ ℓ then -(2 * (r : ℤ))
      else if |x| ≤ ℓ * (r + 1) then 2
      else if |x| ≤ ℓ * (r + 1) + r then 1
      else 0

/-- Step 2 of Lemma 7.1: `g` is supported in `I = {x ∈ ℤ : |x| < ℓ(r+1) + r}`. -/
def OneDimSupportStmt : Prop :=
  ∀ (r ℓ : ℕ) (x : ℤ), ℓ * (r + 1) + r ≤ |x| → oneDimOdometer r ℓ x = 0

/-- Step 3 of Lemma 7.1: `g ≥ 0`, so that `g` takes values in `ℕ`. -/
def OneDimNonnegStmt : Prop :=
  ∀ (r ℓ : ℕ) (x : ℤ), 0 ≤ oneDimOdometer r ℓ x

/-- Step 4 of Lemma 7.1: the bound `g ≤ C_r (ℓ + 1)²` with `C_r = (r + 1)²` ([C5]). -/
def OneDimBoundStmt : Prop :=
  ∀ (r ℓ : ℕ) (x : ℤ), oneDimOdometer r ℓ x ≤ (((r : ℤ) + 1) * (ℓ + 1)) ^ 2

/-- **Reduction of Lemma 7.1** to its four steps, with `C_r = (r + 1)²` and `g = (oneDimOdometer r ℓ)⁺`
(equal to `oneDimOdometer r ℓ` by Step 3). -/
theorem oneDimToppling_of_steps (h1 : OneDimSecondDiffStmt) (h2 : OneDimSupportStmt)
    (h3 : OneDimNonnegStmt) (h4 : OneDimBoundStmt) : OneDimTopplingStmt := by
  intro r
  refine ⟨((r : ℝ) + 1) ^ 2, by positivity, ?_⟩
  intro d ηmax ℓ k hR
  have hg : ∀ x : ℤ, ((oneDimOdometer r ℓ x).toNat : ℤ) = oneDimOdometer r ℓ x := fun x =>
    Int.toNat_of_nonneg (h3 r ℓ x)
  refine ⟨fun x => (oneDimOdometer r ℓ x).toNat, ?_, ?_, ?_⟩
  · intro x
    simp only [hg, hR]
    exact h1 r ℓ x
  · intro x hx
    have := h2 r ℓ x hx
    simp [this]
  · intro x
    have h : ((oneDimOdometer r ℓ x).toNat : ℝ) = ((oneDimOdometer r ℓ x : ℤ) : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) (hg x)
      simpa only [Int.cast_natCast] using this
    rw [h]
    have h4' := h4 r ℓ x
    have : ((oneDimOdometer r ℓ x : ℤ) : ℝ) ≤ (((r : ℝ) + 1) * ((ℓ : ℝ) + 1)) ^ 2 := by
      exact_mod_cast h4'
    nlinarith [this]

end RandomSandpile

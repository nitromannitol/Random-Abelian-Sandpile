import RandomSandpile.Defs.Toppling

/-!
# Section 3: the discrete sandpile PDE (Propositions 3.1-3.4)

Statements of Propositions 3.1-3.4 of `paper/random_piles-corrected.tex`.

Standing assumptions of Section 3 and of the paper:

* `d ≥ 2` (the results of this section hold for every `d ≥ 1`; `d ≥ 2` is the paper's standing
  assumption);
* `A ⊂ ℤ^d` is bounded, that is `A.Finite`, and connected: the subgraph of the nearest-neighbour
  graph `LatticeProb.lattice d` induced on `A` is connected (`SimpleGraph.Connected`, which includes
  `A ≠ ∅`);
* a sandpile is a function `η : ℤ^d → ℤ`; only its values on `A` enter. Boundary data
  `f : ∂A → ℕ` are functions `ℤ^d → ℤ` that are nonnegative on `∂A`; only their values on `∂A`
  enter.

"`v` solves `v ∈ 𝓛(s) ∩ 𝒮(s)` on `A`, `v = f` on `∂A`" is
`v ∈ locLegal s A ∩ stabilizing s A ∧ ∀ y ∈ bdry A, v y = f y`. Locally legal toppling functions
play the role of subsolutions and stabilizing toppling functions that of supersolutions of the
discrete sandpile PDE.

Suprema and infima over `A` and `∂A` (Proposition 3.3) are written pointwise. For finite nonempty
`A`, the boundary `∂A` is finite and nonempty, so suprema and infima over `A` and `∂A` are attained
and, for `φ : A → ℤ`, `ψ : ∂A → ℤ`,
`sup_A φ ≤ sup_{∂A} ψ ↔ ∀ x ∈ A, ∃ y ∈ ∂A, φ x ≤ ψ y` and
`inf_A φ ≥ inf_{∂A} ψ ↔ ∀ x ∈ A, ∃ y ∈ ∂A, ψ y ≤ φ x`.
The pointwise forms avoid the junk value `sSup ∅ = 0` of `ℤ`.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Proposition 3.1 (prop:least_action), the least action principle of
Fey-Levine-Peres, "the discrete sandpile PDE". The odometer function `v` of `η` in `A` (open
boundary condition: `v = 0` off `A`) uniquely solves each of the following problems.
1. Longest legal toppling: `v = sup {w : Ā → ℕ : w ∈ 𝓛(η, A), w = 0 on ∂A}`.
2. Shortest stabilizing toppling: `v = inf {u : Ā → ℕ : u ∈ 𝒮(η, A), u = 0 on ∂A}`.
3. Stabilizing, legal toppling: `v ∈ 𝓛(η, A) ∩ 𝒮(η, A)` and `v = 0` on `∂A`.

The same `v` solves the three problems. The supremum in (1) and the infimum in (2) are attained,
for the pointwise order on `ℤ^d → ℤ`: `v` is the greatest element (`IsGreatest`, whose uniqueness
is automatic) of the first set and the least element (`IsLeast`) of the second; `v` is the unique
element of the solution set of (3). Toppling functions on `Ā` are the functions `ℤ^d → ℤ` that are
nonnegative and vanish off `Ā` (`IsTopplingFn`); every element of `locLegal η A` and of
`stabilizing η A` is one. -/
def LeastActionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (A : Set (Site d)), A.Finite → ((lattice d).induce A).Connected →
    ∀ η : Site d → ℤ, ∃ v : Site d → ℤ,
      IsGreatest {w | w ∈ locLegal η A ∧ ∀ y ∈ bdry A, w y = 0} v ∧
      IsLeast {u | u ∈ stabilizing η A ∧ ∀ y ∈ bdry A, u y = 0} v ∧
      (v ∈ locLegal η A ∩ stabilizing η A ∧ ∀ y ∈ bdry A, v y = 0) ∧
      ∀ v' : Site d → ℤ, v' ∈ locLegal η A ∩ stabilizing η A → (∀ y ∈ bdry A, v' y = 0) →
        v' = v

/-- Proposition 3.2 (Abelian), a consequence of the Abelian property. If
`v ∈ 𝓛(η, A) ∩ 𝒮(η, A)` and `v = f ≥ 0` on `∂A`, then `v = v₁ + v₂` where
`v₁ ∈ 𝓛(η) ∩ 𝒮(η)` on `A` with `v₁ = 0` on `∂A` (`v₁` is the odometer of `η` in `A`, by
Proposition 3.1), and `v₂ ∈ 𝓛(η + Δ_{ℤ^d} v₁) ∩ 𝒮(η + Δ_{ℤ^d} v₁)` on `A` with `v₂ = f` on `∂A`
(`v₂` records the topplings originating from the boundary).

The hypothesis `f ≥ 0` on `∂A` is the paper's; it follows from `v = f` on `∂A`, since `v` is a
toppling function. -/
def AbelianDecompositionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (A : Set (Site d)), A.Finite → ((lattice d).induce A).Connected →
    ∀ (η v f : Site d → ℤ), v ∈ locLegal η A ∩ stabilizing η A → (∀ y ∈ bdry A, v y = f y) →
      (∀ y ∈ bdry A, 0 ≤ f y) →
      ∃ v₁ v₂ : Site d → ℤ, v = v₁ + v₂ ∧
        (v₁ ∈ locLegal η A ∩ stabilizing η A ∧ ∀ y ∈ bdry A, v₁ y = 0) ∧
        (v₂ ∈ locLegal (fun x => η x + lap v₁ x) A ∩ stabilizing (fun x => η x + lap v₁ x) A ∧
          ∀ y ∈ bdry A, v₂ y = f y)

/-- Proposition 3.3 (burning), the maximum principle and the comparison principle
for the discrete sandpile PDE, from Dhar's burning algorithm. For `f : ∂A → ℕ` and a sandpile
`s : A → ℤ`, let `v` solve `v ∈ 𝓛(s) ∩ 𝒮(s)` on `A`, `v = f` on `∂A`.
* (eq:stable) If `s` is stable, then `sup_{x ∈ A} v(x) ≤ sup_{y ∈ ∂A} f(y)`.
* (eq:rec) If `s` is recurrent, then `inf_{x ∈ A} v(x) ≥ inf_{y ∈ ∂A} f(y)`.
* If `s` is stable and recurrent, `u` solves `u ∈ 𝓛(s) ∩ 𝒮(s)` on `A`, `u = f'` on
  `∂A` for some `f' : ∂A → ℕ`, and `g, h : Ā → ℤ` are integer-valued harmonic functions,
  `Δ_{ℤ^d} g = Δ_{ℤ^d} h = 0` in `A`, then
  `inf_{x ∈ A} ((u + g) - (v + h))(x) ≥ inf_{y ∈ ∂A} ((f' + g) - (f + h))(y)`.

The three claims are one conjunction, under the common hypotheses on `f`, `s`, `v`. The suprema
and infima are written pointwise (`∀ x ∈ A, ∃ y ∈ ∂A, …`), equivalent to the printed ones since
`A` and `∂A` are finite and nonempty (module docstring). The functions `g, h` are functions
`ℤ^d → ℤ`; only their values on `Ā` enter, and `Δ_{ℤ^d} g (x)` for `x ∈ A` only involves `Ā`. -/
def BurningStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (A : Set (Site d)), A.Finite → ((lattice d).induce A).Connected →
    ∀ (f s v : Site d → ℤ), (∀ y ∈ bdry A, 0 ≤ f y) →
      v ∈ locLegal s A ∩ stabilizing s A → (∀ y ∈ bdry A, v y = f y) →
      (IsStableOn s A → ∀ x ∈ A, ∃ y ∈ bdry A, v x ≤ f y) ∧
      (IsRecurrentOn s A → ∀ x ∈ A, ∃ y ∈ bdry A, f y ≤ v x) ∧
      (IsStableOn s A → IsRecurrentOn s A →
        ∀ (f' u : Site d → ℤ), (∀ y ∈ bdry A, 0 ≤ f' y) →
          u ∈ locLegal s A ∩ stabilizing s A → (∀ y ∈ bdry A, u y = f' y) →
          ∀ (g h : Site d → ℤ), (∀ x ∈ A, lap g x = 0) → (∀ x ∈ A, lap h x = 0) →
            ∀ x ∈ A, ∃ y ∈ bdry A, (f' y + g y) - (f y + h y) ≤ (u x + g x) - (v x + h x))

/-- Proposition 3.4 (recurrent), an alternative characterization of recurrent
sandpiles: if each site has toppled at least once, what remains is recurrent. Let `A ⊂ W` be
connected subsets of `ℤ^d`. If `w ∈ 𝓛(η, W)` with `w ≥ 1` in `A`, then `Δ_{ℤ^d} w + η` is
recurrent in `A`.

`W` need not be bounded (the paper does not say so). The Section 3 standing assumption that `A` is
bounded is not repeated: it follows from the hypotheses, since `w` coincides on `A ⊆ W` with its
legal part, a finite sum of unit topplings. The configuration `Δ_{ℤ^d} w + η` need not be stable
in `A`; `IsRecurrentOn` is the paper's definition, which does not require stability. -/
def RecurrentOfToppledStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (A W : Set (Site d)), A ⊆ W → ((lattice d).induce A).Connected →
    ((lattice d).induce W).Connected →
    ∀ (η w : Site d → ℤ), w ∈ locLegal η W → (∀ x ∈ A, 1 ≤ w x) →
      IsRecurrentOn (fun x => lap w x + η x) A

end RandomSandpile

import RandomSandpile.Defs.Environment

/-! # Subadditive set functions and subadditive processes

The objects of the multiparameter subadditive ergodic theorem of Akcoglu and Krengel, as modified
by Dal Maso and Modica and restated in Armstrong and Smart (Proposition 5.3):

* `boundedSets d`: the family `𝒰_0` of bounded subsets of `ℤ^d`, that is, of finite subsets;
* `IsSubadditive f`: `f : 𝒰_0 → ℝ` is subadditive over finite partitions into pairwise disjoint
  members of `𝒰_0`;
* `subadditiveClass d C`: the class `𝓜_C` of subadditive `f` with `0 ≤ f(A) ≤ C |A|` on `𝒰_0`;
* `IsSubadditiveProcess C f`: `f : Ω → 𝓜_C` is a *subadditive process*, together with the
  measurability and the stationarity `f(A, T_y η) = f(y + A, η)` that the theorem needs.

Set functions are defined on all of `Set (Site d)`; only their values on `𝒰_0` enter. -/

open MeasureTheory LatticeProb
open scoped Pointwise

namespace RandomSandpile

variable {d : ℕ}

/-- The family `𝒰_0` of bounded subsets of `ℤ^d`. A subset of `ℤ^d` is bounded exactly
when it is finite, so `𝒰_0` is the family of finite subsets. -/
def boundedSets (d : ℕ) : Set (Set (Site d)) := {A | A.Finite}

/-- `f` is *subadditive* on `𝒰_0`: `f(A) ≤ ∑_{j=1}^k f(A_j)` whenever
`A, A_1, …, A_k ∈ 𝒰_0`, the `A_j` are pairwise disjoint and `A = ⋃_j A_j`.

The pieces are indexed by `Fin k`. The case `k = 0` (empty partition of `A = ∅`) asks
`f(∅) ≤ 0`; for members of `𝓜_C` this already follows from `0 ≤ f(∅) ≤ C |∅| = 0`. -/
def IsSubadditive (f : Set (Site d) → ℝ) : Prop :=
  ∀ (k : ℕ) (A : Set (Site d)) (B : Fin k → Set (Site d)), A ∈ boundedSets d →
    (∀ j, B j ∈ boundedSets d) → Pairwise (Function.onFun Disjoint B) → A = ⋃ j, B j →
      f A ≤ ∑ j, f (B j)

/-- The class `𝓜_C`: subadditive functions `f : 𝒰_0 → ℝ` with
`0 ≤ f(A) ≤ C |A|` for every `A ∈ 𝒰_0`, where `|A|` is the cardinality of `A`. -/
def subadditiveClass (d : ℕ) (C : ℝ) : Set (Set (Site d) → ℝ) :=
  {f | IsSubadditive f ∧ ∀ A ∈ boundedSets d, 0 ≤ f A ∧ f A ≤ C * (A.ncard : ℝ)}

/-- A *subadditive process* `f : Ω → 𝓜_C`, written `f(A, η) = f η A`, with the
sample space `Ω` taken to be `Config d`.

Besides `f(η) ∈ 𝓜_C` for every `η` (`mem`), the structure records two conditions that the
multiparameter subadditive ergodic theorem needs and that the paper leaves implicit:

* `measurable`: for every `A ∈ 𝒰_0`, `η ↦ f(A, η)` is measurable for the product σ-algebra on
  `Config d`, so that the events in Proposition 5.3 make sense;
* `stationary`: `f(A, T_y η) = f(y + A, η)` for all `y ∈ ℤ^d`, `A ∈ 𝒰_0` and `η`, where
  `T_y η(z) = η(y + z)` (`shift`). This is the stationarity of the process in
  Armstrong-Smart and Dal Maso-Modica; Proposition 5.3 as printed omits it, and
  without it the conclusion fails: `f(A, η) = |A ∩ H|` for a fixed half-space `H` through the
  origin is additive and lies in `𝓜_1`, but `f(nW ∩ ℤ^d) / |nW ∩ ℤ^d| → |W ∩ H| / |W|` depends
  on `W`. For `f = μ(·, η, l, M)` it holds because `T_y η` restricted to `Ā` is `η` restricted to
  `y + Ā`, and the parabola `q_l + q_M` changes by an affine function under translation. -/
structure IsSubadditiveProcess (C : ℝ) (f : Config d → Set (Site d) → ℝ) : Prop where
  /-- `f(η) ∈ 𝓜_C` for every `η`. -/
  mem : ∀ η, f η ∈ subadditiveClass d C
  /-- Measurability of `η ↦ f(A, η)` for `A ∈ 𝒰_0`. -/
  measurable : ∀ A ∈ boundedSets d, Measurable fun η => f η A
  /-- Stationarity `f(A, T_y η) = f(y + A, η)`. -/
  stationary : ∀ (y : Site d), ∀ A ∈ boundedSets d, ∀ η, f (shift y η) A = f η (y +ᵥ A)

end RandomSandpile

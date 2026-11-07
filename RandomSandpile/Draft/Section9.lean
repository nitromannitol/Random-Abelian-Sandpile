import RandomSandpile.Defs.Obstacle
import RandomSandpile.Defs.Odometer
import RandomSandpile.Defs.Domain

/-! # Statements of Section 9: extensions

* `OpenBoundaryTheoremStmt` — Theorem 9.1 (unlabelled), sandpiles with the open
  boundary condition;
* `SingleSourceTheoremStmt` — Theorem 9.2 (unlabelled), the single source sandpile
  on a random background, with the correction [C3].

Both theorems are stated without printed proof ("the exact same argument", "straightforward
modifications"); they are in scope as results of the paper.

Standing assumptions: `d ≥ 2`, and the law of `η` is a `RandomEnvironment d`
(uniformly bounded, stationary, ergodic). High density `E η(0) > 2d - 1` is the last standing
assumption of the paper; Theorem 9.1 does not override it and its proof is "the
exact same argument" as Theorem 1.1's, which uses it (Section 9.3), so
`OpenBoundaryTheoremStmt` keeps it. Theorem 9.2 replaces it by `η_max = 2d - 2`
(so `E η(0) ≤ 2d - 2`), and `SingleSourceTheoremStmt` does not assume it.

Junk values: the open-boundary odometer of a finite domain is never a junk value
(`stabilizingOpen_nonempty`); the single-source odometer is the junk value `0` when the class of
stabilizing toppling functions of `η + n δ_0` is empty, so `SingleSourceTheoremStmt` asserts that,
almost surely, it is nonempty for every `n`. The least element of the obstacle problem of
Theorem 9.2 is asserted to exist (`IsLeast`), which rules out the junk values of
`singleSourceObstacleSolution`.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Theorem 9.1 (unlabelled): sandpiles with the open boundary condition.

Let `W` be a bounded Lipschitz domain and `v_n = openOdometer η W_n` the odometer of `η` in
`W_n = ℤ^d ∩ nW` with the open boundary condition (`v_n ∈ 𝓛(η, W_n) ∩ 𝓢(η, W_n)`, `v_n = 0` on
`∂W_n`; Proposition 3.1 identifies it with the least stabilizing toppling function vanishing on
`∂W_n`). Then `F̄_η` is a degenerate elliptic operator, and almost surely the rescaled odometers
`v̄_n(x) = n⁻² v_n([nx])` converge uniformly to the unique viscosity solution `v̄ ∈ C(ℝ^d)` of
`F̄_η(D²v̄) = 0` in `W`, `v̄ = 0` on `∂W`.

Reading of "unique" (no statement change): the Dirichlet problem constrains `v̄` only on the
closure `W̄`, so uniqueness in `C(ℝ^d)` is uniqueness on `W̄`: every continuous viscosity solution
`w` of the problem agrees with `v̄` on `W̄`. Off `W̄` the limit is fixed by the uniform convergence
(the `v̄_n` vanish off `W`). "Viscosity solution" is in the sense of Crandall, Ishii and Lions
(`ViscositySolution`: subsolution tested from above, supersolution tested from below). The
qualifier "a unique degenerate elliptic operator" is not a mathematical claim beyond
`F̄_η` being a well-defined degenerate elliptic operator, `DegenerateElliptic (effOp E)`.
High density is kept as a standing assumption (see the module docstring). -/
def OpenBoundaryTheoremStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ E : RandomEnvironment d, HighDensity E.P →
      DegenerateElliptic (effOp E) ∧
      ∃ v : Rd d → ℝ, Continuous v ∧ ViscositySolution (effOp E) W v ∧
        (∀ x ∈ frontier W, v x = 0) ∧
        (∀ w : Rd d → ℝ, Continuous w → ViscositySolution (effOp E) W w →
          (∀ x ∈ frontier W, w x = 0) → Set.EqOn w v (closure W)) ∧
        ∀ᵐ η ∂E.P,
          TendstoUniformly (fun n : ℕ => rescaleOdo (openOdometer η (discretize W n)) n) v atTop

/-- Theorem 9.2 (unlabelled): the single source sandpile on a random background,
with the correction [C3].

Let the background `η` be stationary, ergodic, with `η_min ≤ η ≤ η_max = 2d - 2`, and let
`v_n = singleSourceOdometer η n` be the odometer of `η + n δ_0` on `ℤ^d`
(`v_n ∈ 𝓛(η + n δ_0, ℤ^d) ∩ 𝓢(η + n δ_0, ℤ^d)`). Then the obstacle problem
`v̄ := inf {v ∈ C(ℝ^d) : v ≥ -G and F̄_η(D²(v + G)) ≥ 0}` has a (necessarily unique) solution,
`IsLeast (singleSourceObstacleSet E) (singleSourceObstacleSolution E)`, and almost surely the
odometers are finite for every `n` and the rescaled odometers
`v̄_n(x) = n^{-2/d} v_n([n^{1/d} x])` converge locally uniformly on `ℝ^d \ {0}` to `v̄ + G`, where
`G = fundamentalSolution d` is the fundamental solution of the Laplacian (`ΔG = -δ_0`).

The paper prints `F̄_η(D²(v̄ + G)) ≤ 0`; [C3] changes it to `≥ 0`, in the
viscosity-supersolution sense. Both constraints are imposed on `ℝ^d \ {0}`, where `G` is finite
(see `Defs/Obstacle.lean`). "The unique viscosity solution of the obstacle problem" is read as the
least element of the constraint set. -/
def SingleSourceTheoremStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    IsLeast (singleSourceObstacleSet E) (singleSourceObstacleSolution E) ∧
    ∀ᵐ η ∂E.P,
      (∀ n : ℕ, (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty) ∧
        TendstoLocallyUniformlyOn
          (fun n : ℕ => rescaleSingleSource (singleSourceOdometer η n) n)
          (fun x => singleSourceObstacleSolution E x + fundamentalSolution d x) atTop
          {x : Rd d | x ≠ 0}

end RandomSandpile

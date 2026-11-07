import RandomSandpile.Draft.Section9
import RandomSandpile.Defs.Effective

/-! # Partial variant of Theorem 9.2: flatness of `F̄_η` as an extra hypothesis

* `SingleSourceTheoremFlatStmt` — Theorem 9.2 (`SingleSourceTheoremStmt`, with
  [C3]) under the extra hypothesis that `F̄_η` is flat for the background:
  `μ(F̄_η(M), M) = μ*(F̄_η(M), M) = 0` for every symmetric `M` (the conclusion of Lemma 7.5,
  `FlatStmt`, which the paper proves only under high density).

A partial result for Theorem 9.2, not a correction: the printed statement stays `SingleSourceTheoremStmt`;
flatness for low-density backgrounds (`η_max = 2d - 2`) is an open case.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Theorem 9.2 under the flatness hypothesis on `F̄_η` (a partial result, not a correction). The conclusion is that of `SingleSourceTheoremStmt`. -/
def SingleSourceTheoremFlatStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    (∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm →
      muBar E (effOp E M) M = 0 ∧ muStarBar E (effOp E M) M = 0) →
    IsLeast (singleSourceObstacleSet E) (singleSourceObstacleSolution E) ∧
    ∀ᵐ η ∂E.P,
      (∀ n : ℕ, (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty) ∧
        TendstoLocallyUniformlyOn
          (fun n : ℕ => rescaleSingleSource (singleSourceOdometer η n) n)
          (fun x => singleSourceObstacleSolution E x + fundamentalSolution d x) atTop
          {x : Rd d | x ≠ 0}

end RandomSandpile

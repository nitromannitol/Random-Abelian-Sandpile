import RandomSandpile.Draft.Section9Partial
import RandomSandpile.Defs.Effective

/-! # Section 9: the corrected hypothesis of the partial results

`SingleSourceTheoremFlatStmt` (`Draft/Section9Partial.lean`) assumes the flatness of `F̄_η`
at every symmetric matrix (`FlatEff`). That hypothesis is not a property that a low-density
background can have in general: it fails for every background with `η ≤ d - 1` (in particular for
`η ≡ -1`, and for the zero background), where `μ(F̄_η(M), M) > 0` or `μ*(F̄_η(M), M) > 0` at
`M = 0` (`not_flatEff_of_le`), so the printed partial statement says nothing there.

What the argument needs is the single scalar condition that the *stabilization threshold of the
zero Hessian vanishes*,
`H_η(0) = inf {l : μ*(l, 0) = 0} = 0`, written `StabThresholdZero E`: `μ*(l, 0) = 0` for every
`l > 0` (`μ*(·, 0)` is nonincreasing and `μ*(l, 0) > 0` for `l < 0`, so this is `H_η(0) = 0`).
It is implied by `FlatEff` (`stabThresholdZero_of_flatEff`), it holds whenever `d ≤ η ≤ 2d - 2`
pointwise, and it fails exactly where the low-density statement is open (`η ≤ d - 1`, hence
`η ≡ -1`; `H_η(0) > 0` is the open case of Theorem 9.2).

* `SingleSourceTheoremFlatV2Stmt` — the conclusion of Theorem 9.2 (`SingleSourceTheoremStmt`, with
  [C3]) under `StabThresholdZero E` in place of `FlatEff E`, for every `d ≥ 2`. The old statement
  follows from it (`singleSourceTheoremFlat_of_v2`).
* `SingleSourceTheoremH0Stmt` — the same for `d ≥ 3`: the corrected Theorem 9.2 holds for every
  `d ≥ 3` when `H_η(0) = 0`.

A partial result for Theorem 9.2, not a correction: the printed statement stays
`SingleSourceTheoremStmt`.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- The stabilization threshold of the zero Hessian vanishes, `H_η(0) = 0`: `μ*(l, 0) = 0` for
every `l > 0`. -/
def StabThresholdZero {d : ℕ} (E : RandomEnvironment d) : Prop :=
  ∀ l : ℝ, 0 < l → muStarBar E l 0 = 0

/-- The conclusion of Theorem 9.2 (`SingleSourceTheoremStmt`, [C3]) for the environment `E`. -/
def SingleSourceConclusion {d : ℕ} (E : RandomEnvironment d) : Prop :=
  IsLeast (singleSourceObstacleSet E) (singleSourceObstacleSolution E) ∧
    ∀ᵐ η ∂E.P,
      (∀ n : ℕ, (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty) ∧
        TendstoLocallyUniformlyOn
          (fun n : ℕ => rescaleSingleSource (singleSourceOdometer η n) n)
          (fun x => singleSourceObstacleSolution E x + fundamentalSolution d x) atTop
          {x : Rd d | x ≠ 0}

/-- Theorem 9.2 for every `d ≥ 2` and every background with `H_η(0) = 0`
(`StabThresholdZero E`). A partial result for Theorem 9.2, not a correction. -/
def SingleSourceTheoremFlatV2Stmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    StabThresholdZero E → SingleSourceConclusion E

/-- Theorem 9.2 for every `d ≥ 3` and every background with `H_η(0) = 0`; in particular for every
background with `d ≤ η ≤ 2d - 2` pointwise. A partial result for Theorem 9.2, not a correction. -/
def SingleSourceTheoremH0Stmt : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    StabThresholdZero E → SingleSourceConclusion E

end RandomSandpile

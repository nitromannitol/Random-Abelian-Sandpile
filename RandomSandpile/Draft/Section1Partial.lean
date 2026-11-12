import RandomSandpile.Draft.Section1

/-! # Weaker variant of Theorem 1.1: the support radius chosen after the law

* `MainTheoremLawRadiusStmt` — Theorem 1.1 (`MainTheoremStmt`, with [C3]) with one
  change: the radius `R` of the support clause "`s = 0` in `ℝ^d ∖ B_R(W)`" is chosen after the
  environment `E` and may depend on the whole law.

The printed radius is `R > 0` depending on `W` and `E(η(0))` (`MainTheoremPrintedStmt`). Correction
[C12] gives `R` depending on `W`, `d` and `η_max` (the box of Lemma 7.2, via Lemma 7.1).
`MainTheoremStmt` chooses `R` after `d`, `W` and `η_max`, before the law, so it implies this variant
(`mainTheoremLawRadius_of_mainTheorem`, `Proofs/Sec7/MainTheoremC12.lean`).
-/

open MeasureTheory Filter Topology

namespace RandomSandpile

/-- Theorem 1.1 with the support radius `R` chosen after the environment. It is weaker than the
corrected `MainTheoremStmt` ([C12]). All other clauses are those of `MainTheoremStmt`. -/
def MainTheoremLawRadiusStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ E : RandomEnvironment d, HighDensity E.P → ∃ R : ℝ, 0 < R ∧
      DegenerateElliptic (effOp E) ∧
      IsLeast (obstacleSet E W) (obstacleSolution E W) ∧
      (∀ᵐ η ∂E.P,
        (∀ n : ℕ, (stabilizing ((discretize W n).indicator η) Set.univ).Nonempty) ∧
          TendstoUniformly (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n)
            (obstacleSolution E W) atTop) ∧
      ∃ s : Rd d → ℝ, MemLp s ⊤ volume ∧
        (∀ᵐ η ∂E.P,
          WeakStarTendsto (fun n : ℕ => rescaleSandpile (freeSandpile η (discretize W n)) n) s) ∧
        ∫ x, s x = (volume W).toReal * meanEta E.P ∧
        (∀ᵐ x ∂volume, s x ≤ 2 * (d : ℝ) - 1) ∧
        (∀ᵐ x ∂volume, x ∉ Metric.thickening R W → s x = 0) ∧
        ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, s x * φ x =
            (∫ x, obstacleSolution E W x * Matrix.trace (hessian φ x)) +
              meanEta E.P * ∫ x in W, φ x

end RandomSandpile

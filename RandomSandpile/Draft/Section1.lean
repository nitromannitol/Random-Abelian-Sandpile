import RandomSandpile.Defs.Obstacle
import RandomSandpile.Defs.Odometer
import RandomSandpile.Defs.Domain

/-! # Statements of Section 1: the main theorem

* `MainTheoremStmt` — Theorem 1.1 (`thetheorem`), with the correction [C3] and the correction [C12]: the support radius `R` depends on `W`, `d` and
  `η_max`, not on `W` and `E(η(0))`.
* `MainTheoremPrintedStmt` — the same statement with the radius as printed in the paper ("`R > 0`
  depending on `W` and `E(η(0))`").

Standing assumptions: `d ≥ 2`; the law of `η` is a `RandomEnvironment d` (uniformly
bounded, stationary, ergodic); high density `E η(0) > 2d - 1` (`HighDensity`), which the theorem
uses. `W` is a bounded Lipschitz domain (`IsLipschitzDomain`, which includes boundedness,
openness and connectedness), `W_n = ℤ^d ∩ nW` is `discretize W n`, `v_n` is the free-boundary
odometer `freeOdometer η W_n` of `η 1_{W_n}` and `s_n = freeSandpile η W_n` the stable sandpile.

Junk values: the free-boundary odometer is the junk value `0` when the class of stabilizing
toppling functions is empty (`Defs/Odometer.lean`); the statement asserts that, almost surely, it is
nonempty for every `n` (a pile with finitely many chips stabilizes). The least element of
the constraint set is asserted to exist (`IsLeast`), which rules out the junk value of
`obstacleSolution`; uniqueness of the solution is part of `IsLeast`. The integral `∫ s` is not a
junk value since `s ∈ L^∞` vanishes off the bounded set `B_R(W)`.
-/

open MeasureTheory Filter Topology

namespace RandomSandpile

/-- Theorem 1.1 (`thetheorem`), with the correction [C3]
and the correction [C12].

Let `η` be stationary, ergodic, bounded with `E η(0) > 2d - 1`, `W ⊂ ℝ^d` a bounded Lipschitz
domain, `v_n` the odometer of `η 1_{W_n}` on `ℤ^d` and `s_n` the stable sandpile.

1. `F̄_η` is a nonrandom, degenerate elliptic operator (`DegenerateElliptic (effOp E)`;
   nonrandom because `effOp E` depends only on the law).
2. The obstacle problem `v̄ := min {v ∈ C(ℝ^d) : v ≥ 0, F̄_η(D²v) ≥ 0 in W, F̄_0(D²v) ≤ 0 in ℝ^d}`
   (viscosity sense, test functions touching from below; the paper prints `F̄_η(D²v̄) ≤ 0`, see
   [C3] in `Defs/Obstacle.lean`) has a (necessarily unique) solution:
   `IsLeast (obstacleSet E W) (obstacleSolution E W)`.
3. Almost surely the odometers are finite for every `n` and the rescaled odometers
   `v̄_n(x) = n⁻² v_n([nx])` converge uniformly on `ℝ^d` to `v̄`.
4. There is a deterministic `s ∈ L^∞(ℝ^d)` such that almost surely the rescaled sandpiles
   `s̄_n(x) = s_n([nx])` converge weakly-* to `s`; moreover `∫ s = |W| E η(0)`, `s ≤ 2d - 1`,
   `s = 0` a.e. in `ℝ^d \ B_R(W)`, and weakly (against `C_c^∞` test functions)
   `s = Δv̄ + E η(0)` in `W`, `s = Δv̄` in `ℝ^d \ W`, i.e.
   `∫ s φ = ∫ v̄ Δφ + E η(0) ∫_W φ`.

[C12]. The paper prints "`R > 0` depending on `W`
and `E(η(0))`". The author's reading is "depending on `W`, `d` and `η_max`": the radius
comes from the box of Lemma 7.2, obtained through Lemma 7.1, whose size depends on `η_max`. So
`R` is chosen after `d`, `W` and the upper bound `η_max = E.ηmax`, and before the environment. It
serves every law bounded above by `η_max`, whatever its mean. The printed form is
`MainTheoremPrintedStmt`. `B_R(W)` is the open `R`-neighbourhood `Metric.thickening R W`. -/
def MainTheoremStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ ηmax : ℤ, ∃ R : ℝ, 0 < R ∧
    ∀ E : RandomEnvironment d, E.ηmax = ηmax → HighDensity E.P →
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

/-- Theorem 1.1 with the printed support radius ("`R > 0` depending on `W` and
`E(η(0))`"), with [C3]. It is `MainTheoremStmt` with `R` chosen after `d`, `W` and the value `m`
of `E η(0)`, before the environment, instead of after `d`, `W` and `η_max`. The author's
correction [C12] replaces it by `MainTheoremStmt`. It is kept for the conditional proofs that
take the printed radius as the step `SandpileSupportStmt`. -/
def MainTheoremPrintedStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ m : ℝ, ∃ R : ℝ, 0 < R ∧
    ∀ E : RandomEnvironment d, HighDensity E.P → meanEta E.P = m →
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

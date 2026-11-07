import RandomSandpile.Defs.Viscosity
import Mathlib.MeasureTheory.Integral.Average

/-! # Pegden-Smart, Propositions 2.4 and 2.5, stated as in the source

Literature inputs: Propositions 2.4 and 2.5 of Pegden and Smart, as stated in their source, with the
weak-solution and second-order Taylor notions they use. The touching statement
`PegdenSmartTouchingStmt` (`Inputs/Proposed.lean`) is built from them, and these statements are
explicit hypotheses of the theorems that use them; nothing here is proved.

Source: W. Pegden and C. K. Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013),
627-642, arXiv:1105.0111v2.

Conventions of the source: `u` is a *weak solution* of
`Δu = s` in `B_1` if `∫ u Δφ = ∫ s φ` for all `φ ∈ C_0^∞(B_1)`; *twice differentiable
at `x`* means a second-order Peano expansion at `x` (`HasSecondOrderTaylorAt`, with the symmetric
matrix `D²u(x)`); `D²u(x) < 0` means negative definite. -/

open MeasureTheory

namespace RandomSandpile

variable {d : ℕ}

/-- `u` is a weak solution of `Δu = s` in the open set `U`: `∫ u Δφ = ∫ s φ` for
every `φ ∈ C_0^∞(U)` (smooth, compactly supported, support in `U`), `Δφ = tr D²φ`. -/
def IsWeakSolutionLaplace (U : Set (Rd d)) (u s : Rd d → ℝ) : Prop :=
  ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x, u x * Matrix.trace (hessian φ x) = ∫ x, s x * φ x

/-- **Literature input. Pegden-Smart, Proposition 2.5** (the paper cites Caffarelli-Cabré,
*Fully Nonlinear Elliptic Equations*, Theorem 3.2, for it). Source text (arXiv:1105.0111v2, Proposition 2.5, p. 6):
"If `s ∈ L^∞(B_1)` and `u ∈ C(B_1)` is a weak solution of `Δu = s` in `B_1`, and
`sup_{B_1} u > sup_{∂B_1} u`, then the set `{x ∈ B_1 | u(x) > sup_{∂B_1} u, u is twice
differentiable at x, and D²u(x) < 0}` has positive measure."

Reading. `sup_{∂B_1} u` presupposes the boundary values, so `u` is taken continuous on the closed
ball `B̄_1`; both suprema are then finite. `s ∈ L^∞(B_1)` is `MemLp s ∞` for Lebesgue measure on
`B_1`. Stated for `d ≥ 2`, as in the source. -/
def PegdenSmartProp25Stmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ s u : Rd d → ℝ,
    MemLp s ⊤ (volume.restrict (Metric.ball (0 : Rd d) 1)) →
    ContinuousOn u (Metric.closedBall 0 1) →
    IsWeakSolutionLaplace (Metric.ball 0 1) u s →
    sSup (u '' Metric.sphere 0 1) < sSup (u '' Metric.ball 0 1) →
      0 < volume {x : Rd d | x ∈ Metric.ball 0 1 ∧ sSup (u '' Metric.sphere 0 1) < u x ∧
        ∃ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ),
          X.IsSymm ∧ HasSecondOrderTaylorAt u x p X ∧ (-X).PosDef}

/-- **Literature input. Pegden-Smart, Proposition 2.4** (the paper cites M. Christ, *Lectures on singular
integral operators*, CBMS 77, AMS 1990, Chapter III, Theorem 4, for it). Source text (arXiv:1105.0111v2,
Proposition 2.4, p. 6):
"If `s ∈ L^∞(B_1)` and `u ∈ C(B_1)` is a weak solution of `Δu = s` in `B_1`, then `u` is twice
differentiable and `Δu = s` almost everywhere in `B_1`."

The Lean form keeps the first conclusion only (twice differentiable almost everywhere in `B_1`) and
drops the conjunct "`Δu = s` almost everywhere": a weakening of the source statement. -/
def PegdenSmartProp24Stmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ s u : Rd d → ℝ,
    MemLp s ⊤ (volume.restrict (Metric.ball (0 : Rd d) 1)) →
    ContinuousOn u (Metric.ball 0 1) →
    IsWeakSolutionLaplace (Metric.ball 0 1) u s →
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Rd d) 1)), PeanoTwiceDifferentiableAt u x

/-- **Literature input. Viscosity solutions of `|Δu| ≤ K` are weak solutions of `Δu = s`
with `|s| ≤ K`.** In the terminology of Crandall-Ishii-Lions: a continuous `u` that is a viscosity
subsolution of `-Δu - K = 0` and a viscosity supersolution of `-Δu + K = 0` in `U` is a weak
(distributional) solution of `Δu = s` in `U` for a measurable `s` with `|s| ≤ K`. Source: H. Ishii,
*On the equivalence of two notions of weak solutions, viscosity solutions and distribution solutions*,
Funkcial. Ekvac. 38 (1995), 101-120, Theorem 1, p. 103, with the standard step from the two
distributional inequalities to a bounded density; the domain is nonempty. That step is classical
potential theory: `u + K|x|²/2d` and `K|x|²/2d - u` are subharmonic, so `Δu` is a measure between `-K`
and `K` times Lebesgue measure, hence has a density. Pegden and Smart state no such step and cite
nothing for it; they obtain weak solutions directly from the discrete Laplacian bound by summation by
parts (their Lemma 3.1). The step is needed here because `PegdenSmartTouchingStmt` states its
hypotheses in the viscosity sense. -/
def ViscosityWeakLaplaceStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ U : Set (Rd d), IsOpen U → U.Nonempty → ∀ (K : ℝ) (u : Rd d → ℝ),
    ContinuousOn u U →
    ViscFromAboveGE (fun X => X.trace + K) U u → ViscFromBelowLE (fun X => X.trace - K) U u →
      ∃ s : Rd d → ℝ, Measurable s ∧ (∀ x, |s x| ≤ K) ∧ IsWeakSolutionLaplace U u s

end RandomSandpile

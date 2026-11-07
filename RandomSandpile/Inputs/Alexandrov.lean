import RandomSandpile.Defs.Viscosity
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Alexandrov's theorem

The proposition `AlexandrovStmt` is a literature input. It is not proved in the library: each consumer
takes it as an explicit hypothesis. -/

open MeasureTheory

namespace RandomSandpile

/-- **Literature input. Alexandrov's theorem: convex functions are twice differentiable a.e.**

Source: L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, CRC Press 1992,
Section 6.4, Theorem 1, p. 242. Statement: let `f : ℝⁿ → ℝ` be convex; then for
`Lⁿ`-a.e. `x` there are `Df(x)` and a symmetric `D²f(x)` with
`|f(y) - f(x) - Df(x)·(y - x) - ½ (y - x)ᵀ D²f(x) (y - x)| = o(|y - x|²)` as `y → x`.

Lean form: `HasSecondOrderTaylorAt f x p X` is that Peano expansion with gradient `p = Df(x)` and
matrix `X = D²f(x)` (`½ yᵀXy = qM X y`). Consumer: the touching lemma of Pegden and Smart
(Proposition 2.5, `PegdenSmartTouchingStmt`), through sup-convolutions, which are semiconvex
(`RandomSandpile/Infra/Touching.lean`). -/
def AlexandrovStmt : Prop :=
  ∀ (d : ℕ) (f : Rd d → ℝ), ConvexOn ℝ Set.univ f →
    ∀ᵐ x ∂(volume : Measure (Rd d)), ∃ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ),
      X.IsSymm ∧ HasSecondOrderTaylorAt f x p X

end RandomSandpile

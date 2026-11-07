import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeCore
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeGreen
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeErgodic
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizePoincare
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeLatticeSum
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeHarnack
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeGradient
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeReflect
import RandomSandpile.Infra.SubadditiveCubes

/-!
# Lemma 7.3 (`divisible_homogenize`) from its two inputs

Assembly of the decomposition of `DivisibleHomogenizeStmt` (`Steps/Sec7/DivisibleHomogenize.lean`,
`paper/random_piles-corrected.tex`):

* (ergodic) `CubeErgodicStmt` from Lattice-Probability's rectangle ergodic theorem
  `LatticeProb.RectangleErgodicAll` (`cubeErgodic_of_rectangleErgodicAll`);
* (exit_time) and the boundary layer bound, proved (`greenBallExitTime`,
  `greenBallBoundaryLayer`);
* the discrete Poincaré inequality on boxes, proved (`DivisibleHomogenize.sum_abs_sub_avg_le_box`);
* the deterministic homogenization `GreenHomogenizeStmt` from these and the summed (difference)
  estimate `GreenBallGradientSumStmt` (`greenHomogenize_of_poincare`);
* the summed (difference) estimate from the pointwise one `GreenBallDifferenceStmt`
  and a lattice sum (`greenBallGradientSum_of_difference`).

What remains open is exactly: `LatticeProb.RectangleErgodicAll d` (a `Prop` of
Lattice-Probability, not proved there), and (difference) `GreenBallDifferenceStmt` (cited by the
paper from [LL10]; to be derived from the Lawler-Limic difference estimate
`LawlerLimicHarmonicDifferenceStmt` and bounds on `g_n`).
-/

namespace RandomSandpile

open DivisibleHomogenize

/-- The discrete Poincaré inequality on boxes, in the form used by the deterministic argument. -/
theorem boxPoincare (d : ℕ) : BoxPoincare d :=
  fun l u L hL g => sum_abs_sub_avg_le_box l u L hL g

/-- **Deterministic homogenization** from the summed (difference) estimate. -/
theorem greenHomogenize_of_gradientSum (hGrad : GreenBallGradientSumStmt) : GreenHomogenizeStmt :=
  greenHomogenize_of_poincare boxPoincare greenBallExitTime greenBallBoundaryLayer hGrad

/-- **Lemma 7.3** (`divisible_homogenize`) from the rectangle ergodic theorem of
Lattice-Probability and the summed (difference) estimate for `g_n`. -/
theorem divisibleHomogenize_of_inputs (hErg : ∀ d : ℕ, LatticeProb.RectangleErgodicAll d)
    (hGrad : GreenBallGradientSumStmt) : DivisibleHomogenizeStmt :=
  divisibleHomogenize_of_steps (cubeErgodic_of_rectangleErgodicAll hErg)
    (greenHomogenize_of_gradientSum hGrad)

/-- **Lemma 7.3** (`divisible_homogenize`) from the rectangle ergodic theorem of
Lattice-Probability and the (difference) estimate for `g_n`. -/
theorem divisibleHomogenize_of_difference (hErg : ∀ d : ℕ, LatticeProb.RectangleErgodicAll d)
    (hDiff : GreenBallDifferenceStmt) : DivisibleHomogenizeStmt :=
  divisibleHomogenize_of_inputs hErg (greenBallGradientSum_of_difference hDiff)

/-- **The summed (difference) estimate from the Lawler-Limic input**: the
Lawler-Limic difference estimate and the Harnack inequality bound `|∇_y g_n(x, y)| |x - y|` by
`C_δ g_n(x, y)` away from `x`, and the radial supersolution bounds the weighted occupation
`∑_{y ≠ x} g_n(x, y) / |y - x|` by `3 (n + 1)`. -/
theorem greenBallGradientSum_of_lawlerLimic (hLL : LawlerLimicHarmonicDifferenceStmt) :
    GreenBallGradientSumStmt :=
  greenBallGradientSum_of_harnack (greenBallHarnackGradient_of_lawlerLimic hLL) greenBallWeightedSum

/-- **Lemma 7.3** (`divisible_homogenize`) from the rectangle ergodic theorem of
Lattice-Probability and the Lawler-Limic difference estimate for harmonic functions. -/
theorem divisibleHomogenize_of_rectangleErgodicAll_lawlerLimic
    (hErg : ∀ d : ℕ, LatticeProb.RectangleErgodicAll d) (hLL : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleHomogenizeStmt :=
  divisibleHomogenize_of_inputs hErg (greenBallGradientSum_of_lawlerLimic hLL)

/-- **(ergodic)**: the rectangle ergodic theorem `RandomSandpile.rectangleErgodic`
(`Infra/SubadditiveCubes.lean`, positive orthant) transported to all orthants by coordinate
reflections (`cubeErgodic_of_rectangleErgodic`). -/
theorem cubeErgodic : CubeErgodicStmt :=
  cubeErgodic_of_rectangleErgodic fun _ hd => rectangleErgodic hd

/-- **Lemma 7.3** (`divisible_homogenize`) from the Lawler-Limic difference
estimate for harmonic functions (`LawlerLimicHarmonicDifferenceStmt`, the only hypothesis): the
ergodic input is proved (`cubeErgodic`), the Green's function estimates are proved
(`greenBallExitTime`, `greenBallBoundaryLayer`, `greenBallWeightedSum`) or derived from the
Lawler-Limic estimate and the Harnack inequality (`greenBallGradientSum_of_lawlerLimic`). -/
theorem divisibleHomogenize_of_lawlerLimic (hLL : LawlerLimicHarmonicDifferenceStmt) :
    DivisibleHomogenizeStmt :=
  divisibleHomogenize_of_steps cubeErgodic
    (greenHomogenize_of_gradientSum (greenBallGradientSum_of_lawlerLimic hLL))

end RandomSandpile

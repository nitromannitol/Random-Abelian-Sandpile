import RandomSandpile.Draft.Section7
import RandomSandpile.Steps.Sec7.OdometerLowerBound
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic

/-!
# Steps of Lemma 7.3 (homogenization of the Green potentials on balls)

Carving of `RandomSandpile.DivisibleHomogenizeStmt` (Lemma 7.3, `divisible_homogenize`,
`paper/random_piles-corrected.tex`, proof 1127-1206) into steps and the reduction
`divisibleHomogenize_of_steps`.

Notation: `B_n = ballZ0 n`, `g_n = greenKilled B_n`, `η_avg = E η(0)`
(`meanEta`), `r_n - d_n = ∑_{y ∈ B_n} g_n(·, y) (η(y) - η_avg)` ((eq1)).

The printed proof has two inputs and one deterministic argument.

* **(ergodic)**. For `β` dyadic, the averages of `η` over the pieces
  `A_{βn}(z_i)` of a dyadic partition converge to `E η(0)`. The printed citation ("Proposition
  sub-additive-ergodic", i.e. Lemma 5.5) is mislabelled (N8(a)): what is used is the pointwise
  ergodic theorem for box averages of `η`. Step `CubeErgodicStmt`: almost surely, for every
  `j ∈ ℕ` and `k ∈ ℤ^d`, `N^{-d} ∑_{y ∈ Q_{j,k}(N)} (η(y) - E η(0)) → 0` as `N → ∞`, where
  `Q_{j,k}(N) = ℤ^d ∩ N ∏_i [k_i 2^{-j}, (k_i + 1) 2^{-j})` (`dyadicCube`, Lattice-Probability's
  `rectBox`). It is the specialisation of Lattice-Probability's rectangle ergodic theorem
  `LatticeProb.RectangleErgodicAll` to `h(η) = η(0) - E η(0)` and the shift action
  (`Proofs/Sec7/DivisibleHomogenizeErgodic.lean`).
* **Deterministic homogenization**. Step `GreenHomogenizeStmt`: for every bounded
  `f : ℤ^d → ℝ` whose dyadic cube averages vanish in the limit (the conclusion of (ergodic) for
  `f = η - E η(0)`), `sup_{x ∈ B_n} |∑_{y ∈ B_n} g_n(x, y) f(y)| = o(n²)`. The paper's argument
  (partition of `B_n` into the cubes `A_{βn}(z_i)`, pooling and redistribution of grains, the
  errors `𝓔_1, …, 𝓔_4`) is carried out in `Proofs/Sec7/DivisibleHomogenizeCore.lean` from the
  Green's function estimates below; there the pooling point `z_i` of a cube is replaced by the
  average over the cube, so that the rearrangement error `𝓔_3 + 𝓔_4` of a cube of side `βn` is
  bounded by `βn` times the sum of `|∇_y g_n(x, y)|` over the cube (a discrete Poincaré
  inequality), and its total is `C_δ β n²` (N8(b): not `C β^{-1} n`).
* **(exit_time)**, first line (and "comparing to a quadratic"): step
  `GreenBallExitTimeStmt`, `∑_{y ∈ B_n} g_n(x, y) ≤ ((n + 1)² - |x|²) / (2d)`.
* **Boundary layer**: step `GreenBallBoundaryLayerStmt`,
  `∑_{y ∈ B_n, |y| ≥ ρ} g_n(x, y) ≤ ((n + 1)² - ρ²) / (2d)` for `0 ≤ ρ ≤ n`. It bounds the
  contribution of the cubes meeting `B_n \ B_{(1-δ)n}`, where (difference) is not available
  (the printed proof applies (difference) to them although it requires `|y| < (1 - δ) n`). It
  also replaces the second line of (exit_time) and the cubes `𝓐_x` near `x`,
  which the Poincaré form of the rearrangement does not need to remove.
* **(difference)** (with `(1-δ) n` for the printed `(1-δ) n²`, N8(c)). Step
  `GreenBallDifferenceStmt`: `|g_n(x, y + e_i) - g_n(x, y)| ≤ C_δ (1 + |x - y|)^{1-d}` for
  `|x|, |y| < (1 - δ) n`. The printed additive term `O_δ(n^{2-2d})` is absorbed, since
  `|x - y| < 2n`. The deterministic argument uses its summed form, step
  `GreenBallGradientSumStmt`: `∑_{y ∈ B_{(1-δ)n}} ∑_i |g_n(x, y + e_i) - g_n(x, y)| ≤ C_δ n`.
  Both come from the Lawler-Limic difference estimate for harmonic functions
  (`LawlerLimicHarmonicDifferenceStmt`, `Inputs/Proposed.lean`) applied to `g_n(x, ·)` on balls
  avoiding `x` and `∂B_n`, together with bounds on `g_n` .

The reduction `divisibleHomogenize_of_steps` (this file) takes `CubeErgodicStmt` and
`GreenHomogenizeStmt`, with `C = 1` (the conclusion is `sup_{B_n} |r_n - d_n| = o(n²)`).
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- The dyadic cube `Q_{j,k}(N) = ℤ^d ∩ N ∏_i [k_i 2^{-j}, (k_i + 1) 2^{-j})` (the pieces
`A_{βn}(z_i)` with `β = 2^{-j}`, before intersecting with `B_n`), as
Lattice-Probability's `rectBox` with corners `2^{-j} k` and `2^{-j} (k + 1)`. -/
def dyadicCube (j : ℕ) (k : Site d) (N : ℕ) : Finset (Site d) :=
  rectBox (fun i => (k i : ℝ) / 2 ^ j) (fun i => ((k i : ℝ) + 1) / 2 ^ j) N

/-- **(ergodic)**). Almost surely, for every dyadic scale `2^{-j}`
and every `k ∈ ℤ^d`, the average of `η - E η(0)` over the dyadic cube `Q_{j,k}(N)`, normalised by
`N^d`, tends to `0` as `N → ∞`. -/
def CubeErgodicStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ᵐ η ∂E.P, ∀ (j : ℕ) (k : Site d),
    Tendsto (fun N : ℕ => (∑ y ∈ dyadicCube j k N, ((η y : ℝ) - meanEta E.P)) / (N : ℝ) ^ d)
      atTop (𝓝 0)

/-- **Deterministic homogenization of the Green potential**. For `d ≥ 2`, a
bounded `f : ℤ^d → ℝ` whose normalised dyadic cube sums tend to `0` has Green potential in `B_n`
of order `o(n²)`, uniformly on `B_n`: for every `ε > 0`, eventually
`|∑_{y ∈ B_n} g_n(x, y) f(y)| ≤ ε n²` for all `x ∈ B_n`. -/
def GreenHomogenizeStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (f : Site d → ℝ) (K : ℝ), (∀ y, |f y| ≤ K) →
    (∀ (j : ℕ) (k : Site d),
      Tendsto (fun N : ℕ => (∑ y ∈ dyadicCube j k N, f y) / (N : ℝ) ^ d) atTop (𝓝 0)) →
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x ∈ ballZ0 (d := d) (n : ℝ),
      |greenPotential (ballZ0 (n : ℝ)) f x| ≤ ε * (n : ℝ) ^ 2

/-- **(exit_time)**, first line (1147): `∑_{y ∈ B_n} g_n(x, y) ≤
((n + 1)² - |x|²) / (2d)` for `x ∈ B_n`, by comparison with the quadratic
`((n + 1)² - |y|²) / (2d)`, whose Laplacian is `-1`. -/
def GreenBallExitTimeStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (n : ℕ), ∀ x ∈ ballZ0 (d := d) (n : ℝ),
    greenPotential (ballZ0 (n : ℝ)) (fun _ => 1) x ≤ (((n : ℝ) + 1) ^ 2 - ‖toE x‖ ^ 2) / (2 * d)

/-- **Boundary layer**: for `0 ≤ ρ ≤ n`,
`∑_{y ∈ B_n, |y| ≥ ρ} g_n(x, y) ≤ ((n + 1)² - ρ²) / (2d)` for every `x`, by comparison with
`min((n + 1)² - |y|², (n + 1)² - ρ²) / (2d)`. -/
def GreenBallBoundaryLayerStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (n : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ n → ∀ x : Site d,
    greenPotential (ballZ0 (n : ℝ)) (fun y => if ρ ≤ ‖toE y‖ then 1 else 0) x ≤
      (((n : ℝ) + 1) ^ 2 - ρ ^ 2) / (2 * d)

/-- **(difference)** (with `(1 - δ) n` for the printed `(1 - δ) n²`): for
`d ≥ 2` and `0 < δ < 1` there is `C_δ` with `|g_n(x, y + e_i) - g_n(x, y)| ≤
C_δ (1 + |x - y|)^{1-d}` for all `n` and `|x|, |y| < (1 - δ) n`. The printed `O(|x - y|^{1-d}) +
O_δ(n^{2-2d})` is of this form since `|x - y| < 2n`. -/
def GreenBallDifferenceStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x y : Site d),
    x ∈ ballZ0 ((1 - δ) * n) → y ∈ ballZ0 ((1 - δ) * n) → ∀ i : Fin d,
      |greenKilled (ballZ0 (n : ℝ)) x (y + unit i) - greenKilled (ballZ0 (n : ℝ)) x y| *
          (1 + ‖toE (x - y)‖) ^ (d - 1) ≤ C

/-- **(difference), summed**: for `d ≥ 2` and `0 < δ < 1` there is `C_δ` with
`∑_{y ∈ B_{(1-δ)n}} ∑_i |g_n(x, y + e_i) - g_n(x, y)| ≤ C_δ n` for all `n` and
`x ∈ B_{(1-δ)n}`. It follows from `GreenBallDifferenceStmt` and
`∑_{|z| < 2n} (1 + |z|)^{1-d} = O(n)`. -/
def GreenBallGradientSumStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ),
    ∀ x ∈ ballZ0 (d := d) ((1 - δ) * n),
      ∑ᶠ y ∈ ballZ0 (d := d) ((1 - δ) * n), ∑ i : Fin d,
        |greenKilled (ballZ0 (n : ℝ)) x (y + unit i) - greenKilled (ballZ0 (n : ℝ)) x y| ≤
          C * n

/-- **Gradient bound from the Harnack inequality and the Lawler-Limic difference estimate**
(the route through `LawlerLimicHarmonicDifferenceStmt`): for `d ≥ 2` and
`0 < δ < 1` there are `C_δ`, `R_δ` with `|g_n(x, y + e_i) - g_n(x, y)| |x - y| ≤ C_δ g_n(x, y)`
for `|x|, |y| < (1 - δ) n` and `|x - y| ≥ R_δ`. The Lawler-Limic estimate on a ball `B(y, ρ)`,
`ρ ≈ c_δ |x - y|`, on which `g_n(x, ·)` is nonnegative and harmonic, bounds the difference by
`C ρ⁻¹ sup_{B(y,ρ)} g_n(x, ·)`, and the Harnack inequality bounds the supremum by `C g_n(x, y)`.
In `d = 2` this is weaker than the pointwise (difference) (`g_n(x, y)` grows like
`log(n / |x - y|)`), but its sum over `y` is still `O(n)` (`GreenBallWeightedSumStmt`). -/
def GreenBallHarnackGradientStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C R₀ : ℝ, 0 < C ∧ ∀ (n : ℕ) (x y : Site d),
    x ∈ ballZ0 ((1 - δ) * n) → y ∈ ballZ0 ((1 - δ) * n) → R₀ ≤ ‖toE (x - y)‖ → ∀ i : Fin d,
      |greenKilled (ballZ0 (n : ℝ)) x (y + unit i) - greenKilled (ballZ0 (n : ℝ)) x y| *
          ‖toE (x - y)‖ ≤ C * greenKilled (ballZ0 (n : ℝ)) x y

/-- **Weighted occupation bound**: for `d ≥ 2`,
`∑_{y ∈ B_n, y ≠ x} g_n(x, y) / |y - x| ≤ C (n + 1)` for `x ∈ B_n`, by comparison with a
multiple of `2n + 2 - |y - x|`, since `Δ_{ℤ^d} |z| ≥ c_d / |z|` for `z ≠ 0` (the lattice
analogue of `Δ |z| = (d - 1) / |z|`). -/
def GreenBallWeightedSumStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), ∀ x ∈ ballZ0 (d := d) (n : ℝ),
    greenPotential (ballZ0 (n : ℝ)) (fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹) x ≤
      C * ((n : ℝ) + 1)

namespace DivisibleHomogenize

/-- `r_n - d_n` is the Green potential of `η - m` ((eq1)). -/
theorem greenPotentialBall_sub_mean (n : ℕ) (η : Config d) (m : ℝ) (x : Site d) :
    greenPotentialBall n η x - greenPotentialBallMean n m x =
      greenPotential (ballZ0 (n : ℝ)) (fun y => (η y : ℝ) - m) x := by
  obtain ⟨B, hB⟩ := (OdometerLowerBound.ballZ0_finite (d := d) (n : ℝ)).exists_finset_coe
  rw [greenPotentialBall, greenPotentialBallMean, ← hB, greenPotential_coe_finset,
    greenPotential_coe_finset, greenPotential_coe_finset, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

end DivisibleHomogenize

/-- **Reduction for Lemma 7.3**: (ergodic) and the deterministic homogenization of
the Green potential give `DivisibleHomogenizeStmt`, with `C = 1`. Almost surely `η` is bounded by
`η_min, η_max` at every site (countably many), so `f = η - E η(0)` is bounded. -/
theorem divisibleHomogenize_of_steps (hErg : CubeErgodicStmt) (hHom : GreenHomogenizeStmt) :
    DivisibleHomogenizeStmt := by
  intro d hd E
  have hb : ∀ᵐ η ∂E.P, ∀ x : Site d, E.ηmin ≤ η x ∧ η x ≤ E.ηmax :=
    ae_all_iff.2 E.bounded
  filter_upwards [hErg d hd E, hb] with η hη hηb
  set m := meanEta E.P
  have hK : ∀ y, |(η y : ℝ) - m| ≤ |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| + |m| := by
    intro y
    have h1 : (E.ηmin : ℝ) ≤ η y := by exact_mod_cast (hηb y).1
    have h2 : (η y : ℝ) ≤ E.ηmax := by exact_mod_cast (hηb y).2
    have h3 : |(η y : ℝ)| ≤ |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| := by
      rw [abs_le]; constructor <;> cases abs_cases (E.ηmin : ℝ) <;>
        cases abs_cases (E.ηmax : ℝ) <;> linarith
    calc |(η y : ℝ) - m| ≤ |(η y : ℝ)| + |m| := abs_sub _ _
      _ ≤ _ := by linarith
  refine ⟨1, one_pos, fun ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hHom d hd (fun y => (η y : ℝ) - m) _ hK hη ε hε
  refine ⟨n₀, fun n hn x hx => ?_⟩
  rw [DivisibleHomogenize.greenPotentialBall_sub_mean, mul_one]
  exact hn₀ n hn x hx

end RandomSandpile

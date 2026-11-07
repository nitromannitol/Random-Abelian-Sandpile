import RandomSandpile.Defs.Lattice
import RandomSandpile.Defs.Domain
import RandomSandpile.Defs.Toppling
import RandomSandpile.Defs.Environment
import RandomSandpile.Defs.Mu
import RandomSandpile.Defs.Effective
import RandomSandpile.Defs.Viscosity
import RandomSandpile.Defs.Odometer
import RandomSandpile.Defs.Subadditive
import RandomSandpile.Defs.Green
import RandomSandpile.Defs.Divisible

/-! # Foundational definitions of the paper (Sections 1-6)

* `RandomSandpile.Defs.Lattice`: `ℤ^d`, `ℝ^d`, neighbours, `∂A`, `Ā`, `Δ_{ℤ^d}`, `Δ_i`, balls, cubes,
  `W_n`, `[x]`, `q_M`, `q_l`, supergradient and subgradient sets;
* `RandomSandpile.Defs.Domain`: bounded Lipschitz domains;
* `RandomSandpile.Defs.Toppling`: toppling functions, legal, locally legal and stabilizing topplings,
  stable and recurrent sandpiles;
* `RandomSandpile.Defs.Environment`: configurations, translations, the random environment;
* `RandomSandpile.Defs.Mu`: perturbed sub/supersolutions, `μ`, `μ*`, concave envelopes and
  supergradients on `ℝ^d` (Section 5);
* `RandomSandpile.Defs.Effective`: the deterministic limits `μ(l, M)`, `μ*(l, M)`, the effective
  operator `F̄_η` and the single-source operator `F̄_0` (Sections 1, 5, 6);
* `RandomSandpile.Defs.Viscosity`: Hessians, second-order Taylor expansions, degenerate
  ellipticity, test-function viscosity inequalities and solutions, weak-* convergence in
  `L^∞(ℝ^d)` (Sections 1, 7, 9). -/

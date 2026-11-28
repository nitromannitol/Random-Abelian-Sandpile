# Convergence of the random Abelian sandpile

[![CI](https://github.com/nitromannitol/Random-Abelian-Sandpile/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Random-Abelian-Sandpile/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Random-Abelian-Sandpile/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Random-Abelian-Sandpile/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee,
> [*Convergence of the random Abelian sandpile*](https://arxiv.org/abs/1909.07849),
> Annals of Probability 49(6) (2021), 3168–3196,
> [doi:10.1214/21-AOP1528](https://doi.org/10.1214/21-AOP1528).

The paper proves that the abelian sandpile, started on a large domain from a random stationary and
ergodic configuration of chips, has a deterministic scaling limit, given by an elliptic obstacle
problem. All 28 numbered results are proved in Lean with only the standard axioms, and so are the
results the paper quotes from other works and the two theorems of Section 9 that it states without
proof. Nothing is assumed beyond the setting of the paper. The statements follow a corrected draft;
Theorem 9.2 is false as printed and is proved in a corrected form.

## The paper

A *sandpile* on `ℤᵈ`, `d ≥ 2`, is a function `η : ℤᵈ → ℤ`, a number of chips at each site. A site
with at least `2d` chips is unstable and *topples*: it gives one chip to each of its `2d` neighbours.
Toppling unstable sites until none is left *stabilizes* the sandpile. The final configuration does
not depend on the order of the topplings, and the *odometer* `v(x)` counts how often `x` topples. A
*toppling function* `u ≥ 0` is *legal* if it can be carried out by toppling only unstable sites, and
*stabilizing* if `η + Δu ≤ 2d − 1`, where `Δ` is the graph Laplacian of `ℤᵈ`; the odometer is the
largest legal and the smallest stabilizing toppling function.

Pegden and Smart proved that sandpiles started from a single source, or from a periodic
configuration, have scaling limits. This paper treats random initial configurations. The
background `η` is random, with a law that is stationary and ergodic under the shifts of `ℤᵈ`, and
almost surely bounded, `η_min ≤ η ≤ η_max`. It has *high density* if `E η(0) > 2d − 1`.

- **Theorem 1.1.** Start from `η` on a discretized domain `W_n = nW ∩ ℤᵈ` and stabilize in `ℤᵈ`.
  Almost surely the rescaled odometers converge to the solution of an obstacle problem with two
  operators, and the rescaled sandpiles converge to a deterministic limit. One operator, `F̄_η`,
  depends on the law of `η`; the other, `F̄₀`, is the one of the single-source sandpile.
- **Theorem 8.2.** In the *divisible sandpile* the mass is real-valued, and a site with mass above
  `1` keeps `1` and sends the excess equally to its neighbours. Started from `η`, it has the same
  scaling limit as the divisible sandpile started from the constant `E η(0)`.
- **Theorem 9.1.** The same convergence holds with the open boundary condition, where chips that
  leave `W_n` are lost, and the limit solves a Dirichlet problem for `F̄_η`.
- **Theorem 9.2.** Sandpiles with `n` chips at the origin on a random background converge.

The *effective operator* `F̄_η` is a deterministic, degenerate elliptic operator on symmetric
matrices. It is defined in Section 6 through the almost sure limits of the monotone quantities `μ`
and `μ*` of Section 5, which come from the subadditive ergodic theorem. The operator `F̄₀` is that
of Pegden and Smart: `F̄₀(M)` is the least `s` such that some `u : ℤᵈ → ℤ` with `Δu ≤ 2d − 1`
satisfies `u(y) ≥ ½ yᵀ(M − sI)y` for all `y`.

Precisely, let `W` be a bounded Lipschitz domain and `η` of high density.

**Theorem 1.1.** Let `v_n` and `s_n` be the odometer and the final configuration of the sandpile that
starts from `η` on `W_n` and stabilizes in `ℤᵈ`. Almost surely, the rescaled odometers
`v̄_n(x) = n⁻² v_n([nx])` converge uniformly on `ℝᵈ` to

`v̄ = min { v ∈ C(ℝᵈ) : v ≥ 0, F̄_η(D²v) ≥ 0 in W, F̄₀(D²v) ≤ 0 in ℝᵈ }`,

in the viscosity sense with test functions touching from below. The rescaled sandpiles
`s̄_n(x) = s_n([nx])` converge weakly-* in `L^∞` to a deterministic `s` with `∫ s = |W| E η(0)`,
`s ≤ 2d − 1`, `s = 0` outside `B_R(W)` for a radius `R` depending on `W`, `d` and `η_max`, and
`s = Δv̄ + E η(0) 1_W` weakly.

**Theorem 9.1.** Let `v_n` be the odometer of the sandpile on `W_n` with the open boundary condition.
Almost surely, `v̄_n` converges uniformly to the function `v̄ ∈ C(ℝᵈ)` that vanishes outside `W` and
whose restriction to the closure of `W` is the unique viscosity solution of `F̄_η(D²v̄) = 0` in `W`,
`v̄ = 0` on `∂W`.

**Theorem 9.2** (corrected). Let `η ≤ 2d − 2`, and let `v_n` be the odometer of the sandpile with `n`
chips at the origin on the background `η`. Almost surely every `v_n` is finite, and
`n^{−2/d} v_n([n^{1/d} x])` converges locally uniformly on `ℝᵈ ∖ {0}` to `v̄ + G`, where `G` is the
fundamental solution of `−Δ` and `v̄` is the least element of

`{ w ∈ C(ℝᵈ) : w + G ≥ 0, F̄ᴿ_η(D²(w + G)) ≥ 0 in ℝᵈ ∖ {0} }`,

in the viscosity sense with test functions touching from below. The operator `F̄ᴿ_η` is defined as
`F̄_η`, with recurrent functions in place of the legal and stabilizing ones (correction C13). It is
continuous and degenerate elliptic, and `F̄ᴿ_η(M + tI) = F̄ᴿ_η(M) − dt`. A sandpile is *recurrent*
on a finite set `A` if it is obtained from the constant sandpile `2d − 1` on `A` by adding chips and
toppling legally in `A`. If `η` is almost surely recurrent on every finite set, then `F̄ᴿ_η = F̄_η`;
for `η ≡ 0` the two operators differ.

## The main theorems in Lean

The main theorems are in [`RandomSandpile/Assembly/Main.lean`](RandomSandpile/Assembly/Main.lean),
in the namespace `RandomSandpile`. None takes a hypothesis: each has as its type a statement
`…Stmt`, written out in [`RandomSandpile/Draft/`](RandomSandpile/Draft/) with the paper's notation
in its docstring.

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1 | `RandomSandpile.mainTheorem_final` |
| Theorem 8.2 | `RandomSandpile.divisibleTheorem_final` |
| Theorem 9.1 | `RandomSandpile.openBoundaryTheorem_final` |
| Theorem 9.2, corrected | `RandomSandpile.singleSourceTheoremRecurrent_final` |

How to read the statements: the law of the background is a `RandomSandpile.RandomEnvironment d`,
high density is `HighDensity E.P`, and `W` is a bounded Lipschitz domain, `IsLipschitzDomain W`.
The effective operators `F̄_η` and `F̄ᴿ_η` are `effOp E` and `effOpRecurrent E`.

Further forms of these results are proved as well:

| Result | Lean declaration |
| --- | --- |
| Theorem 1.1 with the printed radius, depending only on `W`, `d` and `E η(0)` | `RandomSandpile.mainTheoremPrinted_final` |
| Theorem 1.1 with the radius chosen after the law | `RandomSandpile.mainTheoremLawRadius_final` |
| Theorem 9.2 for every background whose odometers are finite and have a vanishing tail | `RandomSandpile.singleSourceTheoremRecurrentVT_final` |
| `F̄ᴿ_η = F̄_η` for backgrounds recurrent on every finite set | `RandomSandpile.recurrentOperatorIdentification_final` |
| `F̄ᴿ_η ≠ F̄_η` for `η ≡ 0` | `RandomSandpile.recurrentOperatorZeroBackgroundDifference_final` |
| `F̄ᴿ_η` is continuous, degenerate elliptic, and `F̄ᴿ_η(M + tI) = F̄ᴿ_η(M) − dt` | `RandomSandpile.recurrentOperatorProperties_final` |
| Theorem 9.2 with `F̄_η`, in dimension two | `RandomSandpile.singleSourceTheoremD2_final` |
| Lemma 6.2 with the explicit constant `c(1 − β)²` | `RandomSandpile.strictConcavityBeta_final` |

## All numbered results

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `RandomSandpile.mainTheorem_final` | Sandpiles on `W_n` with a random background converge to the solution of an obstacle problem for `F̄_η`. |
| Proposition 3.1 | `RandomSandpile.leastAction_final` | The least action principle: the odometer is the largest legal and the smallest stabilizing toppling function. |
| Proposition 3.2 | `RandomSandpile.abelianDecomposition_final` | A toppling function with boundary values splits into the odometer and the topplings from the boundary. |
| Proposition 3.3 | `RandomSandpile.burning_final` | The maximum and comparison principles for the sandpile equation, from Dhar's burning algorithm. |
| Proposition 3.4 | `RandomSandpile.recurrentOfToppled_final` | If every site of a connected set has toppled, what remains there is recurrent. |
| Lemma 5.1 | `RandomSandpile.stabilizingLegal_final` | The solution with the boundary values of a legal function has a larger superdifferential; dually for stabilizing functions. |
| Lemma 5.2 | `RandomSandpile.abp_final` | The discrete Alexandroff–Bakelman–Pucci estimate in terms of `μ` and `μ*`. |
| Proposition 5.1 | `RandomSandpile.concaveEnvelopeRep_final` | The concave envelope on a cube is a supremum of convex combinations of `d + 1` values. |
| Lemma 5.3 | `RandomSandpile.mongeAmpereRep_final` | The measure of the superdifferential of a function equals that of its concave envelope. |
| Lemma 5.4 | `RandomSandpile.muBounded_final` | `μ` and `μ*` are bounded by a multiple of the volume, and vanish beyond explicit thresholds in `l`. |
| Proposition 5.2 | `RandomSandpile.harnackQuadratic_final` | A nonnegative function with `f(0) = 0` and bounded Laplacian grows at most quadratically. |
| Proposition 5.3 | `RandomSandpile.subadditiveErgodic_final` | The multiparameter subadditive ergodic theorem, on all bounded Lipschitz domains at once. |
| Lemma 5.5 | `RandomSandpile.muConvergence_final` | The almost sure limits `μ(l, M)` and `μ*(l, M)` of `μ` and `μ*` on `nW ∩ ℤᵈ`, divided by the volume, exist and are bounded. |
| Lemma 6.1 | `RandomSandpile.muMonotone_final` | `μ` is nondecreasing in `l` and `μ*` nonincreasing. |
| Lemma 6.2 | `RandomSandpile.strictConcavity_final` | If `α = μ(l, M) > 0`, some `w_n ∈ S(B_n, η, l, M)` lies `C α n²` below its supporting planes at contact points of `B_{βn}`, on `∂B_n`. |
| Lemma 6.3 | `RandomSandpile.muLipschitz_final` | `μ` and `μ*` are Lipschitz in `l`. |
| Lemma 6.4 | `RandomSandpile.effectiveOperatorBasic_final` | `F̄_η` is degenerate elliptic, Lipschitz and finite. |
| Lemma 7.1 | `RandomSandpile.oneDimToppling_final` | An explicit one-dimensional toppling function with a prescribed second difference. |
| Lemma 7.2 | `RandomSandpile.compactness_final` | The rescaled odometers are precompact for uniform convergence. |
| Lemma 7.3 | `RandomSandpile.divisibleHomogenize_final` | The Green potential of `η` in `B_n` is within `ε n²` of the potential of its mean. |
| Lemma 7.4 | `RandomSandpile.odometerLowerBound_final` | Under high density, every site of `B_{(1−ε)n}` topples at least once. |
| Lemma 7.5 | `RandomSandpile.flat_final` | `μ(l_M, M) = μ*(l_M, M) = 0` at `l_M = F̄_η(M)`. |
| Lemma 7.6 | `RandomSandpile.pegdenSmartRegularity_final` | Where two distinct subsequential limits `v, v'` separate, both are twice differentiable with `D²(v − v') < −δI`, and integer functions with `Δu ≤ 2d − 1` lie above the quadratics of `D²v`. |
| Proposition 8.1 | `RandomSandpile.divisibleLeastAction_final` | The least action principle for the divisible sandpile. |
| Lemma 8.1 | `RandomSandpile.divisibleHomogenizeDomain_final` | Lemma 7.3 on the domains `W_n`. |
| Theorem 8.2 | `RandomSandpile.divisibleTheorem_final` | The divisible sandpile on `W_n` has the scaling limit of the averaged divisible sandpile. |
| Theorem 9.1 | `RandomSandpile.openBoundaryTheorem_final` | With the open boundary condition, the limit solves the Dirichlet problem for `F̄_η`. |
| Theorem 9.2 | `RandomSandpile.singleSourceTheoremRecurrent_final` | Single-source sandpiles on a random background converge, with the operator `F̄ᴿ_η`. |

Propositions 3.1, 3.2, 3.4, 5.1, 5.2, 5.3 and 8.1 and Lemmas 7.1 and 7.6 are quoted in the paper
from other works. The proofs also use Alexandrov's theorem, Propositions 2.4 and 2.5 of Pegden and
Smart, Ishii's equivalence of viscosity and weak solutions, a difference estimate for discrete
harmonic functions from Lawler and Limic, and the radius bound of Fey, Levine and Peres. All of these
are proved in Lean.

## Corrections

The Lean statements follow a corrected draft of the arXiv source,
[`paper/random_piles-corrected.tex`](paper/random_piles-corrected.tex). It differs from the arXiv
source by twelve corrections, C1 to C15 (the numbers C7, C9 and C10 are not used), and a footnote
P1 to a proof. Each is marked in the source by a comment `% CORRECTION [Cn]`.
[`paper/CORRECTIONS.md`](paper/CORRECTIONS.md) lists them with their reasons, and
[`paper/make_corrected.py`](paper/make_corrected.py) produces the corrected draft from the arXiv
source.

| Id | Result | Change | Kind |
| --- | --- | --- | --- |
| C1 | Lemma 6.3 | the second inequality is reversed, `μ*(l, M) ≤ μ*(l + s, M) + sC` | false as printed |
| C2 | Lemma 6.2 | index typos: `μ(l, M)` for `μ(l_M, M)`, and `y − x₀` for `y − x` | typo |
| C3 | Theorems 1.1, 9.2 | the inequality for `F̄_η` is `≥ 0`, in the viscosity sense with test functions touching from below | false as printed |
| C4 | Lemma 6.2 | the witnesses `w_n` also satisfy the first inequality of (spreadout), as the proof uses | vacuous as printed |
| C5 | Lemma 7.1, proof of Lemma 7.2 | `g(x) ≤ C (ℓ + 1)²` in place of `g(x) ≤ C x²` | false as printed |
| C6 | Proposition 5.1 | the contact and affinity claims only for the points with positive weight | false as printed |
| C8 | Proposition 5.3 | the subadditive process is measurable and stationary | false as printed |
| C11 | Lemma 6.2 | the constant `C` also depends on `β` | constant |
| C12 | Theorem 1.1 | the radius `R` depends on `W`, `d` and `η_max` | weakening |
| C13 | Theorem 9.2 | the theorem for the recurrent operator `F̄ᴿ_η`, the extension under a vanishing tail, and the two operator statements | replacement |
| C14 | Section 8.1 | the divisible sandpile runs on a finite domain, the excess mass is `η(x) − 1`, and `v` counts the mass sent to each neighbor | definition |
| C15 | Theorem 9.1 | the limit vanishes outside `W`; uniqueness is on the closure of `W` | statement |
| P1 | Section 6 | a footnote: the continuity in `l` used to define `F̄_η` needs the constant of Lemma 6.3 uniform in `l` | proof |

- **Theorem 9.2 is false as printed.** For `d = 2` and `η ≡ 0`, `F̄_η(0) = 4/3 > 0`. Correction C13
  states it for the recurrent operator `F̄ᴿ_η`, and it is proved in this form in every dimension.
  In dimension two the statement with `F̄_η` and C3 alone is proved too.
- **C12** is a weakening adopted by the author: the printed proof gives a radius depending on
  `η_max`. The printed dependence on `W` and `E η(0)` alone is also proved, by a different argument.

The unmodified arXiv source is [`paper/random_piles.tex`](paper/random_piles.tex); both versions
are included as PDFs. [`paper/CORRECTIONS.md`](paper/CORRECTIONS.md) also lists the places where
the Lean proofs do not follow the printed argument.

## Scope

- **The random background.** A `RandomEnvironment d` is a probability measure on `ℤ^{ℤᵈ}`,
  invariant and ergodic under the shifts, with integer bounds `η_min ≤ η(x) ≤ η_max` almost surely
  at every site. Theorems 1.1 and 9.1 and Lemmas 7.4, 7.5 and 7.6 assume high density, as the paper
  does.
- **Lemma 5.4** is proved for all integer bounds, with the threshold `l ≤ −max(η_max, 0) − tr M`.
  This is the printed threshold when `η_max ≥ 2d`, as in the paper; for a negative upper bound the
  printed threshold is false.
- **Viscosity solutions** are in the sense of Crandall, Ishii and Lions, with `C²` test functions;
  supersolutions are tested from below and subsolutions from above.
- **Rescaling.** `[nx]` is the coordinatewise floor. The rescaled sandpiles are tested against all
  integrable functions (weak-* convergence in `L^∞`).
- **Theorem 9.2.** The main form assumes `η ≤ 2d − 2`; the second form assumes instead that the
  odometers are finite and have a vanishing tail far from the origin.

## Checking the proofs

- **No `sorry`.** The library has none. Each of the four comparator challenges under
  [`RandomSandpileAudit/`](RandomSandpileAudit/) contains one intentional `sorry` at the statement,
  which the matching solution file proves.
- **Standard axioms only.** [`RandomSandpileAudit/Axioms.lean`](RandomSandpileAudit/Axioms.lean)
  prints the axioms of the 36 theorems of `Main.lean`, and
  [`scripts/check_axioms.py`](scripts/check_axioms.py) fails on any axiom other than `propext`,
  `Classical.choice` and `Quot.sound`, on `sorryAx`, and on a missing report.
- **Independent check of the statements.** Theorem 1.1 and Theorem 9.2 (corrected, `η ≤ 2d − 2`)
  each have a comparator pair, in [`RandomSandpileAudit/MainTheoremFinal/`](RandomSandpileAudit/MainTheoremFinal/)
  and [`RandomSandpileAudit/SingleSourceFinal/`](RandomSandpileAudit/SingleSourceFinal/). A
  `Challenge.lean` restates the theorem and every definition it uses with mathlib alone, and a
  `Solution.lean` proves it from the library. [leanprover/comparator](https://github.com/leanprover/comparator)
  checks that the two statements agree, that only the standard axioms are used, and replays the
  proof through an independent implementation of the Lean kernel. Two further pairs,
  [`MainTheorem/`](RandomSandpileAudit/MainTheorem/) and [`SingleSource/`](RandomSandpileAudit/SingleSource/),
  restate the same theorems with the results from other works that the proofs use as hypotheses.
  The other results have no comparator pair.
- **Continuous integration.** The **CI** workflow builds the library, checks the axiom reports and
  builds the comparator pairs. The **Comparator audit** workflow runs the comparator on the four
  pairs after each successful CI run on `main`, and on manual dispatch.
- **The paper is part of the repository.** The corrected draft has SHA-256
  `f772dd2109fd010ed0c83eaa405831121b8698bd061facaee2af457dcc4d27ce`, and the arXiv source
  `ab52e936f60ab3496685184a71f622670d355371c3d4f29356f170e42e8b269e`.

`RandomSandpile/` and `RandomSandpile.lean` contain 383 Lean files with 70,507 lines, built on
mathlib, Lattice-Probability and EllipticRegularityLean.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get                                          # prebuilt mathlib
lake build                                                  # the library
lake env lean RandomSandpileAudit/Axioms.lean 2>&1 | tee axioms-audit.log
python3 scripts/check_axioms.py axioms-audit.log            # the axiom reports
lake build RandomSandpileAudit                              # the comparator pairs
```

The toolchain is Lean `v4.35.0-rc2`, with Mathlib at `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Lattice-Probability and EllipticRegularityLean have no prebuilt cache, so the first build compiles
the modules of them that the library uses. They are public repositories, pinned in
[`lake-manifest.json`](lake-manifest.json):

- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `6c5bebe06b65795cd9daed01d9b2d84795be8ac7`;
- EllipticRegularityLean: `https://github.com/scottnarmstrong/EllipticRegularityLean` at
  `1e29da02bcc6e3c2359a5b8e0559e76d02ec4002`.

`import RandomSandpile` loads the numbered results and what they use.

To rebuild the PDFs of the paper, run `pdflatex` three times on `random_piles.tex` or
`random_piles-corrected.tex` in [`paper/`](paper/); the bibliography is included as `.bbl` files, so
BibTeX is not needed.

## Running the comparators

Each comparator pair has a configuration `RandomSandpileAudit/<Pair>/comparator.json`, which
permits exactly `propext`, `Classical.choice` and `Quot.sound` and enables the nanoda kernel. Build
`leanprover/comparator`, `lean4export`, `landrun` and `nanoda` at the revisions listed in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), then run from the repository
root

```bash
COMPARATOR_BIN=<comparator> COMPARATOR_LANDRUN=<landrun> \
COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  ./scripts/run_comparators.sh
```

The four variables default to the paths under `~/tools` where the workflow builds these tools. The
script builds the library and the audit modules, runs the comparator on every pair and fails if a
pair is missing or rejected.

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
RandomSandpile.lean           the root module
RandomSandpile/
  Defs/                       sandpiles, toppling, odometers, the curvature quantities, the
                              effective operators, viscosity solutions, Green's functions
  Draft/                      the statements of the numbered results, one file per section
  Inputs/                     the statements of the results of other works that the proofs use
  Infra/                      general lemmas (concave envelopes, sup-convolution, touching,
                              subadditive processes)
  Steps/                      one Lean proposition per proof step of the paper
  Proofs/                     the proofs of the steps, by section
  Assembly/
    Main.lean                 the numbered results
    Audit.lean                checks for each result and its axioms
RandomSandpileAudit/
  Axioms.lean                 the axiom report of every theorem in Main.lean
  MainTheoremFinal/, SingleSourceFinal/
                              the mathlib-only comparator pairs of Theorems 1.1 and 9.2
  MainTheorem/, SingleSource/ the pairs with the results from other works as hypotheses
paper/                        the arXiv source and the corrected draft (LaTeX and PDF), figures,
                              CORRECTIONS.md, make_corrected.py, README.md
scripts/                      check_axioms.py, run_comparators.sh, prefetch_toolchain.py (used by CI)
formalization.yaml            source, statement, automation and review metadata
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and OpenAI (GPT),
under the direction of Ahmed Bou-Rabee. Every proof is checked by the Lean kernel. The models,
tooling and review process are disclosed in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors and citation

The paper and the Lean development are by **Ahmed Bou-Rabee**. To cite the formalization, use
[`CITATION.cff`](CITATION.cff). It is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and the library
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability).

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The paper
sources in [`paper/`](paper/) are included by their author and are not covered by the Apache license.

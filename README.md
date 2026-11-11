# Convergence of the random Abelian sandpile

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee,
> [*Convergence of the random Abelian sandpile*](https://arxiv.org/abs/1909.07849),
> Annals of Probability 49(6) (2021), 3168–3196,
> [doi:10.1214/21-AOP1528](https://doi.org/10.1214/21-AOP1528); arXiv:1909.07849.

The statements follow a corrected draft of the arXiv source,
[`paper/random_piles-corrected.tex`](paper/random_piles-corrected.tex). Every change from the arXiv
source is a local correction, marked in the source by a comment `% CORRECTION [Cn]`;
[the table below](#corrections-to-the-published-version) lists them. The unmodified arXiv source is
kept in [`paper/random_piles.tex`](paper/random_piles.tex), and both versions are included as
compiled PDFs.

The paper has 28 numbered results, and all 28 are proved in Lean, with no `sorry` and only the
standard axioms: 19 outright, and 9 from six results of the literature that enter as explicit
hypotheses. The results that the paper quotes from the literature (Propositions 3.1, 3.2, 3.4, 5.1,
5.2, 5.3 and 8.1, and Lemma 7.1) and the two theorems of Section 9, which the paper states without
proof, are proved here as well. Theorem 1.1 is stated with corrections C3 and C12, and Theorem 9.2
in the corrected form C13, which replaces the effective operator by its recurrent version.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on the
public library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability).

[![CI](https://github.com/nitromannitol/Random-Abelian-Sandpile/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Random-Abelian-Sandpile/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Random-Abelian-Sandpile/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Random-Abelian-Sandpile/actions/workflows/comparator.yml)

## What is proved

The initial sandpile is a random configuration `η : ℤᵈ → ℤ`, `d ≥ 2`, whose law is stationary and
ergodic under the lattice shifts and almost surely bounded, `η_min ≤ η ≤ η_max`; it has *high
density* if `E η(0) > 2d − 1`. In Lean the law is a `RandomSandpile.RandomEnvironment d`, high
density is `HighDensity E.P`, and `W` is a bounded Lipschitz domain (`IsLipschitzDomain W`) with
discretizations `W_n = nW ∩ ℤᵈ`. The *effective operator* `F̄_η` (`effOp E`) is the deterministic,
degenerate elliptic operator of Section 6, defined through the almost sure limits of the curvature
quantities `μ` and `μ*` of Section 5.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `RandomSandpile.mainTheorem_final` | Free-boundary sandpiles on a random background converge to the solution of an obstacle problem for `F̄_η`. |
| Theorem 9.1 | `RandomSandpile.openBoundaryTheorem_final` | Sandpiles with the open boundary condition converge to the solution of the Dirichlet problem for `F̄_η`. |
| Theorem 9.2 | `RandomSandpile.singleSourceTheoremRecurrent_final` and three companions | Single-source sandpiles on a random background converge, with the recurrent operator `F̄ᴿ_η`. |

**Theorem 1.1.** Let `W` be a bounded Lipschitz domain and `η` a random background of high density.
Let `v_n` and `s_n` be the odometer and the final configuration of the sandpile that starts from
`η` on `W_n` and stabilizes in `ℤᵈ`. Almost surely, the rescaled odometers
`v̄_n(x) = n⁻² v_n([nx])` converge uniformly on `ℝᵈ` to

`v̄ = min { v ∈ C(ℝᵈ) : v ≥ 0, F̄_η(D²v) ≥ 0 in W, F̄₀(D²v) ≤ 0 in ℝᵈ }`,

in the viscosity sense with test functions touching from below, and the rescaled sandpiles
`s̄_n(x) = s_n([nx])` converge weakly-* in `L^∞` to a deterministic `s` with `∫ s = |W| E η(0)`,
`s ≤ 2d − 1`, `s = 0` outside `B_R(W)` for a radius `R` depending on `W`, `d` and `η_max`, and
`s = Δv̄ + E η(0) 1_W` weakly.

**Theorem 9.1.** For `W` and `η` as above, let `v_n` be the odometer of the sandpile on `W_n` with the
open boundary condition. Almost surely, `v̄_n` converges uniformly to the function `v̄ ∈ C(ℝᵈ)` that
vanishes outside `W` and whose restriction to the closure of `W` is the unique viscosity solution of
`F̄_η(D²v̄) = 0` in `W`, `v̄ = 0` on `∂W`.

**Theorem 9.2.** Let `η` be a random background with `η ≤ 2d − 2`, and `v_n` the odometer of the
sandpile with `n` chips at the origin on the background `η`. Almost surely every `v_n` is finite, and
`n^{−2/d} v_n([n^{1/d} x])` converges locally uniformly on `ℝᵈ ∖ {0}` to `v̄ + G`, where `G` is the
fundamental solution of `−Δ` and `v̄` is the least element of

`{ w ∈ C(ℝᵈ) : w + G ≥ 0, F̄ᴿ_η(D²(w + G)) ≥ 0 in ℝᵈ ∖ {0} }`,

in the viscosity sense with test functions touching from below. Here `F̄ᴿ_η` (`effOpRecurrent E`) is
defined as `F̄_η`, with the recurrent functions of correction C13 in place of the legal and
stabilizing ones. The same
conclusion holds for every bounded stationary ergodic background for which almost surely all `v_n`
are finite and the rescaled odometers have a vanishing tail far from the origin. If `η` is almost
surely recurrent on every finite set, then `F̄ᴿ_η = F̄_η`; the two operators differ for `η ≡ 0`.

The four parts of Theorem 9.2 are `singleSourceTheoremRecurrent_final`,
`singleSourceTheoremRecurrentVT_final`, `recurrentOperatorIdentification_final` and
`recurrentOperatorZeroBackgroundDifference_final`. Each theorem takes as hypotheses the literature
inputs its proof uses, listed in [Assumed literature inputs](#assumed-literature-inputs). Their
statements are definitions `…Stmt` in [`RandomSandpile/Draft/`](RandomSandpile/Draft/), written out
in full with the paper's notation in their docstrings.

### All numbered results

The table lists the 28 numbered results in the order of the paper. All theorems are in
[`RandomSandpile/Assembly/Main.lean`](RandomSandpile/Assembly/Main.lean), in the namespace
`RandomSandpile`; [`RandomSandpile/Assembly/Audit.lean`](RandomSandpile/Assembly/Audit.lean)
restates each one with its exact hypotheses. "Inputs" names the literature inputs a result uses.

| Paper | Statement | Theorem | Inputs |
| --- | --- | --- | --- |
| Theorem 1.1 | `MainTheoremStmt` | `mainTheorem_final` | Alexandrov, Lawler–Limic, PS 2.4, PS 2.5, Ishii |
| Proposition 3.1 | `LeastActionStmt` | `leastAction_final` | — |
| Proposition 3.2 | `AbelianDecompositionStmt` | `abelianDecomposition_final` | — |
| Proposition 3.3 | `BurningStmt` | `burning_final` | — |
| Proposition 3.4 | `RecurrentOfToppledStmt` | `recurrentOfToppled_final` | — |
| Lemma 5.1 | `StabilizingLegalStmt` | `stabilizingLegal_final` | — |
| Lemma 5.2 | `ABPStmt` | `abp_final` | — |
| Proposition 5.1 | `ConcaveEnvelopeRepStmt` | `concaveEnvelopeRep_final` | — |
| Lemma 5.3 | `MongeAmpereRepStmt` | `mongeAmpereRep_final` | — |
| Lemma 5.4 | `MuBoundedStmt` | `muBounded_final` | — |
| Proposition 5.2 | `HarnackQuadraticStmt` | `harnackQuadratic_final` | — |
| Proposition 5.3 | `SubadditiveErgodicStmt` | `subadditiveErgodic_final` | — |
| Lemma 5.5 | `MuConvergenceStmt` | `muConvergence_final` | — |
| Lemma 6.1 | `MuMonotoneStmt` | `muMonotone_final` | — |
| Lemma 6.2 | `StrictConcavityStmt` | `strictConcavity_final` | — |
| Lemma 6.3 | `MuLipschitzStmt` | `muLipschitz_final` | — |
| Lemma 6.4 | `EffectiveOperatorBasicStmt` | `effectiveOperatorBasic_final` | — |
| Lemma 7.1 | `OneDimTopplingStmt` | `oneDimToppling_final` | — |
| Lemma 7.2 | `CompactnessStmt` | `compactness_final` | — |
| Lemma 7.3 | `DivisibleHomogenizeStmt` | `divisibleHomogenize_final` | Lawler–Limic |
| Lemma 7.4 | `OdometerLowerBoundStmt` | `odometerLowerBound_final` | Lawler–Limic |
| Lemma 7.5 | `FlatStmt` | `flat_final` | Lawler–Limic |
| Lemma 7.6 | `PegdenSmartRegularityStmt` | `pegdenSmartRegularity_final` | PS 2.4, PS 2.5, Ishii |
| Proposition 8.1 | `DivisibleLeastActionStmt` | `divisibleLeastAction_final` | — |
| Lemma 8.1 | `DivisibleHomogenizeDomainStmt` | `divisibleHomogenizeDomain_final` | Lawler–Limic |
| Theorem 8.2 | `DivisibleTheoremStmt` | `divisibleTheorem_final` | Lawler–Limic |
| Theorem 9.1 | `OpenBoundaryTheoremStmt` | `openBoundaryTheorem_final` | Alexandrov, Lawler–Limic |
| Theorem 9.2 | `SingleSourceTheoremRecurrentStmt` | `singleSourceTheoremRecurrent_final` | Fey–Levine–Peres, Alexandrov |

Five further theorems in `Main.lean` give other forms of these results:
`mainTheoremLawRadius_final` (Theorem 1.1 with the radius `R` chosen after the law, a corollary of
`mainTheorem_final`), `strictConcavityBeta_final` (Lemma 6.2 with the explicit constant
`c(1 − β)²`), and the three companions of Theorem 9.2 described above (the extension under a
vanishing tail, from Alexandrov's theorem; the two operator statements, outright).

## Corrections to the published version

The corrected draft differs from the arXiv source by the corrections below, each marked in
[`paper/random_piles-corrected.tex`](paper/random_piles-corrected.tex) by a comment
`% CORRECTION [Cn]` at the end of the changed line, with its reason. The full list, with the reason
for each change, is [`paper/CORRECTIONS.md`](paper/CORRECTIONS.md), and the script
[`paper/make_corrected.py`](paper/make_corrected.py) produces the corrected draft from the arXiv
source by applying them. Each correction was tested in an independent model review. The numbers C7,
C9 and C10 are not used.

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

C12 is a weakening adopted by the author: the proof gives a radius depending on `η_max`, and the
printed dependence on `W` and `E η(0)` alone is neither proved nor refuted here. Theorem 9.2 is
false as printed (C3: for `d = 2` and `η ≡ 0`, `F̄_η(0) = 4/3 > 0`); C13 states it for the recurrent
operator `F̄ᴿ_η`, for which the proof goes through. The two operators agree on backgrounds that are
recurrent on every finite set and differ for `η ≡ 0`; the sign-corrected statement with `F̄_η` in
general is not proved here.
[`paper/CORRECTIONS.md`](paper/CORRECTIONS.md) also lists the places where the Lean proofs do not
follow the printed argument.

## Standing assumptions and scope

1. **The random background.** A `RandomEnvironment d` is a probability measure on `ℤ^{ℤᵈ}` that is
   invariant and ergodic under the shifts, with integer bounds `η_min ≤ η(x) ≤ η_max` holding almost
   surely at every site. Theorems 1.1 and 9.1 and Lemmas 7.4, 7.5 and 7.6 assume high density,
   `E η(0) > 2d − 1`, as the paper does.
2. **Lemma 5.4** is proved for all integer bounds, with the threshold `l ≤ −max(η_max, 0) − tr M`.
   This is the printed threshold in the paper's setting, where `η_max ≥ 2d`; for a negative upper
   bound the printed threshold is false, and the Lean statement is the correct generalization.
3. **Viscosity solutions** are in the sense of Crandall, Ishii and Lions, with `C²` test functions;
   supersolutions are tested from below and subsolutions from above.
4. **Rescaling.** `[nx]` is the coordinatewise floor; the rescaled sandpiles are tested against all
   integrable functions (weak-* convergence in `L^∞`).
5. **The divisible sandpile** of Section 8 runs on finite domains, and its odometer counts the mass
   sent to each neighbor (correction C14).
6. **Theorem 9.2** is proved for the recurrent operator (correction C13). Its first form assumes
   `η ≤ 2d − 2` and uses the radius bound of Fey, Levine and Peres for the constant background
   `2d − 2`; the second form assumes instead that the odometers are finite and have a vanishing tail.

## Assumed literature inputs

The six inputs are propositions, stated in [`RandomSandpile/Inputs/`](RandomSandpile/Inputs/) and,
for the last one, in the directory `LatticeProb/External/` of Lattice-Probability, each with its
source in its docstring. They enter as explicit hypotheses of the theorems that use them, not as
axioms.

| Lean name | Statement | Source | Results that use it |
| --- | --- | --- | --- |
| `RandomSandpile.AlexandrovStmt` | a convex function on `ℝᵈ` has a second-order Taylor expansion at almost every point (Alexandrov's theorem) | Evans and Gariepy, *Measure Theory and Fine Properties of Functions* (1992), §6.4, Theorem 1, p. 242 | Theorems 1.1, 9.1, 9.2 |
| `RandomSandpile.LawlerLimicHarmonicDifferenceStmt` | a function harmonic for the simple random walk in the ball of radius `n` and bounded by `M` on its closure has differences at the center at most `CM/n` | Lawler and Limic, *Random Walk: A Modern Introduction* (2010), Theorem 6.3.8(a), for the simple random walk | Theorems 1.1, 8.2, 9.1; Lemmas 7.3, 7.4, 7.5, 8.1 |
| `RandomSandpile.PegdenSmartProp24Stmt` | a continuous weak solution of `Δu = s` in the unit ball with bounded `s` has a second-order Taylor expansion at almost every point | Pegden and Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013), Proposition 2.4 (arXiv:1105.0111v2, p. 6) | Theorem 1.1, Lemma 7.6 |
| `RandomSandpile.PegdenSmartProp25Stmt` | if such a `u`, continuous on the closed ball, exceeds its boundary supremum somewhere in the ball, then on a set of positive measure it does so and has a second-order expansion with negative definite Hessian | Pegden and Smart, *ibid.*, Proposition 2.5 (p. 6) | Theorem 1.1, Lemma 7.6 |
| `RandomSandpile.ViscosityWeakLaplaceStmt` | on a nonempty open set, a continuous viscosity solution of `−K ≤ Δu ≤ K` is a weak solution of `Δu = s` with `\|s\| ≤ K` | Ishii, *On the equivalence of two notions of weak solutions, viscosity solutions and distribution solutions*, Funkcial. Ekvac. 38 (1995), Theorem 1, p. 103, with the passage from the two distributional inequalities to a bounded density | Theorem 1.1, Lemma 7.6 |
| `LatticeProb.External.FeyLevinePeresRadius` | for a constant background `h` with `d ≤ h ≤ 2d − 2` and every `ε > 0`, for all large `n` the sites that topple when `n` chips start at the origin satisfy `max_i \|x_i\| ≤ (d + ε)/(2d − 1 − h) · (n/ω_d)^{1/d}`, `ω_d` the volume of the unit ball | Fey, Levine and Peres, *Growth rates and explosions in sandpiles*, J. Stat. Phys. 138 (2010), Theorem 1.1 (arXiv:0901.3805v2, p. 4) | Theorem 9.2 |

The paper quotes Lemma 7.6 from Pegden and Smart; here it is proved from their Propositions 2.4 and
2.5 and the equivalence of viscosity and weak solutions, by an argument localized to balls.

## Guarantees

- **No `sorry`.** The library has none. The two comparator challenges under
  [`RandomSandpileAudit/`](RandomSandpileAudit/) each contain one intentional statement-level
  `sorry`, which the corresponding solution proves.
- **Standard axioms only.** The axiom report of each of the 33 theorems in `Main.lean` lists exactly
  `propext`, `Classical.choice` and `Quot.sound`.
  [`RandomSandpileAudit/Axioms.lean`](RandomSandpileAudit/Axioms.lean) prints the reports, and
  [`scripts/check_axioms.py`](scripts/check_axioms.py) fails on any other axiom, on `sorryAx`, or on
  a missing report. The literature inputs are hypotheses, not axioms, so they do not appear in the
  reports.
- **Independent check of the statements.** Theorem 1.1 (`mainTheorem_final`) and the first part of
  Theorem 9.2 (`singleSourceTheoremRecurrent_final`, backgrounds with `η ≤ 2d − 2`) are restated
  using mathlib alone in
  [`RandomSandpileAudit/MainTheorem/`](RandomSandpileAudit/MainTheorem/) and
  [`RandomSandpileAudit/SingleSource/`](RandomSandpileAudit/SingleSource/). Each `Challenge.lean`
  restates every definition that its statement unfolds to and the literature inputs that the theorem
  takes as hypotheses; each `Solution.lean` proves the restatement from the library; and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the two statements
  agree, that only the permitted axioms are used, and replays the proof through an independent
  implementation of the Lean kernel. Theorem 9.1, the other three parts of Theorem 9.2 and the other
  numbered results have no comparator pair.
- **Pinned toolchain and dependencies.** Lean `v4.32.0`, Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` and Lattice-Probability
  `99cfc20cb60d38c947523641e991a84350e77309`, as recorded in [`lean-toolchain`](lean-toolchain) and
  [`lake-manifest.json`](lake-manifest.json) (see [Building](#building)).
- **The paper is part of the repository.** [`paper/`](paper/) holds the arXiv source, the corrected
  draft, both compiled to PDF, and the list of corrections. The statements follow the corrected
  draft `paper/random_piles-corrected.tex`, with SHA-256
  `f772dd2109fd010ed0c83eaa405831121b8698bd061facaee2af457dcc4d27ce`; the arXiv source
  `paper/random_piles.tex` has SHA-256
  `ab52e936f60ab3496685184a71f622670d355371c3d4f29356f170e42e8b269e`.
- **Statements and inputs checked against their sources.** Each Lean statement was compared with the
  corrected draft, and each literature input with its source, in an independent model review. The
  inputs remain assumptions.

## Size

`RandomSandpile/` and `RandomSandpile.lean`: 345 Lean files with 65,542 lines, on top of mathlib and
Lattice-Probability. The comparator sources (9 files, 2,252 lines) are counted separately.

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

Lattice-Probability has no prebuilt cache, so the first build compiles it as well as the library.
It is a public repository, pinned in [`lake-manifest.json`](lake-manifest.json):

- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `99cfc20cb60d38c947523641e991a84350e77309`.

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

There are two continuous-integration workflows: **CI** builds the library, checks the axiom reports
and builds the comparator pairs; **Comparator audit** runs the comparator on the two pairs. CI runs
on pushes to `main` that change more than documentation, the paper, `formalization.yaml` or
`CITATION.cff`; the comparator audit runs when it is started manually. Both workflows can be started
manually from the [Actions page](https://github.com/nitromannitol/Random-Abelian-Sandpile/actions).
See [`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
RandomSandpile.lean           the root module
RandomSandpile/
  Defs/                       sandpiles, toppling, odometers, the curvature quantities, the
                              effective operators, viscosity solutions, Green's functions
  Draft/                      the statements of the numbered results, one file per section
  Inputs/                     the literature inputs, stated as propositions
  Infra/                      general lemmas (concave envelopes, sup-convolution, touching,
                              subadditive processes)
  Steps/                      one Lean proposition per proof step of the paper
  Proofs/                     the proofs of the steps, by section
  Assembly/
    Main.lean                 the numbered results, from the literature inputs only
    Audit.lean                each result with its exact hypotheses
RandomSandpileAudit/
  Axioms.lean                 the axiom report of every theorem in Main.lean
  MainTheorem/, SingleSource/ the mathlib-only comparator pairs of Theorems 1.1 and 9.2
paper/                        the arXiv source and the corrected draft (LaTeX and PDF), figures,
                              CORRECTIONS.md, make_corrected.py, README.md
scripts/                      check_axioms.py, run_comparators.sh, prefetch_toolchain.py (used by CI)
.github/workflows/            build.yml (CI) and comparator.yml (Comparator audit)
LICENSE                       the Apache License 2.0
CONTRIBUTING.md               build conventions and contribution notes
CITATION.cff                  citation metadata
formalization.yaml            source, statement, automation and review metadata
lakefile.lean, lake-manifest.json, lean-toolchain   the build
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

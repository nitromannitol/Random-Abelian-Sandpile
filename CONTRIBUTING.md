# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain`.

```bash
lake exe cache get               # prebuilt mathlib
lake build                       # the library
lake build RandomSandpileAudit   # the comparator challenges and solutions
```

The library must build with **no warnings**. Lattice-Probability has no prebuilt cache, so the
first build compiles it as well as the library. The only intentional `sorry`s are the four
statement-level ones in `RandomSandpileAudit/*/Challenge.lean`, one in each; `lake build RandomSandpileAudit`
reports them as warnings, and the comparator checks each against its solution.

## The main results and the axiom audit

The numbered results of the paper are the theorems in `RandomSandpile/Assembly/Main.lean`;
`RandomSandpile/Assembly/Audit.lean` restates each one with its exact hypotheses.

```bash
lake env lean RandomSandpileAudit/Axioms.lean 2>&1 | tee axioms-audit.log
python3 scripts/check_axioms.py axioms-audit.log
```

`RandomSandpileAudit/Axioms.lean` prints the axiom report of each of the 33 theorems of
`Main.lean`. It is not imported by the root module, because a `#print axioms` command runs again
whenever its module is rebuilt. `scripts/check_axioms.py` fails on an error or a warning in the
log, on `sorryAx`, on any axiom other than `propext`, `Classical.choice` and `Quot.sound`, and on
a missing, unexpected or repeated report. The literature inputs are hypotheses of the theorems
that use them, not axioms, so they do not appear in the reports.

## Conventions for Lean files

- No `sorry`, `admit`, `native_decide` or new `axiom` in the library. Avoid
  `set_option maxHeartbeats`; the four existing uses are under `RandomSandpile/Proofs/`.
- Statements stay faithful to the corrected draft `paper/random_piles-corrected.tex` and are
  referred to by their number and LaTeX label, never by line number. Where a statement departs
  from the printed paper, the departure is listed in `paper/CORRECTIONS.md`.
- A result cited from the literature is stated as a proposition in `RandomSandpile/Inputs/`, with
  its source in the docstring, and enters a theorem as an explicit hypothesis. Do not add an
  `axiom` for it.
- New declarations go under `RandomSandpile/`. The dependencies under `.lake/packages/` are
  read-only.
- Keep files short: the longest existing file has 1,164 lines.
- Avoid `lake clean`: it removes the prebuilt mathlib and Lattice-Probability builds and forces
  the dependencies to be rebuilt from source.

## Comparators

`RandomSandpileAudit/` has four pairs. `MainTheoremFinal/` (Theorem 1.1) and `SingleSourceFinal/`
(Theorem 9.2) state the theorems with no literature-input hypothesis, as `mainTheorem_final` and
`singleSourceTheoremRecurrent_final` do; `MainTheorem/` and `SingleSource/` state them with the five
and the two literature inputs as hypotheses. The vocabulary of `MainTheoremFinal/` is that of
`MainTheorem/` byte for byte (its literature inputs are defined but not used), the vocabulary of
`SingleSourceFinal/` is that of `SingleSource/` without the two literature inputs, and the solutions of
the final pairs use the `SolutionBasic.lean` and `Bridge.lean` of the first pairs. Each pair has a mathlib-only `Challenge.lean`, a `Solution.lean`
that proves the same statement from the library, and a `comparator.json` that permits exactly `propext`,
`Classical.choice` and `Quot.sound` and enables the nanoda kernel. Do not add a declaration to a
challenge that the statement does not need, and do not change a challenge without checking it
against the paper's statement.

To run the pairs locally, build `leanprover/comparator`, `lean4export`, `landrun` and `nanoda` at
the revisions listed in `.github/workflows/comparator.yml`, then run `./scripts/run_comparators.sh`
as described in the [`README.md`](README.md). A missing pair, a missing tool or a failed kernel
check is a failure.

## Continuous integration

- **CI** (`.github/workflows/build.yml`) builds the library, rejects any warning and any `sorry`,
  runs the axiom audit and builds the comparator surface. It runs on pushes to `main` that change
  more than documentation, the paper, `formalization.yaml` or `CITATION.cff`.
- **Comparator audit** (`.github/workflows/comparator.yml`) builds the comparator tools at pinned
  revisions and runs both pairs with the Lean kernel and the independent nanoda kernel. It runs
  after each successful CI run on `main` (on the commit that CI built) and on manual dispatch.

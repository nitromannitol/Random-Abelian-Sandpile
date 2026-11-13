import Lake
open Lake DSL

package «random-abelian-sandpile» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "d36783565c4de41cce5cf079ddd5ace3efe6a8ff"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

@[default_target]
lean_lib «RandomSandpile» where
  globs := #[.andSubmodules `RandomSandpile]

/-- The audit surface: the axiom report `RandomSandpileAudit/Axioms.lean` and the comparator pairs
`RandomSandpileAudit/*/Challenge.lean`, `RandomSandpileAudit/*/Solution.lean`. Not a default target:
it builds only on demand (`lake build RandomSandpileAudit`); each challenge elaborates with its one
intentional `sorry`. -/
lean_lib RandomSandpileAudit where
  globs := #[.submodules `RandomSandpileAudit]

import Lake
open Lake DSL

package «random-abelian-sandpile» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "99cfc20cb60d38c947523641e991a84350e77309"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib «RandomSandpile» where
  globs := #[.andSubmodules `RandomSandpile]

/-- The audit surface: the axiom report `RandomSandpileAudit/Axioms.lean` and the comparator pairs
`RandomSandpileAudit/*/Challenge.lean`, `RandomSandpileAudit/*/Solution.lean`. Not a default target:
it builds only on demand (`lake build RandomSandpileAudit`); each challenge elaborates with its one
intentional `sorry`. -/
lean_lib RandomSandpileAudit where
  globs := #[.submodules `RandomSandpileAudit]

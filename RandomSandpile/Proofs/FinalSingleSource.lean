import RandomSandpile.Proofs.Sec9.OpenBoundaryVanish
import RandomSandpile.Steps.Sec9.SingleSource

/-! # Theorem 9.2, step: vanishing ranges of `μ`, `μ*` under flatness

`muVanishFlat : MuVanishFlatStmt` (`Steps/Sec9/SingleSource.lean`), the argument of
`muVanish_of_flat` (`Proofs/Sec9/OpenBoundaryVanish.lean`) with the flatness hypothesis `FlatEff E`
in place of Lemma 7.5: flatness gives `μ(l_M, M) = μ*(l_M, M) = 0`, and Lemma 6.1 (`muMonotone`,
with the finiteness of the averages from Lemma 5.4) makes `μ(·, M)` nondecreasing and `μ*(·, M)`
nonincreasing.
-/

namespace RandomSandpile

open EffectiveOperatorBasic

/-- **Step of Theorem 9.2** (`MuVanishFlatStmt`). -/
theorem muVanishFlat : MuVanishFlatStmt := by
  intro d hd E hflat M hM l
  have hd1 : 1 ≤ d := by omega
  obtain ⟨h1, h2⟩ := hflat M hM
  refine ⟨fun hl => le_antisymm ?_ (muBar_nonneg E l M),
    fun hl => le_antisymm ?_ (muStarBar_nonneg E l M)⟩
  · have := muBar_mono muMonotone hd1 E M hl
    simp only at this
    linarith
  · have := muStarBar_anti muMonotone hd1 E M hl
    simp only at this
    linarith

end RandomSandpile

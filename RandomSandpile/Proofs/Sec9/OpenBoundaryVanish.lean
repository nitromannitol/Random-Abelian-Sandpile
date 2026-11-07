import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasicFinal
import RandomSandpile.Proofs.Sec7.Flat
import RandomSandpile.Proofs.Sec7.OdometerLowerBound
import RandomSandpile.Proofs.Sec7.DivisibleHomogenize
import RandomSandpile.Steps.Sec9.OpenBoundary

/-! # Theorem 9.1 steps and: the shift identity and the vanishing ranges

* `effShift_of_muConvergence : MuConvergenceStmt → EffShiftStmt`: `effOp_add_smul_one`
  (Lemma 6.4 and `q_{M + tI} = q_M + q_{dt}`).
* `flat_of_muConvergence`: Lemma 7.5 (`FlatStmt`) from Lemma 5.5 and the Lawler-Limic input, via `flat_of_bending`.
* `muVanish_of_flat`, `muVanish_of_muConvergence`: `MuVanishStmt`. Lemma 7.5 gives
  `μ(l_M, M) = μ*(l_M, M) = 0`; Lemma 6.1 (`muMonotone`, with the finiteness of the averages from
  Lemma 5.4) makes `μ(·, M)` nondecreasing and `μ*(·, M)` nonincreasing. -/

namespace RandomSandpile

open EffectiveOperatorBasic

/-- **Step** (`EffShiftStmt`) from Lemma 5.5. -/
theorem effShift_of_muConvergence (hconv : MuConvergenceStmt) : EffShiftStmt :=
  fun _ hd E _ _ hM t => effOp_add_smul_one hconv hd E hM t

/-- **Lemma 7.5** (`FlatStmt`) from Lemma 5.5 and the Lawler-Limic input. -/
theorem flat_of_muConvergence (hconv : MuConvergenceStmt)
    (hLL : LawlerLimicHarmonicDifferenceStmt) : FlatStmt :=
  flat_of_bending (nearMaxBendingStabilizing_of_muConvergence hconv)
    (shellBound_of_muConvergence hconv)
    (odometerLowerBound_of_divisibleHomogenize (divisibleHomogenize_of_lawlerLimic hLL))
    (effectiveOperatorBasic_of_muConvergence hconv)

/-- **Step** (`MuVanishStmt`) from Lemma 7.5. -/
theorem muVanish_of_flat (hflat : FlatStmt) : MuVanishStmt := by
  intro d hd E hHD M hM l
  have hd1 : 1 ≤ d := by omega
  obtain ⟨h1, h2⟩ := hflat d hd E hHD M hM
  refine ⟨fun hl => le_antisymm ?_ (muBar_nonneg E l M),
    fun hl => le_antisymm ?_ (muStarBar_nonneg E l M)⟩
  · have := muBar_mono muMonotone hd1 E M hl
    simp only at this
    linarith
  · have := muStarBar_anti muMonotone hd1 E M hl
    simp only at this
    linarith

/-- **Step** (`MuVanishStmt`) from Lemma 5.5 and the Lawler-Limic input. -/
theorem muVanish_of_muConvergence (hconv : MuConvergenceStmt)
    (hLL : LawlerLimicHarmonicDifferenceStmt) : MuVanishStmt :=
  muVanish_of_flat (flat_of_muConvergence hconv hLL)

end RandomSandpile

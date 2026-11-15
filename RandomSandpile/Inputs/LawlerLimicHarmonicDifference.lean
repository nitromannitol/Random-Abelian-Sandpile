import RandomSandpile.Inputs.Proposed
import LatticeProb.Walk.HarmonicDifference.Estimate

/-! # Harmonic difference estimate

The lattice harmonic difference estimate of Lawler and Limic,
*Random Walk: A Modern Introduction*, Theorem 6.3.8(a).
-/

namespace RandomSandpile

/-- The harmonic difference estimate on lattice balls. -/
theorem lawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt := by
  intro d hd
  obtain ⟨C, hC, h⟩ := LatticeProb.HarmonicDifference.harmonic_difference d hd
  refine ⟨C, hC, ?_⟩
  intro n hn f M hharm hf i
  exact h n hn f M hharm hf i

end RandomSandpile

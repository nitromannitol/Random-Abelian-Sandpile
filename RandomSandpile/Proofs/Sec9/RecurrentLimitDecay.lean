import RandomSandpile.Steps.Sec9.RecurrentComparison
import RandomSandpile.Proofs.Sec9.SingleSourceFlatnessStar

/-! # Vanishing at infinity for recurrent single-source limits -/

open MeasureTheory Filter Topology LatticeProb

namespace RandomSandpile

/-- The lattice vanishing-tail condition passes to all punctured-space subsequential limits. -/
theorem recurrentSSLimitDecay : RecurrentSSLimitDecayStmt := by
  intro d hd E
  filter_upwards [] with η
  intro _ htail u hu ε hε
  obtain ⟨R, hR, htail⟩ := htail ε hε
  refine ⟨R + Real.sqrt d + 1, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    have := Real.sqrt_nonneg (d : ℝ)
    linarith
  obtain ⟨nk, hnk, hconv⟩ := hu
  apply le_of_tendsto (hconv.tendsto_at hx0)
  filter_upwards [hnk.tendsto_atTop.eventually htail, eventually_ge_atTop 1] with k hk hge
  have hn : 1 ≤ nk k := le_trans hge (hnk.id_le k)
  have hnR : (1 : ℝ) ≤ nk k := by exact_mod_cast hn
  let s : ℝ := (nk k : ℝ) ^ (1 / (d : ℝ))
  have hs : 1 ≤ s := Real.one_le_rpow hnR (by positivity)
  have hround := norm_toE_latticeRound_ge (s • x)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at hround
  have hsqrt : Real.sqrt d ≤ s * Real.sqrt d :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) hs
  have hfar : R * s ≤ ‖toE (latticeRound (s • x))‖ := by nlinarith
  have hbound := hk (latticeRound (s • x)) hfar
  simpa [rescaleSingleSource, s] using hbound

end RandomSandpile

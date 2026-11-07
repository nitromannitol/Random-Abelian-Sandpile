import RandomSandpile.Proofs.Sec9.RecurrentCompactnessAscoli
import RandomSandpile.Draft.Section9Recurrent
import RandomSandpile.Proofs.Sec9.SingleSourceFlatnessStar

/-! # Vanishing tails provide a bounded corrector anchor -/

noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

/-- The corrector is eventually bounded at every sufficiently distant fixed point. -/
theorem recurrent_corrector_anchor {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (htail : SingleSourceVanishingTail η) (κ C Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ))) :
    ∃ x : Rd d, x ≠ 0 ∧ ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      |ssCorrector d η κ n x| ≤ B := by
  obtain ⟨R, hR, htail⟩ := htail 1 zero_lt_one
  let ρ : ℝ := R + Real.sqrt d + 1
  have hρ : 0 < ρ := by dsimp [ρ]; have := Real.sqrt_nonneg (d : ℝ); linarith
  let x : Rd d := ρ • EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ)
  have hx : ‖x‖ = ρ := by
    simp [x, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  have hx0 : x ≠ 0 := norm_pos_iff.1 (by rw [hx]; exact hρ)
  refine ⟨x, hx0, 2 + |fundamentalSolution d x|, ?_⟩
  obtain ⟨N, hN⟩ := ssGreenErr_small hd hRg hasymp (isCompact_singleton (x := x))
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hx0) one_pos
  filter_upwards [htail, eventually_ge_atTop (max 1 N)] with n hn hnN
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hnN
  have hs : 1 ≤ ssScale d n := one_le_ssScale hn1
  have hround := norm_toE_latticeRound_ge (ssScale d n • x)
  rw [norm_smul, Real.norm_of_nonneg (by positivity), hx] at hround
  have hsqrt : Real.sqrt d ≤ ssScale d n * Real.sqrt d :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) hs
  have hfar : R * ssScale d n ≤ ‖toE (latticeRound (ssScale d n • x))‖ := by
    dsimp [ρ] at hround
    nlinarith
  have hbound := hn (latticeRound (ssScale d n • x)) hfar
  have hres : rescaleSingleSource (singleSourceOdometer η n) n x ≤ 1 := by
    simpa [rescaleSingleSource, ssScale] using hbound
  have hnonneg : 0 ≤ rescaleSingleSource (singleSourceOdometer η n) n x := by
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Int.cast_nonneg (singleSourceOdometer_nonneg _ _ _))
  have herr := hN n (le_trans (le_max_right _ _) hnN) x (Set.mem_singleton x)
  have heq := rescale_eq η κ n x
  have hG := le_abs_self (fundamentalSolution d x)
  have hG' := neg_abs_le (fundamentalSolution d x)
  rw [abs_lt] at herr
  rw [abs_le]
  constructor <;> linarith

end RandomSandpile

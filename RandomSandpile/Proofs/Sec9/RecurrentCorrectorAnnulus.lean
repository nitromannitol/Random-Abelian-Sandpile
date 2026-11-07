import RandomSandpile.Proofs.Sec9.RecurrentCompactnessAnchor
import RandomSandpile.Proofs.Sec9.RecurrentPoissonBoundary

/-! # Tail bounds on macroscopic corrector annuli -/

noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

/-- Vanishing tails and Green asymptotics bound correctors uniformly on each
compact annulus sufficiently far from the origin. -/
theorem recurrent_corrector_annulus_bound {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (htail : SingleSourceVanishingTail η)
    (κ C Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ))) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ x : Rd d, r ≤ ‖x‖ → ‖x‖ ≤ R → |ssCorrector d η κ n x| ≤ B := by
  obtain ⟨r₀, hr₀, htail⟩ := htail 1 zero_lt_one
  let r : ℝ := r₀ + Real.sqrt d + 1
  have hr : 0 < r := by dsimp [r]; have := Real.sqrt_nonneg (d : ℝ); linarith
  refine ⟨r, hr, fun R => ?_⟩
  let K : Set (Rd d) := {x | r ≤ ‖x‖} ∩ Metric.closedBall 0 R
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : Rd d) R).inter_left (isClosed_le continuous_const continuous_norm)
  have hK0 : ∀ x ∈ K, x ≠ 0 := fun x hx => norm_pos_iff.1 (lt_of_lt_of_le hr hx.1)
  have hGcont : ContinuousOn (fundamentalSolution d) K :=
    SingleSourceMin.continuousOn_fundamentalSolution d |>.mono (fun x hx => hK0 x hx)
  obtain ⟨G, hG⟩ := (hK.image_of_continuousOn hGcont).isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := ssGreenErr_small hd hRg hasymp hK hK0 one_pos
  refine ⟨2 + G, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (max 1 N)] with n hn hnN
  intro x hxr hxR
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hnN
  have hs : 1 ≤ ssScale d n := one_le_ssScale hn1
  have hround := norm_toE_latticeRound_ge (ssScale d n • x)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at hround
  have hsqrt : Real.sqrt d ≤ ssScale d n * Real.sqrt d :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) hs
  have hfar : r₀ * ssScale d n ≤ ‖toE (latticeRound (ssScale d n • x))‖ := by
    dsimp [r] at hxr
    nlinarith
  have hbound := hn (latticeRound (ssScale d n • x)) hfar
  have hres : rescaleSingleSource (singleSourceOdometer η n) n x ≤ 1 := by
    simpa [rescaleSingleSource, ssScale] using hbound
  have hnonneg : 0 ≤ rescaleSingleSource (singleSourceOdometer η n) n x :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Int.cast_nonneg (singleSourceOdometer_nonneg _ _ _))
  have hxK : x ∈ K := ⟨hxr, mem_closedBall_zero_iff.2 hxR⟩
  have herr := hN n (le_trans (le_max_right _ _) hnN) x hxK
  have hg := hG (fundamentalSolution d x) ⟨x, hxK, rfl⟩
  rw [Real.norm_eq_abs] at hg
  have heq := rescale_eq η κ n x
  rw [abs_lt] at herr
  rw [abs_le] at hg ⊢
  constructor <;> linarith

/-- The far-annulus estimate at lattice sites, in the normalization used for
the discrete Poisson equation. -/
theorem recurrent_lattice_corrector_annulus_bound {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (htail : SingleSourceVanishingTail η)
    (κ C Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ))) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ z : Site d, r * ssScale d n ≤ ‖toE z‖ → ‖toE z‖ ≤ R * ssScale d n →
        |(n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n z +
          (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n| ≤ B := by
  obtain ⟨r, hr, h⟩ := recurrent_corrector_annulus_bound hd η htail κ C Rg hRg hasymp
  refine ⟨r, hr, fun R => ?_⟩
  obtain ⟨B, hB⟩ := h R
  refine ⟨B, ?_⟩
  filter_upwards [hB, eventually_ge_atTop 1] with n hn hn1
  intro z hzlo hzhi
  have hs := ssScale_pos (d := d) hn1
  let x : Rd d := (ssScale d n)⁻¹ • toE z
  have hxnorm : ‖x‖ = ‖toE z‖ / ssScale d n := by
    simp [x, norm_smul, Real.norm_eq_abs, abs_of_pos hs, div_eq_mul_inv, mul_comm]
  have hxlo : r ≤ ‖x‖ := by
    rw [hxnorm, le_div_iff₀ hs]
    exact hzlo
  have hxhi : ‖x‖ ≤ R := by
    rw [hxnorm, div_le_iff₀ hs]
    exact hzhi
  have hround : latticeRound (ssScale d n • x) = z := by
    dsimp [x]
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, latticeRound_toE]
  have hbound := hn x hxlo hxhi
  simpa [ssCorrector, hround] using hbound

end RandomSandpile

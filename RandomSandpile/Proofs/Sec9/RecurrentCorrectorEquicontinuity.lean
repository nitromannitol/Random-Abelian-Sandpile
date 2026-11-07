import RandomSandpile.Proofs.Sec9.RecurrentCorrectorTransfer
import RandomSandpile.Proofs.Sec9.RecurrentCompactnessEventuallyCorrector

/-! # Asymptotic equicontinuity of recurrent correctors -/

noncomputable section
open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

/-- Dyadic control at small radii implies asymptotic equicontinuity. -/
theorem asymptoticEquicontinuous_of_small_dyadic (d : ℕ) (F : ℕ → Rd d → ℝ)
    (h : ∀ m : ℕ, ∃ q B C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ρ > 0, ρ ≤ 1 → ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ x y : Rd d,
        ‖x‖ ≤ m → ‖y‖ ≤ m → dist x y < ρ / (2 : ℝ) ^ k →
        |F n x - F n y| ≤ q ^ k * B + C * ρ ^ 2) :
    ∀ m : ℕ, ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ,
      ∀ n ≥ N, ∀ x y : Rd d, ‖x‖ ≤ m → ‖y‖ ≤ m → dist x y < δ →
        |F n x - F n y| < ε := by
  intro m ε hε
  obtain ⟨q, B, C, hq0, hq1, hB, hC, hosc⟩ := h m
  let ρ : ℝ := min 1 (ε / (4 * (C + 1)))
  have hρ : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρ2 : ρ ≤ ε / (4 * (C + 1)) := min_le_right _ _
  have hforce : C * ρ ^ 2 < ε / 2 := by
    have hmul : C * ρ ≤ C * (ε / (4 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hρ2 hC
    have hcalc : (C + 1) * (ε / (4 * (C + 1))) = ε / 4 := by field_simp
    nlinarith [sq_nonneg ρ]
  have ht : Tendsto (fun k : ℕ => q ^ k * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const B
  obtain ⟨k, hk⟩ := (ht.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 2))).exists
  obtain ⟨N, hN⟩ := hosc ρ hρ hρ1 k
  refine ⟨ρ / (2 : ℝ) ^ k, by positivity, N, ?_⟩
  intro n hn x y hx hy hxy
  have := hN n hn x y hx hy hxy
  linarith

/-- Bounded recurrent backgrounds and vanishing tails yield a small-radius
dyadic oscillation estimate for the rescaled correctors. -/
theorem recurrent_corrector_small_dyadic {d : ℕ} (hd : 2 ≤ d)
    {ηmin ηmax : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) (hfinite : SingleSourceFinite η)
    (htail : SingleSourceVanishingTail η) (κ Cg Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ Cg * ‖toE z‖ ^ (-(d : ℝ)))
    (m : ℕ) : ∃ q B C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ρ > 0, ρ ≤ 1 → ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ x y : Rd d,
        ‖x‖ ≤ m → ‖y‖ ≤ m → dist x y < ρ / (2 : ℝ) ^ k →
        |ssCorrector d η κ n x - ssCorrector d η κ n y| ≤ q ^ k * B + C * ρ ^ 2 := by
  let M : ℝ := m + 3 * Real.sqrt d + 1
  obtain ⟨q, B, C, hq0, hq1, hB, hC, hdyadic⟩ :=
    recurrent_corrector_lattice_dyadic hd hη hfinite htail κ Cg Rg hRg hasymp M
  refine ⟨q, B, 4 * C, hq0, hq1, hB, by positivity, ?_⟩
  intro ρ hρ hρ1 k
  have hscale := (ssScale_tendsto (d := d) (by omega)).eventually_ge_atTop
    (max 1 (3 * (2 : ℝ) ^ k / ρ))
  filter_upwards [hdyadic, hscale] with n hn hscale
  intro x y hx hy hxy
  let s := ssScale d n
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hscale
  have hs : 0 < s := by linarith
  have hlarge : 3 * (2 : ℝ) ^ k ≤ ρ * s := by
    have := le_trans (le_max_right (1 : ℝ) (3 * (2 : ℝ) ^ k / ρ)) hscale
    simpa [s, mul_comm] using (div_le_iff₀ hρ).1 this
  obtain ⟨R, S, hR, hRS, hinner, houter⟩ :=
    recurrent_corrector_choose_dyadic_radii s ρ k hs hρ hlarge
  have hdist : s * dist x y + 1 ≤ R := by
    have := mul_le_mul_of_nonneg_left hxy.le hs.le
    linarith
  have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsize : s * ‖x‖ + Real.sqrt d + Real.sqrt d * S ≤ M * s := by
    have hxm := mul_le_mul_of_nonneg_left hx hs.le
    have hS : (S : ℝ) ≤ 2 * s := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hS hsqrt
    have hround : Real.sqrt d ≤ Real.sqrt d * s := by nlinarith
    dsimp [M]
    nlinarith
  have hball := recurrent_corrector_rounded_box_containment s M x hs.le hsize
  have hbound := recurrent_corrector_dyadic_transfer κ n k R S q B C M x y hs.le hdist
    (hn k R S · hR hRS) hball
  have hratio : ((S : ℝ) + 1) / s ≤ 2 * ρ := by
    apply (div_le_iff₀ hs).2
    nlinarith
  have hratio0 : 0 ≤ ((S : ℝ) + 1) / s := by positivity
  have hsq : (((S : ℝ) + 1) / s) ^ 2 ≤ (2 * ρ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hsq hC
  nlinarith

/-- Recurrent single-source correctors are asymptotically equicontinuous. -/
theorem recurrentCorrectorEquicontinuity : RecurrentCorrectorEquicontinuityStmt := by
  intro d hd E
  obtain ⟨κ₀, Cg, Rg, hRg, hasymp⟩ := ssGreen_asymp hd
  have hb : ∀ᵐ η ∂E.P, ∀ x : Site d, E.ηmin ≤ η x ∧ η x ≤ E.ηmax :=
    ae_all_iff.2 E.bounded
  filter_upwards [hb] with η hη
  intro hfinite htail nk hnk κ
  apply asymptoticEquicontinuous_of_small_dyadic d _
  intro m
  obtain ⟨q, B, C, hq0, hq1, hB, hC, hD⟩ :=
    recurrent_corrector_small_dyadic hd hη hfinite htail κ₀ Cg Rg hRg hasymp m
  refine ⟨q, B, C, hq0, hq1, hB, hC, ?_⟩
  intro ρ hρ hρ1 k
  have hnkT : Tendsto (fun j => nk (j + 1)) atTop atTop :=
    hnk.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hnkT.eventually (hD ρ hρ hρ1 k))
  refine ⟨N, ?_⟩
  intro j hj x y hx hy hxy
  have h := hN j hj x y hx hy hxy
  have heq : ssCorrector d η κ (nk (j + 1)) x - ssCorrector d η κ (nk (j + 1)) y =
      ssCorrector d η κ₀ (nk (j + 1)) x - ssCorrector d η κ₀ (nk (j + 1)) y := by
    simp only [ssCorrector]
    ring
  rw [heq]
  exact h

/-- The recurrent single-source compactness step follows from the
asymptotic equicontinuity of the correctors. -/
theorem recurrentSSCompactness : RecurrentSSCompactnessStmt :=
  recurrentSSCompactness_of_corrector_equicontinuity recurrentCorrectorEquicontinuity

end RandomSandpile

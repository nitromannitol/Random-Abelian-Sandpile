import RandomSandpile.Proofs.Sec9.RecurrentCenterBound
import RandomSandpile.Proofs.Sec9.RecurrentSymmetric
import RandomSandpile.Proofs.Sec9.RecurrentCommonZeroExists

/-! Uniqueness of the common zero of recurrent curvature densities. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal
noncomputable section
namespace RandomSandpile
open EffectiveOperatorBasic MuLipschitz SingleSourceH0
variable {d : ℕ}

/-- An interval cannot separate a lower zero from a later upper zero. -/
theorem recurrent_no_common_zero_interval (hd : 2 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) (l₁ l₂ : ℝ) (hl : l₁ < l₂)
    (h1 : muStarRecurrentBar E l₁ M = 0) (h2 : muRecurrentBar E l₂ M = 0) : False := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨C, hC, hABP⟩ := recurrent_abp d hd
  obtain ⟨η, hη1, hη2⟩ := ((muStarRecurrent_convergence_anyMatrix hd E l₁ M).and (muRecurrent_convergence hd E l₂ M).2.2).exists
  have hW := StrictConcavityBall.isLipschitzDomain_ball (0 : Rd d) one_pos
  obtain ⟨hfin1, hT1⟩ := hη1 _ hW
  obtain ⟨hfin2, hT2⟩ := hη2 _ hW
  rw [h1] at hT1
  rw [h2] at hT2
  have hD0 : 0 < l₂ - l₁ := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (l₂ - l₁) / (24 * d * C) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈4 * d / (l₂ - l₁)⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨n, hr1, hr2, hnN⟩ :=
    ((hT1.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ d))).and
      ((hT2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ d))).and
        (eventually_ge_atTop N))).exists
  have hn1 : 1 ≤ n := by rw [hN] at hnN; omega
  have hnD : 4 * d / (l₂ - l₁) < n := by
    have h1' : 4 * d / (l₂ - l₁) ≤ (⌈4 * d / (l₂ - l₁)⌉₊ : ℝ) := Nat.le_ceil _
    have h2' : ((⌈4 * d / (l₂ - l₁)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by rw [← hN]; exact_mod_cast hnN
    push_cast at h2'
    linarith
  simp only [discretize_unitBall_eq' hn1] at hr1 hr2
  have hf1 := hfin1 n
  have hf2 := hfin2 n
  rw [discretize_unitBall_eq' hn1] at hf1 hf2
  have hcard : (0 : ℝ) < ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
    exact_mod_cast ncard_ballZ0_pos hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hcard9 : ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) ≤ (3 * (n : ℝ)) ^ d :=
    (ncard_ballZ0_le n).trans (pow_le_pow_left₀ (by positivity) (by linarith) d)
  have hs : ∀ t : ℝ, 0 ≤ t → t / ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) < δ ^ d →
      t ^ (1 / (d : ℝ)) ≤ 3 * δ * n := by
    intro t ht htb
    rw [div_lt_iff₀ hcard] at htb
    have h3 : t ≤ (3 * δ * n) ^ d := by
      calc t ≤ δ ^ d * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := htb.le
        _ ≤ δ ^ d * (3 * (n : ℝ)) ^ d := by gcongr
        _ = (3 * δ * n) ^ d := by rw [← mul_pow]; ring_nf
    calc t ^ (1 / (d : ℝ)) ≤ ((3 * δ * n) ^ d) ^ (1 / (d : ℝ)) :=
          Real.rpow_le_rpow ht h3 (by positivity)
      _ = 3 * δ * n := by
          rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  have hs1 := hs _ ENNReal.toReal_nonneg hr1
  have hs2 := hs _ ENNReal.toReal_nonneg hr2
  have hkey := recurrent_center_bound hd hABP hn1 η hl hf1 hf2
  have hCn : 0 ≤ C * n := by positivity
  have h3 := mul_le_mul_of_nonneg_left hs1 hCn
  have h4 := mul_le_mul_of_nonneg_left hs2 hCn
  have hδC : C * n * (3 * δ * n) = (l₂ - l₁) / (8 * d) * (n : ℝ) ^ 2 := by
    rw [hδ]; field_simp; ring
  have hnD' : 4 * d < (l₂ - l₁) * n := by
    have := (div_lt_iff₀ hD0).1 hnD
    linarith
  have e1 : (l₂ - l₁) / (2 * d) * (n : ℝ) ^ 2 - 2 * ((l₂ - l₁) / (8 * d) * (n : ℝ) ^ 2) =
      (l₂ - l₁) / (4 * d) * (n : ℝ) ^ 2 := by field_simp; ring
  have h5 : 1 < (l₂ - l₁) / (4 * d) * (n : ℝ) ^ 2 := by
    have : (l₂ - l₁) / (4 * d) * (n : ℝ) ^ 2 = ((l₂ - l₁) * n) / (4 * d) * n := by
      field_simp
    rw [this]
    have hq : 1 < ((l₂ - l₁) * n) / (4 * d) := by rw [lt_div_iff₀ (by positivity)]; linarith
    nlinarith
  linarith

/-- The recurrent upper and lower densities have a unique common zero. -/
theorem recurrent_common_zero : RecurrentCommonZeroStmt := by
  intro d hd E M
  obtain ⟨l, hl⟩ := recurrent_common_zero_exists hd E M
  refine ⟨l, hl, ?_⟩
  intro k hk
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim (recurrent_no_common_zero_interval hd E M k l h hk.2 hl.1)
  · exact h
  · exact False.elim (recurrent_no_common_zero_interval hd E M l k h hl.2 hk.1)

end RandomSandpile

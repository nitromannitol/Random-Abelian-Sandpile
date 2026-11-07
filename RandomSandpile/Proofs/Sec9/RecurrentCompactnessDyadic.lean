import RandomSandpile.Proofs.Sec9.RecurrentCompactnessEquicontCorrector
import RandomSandpile.Proofs.Sec9.RecurrentOscillationIteration

/-! # From dyadic oscillation estimates to corrector compactness -/

noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

/-- The dyadic Poisson estimate with its geometric forcing sum uniformly bounded. -/
theorem poisson_pairwise_dyadic_uniform (d : ℕ) (hd : 1 ≤ d) :
    ∃ q C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 < C ∧
      ∀ (k R S : ℕ) (c : Site d) (f : Site d → ℝ) (B M : ℝ),
        1 ≤ R → 2 ^ k * R ≤ S → 0 ≤ M →
        (∀ x ∈ box d S, ∀ y ∈ box d S, |f (c + x) - f (c + y)| ≤ B) →
        (∀ z ∈ box d S, |nbrSum f (c + z) - 2 * (d : ℝ) * f (c + z)| ≤ M) →
        ∀ x ∈ box d R, ∀ y ∈ box d R,
          |f (c + x) - f (c + y)| ≤ q ^ k * B + C * M * ((S : ℝ) + 1) ^ 2 := by
  obtain ⟨q, C, hq0, hq1, hC, h⟩ := poisson_pairwise_dyadic d hd
  refine ⟨q, C / (1 - q), hq0, hq1, div_pos hC (by linarith), ?_⟩
  intro k R S c f B M hR hRS hM hb hl x hx y hy
  have hs : (∑ i ∈ Finset.range k, q ^ i) ≤ (1 - q)⁻¹ := by
    have hsum := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hq0 hq1
    simpa [Nat.Ico_zero_eq_range, one_div] using hsum
  have hm : 0 ≤ C * M * ((S : ℝ) + 1) ^ 2 := by positivity
  have hbound := h k R S c f B M hR hRS hM hb hl x hx y hy
  have hsum := mul_le_mul_of_nonneg_left hs hm
  rw [div_eq_mul_inv]
  nlinarith

/-- A geometric oscillation bound with quadratic forcing yields asymptotic
equicontinuity. The starting radius is chosen before the contraction depth. -/
theorem asymptoticEquicontinuous_of_dyadic (d : ℕ) (F : ℕ → Rd d → ℝ)
    (h : ∀ m : ℕ, ∃ q B C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ρ > 0, ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ x y : Rd d,
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
  obtain ⟨N, hN⟩ := hosc ρ hρ k
  refine ⟨ρ / (2 : ℝ) ^ k, by positivity, N, ?_⟩
  intro n hn x y hx hy hxy
  have := hN n hn x y hx hy hxy
  linarith

/-- Local bounds and a dyadic oscillation estimate imply recurrent corrector compactness. -/
theorem recurrent_compactness_of_corrector_dyadic {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (nk : ℕ → ℕ) (hnk : StrictMono nk) (κ C1 R1 : ℝ)
    (hR1 : 1 ≤ R1)
    (hasymp : ∀ z : Site d, R1 ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C1 * ‖toE z‖ ^ (-(d : ℝ)))
    (hK : ∀ m : ℕ, ∃ K : ℝ, ∀ (j : ℕ) (x : Rd d), ‖x‖ ≤ m →
      |ssCorrector d η κ (nk (j + 1)) x| ≤ K)
    (hD : ∀ m : ℕ, ∃ q B C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ρ > 0, ∀ k : ℕ, ∃ N : ℕ, ∀ j ≥ N, ∀ x y : Rd d,
        ‖x‖ ≤ m → ‖y‖ ≤ m → dist x y < ρ / (2 : ℝ) ^ k →
        |ssCorrector d η κ (nk (j + 1)) x - ssCorrector d η κ (nk (j + 1)) y| ≤
          q ^ k * B + C * ρ ^ 2) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ v : Rd d → ℝ, Continuous v ∧
      TendstoLocallyUniformlyOn
        (fun j => rescaleSingleSource (singleSourceOdometer η (nk (ψ j))) (nk (ψ j)))
        (fun x => v x + fundamentalSolution d x) atTop {x : Rd d | x ≠ 0} := by
  exact recurrent_compactness_of_corrector_equicontinuity hd η nk hnk κ C1 R1 hR1 hasymp hK
    (asymptoticEquicontinuous_of_dyadic d _ hD)

end RandomSandpile

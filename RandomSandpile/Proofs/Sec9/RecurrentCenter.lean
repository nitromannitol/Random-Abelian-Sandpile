import RandomSandpile.Proofs.Sec9.RecurrentShell
import RandomSandpile.Proofs.Sec6.StrictConcavity

/-! Positive contact mass in the center of a lattice ball. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal Topology Matrix
noncomputable section
namespace RandomSandpile
open MuLipschitz StrictConcavity
variable {d : ℕ}

/-- A strict total-versus-shell mass gap forces positive mass at central sites. -/
private theorem center_mass_pos {S T U : Set (Rd d)}
    (hcover : S ⊆ T ∪ U) (hgap : volume U < volume S) : 0 < volume T := by
  by_contra h
  have hzero : volume T = 0 := le_antisymm (not_lt.mp h) zero_le
  have hle : volume S ≤ volume U := by
    calc
      volume S ≤ volume (T ∪ U) := measure_mono hcover
      _ ≤ volume T + volume U := measure_union_le _ _
      _ = volume U := by rw [hzero, zero_add]
  exact (not_lt_of_ge hle) hgap

/-- Near-maximal upper contact mass has positive mass at sites in any fixed
concentric sub-ball. -/
theorem recurrent_upper_center (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hα : 0 < muRecurrentBar E l M) :
    ∀ᵐ η ∂E.P, ∀ β : ℝ, 0 < β → β < 1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
        ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M,
          ENNReal.ofReal ((muRecurrentBar E l M - ε) *
              ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
            volume (supGradSet w (ballZ0 (n : ℝ))) →
          0 < volume (⋃ x ∈ ballZ0 (d := d) (β * n), supGrad w x (ballZ0 (n : ℝ))) := by
  filter_upwards [recurrent_upper_shell hd E l M] with η hshell
  intro β hβ hβ1
  let ρ := β / 2
  let ε := muRecurrentBar E l M * ρ ^ d / 4
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρβ : ρ < β := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := lt_trans hρβ hβ1
  have hp : 0 < ρ ^ d := pow_pos hρ _
  have he : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, he, ?_⟩
  filter_upwards [hshell ρ β hρ hρβ hβ1 ε he, eventually_ge_atTop 1] with n hn hn1 w hw hnear
  have hN : 0 < ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) :=
    Nat.cast_pos.2 (ncard_ballZ0_pos hn1)
  have hp1 : ρ ^ d ≤ 1 := pow_le_one₀ hρ.le hρ1.le
  have hleft : 0 ≤ (muRecurrentBar E l M * (1 - ρ ^ d) + ε) *
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by positivity
  have hreal : (muRecurrentBar E l M * (1 - ρ ^ d) + ε) *
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) <
      (muRecurrentBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
    apply mul_lt_mul_of_pos_right _ hN
    dsimp [ε]
    nlinarith [mul_pos hα hp]
  have hgap := (hn w hw).trans_lt (((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hleft).2 hreal).trans_le hnear)
  exact center_mass_pos (supGradSet_subset_union w β n) hgap

/-- The corresponding central mass estimate for lower contacts. -/
theorem recurrent_lower_center (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hα : 0 < muStarRecurrentBar E l M) :
    ∀ᵐ η ∂E.P, ∀ β : ℝ, 0 < β → β < 1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
        ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M,
          ENNReal.ofReal ((muStarRecurrentBar E l M - ε) *
              ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
            volume (subGradSet w (ballZ0 (n : ℝ))) →
          0 < volume (⋃ x ∈ ballZ0 (d := d) (β * n), subGrad w x (ballZ0 (n : ℝ))) := by
  filter_upwards [recurrent_lower_shell hd E l M] with η hshell
  intro β hβ hβ1
  let ρ := β / 2
  let ε := muStarRecurrentBar E l M * ρ ^ d / 4
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρβ : ρ < β := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := lt_trans hρβ hβ1
  have hp : 0 < ρ ^ d := pow_pos hρ _
  have he : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, he, ?_⟩
  filter_upwards [hshell ρ β hρ hρβ hβ1 ε he, eventually_ge_atTop 1] with n hn hn1 w hw hnear
  have hN : 0 < ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) :=
    Nat.cast_pos.2 (ncard_ballZ0_pos hn1)
  have hp1 : ρ ^ d ≤ 1 := pow_le_one₀ hρ.le hρ1.le
  have hleft : 0 ≤ (muStarRecurrentBar E l M * (1 - ρ ^ d) + ε) *
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by positivity
  have hreal : (muStarRecurrentBar E l M * (1 - ρ ^ d) + ε) *
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) <
      (muStarRecurrentBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
    apply mul_lt_mul_of_pos_right _ hN
    dsimp [ε]
    nlinarith [mul_pos hα hp]
  have hgap := (hn w hw).trans_lt (((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hleft).2 hreal).trans_le hnear)
  exact center_mass_pos (subGradSet_subset_union w β n) hgap

end RandomSandpile

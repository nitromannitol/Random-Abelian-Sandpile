import RandomSandpile.Proofs.Sec9.RecurrentMassUniform
import RandomSandpile.Proofs.Sec6.MuLipschitzShell

/-! Annular mass bounds for recurrent perturbed functions. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal Topology Matrix
noncomputable section
namespace RandomSandpile
open MuLipschitzShell
variable {d : ℕ}

/-- Upper contact mass on a shell is bounded by the density times the volume
of any slightly larger annulus. -/
theorem recurrent_upper_shell (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∀ᵐ η ∂E.P, ∀ ρ β : ℝ, 0 < ρ → ρ < β → β < 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M,
        volume (⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 (β * n),
          supGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((muRecurrentBar E l M * (1 - ρ ^ d) + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  filter_upwards [recurrent_subdomain_mass_upper_all hd E l M] with η hη
  intro ρ β hρ hρβ hβ ε hε
  have hρ1 : ρ < 1 := lt_trans hρβ hβ
  have hθ : 0 ≤ 1 - ρ ^ d := by
    have := pow_le_one₀ hρ.le hρ1.le (n := d)
    linarith
  have hmass := hη (annulus d ρ) (MuLipschitzAnnulus.annulus_isLipschitzDomain hd hρ hρ1)
    Set.sdiff_subset (isOpen_ball.sdiff isClosed_closedBall).measurableSet
    (volume_frontier_annulus (by omega) ρ) (1 - ρ ^ d) hθ
    (volume_real_annulus hρ.le hρ1) ε hε
  filter_upwards [hmass, eventually_ge_atTop 1] with n hn hn1 w hw
  refine (measure_mono ?_).trans (hn w hw)
  have hsub := shell_subset_discretize (d := d) (τ := 1 - β) hn1 (by linarith : ρ < 1 - (1 - β))
  refine Set.iUnion₂_subset fun x hx p hp => ?_
  exact Set.mem_iUnion₂.mpr ⟨x, hsub (by simpa using hx), hp⟩

/-- The dual shell estimate for lower contact mass. -/
theorem recurrent_lower_shell (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∀ᵐ η ∂E.P, ∀ ρ β : ℝ, 0 < ρ → ρ < β → β < 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M,
        volume (⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 (β * n),
          subGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((muStarRecurrentBar E l M * (1 - ρ ^ d) + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  filter_upwards [recurrent_subdomain_mass_lower_all hd E l M] with η hη
  intro ρ β hρ hρβ hβ ε hε
  have hρ1 : ρ < 1 := lt_trans hρβ hβ
  have hθ : 0 ≤ 1 - ρ ^ d := by
    have := pow_le_one₀ hρ.le hρ1.le (n := d)
    linarith
  have hmass := hη (annulus d ρ) (MuLipschitzAnnulus.annulus_isLipschitzDomain hd hρ hρ1)
    Set.sdiff_subset (isOpen_ball.sdiff isClosed_closedBall).measurableSet
    (volume_frontier_annulus (by omega) ρ) (1 - ρ ^ d) hθ
    (volume_real_annulus hρ.le hρ1) ε hε
  filter_upwards [hmass, eventually_ge_atTop 1] with n hn hn1 w hw
  refine (measure_mono ?_).trans (hn w hw)
  have hsub := shell_subset_discretize (d := d) (τ := 1 - β) hn1 (by linarith : ρ < 1 - (1 - β))
  refine Set.iUnion₂_subset fun x hx p hp => ?_
  exact Set.mem_iUnion₂.mpr ⟨x, hsub (by simpa using hx), hp⟩

end RandomSandpile

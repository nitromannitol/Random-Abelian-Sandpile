import RandomSandpile.Proofs.Sec9.RecurrentMass

/-! Simultaneous subdomain mass bounds on a common full-probability event. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal Topology Matrix
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- Upper mass bounds hold simultaneously for every regular subdomain. -/
theorem recurrent_subdomain_mass_upper_all (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∀ᵐ η ∂E.P, ∀ (W : Set (Rd d)), IsLipschitzDomain W → W ⊆ ball 0 1 →
      MeasurableSet W → volume (frontier W) = 0 → ∀ (θ : ℝ), 0 ≤ θ →
      volume.real W = θ * volume.real (ball (0 : Rd d) 1) → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M,
        volume (⋃ x ∈ discretize W n, supGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((muRecurrentBar E l M * θ + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  filter_upwards [(muRecurrent_convergence hd E l M).2.2] with η hη
  intro W hW hsub hmeas hfront θ hθ hvol ε hε
  obtain ⟨hfin, hconv⟩ := hη W hW
  filter_upwards [NearMaxSequence.eventually_le_of_tendsto (by omega) hsub hW.1 hmeas hfront hθ hvol
    (muRecurrent_convergence hd E l M).1 hfin hconv ε hε, eventually_ge_atTop 1] with n hn hn1 w hw
  rcases hn with hD | hD
  · rw [hD]; simp
  · exact (volume_supGrad_le_muRecurrent (NearMaxSequence.discretize_subset_ballZ0 hsub hn1)
      le_rfl hw).trans hD

/-- Lower mass bounds hold simultaneously for every regular subdomain. -/
theorem recurrent_subdomain_mass_lower_all (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∀ᵐ η ∂E.P, ∀ (W : Set (Rd d)), IsLipschitzDomain W → W ⊆ ball 0 1 →
      MeasurableSet W → volume (frontier W) = 0 → ∀ (θ : ℝ), 0 ≤ θ →
      volume.real W = θ * volume.real (ball (0 : Rd d) 1) → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M,
        volume (⋃ x ∈ discretize W n, subGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((muStarRecurrentBar E l M * θ + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  filter_upwards [muStarRecurrent_convergence_anyMatrix hd E l M] with η hη
  intro W hW hsub hmeas hfront θ hθ hvol ε hε
  obtain ⟨hfin, hconv⟩ := hη W hW
  have hα : 0 ≤ muStarRecurrentBar E l M := ENNReal.toReal_nonneg
  filter_upwards [NearMaxSequence.eventually_le_of_tendsto (by omega) hsub hW.1 hmeas hfront hθ hvol
    hα hfin hconv ε hε, eventually_ge_atTop 1] with n hn hn1 w hw
  rcases hn with hD | hD
  · rw [hD]; simp
  · exact (volume_subGrad_le_muStarRecurrent (NearMaxSequence.discretize_subset_ballZ0 hsub hn1)
      le_rfl hw).trans hD

end RandomSandpile

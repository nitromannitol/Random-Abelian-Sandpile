import RandomSandpile.Proofs.Sec9.RecurrentNearMax
import RandomSandpile.Proofs.Sec9.RecurrentSymmetric

/-! Subdomain bounds for the gradient mass of recurrent competitors. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal Topology Matrix
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- Restricting a recurrent upper competitor bounds its gradient mass on a subdomain. -/
theorem volume_supGrad_le_muRecurrent {η : Site d → ℤ} {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {A D S : Set (Site d)}
    (hD : D ⊆ A) (hS : S ⊆ D) {w : Site d → ℝ}
    (hw : w ∈ recurrentPerturbed A η l M) :
    volume (⋃ x ∈ S, supGrad w x A) ≤ muRecurrent D η l M := by
  obtain ⟨r, hr, rfl⟩ := hw
  let w : Site d → ℝ := fun x => (r x : ℝ) - (qlZ l x + qMZ M x)
  have hw' : w ∈ recurrentPerturbed D η l M := ⟨r, hr.mono hD, rfl⟩
  refine (measure_mono ?_).trans (le_iSup₂ (f := fun w (_ : w ∈ recurrentPerturbed D η l M) =>
    volume (supGradSet w D)) w hw')
  intro p hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨x, hx, hp⟩ := hp
  exact Set.mem_biUnion (hS hx) (fun y hy => hp y (dClosure_mono hD hy))

/-- The corresponding restriction bound for recurrent lower gradient mass. -/
theorem volume_subGrad_le_muStarRecurrent {η : Site d → ℤ} {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {A D S : Set (Site d)}
    (hD : D ⊆ A) (hS : S ⊆ D) {w : Site d → ℝ}
    (hw : w ∈ recurrentPerturbed A η l M) :
    volume (⋃ x ∈ S, subGrad w x A) ≤ muStarRecurrent D η l M := by
  obtain ⟨r, hr, rfl⟩ := hw
  let w : Site d → ℝ := fun x => (r x : ℝ) - (qlZ l x + qMZ M x)
  have hw' : w ∈ recurrentPerturbed D η l M := ⟨r, hr.mono hD, rfl⟩
  refine (measure_mono ?_).trans (le_iSup₂ (f := fun w (_ : w ∈ recurrentPerturbed D η l M) =>
    volume (subGradSet w D)) w hw')
  intro p hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨x, hx, hp⟩ := hp
  exact Set.mem_biUnion (hS hx) (fun y hy => hp y (dClosure_mono hD hy))

/-- The upper gradient mass on a regular subdomain has the limiting density bound. -/
theorem recurrent_subdomain_mass_upper (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {W : Set (Rd d)}
    (hW : IsLipschitzDomain W) (hsub : W ⊆ ball 0 1) (hmeas : MeasurableSet W)
    (hfront : volume (frontier W) = 0) {θ : ℝ} (hθ : 0 ≤ θ)
    (hvol : volume.real W = θ * volume.real (ball (0 : Rd d) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ η ∂E.P, ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M,
        volume (⋃ x ∈ discretize W n, supGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((muRecurrentBar E l M * θ + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  filter_upwards [(muRecurrent_convergence hd E l M).2.2] with η hη
  obtain ⟨hfin, hconv⟩ := hη W hW
  filter_upwards [NearMaxSequence.eventually_le_of_tendsto (by omega) hsub hW.1 hmeas hfront hθ hvol
    (muRecurrent_convergence hd E l M).1 hfin hconv ε hε, eventually_ge_atTop 1] with n hn hn1 w hw
  rcases hn with hD | hD
  · rw [hD]; simp
  · exact (volume_supGrad_le_muRecurrent (NearMaxSequence.discretize_subset_ballZ0 hsub hn1)
      le_rfl hw).trans hD

/-- The lower gradient mass on a regular subdomain has the limiting density bound. -/
theorem recurrent_subdomain_mass_lower (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {W : Set (Rd d)}
    (hW : IsLipschitzDomain W) (hsub : W ⊆ ball 0 1) (hmeas : MeasurableSet W)
    (hfront : volume (frontier W) = 0) {θ : ℝ} (hθ : 0 ≤ θ)
    (hvol : volume.real W = θ * volume.real (ball (0 : Rd d) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ η ∂E.P, ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M,
        volume (⋃ x ∈ discretize W n, subGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((muStarRecurrentBar E l M * θ + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  filter_upwards [muStarRecurrent_convergence_anyMatrix hd E l M] with η hη
  obtain ⟨hfin, hconv⟩ := hη W hW
  have hα : 0 ≤ muStarRecurrentBar E l M := ENNReal.toReal_nonneg
  filter_upwards [NearMaxSequence.eventually_le_of_tendsto (by omega) hsub hW.1 hmeas hfront hθ hvol
    hα hfin hconv ε hε, eventually_ge_atTop 1] with n hn hn1 w hw
  rcases hn with hD | hD
  · rw [hD]; simp
  · exact (volume_subGrad_le_muStarRecurrent (NearMaxSequence.discretize_subset_ballZ0 hsub hn1)
      le_rfl hw).trans hD

end RandomSandpile

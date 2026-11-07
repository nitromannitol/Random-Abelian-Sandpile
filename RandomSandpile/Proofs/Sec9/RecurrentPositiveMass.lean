import RandomSandpile.Proofs.Sec9.RecurrentPositiveLimit
import RandomSandpile.Proofs.Sec9.OpenBoundaryMaxPrinciple

/-! # Recurrent gradient bounds on the positivity set -/

open Filter MeasureTheory LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- The upper gradient measure of an affine perturbation of a recurrent
function is bounded by the recurrent upper curvature measure. -/
theorem volume_le_muRecurrent {d : ℕ} {η u : Site d → ℤ}
    {A B : Set (Site d)} (hBA : B ⊆ A) (hu : IsRecurrentFunction η A u)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {g : Site d → ℝ}
    (c : Rd d) (c0 : ℝ)
    (hg : ∀ z ∈ dClosure B,
      g z = ((u z : ℝ) - (qlZ l z + qMZ M z)) + inner ℝ c (toE z) + c0) :
    volume (supGradSet g B) ≤ muRecurrent B η l M := by
  let w : Site d → ℝ := fun z => (u z : ℝ) - (qlZ l z + qMZ M z)
  have hw : w ∈ recurrentPerturbed B η l M := ⟨u, hu.mono hBA, rfl⟩
  rw [OpenMaxPrinciple.volume_supGradSet_affine (w₂ := w) c c0 hg]
  exact le_iSup₂_of_le w hw le_rfl

/-- Uniform positivity of a limit supplies the recurrent gradient bound on
any sequence of lattice domains contained in its rescaled compact positivity set. -/
theorem eventually_volume_le_muRecurrent_of_positive_limit {d : ℕ} (hd : 0 < d)
    {η : Site d → ℤ} (hfinite : SingleSourceFinite η) {u : Rd d → ℝ}
    {nk : ℕ → ℕ} (hnk : StrictMono nk) (hconv : TendstoLocallyUniformlyOn
      (fun k => rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k)) u atTop
      {x : Rd d | x ≠ 0})
    {K : Set (Rd d)} (hK : IsCompact K) (hK0 : K ⊆ {x : Rd d | x ≠ 0})
    (hcont : ContinuousOn u K) (hpos : ∀ x ∈ K, 0 < u x)
    (B : ℕ → Set (Site d)) (hB : ∀ k z, z ∈ B k →
      ((nk k : ℝ) ^ (1 / (d : ℝ)))⁻¹ • toE z ∈ K)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : ℕ → Site d → ℝ)
    (c : ℕ → Rd d) (c0 : ℕ → ℝ)
    (hg : ∀ k z, z ∈ dClosure (B k) →
      g k z = ((singleSourceOdometer η (nk k) z : ℝ) - (qlZ l z + qMZ M z)) +
        inner ℝ (c k) (toE z) + c0 k) :
    ∀ᶠ k in atTop, volume (supGradSet (g k) (B k)) ≤ muRecurrent (B k) η l M := by
  filter_upwards [recurrent_on_scaled_compact_of_positive_limit hd hfinite hnk hconv
    hK hK0 hcont hpos] with k hk
  exact volume_le_muRecurrent (fun z hz => hB k z hz) hk l M (c k) (c0 k) (hg k)

end RandomSandpile

import RandomSandpile.Proofs.PegdenSmartProp24
import LatticeProb.Analysis.PegdenSmartProp24Printed
import RandomSandpile.Proofs.BilinearMatrix

/-!
# Trace identities at Pegden–Smart contact points

The second-order expansions of the two rescaled weak solutions can be chosen with matrices whose
traces equal their respective densities, simultaneously on the positive-measure contact set.
-/

open MeasureTheory Filter Topology Asymptotics Metric
open scoped InnerProductSpace Laplacian

namespace RandomSandpile

/-- The Peano coefficient and the density trace use the same symmetric matrix. -/
theorem peano_matrix_trace_ae (d : ℕ) (s u : Rd d → ℝ)
    (hs : MemLp s ⊤ (volume.restrict (ball (0 : Rd d) 1)))
    (hu : ContinuousOn u (ball 0 1))
    (hw : IsWeakSolutionLaplace (ball 0 1) u s) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : Rd d) 1)),
      ∃ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ),
        X.IsSymm ∧ HasSecondOrderTaylorAt u x p X ∧ Matrix.trace X = s x := by
  have h := LatticeProb.PegdenSmart.pegdenSmartProp24Printed
    HessianAdapter.hessianLpStmt_proved (Rd d) volume s u hs hu
    ((isWeakSolutionLaplace_iff _ u s).1 hw)
  filter_upwards [h] with x hx
  obtain ⟨q, H, hH, hexp, htrace⟩ := hx
  obtain ⟨X, hX, hq, ht⟩ := exists_matrix_of_symmetric_bilinear H hH
  refine ⟨(InnerProductSpace.toDual ℝ (Rd d)).symm q, X, hX, ?_, ht.trans htrace⟩
  unfold HasSecondOrderTaylorAt
  simpa only [InnerProductSpace.toDual_symm_apply, hq] using hexp

/-- The two rescaled solutions have matching trace identities at almost every contact point. -/
theorem volume_pos_rescaled_contact_trace (d : ℕ) (u' v s₁ s₂ : Rd d → ℝ)
    (x₁ : Rd d) (ρ C : ℝ)
    (hs₁m : Measurable s₁) (hs₂m : Measurable s₂)
    (hs₁b : ∀ x, |s₁ x| ≤ C) (hs₂b : ∀ x, |s₂ x| ≤ C)
    (hũc : ContinuousOn (fun y => u' (x₁ + ρ • y)) (closedBall 0 1))
    (hvtc : ContinuousOn (fun y => v (x₁ + ρ • y)) (closedBall 0 1))
    (hs₁w : IsWeakSolutionLaplace (ball 0 1) (fun y => u' (x₁ + ρ • y)) s₁)
    (hs₂w : IsWeakSolutionLaplace (ball 0 1) (fun y => v (x₁ + ρ • y)) s₂)
    (hP : 0 < volume {y : Rd d | y ∈ ball 0 1 ∧
      sSup ((fun z => u' (x₁ + ρ • z) - v (x₁ + ρ • z)) '' sphere 0 1) <
        u' (x₁ + ρ • y) - v (x₁ + ρ • y) ∧
      ∃ (q : Rd d) (Y : Matrix (Fin d) (Fin d) ℝ), Y.IsSymm ∧
        HasSecondOrderTaylorAt (fun z => u' (x₁ + ρ • z) - v (x₁ + ρ • z)) y q Y ∧
        (-Y).PosDef}) :
    0 < volume {y : Rd d | y ∈ ball 0 1 ∧
      sSup ((fun z => u' (x₁ + ρ • z) - v (x₁ + ρ • z)) '' sphere 0 1) <
        u' (x₁ + ρ • y) - v (x₁ + ρ • y) ∧
      (∃ (q : Rd d) (Y : Matrix (Fin d) (Fin d) ℝ), Y.IsSymm ∧
        HasSecondOrderTaylorAt (fun z => u' (x₁ + ρ • z) - v (x₁ + ρ • z)) y q Y ∧
        (-Y).PosDef) ∧
      (∃ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ), X.IsSymm ∧
        HasSecondOrderTaylorAt (fun z => u' (x₁ + ρ • z)) y p X ∧ X.trace = s₁ y) ∧
      (∃ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ), X.IsSymm ∧
        HasSecondOrderTaylorAt (fun z => v (x₁ + ρ • z)) y p X ∧ X.trace = s₂ y)} := by
  have hmem : ∀ s : Rd d → ℝ, Measurable s → (∀ x, |s x| ≤ C) →
      MemLp s ⊤ (volume.restrict (ball (0 : Rd d) 1)) := fun s hs hC =>
    memLp_top_of_bound hs.aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hu := peano_matrix_trace_ae d s₁ (fun y => u' (x₁ + ρ • y))
    (hmem s₁ hs₁m hs₁b) (hũc.mono ball_subset_closedBall) hs₁w
  have hv := peano_matrix_trace_ae d s₂ (fun y => v (x₁ + ρ • y))
    (hmem s₂ hs₂m hs₂b) (hvtc.mono ball_subset_closedBall) hs₂w
  rw [ae_restrict_iff' measurableSet_ball] at hu hv
  apply lt_of_lt_of_le hP
  apply measure_mono_ae
  filter_upwards [hu, hv] with y hyu hyv
  rintro ⟨hyB, hymax, hyP⟩
  exact ⟨hyB, hymax, hyP, hyu hyB, hyv hyB⟩

end RandomSandpile

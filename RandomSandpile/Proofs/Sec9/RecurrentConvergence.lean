import RandomSandpile.Proofs.Sec9.RecurrentStationary
import RandomSandpile.Proofs.Sec5.SubadditiveErgodicFinal

/-! The subadditive ergodic limit of the recurrent upper measure. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal Pointwise Matrix
noncomputable section
namespace RandomSandpile

/-- Recurrent upper gradient measures converge simultaneously on Lipschitz domains. -/
theorem muRecurrent_convergence {d : ℕ} (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    0 ≤ muRecurrentBar E l M ∧
    muRecurrentBar E l M ≤ (max ((E.ηmax : ℝ) + l + M.trace) 0 / d) ^ d ∧
    ∀ᵐ η ∂E.P, ∀ W : Set (Rd d), IsLipschitzDomain W →
      (∀ n : ℕ, muRecurrent (discretize W n) η l M ≠ ⊤) ∧
      Tendsto (fun n : ℕ => (muRecurrent (discretize W n) η l M).toReal /
        ((discretize W n).ncard : ℝ)) atTop (𝓝 (muRecurrentBar E l M)) := by
  obtain ⟨a, ha0, haK, ha, hlim⟩ :=
    subadditive_limit_of_steps subadditiveErgodic unitBallLipschitz discretizeFinite hd E
      (fun A η => muRecurrent A η l M) _ _ (by positivity)
      (le_ηmax_event E).1 (le_ηmax_event E).2.1
      (le_ηmax_event E).2.2
      (fun A hA => measurable_muRecurrent hA l M)
      (fun y A η => muRecurrent_shift_eq η l M y A)
      (fun η k A B h => muRecurrent_subadditive η l M k A B h)
      (fun η hη A hA => muRecurrent_le_ncard (by omega) hA (fun x _ => hη x) l M)
  change muRecurrentBar E l M = a at ha
  rw [ha]
  exact ⟨ha0, haK, hlim⟩

end RandomSandpile

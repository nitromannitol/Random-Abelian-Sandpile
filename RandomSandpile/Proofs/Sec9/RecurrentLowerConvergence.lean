import RandomSandpile.Proofs.Sec9.RecurrentConvergence
import RandomSandpile.Proofs.Sec9.RecurrentMuStar
import RandomSandpile.Steps.Sec6.MuLipschitz

/-! The recurrent lower density agrees with the standard lower density. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal Pointwise Matrix
noncomputable section
namespace RandomSandpile

/-- Recurrent and standard lower densities agree in dimension at least two. -/
theorem muStarRecurrentBar_eq {d : ℕ} (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStarRecurrentBar E l M = muStarBar E l M := by
  unfold muStarRecurrentBar muStarBar
  congr 2
  funext η
  congr 1
  funext n
  rw [recurrentMuStarEquality d hd _ (MuLipschitz.ballZ0_finite _) η l M]

/-- Recurrent lower gradient measures converge on every Lipschitz domain. -/
theorem muStarRecurrent_convergence {d : ℕ} (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsSymm) :
    ∀ᵐ η ∂E.P, ∀ W : Set (Rd d), IsLipschitzDomain W →
      (∀ n : ℕ, muStarRecurrent (discretize W n) η l M ≠ ⊤) ∧
      Tendsto (fun n : ℕ => (muStarRecurrent (discretize W n) η l M).toReal /
        ((discretize W n).ncard : ℝ)) atTop (𝓝 (muStarRecurrentBar E l M)) := by
  filter_upwards [(muConvergence_unconditional d hd).1 E M hM l] with η hη W hW
  have h := hη W hW
  have heq : ∀ n : ℕ, muStarRecurrent (discretize W n) η l M =
      muStar (discretize W n) η l M := fun n =>
    recurrentMuStarEquality d hd _ (discretizeFinite d W hW.1 n) η l M
  rw [muStarRecurrentBar_eq hd E l M]
  simp_rw [heq]
  exact ⟨fun n => (h.1 n).2, h.2.2⟩

end RandomSandpile

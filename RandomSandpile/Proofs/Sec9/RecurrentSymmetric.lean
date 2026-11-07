import RandomSandpile.Proofs.Sec9.RecurrentLowerConvergence
import RandomSandpile.Proofs.Sec6.MuLipschitzShell

/-! Recurrent curvature measures depend only on the symmetric matrix part. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal Pointwise Matrix
noncomputable section
namespace RandomSandpile
open MuLipschitzShell
variable {d : ℕ}

theorem recurrentPerturbed_symmPart (A : Set (Site d)) (η : Site d → ℤ)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    recurrentPerturbed A η l (symmPart M) = recurrentPerturbed A η l M := by
  simp only [recurrentPerturbed, qMZ_symmPart]

theorem muRecurrent_symmPart (A : Set (Site d)) (η : Site d → ℤ)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muRecurrent A η l (symmPart M) = muRecurrent A η l M := by
  simp only [muRecurrent, recurrentPerturbed_symmPart]

theorem muStarRecurrent_symmPart (A : Set (Site d)) (η : Site d → ℤ)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStarRecurrent A η l (symmPart M) = muStarRecurrent A η l M := by
  simp only [muStarRecurrent, recurrentPerturbed_symmPart]

theorem muRecurrentBar_symmPart (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muRecurrentBar E l (symmPart M) = muRecurrentBar E l M := by
  simp only [muRecurrentBar, muRecurrent_symmPart]

theorem muStarRecurrentBar_symmPart (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStarRecurrentBar E l (symmPart M) = muStarRecurrentBar E l M := by
  simp only [muStarRecurrentBar, muStarRecurrent_symmPart]

/-- The lower convergence holds for arbitrary matrices, since only their symmetric part matters. -/
theorem muStarRecurrent_convergence_anyMatrix (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∀ᵐ η ∂E.P, ∀ W : Set (Rd d), IsLipschitzDomain W →
      (∀ n : ℕ, muStarRecurrent (discretize W n) η l M ≠ ⊤) ∧
      Tendsto (fun n : ℕ => (muStarRecurrent (discretize W n) η l M).toReal /
        ((discretize W n).ncard : ℝ)) atTop (𝓝 (muStarRecurrentBar E l M)) := by
  simpa only [muStarRecurrent_symmPart, muStarRecurrentBar_symmPart] using
    muStarRecurrent_convergence hd E l (symmPart M) (symmPart_isSymm M)

end RandomSandpile

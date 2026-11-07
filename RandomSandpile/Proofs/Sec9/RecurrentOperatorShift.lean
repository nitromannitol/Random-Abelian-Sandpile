import RandomSandpile.Proofs.Sec9.RecurrentCommonZero
import RandomSandpile.Steps.Sec9.RecurrentViscosity

/-! Trace shifts of recurrent curvature measures and their effective operator. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal
noncomputable section
namespace RandomSandpile
open EffectiveOperatorBasic
variable {d : ℕ}

/-- Adding a scalar multiple of the identity shifts the scalar curvature parameter. -/
theorem recurrentPerturbed_shift (hd : 1 ≤ d) (A : Set (Site d)) (η : Site d → ℤ)
    (l t : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    recurrentPerturbed A η l (M + t • 1) = recurrentPerturbed A η (l + d * t) M := by
  have hf : ∀ r : Site d → ℤ,
      (fun x => (r x : ℝ) - (qlZ l x + qMZ (M + t • 1) x)) =
      (fun x => (r x : ℝ) - (qlZ (l + d * t) x + qMZ M x)) := by
    intro r; funext x; rw [qlZ_add_qMZ_shift hd]
  simp only [recurrentPerturbed, hf]

/-- Both recurrent densities obey the trace shift. -/
theorem recurrentBar_shift (hd : 1 ≤ d) (E : RandomEnvironment d) (l t : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    muRecurrentBar E l (M + t • 1) = muRecurrentBar E (l + d * t) M ∧
    muStarRecurrentBar E l (M + t • 1) = muStarRecurrentBar E (l + d * t) M := by
  have hu : ∀ A η, muRecurrent A η l (M + t • 1) = muRecurrent A η (l + d * t) M := by
    intro A η; simp only [muRecurrent, recurrentPerturbed_shift hd]
  have hs : ∀ A η, muStarRecurrent A η l (M + t • 1) = muStarRecurrent A η (l + d * t) M := by
    intro A η; simp only [muStarRecurrent, recurrentPerturbed_shift hd]
  constructor
  · simp only [muRecurrentBar, hu]
  · simp only [muStarRecurrentBar, hs]

/-- The recurrent effective operator has the trace-shift property. -/
theorem effOpRecurrent_shift (hd : 2 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    effOpRecurrent E (M + t • 1) = effOpRecurrent E M - (d : ℝ) * t := by
  obtain ⟨l, hl, hu⟩ := recurrent_common_zero d hd E M
  have heq := effOpRecurrent_eq_of_unique E M l hl hu
  obtain ⟨k, hk, hku⟩ := recurrent_common_zero d hd E (M + t • 1)
  have heq' := effOpRecurrent_eq_of_unique E (M + t • 1) k hk hku
  have hz : muRecurrentBar E (k + d * t) M = 0 ∧
      muStarRecurrentBar E (k + d * t) M = 0 := by
    rw [← (recurrentBar_shift (by omega) E k t M).1,
      ← (recurrentBar_shift (by omega) E k t M).2]
    exact hk
  have hkl := hu _ hz
  rw [heq, heq']
  linarith

end RandomSandpile

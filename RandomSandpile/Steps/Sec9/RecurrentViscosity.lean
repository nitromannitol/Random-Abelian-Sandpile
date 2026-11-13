import RandomSandpile.Steps.Sec9.Recurrent

/-! # Recurrent viscosity and common-zero reductions -/

open MeasureTheory Filter LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Corrector comparison gives the Crandall–Ishii–Lions supersolution inequality off the source. -/
def RecurrentSSSupersolutionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ᵐ η ∂E.P, SingleSourceFinite η → SingleSourceVanishingTail η →
      ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
        ViscFromBelowGE (effOpRecurrent E) {x : Rd d | x ≠ 0} u

/-- Admissibility follows from the viscosity inequality and the proved nonnegativity of limits. -/
theorem recurrentSSAdmissibility_of_supersolution (h : RecurrentSSSupersolutionStmt) :
    RecurrentSSAdmissibilityStmt := by
  intro d hd E
  filter_upwards [h d hd E] with η hη
  intro hfinite htail v hvc hv
  exact ⟨hvc, fun x hx => hv.nonneg hx, hη hfinite htail _ hv⟩

/-- The operator selected by a unique common zero is that zero. -/
theorem effOpRecurrent_eq_of_unique {d : ℕ} (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) (l : ℝ)
    (hl : muRecurrentBar E l M = 0 ∧ muStarRecurrentBar E l M = 0)
    (hu : ∀ t : ℝ, muRecurrentBar E t M = 0 ∧ muStarRecurrentBar E t M = 0 → t = l) :
    effOpRecurrent E M = l := by
  have hs : {t : ℝ | muRecurrentBar E t M = 0 ∧ muStarRecurrentBar E t M = 0} = {l} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨hu t, fun ht => ht ▸ hl⟩
  simp [effOpRecurrent, hs]

/-- Under the common-zero step, the recurrent operator is indeed a common zero. -/
theorem recurrentCommonZero_at_operator (h : RecurrentCommonZeroStmt)
    {d : ℕ} (hd : 2 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    muRecurrentBar E (effOpRecurrent E M) M = 0 ∧
      muStarRecurrentBar E (effOpRecurrent E M) M = 0 := by
  obtain ⟨l, hl, hu⟩ := h d hd E M
  rw [effOpRecurrent_eq_of_unique E M l hl hu]
  exact hl

end RandomSandpile

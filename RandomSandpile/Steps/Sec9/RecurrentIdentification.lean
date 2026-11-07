import RandomSandpile.Steps.Sec9.RecurrentHomogenization
import RandomSandpile.Proofs.Sec6.MuMonotone
import RandomSandpile.Steps.Sec6.EffectiveOperatorBasic

/-! # Identification of the recurrent and original effective operators -/

open MeasureTheory Filter LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Recurrent backgrounds give the same deterministic upper curvature density. -/
def RecurrentUpperDensityEqualityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    (∀ᵐ η ∂E.P, ∀ A : Set (Site d), A.Finite → IsRecurrentOn η A) →
      ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), muRecurrentBar E l M = muBar E l M

/-- Equality of upper densities, recurrentization of the lower density, and the unique common
zero imply C13's operator identification. The Section 6 monotonicity theorem is reused. -/
theorem recurrentOperatorIdentification_of_densitySteps
    (hupper : RecurrentUpperDensityEqualityStmt) (hlower : RecurrentMuStarEqualityStmt)
    (hzero : RecurrentCommonZeroStmt) : RecurrentOperatorIdentificationStmt := by
  intro d hd E hrec
  funext M
  obtain ⟨l, hl, hu⟩ := hzero d hd E M
  have huEq : ∀ t, muRecurrentBar E t M = muBar E t M := fun t => hupper d hd E hrec t M
  have hsEq : ∀ t, muStarRecurrentBar E t M = muStarBar E t M :=
    fun t => muStarRecurrentBar_eq_of_finiteEquality hlower hd E t M
  have hlU : muBar E l M = 0 := by rw [← huEq l]; exact hl.1
  have hlS : muStarBar E l M = 0 := by rw [← hsEq l]; exact hl.2
  have hset : muEqSet E M = {l} := by
    ext t
    simp only [muEqSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ht
      have h0 : muBar E t M = 0 ∧ muStarBar E t M = 0 := by
        rcases le_total t l with htl | hlt
        · have hle := EffectiveOperatorBasic.muBar_mono muMonotone (by omega : 1 ≤ d) E M htl
          have hzt : muBar E t M = 0 := le_antisymm (by simpa [hlU] using hle)
            (EffectiveOperatorBasic.muBar_nonneg E t M)
          exact ⟨hzt, by rw [← ht, hzt]⟩
        · have hle := EffectiveOperatorBasic.muStarBar_anti muMonotone (by omega : 1 ≤ d) E M hlt
          have hzt : muStarBar E t M = 0 := le_antisymm (by simpa [hlS] using hle)
            (EffectiveOperatorBasic.muStarBar_nonneg E t M)
          exact ⟨by rw [ht, hzt], hzt⟩
      apply hu t
      exact ⟨by rw [huEq t]; exact h0.1, by rw [hsEq t]; exact h0.2⟩
    · intro ht
      subst t
      simp [hlU, hlS]
  rw [effOpRecurrent_eq_of_unique E M l hl hu]
  simp [effOp, hset]

end RandomSandpile

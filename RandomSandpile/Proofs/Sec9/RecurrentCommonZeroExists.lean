import RandomSandpile.Proofs.Sec9.RecurrentLipschitz
import RandomSandpile.Proofs.Sec9.RecurrentSeparation
import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasicFinal
import RandomSandpile.Proofs.Sec5.SubadditiveErgodicFinal

/-! Existence of a common zero of the recurrent curvature densities. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal
noncomputable section
namespace RandomSandpile
open EffectiveOperatorBasic
variable {d : ℕ}

/-- The recurrent upper and lower curvature densities have a common zero. -/
theorem recurrent_common_zero_exists (hd : 2 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ l : ℝ, muRecurrentBar E l M = 0 ∧ muStarRecurrentBar E l M = 0 := by
  let a : ℝ := -(E.ηmax : ℝ) - M.trace
  have ha : muRecurrentBar E a M = 0 := muRecurrentBar_eq_zero hd E le_rfl
  by_cases hzero : muStarRecurrentBar E a M = 0
  · exact ⟨a, ha, hzero⟩
  have hgpos : 0 < muStarRecurrentBar E a M :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
  let Z : Set ℝ := {l | muStarRecurrentBar E l M = 0}
  have hcont : Continuous (fun l => muStarRecurrentBar E l M) := by
    have heq : (fun l => muStarRecurrentBar E l M) = (fun l => muStarBar E l M) := by
      funext l
      exact muStarRecurrentBar_eq hd E l M
    rw [heq]
    exact continuous_muStarBar muMonotone (muLipschitzLoc_of_muConvergence muConvergence_unconditional) hd E M
  have hclosed : IsClosed Z := isClosed_eq hcont continuous_const
  have hne : Z.Nonempty := by
    refine ⟨(2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - M.trace, ?_⟩
    change muStarRecurrentBar E _ M = 0
    rw [muStarRecurrentBar_eq hd E]
    exact muStarBar_eq_zero (by omega) E le_rfl
  have hbelow : BddBelow Z := by
    refine ⟨a, ?_⟩
    intro z hz
    by_contra h
    have hza : z ≤ a := le_of_lt (lt_of_not_ge h)
    have hanti := muStarRecurrentBar_anti hd E M hza
    change muStarRecurrentBar E z M = 0 at hz
    linarith
  let b := sInf Z
  have hb : muStarRecurrentBar E b M = 0 := hclosed.csInf_mem hne hbelow
  have hupper : muRecurrentBar E b M = 0 := by
    by_contra hnot
    have hpos : 0 < muRecurrentBar E b M :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hnot)
    obtain ⟨C, hC, hLip⟩ := recurrent_upper_lipschitz_at hd E b M hpos
    let s : ℝ := muRecurrentBar E b M / (2 * (C + 1))
    have hs : 0 < s := by dsimp [s]; positivity
    have hsmall : s * C < muRecurrentBar E b M := by
      dsimp [s]
      have hden : 0 < 2 * (C + 1) := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    have hprev : 0 < muRecurrentBar E (b - s) M := by linarith [hLip s hs]
    have hprevzero : muStarRecurrentBar E (b - s) M = 0 := by
      have hn := recurrent_densities_not_both_pos hd E (b - s) M
      have hnn : 0 ≤ muStarRecurrentBar E (b - s) M := ENNReal.toReal_nonneg
      by_contra h
      have hp : 0 < muStarRecurrentBar E (b - s) M := lt_of_le_of_ne hnn (Ne.symm h)
      exact hn ⟨hprev, hp⟩
    have hleast : b ≤ b - s := csInf_le hbelow hprevzero
    linarith
  exact ⟨b, hupper, hb⟩

end RandomSandpile

import RandomSandpile.Proofs.Sec9.RecurrentLipschitzFinite
import RandomSandpile.Proofs.Sec9.RecurrentBending
import RandomSandpile.Proofs.Sec9.RecurrentShell
import RandomSandpile.Proofs.Sec6.MuLipschitz

/-! Continuity of the recurrent upper curvature density. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 400000
namespace RandomSandpile
open MuLipschitz
variable {d : ℕ}

/-- At a positive upper density, decreasing scalar curvature changes the
recurrent upper density at most linearly. -/
theorem recurrent_upper_lipschitz_at (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hα : 0 < muRecurrentBar E l M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s →
      muRecurrentBar E l M ≤ muRecurrentBar E (l - s) M + s * C := by
  obtain ⟨c, hc, hb⟩ := recurrent_upper_bending hd E l M hα
  refine ⟨3 / c, by positivity, ?_⟩
  intro s hs
  set α := muRecurrentBar E l M with hαdef
  have hnn : 0 ≤ muRecurrentBar E (l - s) M := ENNReal.toReal_nonneg
  by_cases hsmall : α ≤ 3 / c * s
  · linarith
  have hlarge : 3 / c * s < α := lt_of_not_ge hsmall
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set τ := 3 * s / (2 * d * c * α) with hτ
  have hτpos : 0 < τ := by positivity
  have hτsmall : 2 * τ < 1 := by
    have hdge : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    rw [hτ]
    have hmul : 3 * s < c * α := by
      have : 0 < c := hc
      have hh : (3 * s) / c < α := by convert hlarge using 1; ring
      have := (div_lt_iff₀ hc).1 hh
      linarith
    rw [show 2 * (3 * s / (2 * (d : ℝ) * c * α)) = (3 * s) / (d * c * α) by ring]
    rw [div_lt_one (by positivity)]
    nlinarith
  have hdτα : 2 * d * τ * α = 3 / c * s := by
    rw [hτ]; field_simp
  have hκ : ∀ n : ℕ, 3 * s * n / (2 * d) ≤ c * α * ((1 - (1 - τ)) * n) := by
    intro n
    rw [sub_sub_cancel, hτ]
    apply le_of_eq
    field_simp
  suffices h : α - 3 / c * s ≤ muRecurrentBar E (l - s) M by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ᵐ η ∂E.P, ∀ n : ℕ,
      muRecurrent (ballZ0 (n : ℝ)) η (l - s) M ≤
        ENNReal.ofReal (K * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
    refine ⟨(max (((max E.ηmax 0 : ℤ) : ℝ) + (l - s) + M.trace) 0 / d) ^ d, (ae_all_iff.2 fun x => (E.bounded x).mono fun _ h => h.2).mono fun η hη n => ?_⟩
    exact (recurrentMuLe d hd _ (ballZ0_finite _) η (l - s) M).trans
      (mu_le_ncard hd1 (ballZ0_finite _) (fun x _ => hη x) (l - s) M)
  unfold muRecurrentBar
  refine le_toReal_lintegral_limsup (K := K)
    (hK.mono fun η h => Eventually.of_forall fun n => div_ncard_le_ofReal (h n)) ?_
  filter_upwards [hb, recurrent_upper_shell hd E l M] with η hb hsh
  obtain ⟨r, hr, hnear, hbend⟩ := hb
  intro ε hε
  have hτ1 : τ < 1 := by linarith
  have hρ0 : 0 < 1 - 2 * τ := by linarith
  have hρβ : 1 - 2 * τ < 1 - τ := by linarith
  have hβ1 : 1 - τ < 1 := by linarith
  filter_upwards [hnear (ε / 2) (by positivity), hbend (1 - τ) (by linarith) hβ1,
    hsh (1 - 2 * τ) (1 - τ) hρ0 hρβ hβ1 (ε / 2) (by positivity),
    eventually_ge_atTop 1] with n hN hB hS hn
  let w : Site d → ℝ := fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)
  have hw : w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M := ⟨r n, hr n, rfl⟩
  have hbern : 1 - d * (2 * τ) ≤ (1 - 2 * τ) ^ d := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(2 * τ) by linarith) d
    rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
    exact this
  have hcoef : (1 - (1 - 2 * τ) ^ d) * α ≤ 3 / c * s := by
    rw [← hdτα]
    nlinarith
  have hS' : volume (⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 ((1 - τ) * n),
      supGrad w x (ballZ0 (n : ℝ))) ≤
      ENNReal.ofReal ((3 / c * s + ε / 2) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
    refine (hS w hw).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [← hαdef]
    linarith
  have h := recurrent_ofReal_le_mu_sub (Cs := 3 / c * s) boundaryGap hd1 hs (by positivity) (hκ n)
    hw hN hB hS'
  change ENNReal.ofReal (α - 3 / c * s - ε) ≤
    muRecurrent (ballZ0 (n : ℝ)) η (l - s) M / ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)
  apply MuLipschitz.ofReal_le_div_ncard (d := d) hn
  convert h using 1; congr 1; ring

end RandomSandpile

import RandomSandpile.Proofs.Sec9.RecurrentABP
import RandomSandpile.Proofs.Sec9.RecurrentBound
import RandomSandpile.Proofs.Sec9.SingleSourceH0Operator

/-! The fixed-boundary estimate for recurrent curvature measures. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
noncomputable section
namespace RandomSandpile
open EffectiveOperatorBasic MuLipschitz SingleSourceH0
variable {d : ℕ}

/-- The two recurrent ABP bounds control the separation of scalar curvatures. -/
theorem recurrent_center_bound (hd : 2 ≤ d) {C : ℝ}
    (hABP : ∀ (n : ℕ) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), (muRecurrent (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
        ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
          w x ≤ sSup (w '' bdry (ballZ0 (n : ℝ))) +
            C * n * (muRecurrent (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / (d : ℝ))) ∧
      (muStarRecurrent (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
        ∀ w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
          sInf (w '' bdry (ballZ0 (n : ℝ))) ≤
            w x + C * n * (muStarRecurrent (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / (d : ℝ))))
    {n : ℕ} (hn1 : 1 ≤ n) (η : Site d → ℤ) {M : Matrix (Fin d) (Fin d) ℝ}
    {l₁ l₂ : ℝ} (hl : l₁ < l₂) (hf1 : muStarRecurrent (ballZ0 (n : ℝ)) η l₁ M ≠ ⊤)
    (hf2 : muRecurrent (ballZ0 (n : ℝ)) η l₂ M ≠ ⊤) :
    (l₂ - l₁) / (2 * d) * (n : ℝ) ^ 2 ≤
      1 + C * n * (muStarRecurrent (ballZ0 (n : ℝ)) η l₁ M).toReal ^ (1 / (d : ℝ)) +
        C * n * (muRecurrent (ballZ0 (n : ℝ)) η l₂ M).toReal ^ (1 / (d : ℝ)) := by
  have hd0 : 0 < d := by omega
  set B := ballZ0 (d := d) (n : ℝ)
  have hfinB : B.Finite := ballZ0_finite _
  have hfinD : (dClosure B).Finite := dClosure_finite hfinB
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℤ, ∀ y ∈ dClosure B, -⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉ ≤ C₀ := by
    obtain ⟨C₀, hC₀⟩ := (hfinD.image fun y => -⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉).bddAbove
    exact ⟨C₀, fun y hy => hC₀ ⟨y, hy, rfl⟩⟩
  obtain ⟨u, hudef⟩ : ∃ u : Site d → ℤ,
      u = (dClosure B).indicator fun y => ⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉ + C₀ := ⟨_, rfl⟩
  have hu : IsTopplingFn B u := by
    rw [hudef]
    refine ⟨fun y => ?_, fun y hy => Set.indicator_of_notMem hy _⟩
    by_cases hy : y ∈ dClosure B
    · rw [Set.indicator_of_mem hy]; linarith [hC₀ y hy]
    · rw [Set.indicator_of_notMem hy]
  obtain ⟨v, ⟨_, hS⟩, hvbd⟩ :=
    NearMaxSequence.exists_locLegal_stabilizing hd0 hfinB η hu
  obtain ⟨h, hh, hhbd, _⟩ := recurrentizeFixedBoundary d hd B hfinB η v hS.2
  have hbd : ∀ y ∈ bdry B, h y = u y := fun y hy => (hhbd y hy).trans (hvbd y hy)
  have hbd' : ∀ y ∈ bdry B, (h y : ℝ) = ⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉ + C₀ := by
    intro y hy
    rw [hbd y hy, hudef, Set.indicator_of_mem (bdry_subset_dClosure B hy)]
    push_cast
    ring
  have hfar : ∀ y ∈ bdry B, (n : ℝ) ^ 2 ≤ ‖toE y‖ ^ 2 := by
    intro y hy
    have hyn : (n : ℝ) ≤ ‖toE y‖ := by
      by_contra hlt
      exact hy.1 (mem_ballZ0.2 (not_le.mp hlt))
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hne : (bdry B).Nonempty := Burning.bdry_nonempty hd0 hfinB
    ⟨0, mem_ballZ0.2 (by rw [toE_zero, norm_zero]; exact_mod_cast hn1)⟩
  have h0B : (0 : Site d) ∈ B := mem_ballZ0.2 (by rw [toE_zero, norm_zero]; exact_mod_cast hn1)
  have hw₁ : (fun y => (h y : ℝ) - (qlZ l₁ y + qMZ M y)) ∈ recurrentPerturbed B η l₁ M := ⟨h, hh, rfl⟩
  have hw₂ : (fun y => (h y : ℝ) - (qlZ l₂ y + qMZ M y)) ∈ recurrentPerturbed B η l₂ M := ⟨h, hh, rfl⟩
  have hA1 := (hABP n η l₁ M).2 hf1 _ hw₁ 0 h0B
  have hA2 := (hABP n η l₂ M).1 hf2 _ hw₂ 0 h0B
  have hq0 : ∀ l : ℝ, qlZ l (0 : Site d) + qMZ M 0 = 0 := fun l => by
    simp [qlZ, ql, qMZ, qM, toE_zero]
  simp only [hq0, sub_zero] at hA1 hA2
  have hinf := le_sInf_bdry_gen hd0 hne (h := h) (l := l₁) (by linarith) hbd' hfar
  have hsup := sSup_bdry_le_gen hd0 hne (h := h) (l := l₂) (by linarith) hbd' hfar
  have e : ((l₁ + l₂) / 2 - l₁) / (2 * d) * (n : ℝ) ^ 2 -
      ((l₁ + l₂) / 2 - l₂) / (2 * d) * (n : ℝ) ^ 2 = (l₂ - l₁) / (2 * d) * (n : ℝ) ^ 2 := by
    ring
  linarith

end RandomSandpile

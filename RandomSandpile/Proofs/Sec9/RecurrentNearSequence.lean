import RandomSandpile.Proofs.Sec9.RecurrentMass

/-! Almost-sure recurrent near-maximizers on expanding lattice balls. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal Topology Matrix
noncomputable section
namespace RandomSandpile
open MuLipschitz
variable {d : ℕ}

/-- Recurrent near-maximizers can be selected with asymptotically maximal upper mass. -/
theorem recurrent_upper_nearMax_sequence (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∀ᵐ η ∂E.P, ∃ r : ℕ → Site d → ℤ,
      (∀ n : ℕ, IsRecurrentFunction η (ballZ0 (n : ℝ)) (r n)) ∧
      (∀ (n : ℕ) x, x ∈ ballZ0 (d := d) (n : ℝ) →
        |lapR (fun y => (r n y : ℝ) - (qlZ l y + qMZ M y)) x| ≤
          NearMaxSequence.lapBound d E.ηmin E.ηmax l M) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((muRecurrentBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (supGradSet (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) (ballZ0 (n : ℝ)))) := by
  set δ : ℕ → ℝ := fun n => (((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) + 1) / ((n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      δ n ≤ ε / 2 * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (4 / ε)
    filter_upwards [eventually_ge_atTop (max m 1)] with n hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hN1 : (1 : ℝ) ≤ ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
      exact_mod_cast ncard_ballZ0_pos hn1
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
    have h4 : 4 < ε * ((n : ℝ) + 1) := by
      have := (div_lt_iff₀ hε).1 (hm.trans_le (by linarith : (m : ℝ) ≤ n + 1))
      linarith
    simp only [δ]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  filter_upwards [(muRecurrent_convergence hd E l M).2.2, ae_all_iff.2 E.bounded] with η hconv hη
  choose r hr hvol using fun n : ℕ =>
    exists_nearMax_recurrent hd (ballZ0_finite (n : ℝ)) η l M (fun x => (hη x).2) (hδpos n)
  refine ⟨r, hr, fun n x hx => recurrent_abs_lapR_le (by omega) hη (hr n) l M hx, ?_⟩
  have hball := (hconv (ball (0 : Rd d) 1) (unitBallLipschitz d)).2
  have hlim : Tendsto (fun n : ℕ => (muRecurrent (ballZ0 (n : ℝ)) η l M).toReal /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) atTop (𝓝 (muRecurrentBar E l M)) :=
    hball.congr' ((eventually_ge_atTop 1).mono fun n hn => by rw [discretize_unitBall hn])
  intro ε hε
  filter_upwards [hlim.eventually (lt_mem_nhds (show muRecurrentBar E l M - ε / 2 <
    muRecurrentBar E l M by linarith)), hδsmall ε hε, eventually_ge_atTop 1] with n h1 h2 hn
  have hNpos : (0 : ℝ) < ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) :=
    Nat.cast_pos.2 (ncard_ballZ0_pos hn)
  have h1' := (lt_div_iff₀ hNpos).1 h1
  refine (ENNReal.ofReal_le_ofReal ?_).trans (hvol n)
  nlinarith


/-- Recurrent near-maximizers can be selected with asymptotically maximal lower mass. -/
theorem recurrent_lower_nearMax_sequence (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∀ᵐ η ∂E.P, ∃ r : ℕ → Site d → ℤ,
      (∀ n : ℕ, IsRecurrentFunction η (ballZ0 (n : ℝ)) (r n)) ∧
      (∀ (n : ℕ) x, x ∈ ballZ0 (d := d) (n : ℝ) →
        |lapR (fun y => (r n y : ℝ) - (qlZ l y + qMZ M y)) x| ≤
          NearMaxSequence.lapBound d E.ηmin E.ηmax l M) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((muStarRecurrentBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (subGradSet (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) (ballZ0 (n : ℝ)))) := by
  set δ : ℕ → ℝ := fun n => (((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) + 1) / ((n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      δ n ≤ ε / 2 * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (4 / ε)
    filter_upwards [eventually_ge_atTop (max m 1)] with n hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hN1 : (1 : ℝ) ≤ ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
      exact_mod_cast ncard_ballZ0_pos hn1
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
    have h4 : 4 < ε * ((n : ℝ) + 1) := by
      have := (div_lt_iff₀ hε).1 (hm.trans_le (by linarith : (m : ℝ) ≤ n + 1))
      linarith
    simp only [δ]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  filter_upwards [muStarRecurrent_convergence_anyMatrix hd E l M, ae_all_iff.2 E.bounded] with η hconv hη
  choose r hr hvol using fun n : ℕ =>
    exists_nearMax_recurrent_lower hd (ballZ0_finite (n : ℝ)) η l M (fun x => (hη x).1) (hδpos n)
  refine ⟨r, hr, fun n x hx => recurrent_abs_lapR_le (by omega) hη (hr n) l M hx, ?_⟩
  have hball := (hconv (ball (0 : Rd d) 1) (unitBallLipschitz d)).2
  have hlim : Tendsto (fun n : ℕ => (muStarRecurrent (ballZ0 (n : ℝ)) η l M).toReal /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) atTop (𝓝 (muStarRecurrentBar E l M)) :=
    hball.congr' ((eventually_ge_atTop 1).mono fun n hn => by rw [discretize_unitBall hn])
  intro ε hε
  filter_upwards [hlim.eventually (lt_mem_nhds (show muStarRecurrentBar E l M - ε / 2 <
    muStarRecurrentBar E l M by linarith)), hδsmall ε hε, eventually_ge_atTop 1] with n h1 h2 hn
  have hNpos : (0 : ℝ) < ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) :=
    Nat.cast_pos.2 (ncard_ballZ0_pos hn)
  have h1' := (lt_div_iff₀ hNpos).1 h1
  refine (ENNReal.ofReal_le_ofReal ?_).trans (hvol n)
  nlinarith

end RandomSandpile

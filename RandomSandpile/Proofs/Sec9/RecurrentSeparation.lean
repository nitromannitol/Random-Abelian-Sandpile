import RandomSandpile.Proofs.Sec9.RecurrentSeparationFinite
import RandomSandpile.Proofs.Sec9.RecurrentContact
import RandomSandpile.Proofs.Sec5.HarnackQuadratic

/-! Separation of the recurrent upper and lower curvature densities. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped Topology
set_option maxHeartbeats 400000
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- The upper and lower recurrent curvature densities cannot both be positive. -/
theorem recurrent_densities_not_both_pos (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ¬ (0 < muRecurrentBar E l M ∧ 0 < muStarRecurrentBar E l M) := by
  rintro ⟨hα, hγ⟩
  obtain ⟨c, hc, hu⟩ := recurrent_upper_contact hd E l M hα
  obtain ⟨_, _, hv⟩ := recurrent_lower_contact hd E l M hγ
  let K := NearMaxSequence.lapBound d E.ηmin E.ηmax l M
  obtain ⟨C₀, hC₀⟩ := harnackQuadratic d hd (1 / 2) (by norm_num) (by norm_num) K
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hHarn : ∀ (R : ℝ) (f : Site d → ℝ), (∀ x, 0 ≤ f x) → f 0 = 0 →
      (∀ x ∈ ballZ0 R, |lapR f x| ≤ K) → ∀ x ∈ ballZ0 (1 / 2 * R), f x ≤ C * ‖toE x‖ ^ 2 := by
    intro R f hf hf0 hl x hx
    exact (hC₀ R f hf hf0 hl x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  let a := c * muRecurrentBar E l M
  have ha : 0 < a := mul_pos hc hα
  have hden : 0 < 32 * (C + 1) := by positivity
  obtain ⟨β, hβ, hβsmall⟩ := exists_between (show (0 : ℝ) < min (1 / 8) (a / (32 * (C + 1))) from
    lt_min (by norm_num) (div_pos ha hden))
  have hβ8 : β < 1 / 8 := lt_of_lt_of_le hβsmall (min_le_left _ _)
  have hβa : β < a / (32 * (C + 1)) := lt_of_lt_of_le hβsmall (min_le_right _ _)
  have hβ1 : β < 1 := by linarith
  have hβsq : β ^ 2 ≤ β := by nlinarith
  have hβbound : 32 * (C + 1) * β < a := by simpa [mul_comm] using (lt_div_iff₀ hden).1 hβa
  have hsmall : 4 * C * β ^ 2 < a / 4 := by
    have := mul_le_mul_of_nonneg_left hβsq hC
    nlinarith [mul_nonneg hC hβ.le]
  let δ := a / 4 - 4 * C * β ^ 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let B : ℝ := 3 * ((d : ℝ) + 1) + 2
  obtain ⟨N, hN⟩ := exists_nat_gt (B / δ)
  have hevent : ∀ᵐ η ∂E.P, (∃ r : ℕ → Site d → ℤ,
      (∀ n : ℕ, IsRecurrentFunction η (ballZ0 (n : ℝ)) (r n)) ∧
      ∀ᶠ n : ℕ in atTop, ∃ x ∈ ballZ0 (d := d) (β * n),
        ∃ p ∈ supGrad (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) x (ballZ0 (n : ℝ)),
          ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
            ((r n y : ℝ) - (qlZ l y + qMZ M y)) ≤
              ((r n x : ℝ) - (qlZ l x + qMZ M x)) + inner ℝ p (toE y - toE x) -
                a * ((1 - β) * n) * ‖toE y - toE x‖) ∧
      (∃ s : ℕ → Site d → ℤ, (∀ n : ℕ, IsRecurrentFunction η (ballZ0 (n : ℝ)) (s n)) ∧
      ∀ᶠ n : ℕ in atTop, ∃ z ∈ ballZ0 (d := d) (β * n),
        ∃ t ∈ subGrad (fun x => (s n x : ℝ) - (qlZ l x + qMZ M x)) z (ballZ0 (n : ℝ)), True) ∧
      ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := by
    filter_upwards [hu, hv, ae_all_iff.2 E.bounded] with η hu hv hη
    obtain ⟨r, hr, hrc⟩ := hu
    obtain ⟨s, hs, hsc⟩ := hv
    refine ⟨⟨r, hr, hrc β hβ hβ1⟩, ⟨s, hs, ?_⟩, hη⟩
    filter_upwards [hsc β hβ hβ1] with n hn
    obtain ⟨z, hz, t, ht, _⟩ := hn
    exact ⟨z, hz, t, ht, trivial⟩
  obtain ⟨η, ⟨r, hr, hrc⟩, ⟨s, hs, hsc⟩, hη⟩ := hevent.exists
  have hn_event := (hrc.and hsc).and (eventually_ge_atTop (max N 1))
  obtain ⟨n, ⟨⟨⟨x, hx, p, _, hbend⟩, ⟨z, hz, t, ht, _⟩⟩, hn⟩⟩ := hn_event.exists
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hnlarge : B < δ * n := by
    have := (div_lt_iff₀ hδ).1 (hN.trans_le hNn)
    linarith
  have hlap : ∀ y ∈ ballZ0 (d := d) (n : ℝ),
      |lapR (fun z => (s n z : ℝ) - (qlZ l z + qMZ M z)) y| ≤ K := by
    intro y hy
    exact recurrent_abs_lapR_le (by omega) hη (hs n) l M hy
  have hfin := recurrent_separation_finite hHarn hC hβ.le hβ8 hnpos ha.le (hr n) (hs n)
    (fun z => qlZ l z + qMZ M z) hlap hx hz p t hbend ht
  have hcoef : ((d : ℝ) + 1) * (2 * n + 1) + 2 ≤ B * n := by
    dsimp [B]
    have : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have hnorm : δ * (n : ℝ) ^ 2 ≤ B * n := by
    dsimp [δ]
    nlinarith [hfin, hcoef]
  have := mul_lt_mul_of_pos_right hnlarge (show (0 : ℝ) < n by linarith)
  nlinarith

end RandomSandpile

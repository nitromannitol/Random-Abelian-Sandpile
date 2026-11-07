import RandomSandpile.Proofs.Sec9.RecurrentNearSequence
import RandomSandpile.Proofs.Sec9.RecurrentMassUniform
import RandomSandpile.Proofs.Sec6.StrictConcavityFinal

/-! Bending of recurrent upper near-maximizers. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal Topology Matrix
noncomputable section
namespace RandomSandpile
open NearMaxSequence
variable {d : ℕ}

/-- Positive recurrent upper density produces recurrent near-maximizers with
strict concave bending at all interior supergradient contact points. -/
theorem recurrent_upper_bending (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hα : 0 < muRecurrentBar E l M) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ η ∂E.P, ∃ r : ℕ → Site d → ℤ,
      (∀ n : ℕ, IsRecurrentFunction η (ballZ0 (n : ℝ)) (r n)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((muRecurrentBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (supGradSet (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) (ballZ0 (n : ℝ)))) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ᶠ n : ℕ in atTop,
        ∀ x₀ ∈ ballZ0 (β * n),
          ∀ p₀ ∈ supGrad (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) x₀ (ballZ0 (n : ℝ)),
          ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
            ((r n y : ℝ) - (qlZ l y + qMZ M y)) ≤
              ((r n x₀ : ℝ) - (qlZ l x₀ + qMZ M x₀)) + inner ℝ p₀ (toE y - toE x₀) -
                c * muRecurrentBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖ := by
  haveI : NeZero d := ⟨by omega⟩
  let K := NearMaxSequence.lapBound d E.ηmin E.ηmax l M
  have hcore : AlmostMaximalBendingStmt :=
    almostMaximalBending_of_limit (rescaledEnvelopeLimit_of_steps envelopeCompactness limitUniformConcavity)
  obtain ⟨c, hc, hbend⟩ := hcore d hd K (NearMaxSequence.lapBound_nonneg d E.ηmin E.ηmax l M)
  refine ⟨c, hc, ?_⟩
  filter_upwards [recurrent_upper_nearMax_sequence hd E l M,
    recurrent_subdomain_mass_upper_all hd E l M] with η hseq hmass
  obtain ⟨r, hr, hlap, hnear⟩ := hseq
  let w : ℕ → Site d → ℝ := fun n x => (r n x : ℝ) - (qlZ l x + qMZ M x)
  have hballs : ∀ (z : Rd d) (ρ : ℝ), 0 < ρ → ball z ρ ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, volume (⋃ x ∈ discretize (ball z ρ) n, supGrad (w n) x (ballZ0 (n : ℝ))) ≤
        ENNReal.ofReal ((muRecurrentBar E l M * ρ ^ d + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
    intro z ρ hρ hsub ε hε
    have hvol : volume.real (ball z ρ) = ρ ^ d * volume.real (ball (0 : Rd d) 1) := by
      rw [measureReal_def, Measure.addHaar_ball _ _ hρ.le, finrank_euclideanSpace_fin,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hρ.le d), measureReal_def]
    have h := hmass (ball z ρ) (StrictConcavityBall.isLipschitzDomain_ball z hρ) hsub
      measurableSet_ball (by rw [frontier_ball z hρ.ne']; exact Measure.addHaar_sphere _ _ _)
      (ρ ^ d) (pow_nonneg hρ.le d) hvol ε hε
    exact h.mono fun n hn => hn (w n) ⟨r n, hr n, rfl⟩
  have hann : ∀ (z : Rd d) (ρ : ℝ), 0 < ρ → closedBall z ρ ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        volume (⋃ x ∈ discretize (ball (0 : Rd d) 1 \ closedBall z ρ) n, supGrad (w n) x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((muRecurrentBar E l M * (1 - ρ ^ d) + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
    intro z ρ hρ hsub ε hε
    have hvol := NearMaxSequence.volume_real_ball_sdiff_closedBall z hρ.le hsub
    have hθ : 0 ≤ 1 - ρ ^ d := by
      have hV : 0 < volume.real (ball (0 : Rd d) 1) :=
        ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
      have := measureReal_nonneg (μ := volume) (s := ball (0 : Rd d) 1 \ closedBall z ρ)
      nlinarith
    have h := hmass (ball (0 : Rd d) 1 \ closedBall z ρ)
      (MuLipschitzAnnulusOff.isLipschitzDomain_ball_sdiff_closedBall hd z hρ hsub)
      Set.sdiff_subset (isOpen_ball.sdiff isClosed_closedBall).measurableSet
      (NearMaxSequence.volume_frontier_ball_sdiff_closedBall (by omega) z ρ)
      (1 - ρ ^ d) hθ hvol ε hε
    exact h.mono fun n hn => hn (w n) ⟨r n, hr n, rfl⟩
  exact ⟨r, hr, hnear, hbend _ hα w hlap hnear hballs hann⟩


/-- Positive recurrent lower density produces recurrent near-maximizers with
strict convex bending at all interior supergradient contact points. -/
theorem recurrent_lower_bending (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hα : 0 < muStarRecurrentBar E l M) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ η ∂E.P, ∃ r : ℕ → Site d → ℤ,
      (∀ n : ℕ, IsRecurrentFunction η (ballZ0 (n : ℝ)) (r n)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((muStarRecurrentBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (subGradSet (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) (ballZ0 (n : ℝ)))) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ᶠ n : ℕ in atTop,
        ∀ x₀ ∈ ballZ0 (β * n),
          ∀ p₀ ∈ subGrad (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) x₀ (ballZ0 (n : ℝ)),
          ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
            ((r n y : ℝ) - (qlZ l y + qMZ M y)) ≥
              ((r n x₀ : ℝ) - (qlZ l x₀ + qMZ M x₀)) + inner ℝ p₀ (toE y - toE x₀) +
                c * muStarRecurrentBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖ := by
  haveI : NeZero d := ⟨by omega⟩
  let K := NearMaxSequence.lapBound d E.ηmin E.ηmax l M
  have hcore : AlmostMaximalBendingStmt :=
    almostMaximalBending_of_limit (rescaledEnvelopeLimit_of_steps envelopeCompactness limitUniformConcavity)
  obtain ⟨c, hc, hbend⟩ := hcore d hd K (NearMaxSequence.lapBound_nonneg d E.ηmin E.ηmax l M)
  refine ⟨c, hc, ?_⟩
  filter_upwards [recurrent_lower_nearMax_sequence hd E l M,
    recurrent_subdomain_mass_lower_all hd E l M] with η hseq hmass
  obtain ⟨r, hr, hlap, hnear⟩ := hseq
  let w : ℕ → Site d → ℝ := fun n x => (r n x : ℝ) - (qlZ l x + qMZ M x)
  have hballs : ∀ (z : Rd d) (ρ : ℝ), 0 < ρ → ball z ρ ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, volume (⋃ x ∈ discretize (ball z ρ) n, subGrad (w n) x (ballZ0 (n : ℝ))) ≤
        ENNReal.ofReal ((muStarRecurrentBar E l M * ρ ^ d + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
    intro z ρ hρ hsub ε hε
    have hvol : volume.real (ball z ρ) = ρ ^ d * volume.real (ball (0 : Rd d) 1) := by
      rw [measureReal_def, Measure.addHaar_ball _ _ hρ.le, finrank_euclideanSpace_fin,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hρ.le d), measureReal_def]
    have h := hmass (ball z ρ) (StrictConcavityBall.isLipschitzDomain_ball z hρ) hsub
      measurableSet_ball (by rw [frontier_ball z hρ.ne']; exact Measure.addHaar_sphere _ _ _)
      (ρ ^ d) (pow_nonneg hρ.le d) hvol ε hε
    exact h.mono fun n hn => hn (w n) ⟨r n, hr n, rfl⟩
  have hann : ∀ (z : Rd d) (ρ : ℝ), 0 < ρ → closedBall z ρ ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        volume (⋃ x ∈ discretize (ball (0 : Rd d) 1 \ closedBall z ρ) n, subGrad (w n) x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((muStarRecurrentBar E l M * (1 - ρ ^ d) + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
    intro z ρ hρ hsub ε hε
    have hvol := NearMaxSequence.volume_real_ball_sdiff_closedBall z hρ.le hsub
    have hθ : 0 ≤ 1 - ρ ^ d := by
      have hV : 0 < volume.real (ball (0 : Rd d) 1) :=
        ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
      have := measureReal_nonneg (μ := volume) (s := ball (0 : Rd d) 1 \ closedBall z ρ)
      nlinarith
    have h := hmass (ball (0 : Rd d) 1 \ closedBall z ρ)
      (MuLipschitzAnnulusOff.isLipschitzDomain_ball_sdiff_closedBall hd z hρ hsub)
      Set.sdiff_subset (isOpen_ball.sdiff isClosed_closedBall).measurableSet
      (NearMaxSequence.volume_frontier_ball_sdiff_closedBall (by omega) z ρ)
      (1 - ρ ^ d) hθ hvol ε hε
    exact h.mono fun n hn => hn (w n) ⟨r n, hr n, rfl⟩
  let v : ℕ → Site d → ℝ := fun n y => -w n y
  have hb := hbend _ hα v
    (fun n x hx => by simp only [v, NearMaxBending.lapR_neg, abs_neg]; exact hlap n x hx)
    (fun ε hε => (hnear ε hε).mono fun n h => by
      simp only [v, supGradSet]; rw [NearMaxBending.volume_biUnion_supGrad_neg]; exact h)
    (fun z ρ hρ hsub ε hε => (hballs z ρ hρ hsub ε hε).mono fun n h => by
      simp only [v]; rw [NearMaxBending.volume_biUnion_supGrad_neg]; exact h)
    (fun z ρ hρ hsub ε hε => (hann z ρ hρ hsub ε hε).mono fun n h => by
      simp only [v]; rw [NearMaxBending.volume_biUnion_supGrad_neg]; exact h)
  refine ⟨r, hr, hnear, fun β hβ0 hβ1 => (hb β hβ0 hβ1).mono ?_⟩
  intro n hn x₀ hx₀ p₀ hp₀ y hy
  have hp : -p₀ ∈ supGrad (v n) x₀ (ballZ0 (n : ℝ)) := by
    rw [NearMaxBending.mem_supGrad_neg_iff, neg_neg]
    exact hp₀
  have h := hn x₀ hx₀ (-p₀) hp y hy
  simp only [v, inner_neg_left] at h
  dsimp [w] at h
  linarith

end RandomSandpile

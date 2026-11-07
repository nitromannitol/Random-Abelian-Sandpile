import RandomSandpile.Proofs.Sec9.RecurrentViscosityPositive

/-! # Interior minimum principle away from the source -/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

open SingleSourceMin OpenMaxPrinciple

/-- Source: `RandomSandpile/Proofs/Sec9/SingleSourceMinPrinciple.lean`,
`ssInteriorMinPrinciple_of_compactness`, adapted to an arbitrary finite
single-source odometer and an individually continuous subsequential limit. -/
theorem recurrent_interior_min_of_vanishing {d : ℕ} (hd : 2 ≤ d)
    {η : Site d → ℤ} (hfinite : SingleSourceFinite η) {u : Rd d → ℝ}
    {nk : ℕ → ℕ} (hnk : StrictMono nk)
    (hconvu : TendstoLocallyUniformlyOn
      (fun k => rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k)) u atTop
      {x : Rd d | x ≠ 0})
    (hucont : ContinuousOn u {x : Rd d | x ≠ 0})
    (a p : Rd d) (r : ℝ) (hr : 0 < r)
    (hball : closedBall a r ⊆ {x : Rd d | x ≠ 0})
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsSymm)
    (hfinμ : ∀ n, muStar (discretize (ball a r) n) η l M ≠ ⊤)
    (hlimμ : Tendsto (fun n : ℕ => (muStar (discretize (ball a r) n) η l M).toReal /
      ((discretize (ball a r) n).ncard : ℝ)) atTop (𝓝 0))
    {x : Rd d} (hx : x ∈ closedBall a r) :
    ∃ y ∈ sphere a r,
      u y - (inner ℝ p (y - a) + qM M (y - a) + ql l (y - a)) ≤
      u x - (inner ℝ p (x - a) + qM M (x - a) + ql l (x - a)) := by
  have hd1 : 1 ≤ d := by omega
  have hopen : IsOpen {x : Rd d | x ≠ 0} := isOpen_ne
  by_cases hxs : x ∈ sphere a r
  · exact ⟨x, hxs, le_rfl⟩
  have hxb : x ∈ ball a r := by
    rw [mem_closedBall] at hx; rw [mem_sphere] at hxs; rw [mem_ball]; exact lt_of_le_of_ne hx hxs
  have hra : r < ‖a‖ := by
    by_contra hcon
    have h0 : (0 : Rd d) ∈ closedBall a r := by
      rw [mem_closedBall, dist_comm, dist_zero_right]; linarith
    exact hball h0 rfl
  set r₂ := (r + ‖a‖) / 2 with hr₂
  set r₁ := (r + r₂) / 2 with hr₁
  have hball₂ : closedBall a r₂ ⊆ {x : Rd d | x ≠ 0} := by
    intro y hy hy0
    rw [hy0, mem_closedBall, dist_comm, dist_zero_right] at hy
    linarith
  have hFunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).1 hconvu _ hball₂
    (isCompact_closedBall a r₂)
  have hdpos : (0 : ℝ) < 1 / (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    positivity
  set hk : ℕ → ℝ := fun k => (nk k : ℝ) ^ (1 / (d : ℝ)) with hhk_def
  set mk : ℕ → ℕ := fun k => ⌊hk k⌋₊ with hmk_def
  have hhk : Tendsto hk atTop atTop :=
    (tendsto_rpow_atTop hdpos).comp (tendsto_natCast_atTop_atTop.comp hnk.tendsto_atTop)
  have hmk : Tendsto mk atTop atTop := tendsto_nat_floor_atTop.comp hhk
  have ht : Tendsto (fun k => (mk k : ℝ) / hk k) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hhk
  have hc : Tendsto (fun k => (hk k / mk k) ^ 2) atTop (𝓝 1) := by
    have h := (ht.inv₀ one_ne_zero).pow 2
    simp only [inv_one, one_pow] at h
    exact h.congr fun k => by rw [inv_div]
  have hG : TendstoUniformlyOn (fun k => rescaleOdo (singleSourceOdometer η (nk k)) (mk k)) u
      atTop (closedBall a r₁) := by
    have h := tendstoUniformlyOn_rescale (by linarith : r₁ < r₂) (hucont.mono hball₂) hFunif hc ht
    refine h.congr ?_
    filter_upwards [hmk.eventually (eventually_ge_atTop 1),
      hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk1 hn1 y _
    exact (rescaleOdo_eq _ (by omega) (by omega) y).symm
  have hV : Tendsto (fun k => (muStar (discretize (ball a r) (mk k)) η l M).toReal /
      (mk k : ℝ) ^ d) atTop (𝓝 0) :=
    (div_pow_tendsto_zero hd1 hr (fun A => muStar A η l M) (muStar_empty η l M) hlimμ
      strictMono_id).comp hmk
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (-1 : ℝ) *
      ((singleSourceOdometer η (nk k) z : ℝ) - (mk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a))
          ((mk k : ℝ)⁻¹ • toE z))) (discretize (ball a r) (mk k))) ≤
        muStar (discretize (ball a r) (mk k)) η l M ∧
      muStar (discretize (ball a r) (mk k)) η l M ≠ ⊤ := by
    filter_upwards [hmk.eventually (eventually_ge_atTop 1)] with k hk1
    have hn0 : (mk k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨c, c0, hcq⟩ := rescaled_quad_affine hM p a l hn0
    have hne := hfinite (nk k)
    have hst := (isLeast_singleSourceOdometer hne).1
    have hres := stabilizingRestrict d _ Set.univ (discretize (ball a r) (mk k)) _
      (Set.subset_univ _) hst
    have h0B : ∀ z ∈ discretize (ball a r) (mk k), z ≠ 0 := by
      intro z hz hz0
      rw [mem_discretize_iff' (by omega)] at hz
      rw [hz0, ABP.toE_zero, smul_zero] at hz
      exact hball (ball_subset_closedBall hz) rfl
    have hres' := FreeMaxPrinciple.stabilizing_congr (η' := η) (fun z hz => by
      simp [LatticeProb.Sandpile.dirac, h0B z hz]) hres
    refine ⟨volume_le_muStar_of_restrict hres' l M c c0 (fun z _ => ?_), hfinμ (mk k)⟩
    have h1 := hcq (toE z)
    simp only [qlZ, qMZ]
    rw [h1]
    ring
  obtain ⟨y, hy, h⟩ := principle_generic_on hd1 (σ := -1) (continuous_quadratic p a M l) hr
    (by linarith : r < r₁)
    (hucont.mono ((closedBall_subset_closedBall (by linarith : r₁ ≤ r₂)).trans hball₂))
    hmk hG hvol hV hxb
  refine ⟨y, hy, ?_⟩
  simp only [neg_mul, one_mul, neg_le_neg_iff] at h
  exact h

end RandomSandpile

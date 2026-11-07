import RandomSandpile.Proofs.Sec9.RecurrentScaleGeometry
import RandomSandpile.Proofs.Sec9.SingleSourceMinPrinciple
import RandomSandpile.Proofs.Sec9.RecurrentConvergence

/-! # Interior maximum principle on the positive set -/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

open SingleSourceMin OpenMaxPrinciple

/-- The recurrent upper measure of the empty lattice set vanishes. -/
theorem muRecurrent_empty {d : ℕ} (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : muRecurrent ∅ η l M = 0 := by
  simp [muRecurrent, supGradSet]

/-- Vanishing of the effective recurrent measure implies sub-volume growth on
every ball, simultaneously on a full-measure event. -/
theorem ae_recurrent_ball_mass_vanishing {d : ℕ} (hd : 2 ≤ d)
    (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (hμ : muRecurrentBar E l M = 0) :
    ∀ᵐ η ∂E.P, ∀ (a : Rd d) (r : ℝ), 0 < r →
      (∀ n, muRecurrent (discretize (ball a r) n) η l M ≠ ⊤) ∧
      Tendsto (fun n : ℕ => (muRecurrent (discretize (ball a r) n) η l M).toReal /
        (n : ℝ) ^ d) atTop (𝓝 0) := by
  filter_upwards [(muRecurrent_convergence hd E l M).2.2] with η hη
  intro a r hr
  obtain ⟨hfin, hlim⟩ := hη (ball a r) (StrictConcavityBall.isLipschitzDomain_ball a hr)
  rw [hμ] at hlim
  exact ⟨hfin, div_pow_tendsto_zero (by omega) hr (fun A => muRecurrent A η l M)
    (muRecurrent_empty η l M) hlim strictMono_id⟩

/-- Vanishing recurrent upper gradient mass yields the interior maximum principle
on a ball compactly contained in the positive set. -/
theorem recurrent_interior_max_of_vanishing {d : ℕ} (hd : 2 ≤ d)
    {η : Site d → ℤ} (hfinite : SingleSourceFinite η) {u : Rd d → ℝ}
    {nk : ℕ → ℕ} (hnk : StrictMono nk)
    (hconv : TendstoLocallyUniformlyOn
      (fun k => rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k)) u atTop
      {x : Rd d | x ≠ 0})
    {a p : Rd d} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hK0 : closedBall a R ⊆ {x : Rd d | x ≠ 0})
    (hcont : ContinuousOn u (closedBall a R))
    (hpos : ∀ x ∈ closedBall a R, 0 < u x)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsSymm)
    (hfinμ : ∀ n, muRecurrent (discretize (ball a r) n) η l M ≠ ⊤)
    (hlimμ : Tendsto (fun n : ℕ => (muRecurrent (discretize (ball a r) n) η l M).toReal /
      (n : ℝ) ^ d) atTop (𝓝 0))
    {x : Rd d} (hx : x ∈ closedBall a r) :
    ∃ y ∈ sphere a r,
      u x - (inner ℝ p (x - a) + qM M (x - a) + ql l (x - a)) ≤
      u y - (inner ℝ p (y - a) + qM M (y - a) + ql l (y - a)) := by
  have hd1 : 1 ≤ d := by omega
  by_cases hxs : x ∈ sphere a r
  · exact ⟨x, hxs, le_rfl⟩
  have hxb : x ∈ ball a r := by
    rw [mem_closedBall] at hx
    rw [mem_sphere] at hxs
    rw [mem_ball]
    exact lt_of_le_of_ne hx hxs
  set r₁ := (r + R) / 2 with hr₁
  have hFunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ne).1 hconv _ hK0
    (isCompact_closedBall a R)
  have hdpos : (0 : ℝ) < 1 / (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    positivity
  set hk : ℕ → ℝ := fun k => (nk k : ℝ) ^ (1 / (d : ℝ))
  set mk : ℕ → ℕ := fun k => ⌊hk k⌋₊
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
    have h := tendstoUniformlyOn_rescale (by linarith : r₁ < R) hcont hFunif hc ht
    refine h.congr ?_
    filter_upwards [hmk.eventually (eventually_ge_atTop 1),
      hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk1 hn1 y _
    exact (rescaleOdo_eq _ (by omega) (by omega) y).symm
  have hrec := eventually_recurrent_discretize_ball (by omega) hfinite hnk hconv hrR
    hK0 hcont hpos (hmk.eventually (eventually_ge_atTop 1)) ht
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (1 : ℝ) *
      ((singleSourceOdometer η (nk k) z : ℝ) - (mk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a))
          ((mk k : ℝ)⁻¹ • toE z))) (discretize (ball a r) (mk k))) ≤
        muRecurrent (discretize (ball a r) (mk k)) η l M ∧
      muRecurrent (discretize (ball a r) (mk k)) η l M ≠ ⊤ := by
    filter_upwards [hmk.eventually (eventually_ge_atTop 1), hrec] with k hk1 hrk
    have hn0 : (mk k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨c, c0, hcq⟩ := rescaled_quad_affine hM p a l hn0
    refine ⟨volume_le_muRecurrent subset_rfl hrk l M (-c) (-c0) (fun z hz => ?_), hfinμ (mk k)⟩
    have h1 := hcq (toE z)
    simp only [one_mul, qlZ, qMZ, inner_neg_left]
    rw [h1]
    ring
  obtain ⟨y, hy, h⟩ := principle_generic_on hd1 (σ := 1) (continuous_quadratic p a M l) hr
    (by linarith : r < r₁)
    (hcont.mono (closedBall_subset_closedBall (by linarith : r₁ ≤ R)))
    hmk hG hvol (hlimμ.comp hmk) hxb
  exact ⟨y, hy, by simpa using h⟩

end RandomSandpile

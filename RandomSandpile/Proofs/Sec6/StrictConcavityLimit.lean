import RandomSandpile.Proofs.Sec6.StrictConcavityCompact

/-! # Lemma 6.2', step L2-0: basic properties of limits of rescaled envelopes

`rescaled_eventually_bounds` restates the uniform bounds from the proof of `envelopeCompactness`
for an arbitrary strictly increasing sequence of radii. Along such a sequence, for every `δ < 1`
and all large `k`, the rescaled envelope satisfies four properties:
* it is bounded by `M` on `B̄_δ`;
* it is `L`-Lipschitz on `B̄_δ`;
* it is concave on a larger ball `B_δ'`;
* it is `≤ 0` on `B_δ'`.

`limitBasic : LimitBasicStmt` follows: the limit is concave and `≤ 0`, and since every
`V_n(x₀/n) = 0`, the Lipschitz bounds give `V(z) = 0`. -/

open MeasureTheory LatticeProb Filter Metric
open scoped Topology

namespace RandomSandpile

namespace LimitBasic

open MuLipschitz EnvelopeCompactness

/-- Eventual uniform bounds, Lipschitz bounds, concavity and nonpositivity of the rescaled envelopes
along contact data. -/
theorem rescaled_eventually_bounds {d : ℕ} (hd : 2 ≤ d) {K : ℝ} (hK : 0 ≤ K)
    {w : ℕ → Site d → ℝ} (hlap : ∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℕ → ℕ} (hm : StrictMono m) {x₀ : ℕ → Site d}
    {p : ℕ → Rd d} (hx₀ : ∀ k, x₀ k ∈ ballZ0 (β * m k))
    (hp : ∀ k, p k ∈ supGrad (w (m k)) (x₀ k) (ballZ0 (m k : ℝ))) (δ : ℝ) (hδ : δ < 1) :
    ∃ (M L δ' : ℝ) (k₀ : ℕ), δ < δ' ∧ δ' < 1 ∧ ∀ k, k₀ ≤ k →
      (∀ X ∈ closedBall (0 : Rd d) δ,
        |rescaledEnvelope (w (m k)) (m k) (x₀ k) (p k) X| ≤ M) ∧
      LipschitzOnWith L.toNNReal (rescaledEnvelope (w (m k)) (m k) (x₀ k) (p k))
        (closedBall (0 : Rd d) δ) ∧
      ConcaveOn ℝ (ball (0 : Rd d) δ') (rescaledEnvelope (w (m k)) (m k) (x₀ k) (p k)) ∧
      ∀ X ∈ ball (0 : Rd d) δ', rescaledEnvelope (w (m k)) (m k) (x₀ k) (p k) X ≤ 0 := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ρ, hρ, hcomb⟩ := localConvexComb d hd1
  set F : ℕ → Rd d → ℝ := fun k => rescaledEnvelope (w (m k)) (m k) (x₀ k) (p k)
  set δ₁ := max δ β
  have hδ₁ : δ₁ < 1 := max_lt hδ hβ1
  set δ₂ := (δ₁ + 1) / 2
  set δ₃ := (δ₂ + 1) / 2
  set δ₄ := (δ₃ + 1) / 2
  have hδ₂1 : δ₂ < 1 := by simp only [δ₂]; linarith
  have hδ₃1 : δ₃ < 1 := by simp only [δ₃]; linarith
  have hβδ₄ : β < δ₄ := by
    have := le_max_right δ β; simp only [δ₄, δ₃, δ₂]; linarith
  obtain ⟨C, hC0, n₀, hH⟩ := StrictConcavityHarnack.harnack_chain hd1 hβ0 hβδ₄
    (by simp only [δ₄, δ₃, δ₂]; linarith)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (ρ / (δ₄ - δ₃))
  refine ⟨C * K, 2 * (C * K) / (δ₃ - δ₂), δ₃, max n₀ (N₁ + 1),
    (by have h : δ ≤ δ₁ := le_max_left δ β; simp only [δ₃, δ₂]; linarith), hδ₃1, fun k hk => ?_⟩
  set n := m k
  have hkn : max n₀ (N₁ + 1) ≤ n := hk.trans (hm.id_le k)
  have hn1 : 1 ≤ n := le_trans (by omega) hkn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hρn : ρ ≤ (δ₄ - δ₃) * n := by
    have h1 : (N₁ : ℝ) + 1 ≤ n := by exact_mod_cast (le_max_right _ _).trans hkn
    have h2 := (div_lt_iff₀ (by simp only [δ₄]; linarith : (0 : ℝ) < δ₄ - δ₃)).1 hN₁
    nlinarith
  -- the gap `f` and the Harnack bound
  set f : Site d → ℝ := fun y =>
    w n (x₀ k) + inner ℝ (p k) (toE y - toE (x₀ k)) - w n y
  have hf0 : ∀ y ∈ dClosure (ballZ0 (d := d) (n : ℝ)), 0 ≤ f y := fun y hy => by
    have h : w n y ≤ w n (x₀ k) + inner ℝ (p k) (toE y - toE (x₀ k)) :=
      hp k y hy
    simp only [f]; linarith
  have hflap : ∀ y ∈ ballZ0 (d := d) (n : ℝ), |lapR f y| ≤ K := fun y hy => by
    have : lapR f y = -lapR (w n) y := by
      simp only [f]
      rw [lapR_sub', lapR_affine]; ring
    rw [this, abs_neg]; exact hlap n y hy
  have hfx₀ : f (x₀ k) = 0 := by simp only [f, sub_self, inner_zero_right]; ring
  have hHarn := hH n ((le_max_left _ _).trans hkn) K f hK hf0 hflap (x₀ k) (hx₀ k) hfx₀
  have hx₀c : x₀ k ∈ dClosure (ballZ0 (d := d) (n : ℝ)) := by
    refine Or.inl (mem_ballZ0.2 ?_)
    have := mem_ballZ0.1 (hx₀ k); nlinarith
  -- convex combinations for points of `n B_{δ₃}`
  have hcomb' : ∀ X ∈ ball (0 : Rd d) δ₃, ∃ (ι : Type) (_ : Fintype ι) (zz : ι → Site d)
      (lam : ι → ℝ), (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧
        ∑ i, lam i • toE (zz i) = (n : ℝ) • X ∧ ∀ i, zz i ∈ ballZ0 (d := d) (δ₄ * n) := by
    intro X hX
    obtain ⟨ι, hι, zz, lam, h0, h1, hs, hd⟩ := hcomb ((n : ℝ) • X)
    refine ⟨ι, hι, zz, lam, h0, h1, hs, fun i => mem_ballZ0.2 ?_⟩
    have hXn : ‖(n : ℝ) • X‖ < δ₃ * n := by
      rw [norm_smul, Real.norm_natCast, mul_comm]
      exact mul_lt_mul_of_pos_right (mem_ball_zero_iff.1 hX) hn0
    calc ‖toE (zz i)‖ = ‖(toE (zz i) - (n : ℝ) • X) + (n : ℝ) • X‖ := by rw [sub_add_cancel]
      _ ≤ ‖toE (zz i) - (n : ℝ) • X‖ + ‖(n : ℝ) • X‖ := norm_add_le _ _
      _ < δ₄ * n := by linarith [hd i]
  have hsubB : ∀ y ∈ ballZ0 (d := d) (δ₄ * n), y ∈ dClosure (ballZ0 (d := d) (n : ℝ)) :=
    fun y hy => Or.inl (mem_ballZ0.2 (by
      have := mem_ballZ0.1 hy
      have : δ₄ * n < n := by simp only [δ₄, δ₃, δ₂]; nlinarith
      linarith))
  have hhull : ∀ X ∈ ball (0 : Rd d) δ₃,
      (n : ℝ) • X ∈ convexHull ℝ (toE '' dClosure (ballZ0 (d := d) (n : ℝ))) := by
    intro X hX
    obtain ⟨ι, hι, zz, lam, h0, h1, hs, hz⟩ := hcomb' X hX
    rw [← hs]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => h0 i) h1
      (fun i _ => subset_convexHull ℝ _ ⟨zz i, hsubB _ (hz i), rfl⟩)
  have hbound : ∀ X ∈ ball (0 : Rd d) δ₃, |F k X| ≤ C * K := by
    intro X hX
    obtain ⟨ι, hι, zz, lam, h0, h1, hs, hz⟩ := hcomb' X hX
    have hup := rescaled_le_zero hn1 hx₀c (hp k) (hhull X hX)
    have hlo := rescaled_ge (w := w n) hn1 (fun i => hsubB _ (hz i)) h0 h1 hs
      (B := C * K * (n : ℝ) ^ 2) (fun i => hHarn _ (hz i))
    rw [neg_div, mul_div_assoc, div_self (by positivity), mul_one] at hlo
    rw [abs_le]
    exact ⟨hlo, hup.trans (by positivity)⟩
  have hδle : δ ≤ δ₁ := le_max_left δ β
  have hδδ₃ : δ < δ₃ := by simp only [δ₃, δ₂]; linarith
  have hδδ₂ : δ < δ₂ := by simp only [δ₂]; linarith

  have hconc : ConcaveOn ℝ (ball (0 : Rd d) δ₃) (F k) := concaveOn_rescaled hn1 hhull
  have hlip := hconc.lipschitzOnWith_of_abs_le (ε := δ₃ - δ₂) (by simp only [δ₃]; linarith)
    (M := C * K) (fun a ha => hbound a (mem_ball.2 ha))
  rw [sub_sub_cancel] at hlip
  exact ⟨fun X hX => hbound X (closedBall_subset_ball hδδ₃ hX),
    hlip.mono (closedBall_subset_ball hδδ₂), hconc,
    fun X hX => rescaled_le_zero hn1 hx₀c (hp k) (hhull X hX)⟩

end LimitBasic

open MuLipschitz LimitBasic in
/-- **Step L2-0** (`LimitBasicStmt`): limits of normalized rescaled envelopes are concave on `B_1`,
nonpositive, and vanish at the limit of the rescaled contact points. -/
theorem limitBasic : LimitBasicStmt := by
  intro d hd K hK α hα w hlap hnear hballs hann β hβ0 hβ1 m hm x₀ p hx₀ hp φ V z hφ hz hconv
  set F : ℕ → Rd d → ℝ := fun k =>
    rescaledEnvelope (w (m (φ k))) (m (φ k)) (x₀ (φ k)) (p (φ k))
  have hB := fun δ hδ => rescaled_eventually_bounds hd hK hlap hβ0 hβ1 (hm.comp hφ)
    (x₀ := x₀ ∘ φ) (p := p ∘ φ) (fun k => hx₀ (φ k)) (fun k => hp (φ k)) δ hδ
  have hpt : ∀ Y ∈ ball (0 : Rd d) 1, Tendsto (fun k => F k Y) atTop (𝓝 (V Y)) := by
    intro Y hY
    exact (hconv ‖Y‖ (mem_ball_zero_iff.1 hY)).tendsto_at (mem_closedBall_zero_iff.2 le_rfl)
  refine ⟨⟨convex_ball _ _, fun X hX Y hY a b ha hb hab => ?_⟩, fun Y hY => ?_, ?_⟩
  · have hδ : max ‖X‖ ‖Y‖ < 1 := max_lt (mem_ball_zero_iff.1 hX) (mem_ball_zero_iff.1 hY)
    obtain ⟨M, L, δ', k₀, hδδ', hδ'1, hk⟩ := hB _ hδ
    have hXb : X ∈ ball (0 : Rd d) δ' :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt (le_max_left _ _) hδδ')
    have hYb : Y ∈ ball (0 : Rd d) δ' :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt (le_max_right _ _) hδδ')
    have hev : ∀ᶠ k in atTop, a • F k X + b • F k Y ≤ F k (a • X + b • Y) :=
      (eventually_ge_atTop k₀).mono fun k hk' => ((hk k hk').2.2.1).2 hXb hYb ha hb hab
    have hmid : a • X + b • Y ∈ ball (0 : Rd d) 1 := (convex_ball (0 : Rd d) 1) hX hY ha hb hab
    exact le_of_tendsto_of_tendsto (((hpt X hX).const_smul a).add ((hpt Y hY).const_smul b))
      (hpt _ hmid) hev
  · obtain ⟨M, L, δ', k₀, hδδ', hδ'1, hk⟩ := hB ‖Y‖ (mem_ball_zero_iff.1 hY)
    exact le_of_tendsto (hpt Y hY) ((eventually_ge_atTop k₀).mono fun k hk' =>
      (hk k hk').2.2.2 Y (mem_ball_zero_iff.2 hδδ'))
  · have hδ : (β + 1) / 2 < 1 := by linarith
    obtain ⟨M, L, δ', k₀, -, -, hk⟩ := hB _ hδ
    have hmpos : ∀ k, (0 : ℝ) < m (φ k) := fun k => by
      have := mem_ballZ0.1 (hx₀ (φ k))
      by_contra h; rw [not_lt] at h
      have : β * (m (φ k) : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ0.le h
      linarith [norm_nonneg (toE (x₀ (φ k)))]
    have hzk : ∀ k, ((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k)) ∈ closedBall (0 : Rd d) ((β + 1) / 2) :=
      fun k => by
        rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_natCast,
          inv_mul_le_iff₀ (hmpos k)]
        have := mem_ballZ0.1 (hx₀ (φ k))
        nlinarith [hmpos k]
    have hFz : ∀ k, F k (((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k))) = 0 := fun k => by
      have hx₀c : x₀ (φ k) ∈ dClosure (ballZ0 (d := d) (m (φ k) : ℝ)) := by
        refine Or.inl (mem_ballZ0.2 ?_)
        have := mem_ballZ0.1 (hx₀ (φ k)); nlinarith [hmpos k]
      simp only [F, rescaledEnvelope]
      rw [smul_smul, mul_inv_cancel₀ (hmpos k).ne', one_smul, sub_self, inner_zero_right,
        concaveEnvelopeOn_eq_of_mem_supGrad (ballZ0_finite _) hx₀c (hp (φ k))]
      simp
    have hz' : z ∈ closedBall (0 : Rd d) ((β + 1) / 2) :=
      isClosed_closedBall.mem_of_tendsto hz (Eventually.of_forall hzk)
    have hlim1 : Tendsto (fun k => F k z) atTop (𝓝 (V z)) := (hconv _ hδ).tendsto_at hz'
    have hdist : Tendsto (fun k => ((L.toNNReal : ℝ)) *
        dist z (((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k)))) atTop (𝓝 0) := by
      have h := (tendsto_iff_dist_tendsto_zero.1 hz).const_mul ((L.toNNReal : ℝ))
      rw [mul_zero] at h
      exact h.congr fun k => by rw [dist_comm]
    have hlim2 : Tendsto (fun k => F k z) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ((eventually_ge_atTop k₀).mono fun k hk' => ?_) hdist
      have := ((hk k hk').2.1).dist_le_mul z hz' _ (hzk k)
      change dist (F k z) (F k (((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k)))) ≤ _ at this
      rw [hFz k, dist_zero_right] at this
      exact this
    exact tendsto_nhds_unique hlim1 hlim2

end RandomSandpile

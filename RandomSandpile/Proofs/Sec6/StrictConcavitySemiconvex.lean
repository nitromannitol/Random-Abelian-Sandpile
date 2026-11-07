import RandomSandpile.Proofs.Sec6.StrictConcavitySlope
import RandomSandpile.Proofs.Sec5.HarnackQuadratic

/-! # Lemma 6.2', step L2-A: the `C^{1,1}` bound for limits of rescaled envelopes

`limitSemiconvex : LimitSemiconvexStmt`, with `Λ = max C 0`, where `C = C(d, 1/2, K)` is the constant
of Proposition 5.2 (`harnackQuadratic`).
* At a contact point `x` of `w_n` with slope `p'`, the gap `w(x) + p'·(· - x) - w` is nonnegative on
  `B̄_n` and has `|Δ| ≤ K`; Proposition 5.2 bounds it by `C|· - x|²` (`gap_le_quadratic`).
* Rescaled, the envelope is touched from below at `x/n` by the paraboloid of opening `Λ`, up to an
  `O(1/n)` error (`rescaled_lower`, via `rescaled_shift` and convex combinations of lattice points).
* Contact points exist in every closed sub-ball for large `n` (`exists_contact_near`: the slope mass
  there is positive). Taking contact points converging to `X` and a convergent subsequence of their
  rescaled slopes, the limit `V` is touched from below at `X` by a paraboloid of opening `Λ` with
  some slope `q*`; since `q` touches `V` from above at `X`, `q = q*`. -/

open MeasureTheory LatticeProb Filter Metric Module
open scoped Topology ENNReal Pointwise

namespace RandomSandpile

namespace LimitSemiconvex

open MuLipschitz EnvelopeCompactness LimitSlopeMass

variable {d : ℕ}

/-- Proposition 5.2 at a contact point: the gap is at most `C |y - x|²` on `B(x, R/2)` when
`B(x, R) ⊆ B_n`. -/
theorem gap_le_quadratic {w : Site d → ℝ} {K C R : ℝ} {n : ℕ}
    (hHarn : ∀ (R : ℝ) (f : Site d → ℝ), (∀ x, 0 ≤ f x) → f 0 = 0 →
      (∀ x ∈ ballZ0 R, |lapR f x| ≤ K) → ∀ x ∈ ballZ0 (1 / 2 * R), f x ≤ C * ‖toE x‖ ^ 2)
    (hlap : ∀ y ∈ ballZ0 (d := d) (n : ℝ), |lapR w y| ≤ K) {x : Site d} {p' : Rd d}
    (hp' : p' ∈ supGrad w x (ballZ0 (n : ℝ)))
    (hR : ∀ y : Site d, ‖toE y - toE x‖ < R → y ∈ ballZ0 (d := d) (n : ℝ))
    {y : Site d} (hy : ‖toE y - toE x‖ < 1 / 2 * R) :
    w x + inner ℝ p' (toE y - toE x) - w y ≤ C * ‖toE y - toE x‖ ^ 2 := by
  set gap : Site d → ℝ := fun y => w x + inner ℝ p' (toE y - toE x) - w y with hgap
  have hgap0 : ∀ y ∈ dClosure (ballZ0 (d := d) (n : ℝ)), 0 ≤ gap y := fun y hy => by
    have := hp' y hy; simp only [gap]; linarith
  set g : Site d → ℝ := fun z => max (gap (z + x)) 0 with hg
  have hzmem : ∀ z : Site d, z ∈ ballZ0 (d := d) R → z + x ∈ ballZ0 (d := d) (n : ℝ) := by
    intro z hz
    apply hR
    rw [toE_add, add_sub_cancel_right]
    exact mem_ballZ0.1 hz
  have hlapg : ∀ z ∈ ballZ0 (d := d) R, |lapR g z| ≤ K := by
    intro z hz
    have hzx := hzmem z hz
    have heq : lapR g z = lapR (fun z => gap (z + x)) z := by
      simp only [lapR, nbrSum]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        have h1 : 0 ≤ gap (z + unit i + x) := hgap0 _ (by
          rw [add_right_comm]; exact mem_dClosure_of_adj hzx (adj_add_unit _ i))
        have h2 : 0 ≤ gap (z - unit i + x) := hgap0 _ (by
          rw [sub_add_eq_add_sub]; exact mem_dClosure_of_adj hzx (adj_sub_unit _ i))
        simp only [g, max_eq_left h1, max_eq_left h2]
      · simp only [g, max_eq_left (hgap0 _ (mem_dClosure_of_mem hzx))]
    rw [heq, lapR_comp_add]
    have : lapR gap (z + x) = -lapR w (z + x) := by
      simp only [gap]
      rw [lapR_sub', lapR_affine]; ring
    rw [this, abs_neg]; exact hlap _ hzx
  have hg0 : g 0 = 0 := by simp [g, gap]
  have hz : y - x ∈ ballZ0 (d := d) (1 / 2 * R) := by
    rw [mem_ballZ0, toE_sub]; exact hy
  have h := hHarn R g (fun z => le_max_right _ _) hg0 hlapg (y - x) hz
  have hyx : y - x + x = y := sub_add_cancel y x
  simp only [g, hyx] at h
  rw [toE_sub] at h
  exact (le_max_left _ _).trans h

/-- Change of contact datum for the rescaled envelope. -/
theorem rescaled_shift {w : Site d → ℝ} {n : ℕ} (hn : 1 ≤ n) {x₀ x : Site d} {p p' : Rd d}
    (hx : x ∈ dClosure (ballZ0 (d := d) (n : ℝ))) (hp' : p' ∈ supGrad w x (ballZ0 (n : ℝ)))
    (Y : Rd d) :
    rescaledEnvelope w n x₀ p Y = rescaledEnvelope w n x₀ p ((n : ℝ)⁻¹ • toE x) +
      inner ℝ ((n : ℝ)⁻¹ • (p' - p)) (Y - (n : ℝ)⁻¹ • toE x) + rescaledEnvelope w n x p' Y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have heq := concaveEnvelopeOn_eq_of_mem_supGrad (ballZ0_finite (d := d) (n : ℝ)) hx hp'
  unfold rescaledEnvelope
  rw [smul_smul, mul_inv_cancel₀ hn0.ne', one_smul, heq]
  have hv : Y - (n : ℝ)⁻¹ • toE x = (n : ℝ)⁻¹ • ((n : ℝ) • Y - toE x) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hn0.ne', one_smul]
  rw [hv, real_inner_smul_left, real_inner_smul_right, inner_sub_left]
  have h3 : inner ℝ p ((n : ℝ) • Y - toE x₀) =
      inner ℝ p ((n : ℝ) • Y - toE x) + inner ℝ p (toE x - toE x₀) := by
    rw [← inner_add_right]; congr 1; abel
  rw [h3]
  field_simp
  ring

/-- The rescaled envelope is touched from below at a contact point by a paraboloid of opening `Λ`,
up to the error `ρ/n`. -/
theorem rescaled_lower {w : Site d → ℝ} {n : ℕ} (hn : 1 ≤ n) {x₀ x : Site d} {p p' : Rd d}
    (hx : x ∈ dClosure (ballZ0 (d := d) (n : ℝ))) (hp' : p' ∈ supGrad w x (ballZ0 (n : ℝ)))
    {Λ ρ R : ℝ} (hΛ : 0 ≤ Λ)
    (hgap : ∀ y : Site d, ‖toE y - toE x‖ < R → y ∈ ballZ0 (d := d) (n : ℝ) ∧
      w x + inner ℝ p' (toE y - toE x) - w y ≤ Λ * ‖toE y - toE x‖ ^ 2)
    {Y : Rd d} {ι : Type} [Fintype ι] {z : ι → Site d} {lam : ι → ℝ}
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) (hs : ∑ i, lam i • toE (z i) = (n : ℝ) • Y)
    (hdist : ∀ i, ‖toE (z i) - (n : ℝ) • Y‖ ≤ ρ)
    (hY : (n : ℝ) * ‖Y - (n : ℝ)⁻¹ • toE x‖ + ρ < R) :
    rescaledEnvelope w n x₀ p ((n : ℝ)⁻¹ • toE x) +
      inner ℝ ((n : ℝ)⁻¹ • (p' - p)) (Y - (n : ℝ)⁻¹ • toE x) -
      Λ * (‖Y - (n : ℝ)⁻¹ • toE x‖ + ρ / n) ^ 2 ≤ rescaledEnvelope w n x₀ p Y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [rescaled_shift hn hx hp' Y]
  set a := ‖Y - (n : ℝ)⁻¹ • toE x‖ with ha
  have hnY : ‖(n : ℝ) • Y - toE x‖ = (n : ℝ) * a := by
    have : (n : ℝ) • Y - toE x = (n : ℝ) • (Y - (n : ℝ)⁻¹ • toE x) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
    rw [this, norm_smul, Real.norm_of_nonneg hn0.le]
  have hzi : ∀ i, ‖toE (z i) - toE x‖ ≤ (n : ℝ) * a + ρ := by
    intro i
    calc ‖toE (z i) - toE x‖ = ‖(toE (z i) - (n : ℝ) • Y) + ((n : ℝ) • Y - toE x)‖ := by
          congr 1; abel
      _ ≤ ‖toE (z i) - (n : ℝ) • Y‖ + ‖(n : ℝ) • Y - toE x‖ := norm_add_le _ _
      _ ≤ (n : ℝ) * a + ρ := by rw [hnY]; linarith [hdist i]
  have hB : ∀ i, w x + inner ℝ p' (toE (z i) - toE x) - w (z i) ≤ Λ * ((n : ℝ) * a + ρ) ^ 2 := by
    intro i
    have h := (hgap (z i) ((hzi i).trans_lt hY)).2
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hΛ)
    exact pow_le_pow_left₀ (norm_nonneg _) (hzi i) 2
  have hzc : ∀ i, z i ∈ dClosure (ballZ0 (d := d) (n : ℝ)) := fun i =>
    mem_dClosure_of_mem (hgap (z i) ((hzi i).trans_lt hY)).1
  have hge := rescaled_ge (w := w) hn hzc h0 h1 hs hB
  have hval : Λ * ((n : ℝ) * a + ρ) ^ 2 / (n : ℝ) ^ 2 = Λ * (a + ρ / n) ^ 2 := by
    field_simp
  rw [neg_div, hval] at hge
  linarith

/-- Contact points exist in every closed sub-ball `B̄(c, ρ) ⊆ B_1` for large `n`. -/
theorem exists_contact_near (hd : 1 ≤ d) {w : ℕ → Site d → ℝ} {α : ℝ} (hα : 0 < α)
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
        volume (supGradSet (w n) (ballZ0 (n : ℝ))))
    (hann : ∀ (c : Rd d) (ρ : ℝ), 0 < ρ → closedBall c ρ ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        volume (⋃ x ∈ discretize (ball (0 : Rd d) 1 \ closedBall c ρ) n,
            supGrad (w n) x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((α * (1 - ρ ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)))
    {c : Rd d} {ρ : ℝ} (hρ : 0 < ρ) (hK : closedBall c ρ ⊆ ball 0 1) :
    ∀ᶠ n : ℕ in atTop, ∃ x ∈ discretize (closedBall c ρ) n, ∃ p' : Rd d,
      p' ∈ supGrad (w n) x (ballZ0 (n : ℝ)) := by
  have hε : 0 < α * ρ ^ d / 4 := by positivity
  filter_upwards [mass_closedBall_lower hd hnear hann hα.le hρ hK hε, eventually_ge_atTop 1]
    with n h hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (1 : ℝ) ≤ (ballZ0 (d := d) (n : ℝ)).ncard := by
    have h0 : (0 : Site d) ∈ ballZ0 (d := d) (n : ℝ) :=
      mem_ballZ0.2 (by rw [toE_zero, norm_zero]; exact hn0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (ballZ0_finite _)).2 ⟨0, h0⟩).ne'
  have hpos : 0 < volume (⋃ x ∈ discretize (closedBall c ρ) n,
      supGrad (w n) x (ballZ0 (n : ℝ))) := by
    refine lt_of_lt_of_le ?_ h
    rw [ENNReal.ofReal_pos]
    have : 0 < α * ρ ^ d := by positivity
    nlinarith
  by_contra hne
  have hempty : (⋃ x ∈ discretize (closedBall c ρ) n, supGrad (w n) x (ballZ0 (n : ℝ))) = ∅ := by
    ext q
    simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, hx, hq⟩
    exact hne ⟨x, hx, q, hq⟩
  rw [hempty, measure_empty] at hpos
  exact lt_irrefl _ hpos

end LimitSemiconvex

open MuLipschitz EnvelopeCompactness LimitSlopeMass LimitSemiconvex in
/-- **Step L2-A** (`LimitSemiconvexStmt`): limits of rescaled envelopes are touched from below by
paraboloids of opening `Λ = max C 0` at every point of `B̄_δ`, `C` the constant of Proposition 5.2. -/
theorem limitSemiconvex : LimitSemiconvexStmt := by
  intro d hd K hK
  obtain ⟨C, hC⟩ := harnackQuadratic d hd (1 / 2) (by norm_num) (by norm_num) K
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro α hα w hlap hnear hballs hann β hβ0 hβ1 m hm x₀ p hx₀ hp φ V z hφ hz hconv δ hδ
  set Λ := max C 0 with hΛ_def
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hd1 : 1 ≤ d := by omega
  set δ₁ := max δ 0 with hδ₁_def
  have hδ₁1 : δ₁ < 1 := max_lt hδ one_pos
  have hδ₁0 : 0 ≤ δ₁ := le_max_right _ _
  set η := (1 - δ₁) / 8 with hη_def
  have hη : 0 < η := by rw [hη_def]; linarith
  set δ₂ := δ₁ + 2 * η with hδ₂_def
  have hδ₂1 : δ₂ < 1 := by rw [hδ₂_def, hη_def]; linarith
  refine ⟨η, hη, ?_⟩
  intro X hX q hq
  have hXn : ‖X‖ ≤ δ₁ := (mem_closedBall_zero_iff.1 hX).trans (le_max_left _ _)
  have hXX : X ∈ ball (0 : Rd d) 1 := mem_ball_zero_iff.2 (by linarith)
  have hX2 : X ∈ closedBall (0 : Rd d) δ₂ := mem_closedBall_zero_iff.2 (by linarith)
  set n : ℕ → ℕ := fun k => m (φ k) with hn_def
  have hnmono : StrictMono n := hm.comp hφ
  have hntend : Tendsto n atTop atTop := hnmono.tendsto_atTop
  have hn1 : ∀ k, 1 ≤ k → 1 ≤ n k := fun k hk => hk.trans (hnmono.id_le k)
  set F : ℕ → Rd d → ℝ := fun k =>
    rescaledEnvelope (w (n k)) (n k) (x₀ (φ k)) (p (φ k)) with hF_def
  obtain ⟨M, L, δ', k₀, -, -, hk⟩ := LimitBasic.rescaled_eventually_bounds hd hK hlap hβ0 hβ1
    hnmono (x₀ := fun k => x₀ (φ k)) (p := fun k => p (φ k)) (fun k => hx₀ (φ k))
    (fun k => hp (φ k)) δ₂ hδ₂1
  have hLip : ∀ k, k₀ ≤ k → LipschitzOnWith L.toNNReal (F k) (closedBall (0 : Rd d) δ₂) :=
    fun k hk' => (hk k hk').2.1
  obtain ⟨ρ, hρ, hcomb⟩ := localConvexComb d hd1
  have hpt : ∀ Y ∈ ball (0 : Rd d) 1, Tendsto (fun k => F k Y) atTop (𝓝 (V Y)) := fun Y hY =>
    (hconv ‖Y‖ (mem_ball_zero_iff.1 hY)).tendsto_at (mem_closedBall_zero_iff.2 le_rfl)
  have hηj : ∀ j : ℕ, η / ((j : ℝ) + 1) ≤ η := fun j =>
    div_le_self hη.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  -- contact points near `X`
  have hball : ∀ j : ℕ, closedBall X (η / ((j : ℝ) + 1)) ⊆ ball (0 : Rd d) 1 := by
    intro j Y hY
    rw [mem_ball_zero_iff]
    have h1 := mem_closedBall.1 hY
    rw [dist_eq_norm] at h1
    have h2 := hηj j
    calc ‖Y‖ = ‖(Y - X) + X‖ := by rw [sub_add_cancel]
      _ ≤ ‖Y - X‖ + ‖X‖ := norm_add_le _ _
      _ < 1 := by linarith
  have hchoice : ∀ j : ℕ, ∃ k, j ≤ k ∧ k₀ ≤ k ∧ 1 ≤ k ∧
      (∀ Y ∈ closedBall (0 : Rd d) δ₂,
        (n k : ℝ) • Y ∈ convexHull ℝ (toE '' dClosure (ballZ0 (d := d) (n k : ℝ)))) ∧
      ρ < η * n k ∧
      ∃ x ∈ discretize (closedBall X (η / ((j : ℝ) + 1))) (n k), ∃ p' : Rd d,
        p' ∈ supGrad (w (n k)) x (ballZ0 (n k : ℝ)) := by
    intro j
    have hρn : ∀ᶠ k in atTop, ρ < η * n k := by
      have : Tendsto (fun k => η * (n k : ℝ)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.comp hntend).const_mul_atTop hη
      exact this.eventually_gt_atTop ρ
    have hev := (eventually_ge_atTop j).and ((eventually_ge_atTop k₀).and
      ((eventually_ge_atTop 1).and ((hntend.eventually (hull_eventually hd1 hδ₂1)).and
      (hρn.and (hntend.eventually (exists_contact_near hd1 hα hnear hann
        (by positivity : (0 : ℝ) < η / ((j : ℝ) + 1)) (hball j)))))))
    obtain ⟨k, hk⟩ := hev.exists
    exact ⟨k, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2⟩
  choose kj hkj hkj₀ hkj1 hkjhull hkjρ xj hxj pj hpj using hchoice
  set Xj : ℕ → Rd d := fun j => ((n (kj j) : ℝ))⁻¹ • toE (xj j) with hXj_def
  set qj : ℕ → Rd d := fun j => ((n (kj j) : ℝ))⁻¹ • (pj j - p (φ (kj j))) with hqj_def
  have hnk0 : ∀ j, (0 : ℝ) < n (kj j) := fun j => by exact_mod_cast hn1 _ (hkj1 j)
  have hXjX : ∀ j, ‖Xj j - X‖ ≤ η / ((j : ℝ) + 1) := fun j => by
    have := (mem_discretize_iff (hn1 _ (hkj1 j))).1 (hxj j)
    rw [mem_closedBall, dist_eq_norm] at this
    exact this
  have hXjn : ∀ j, ‖Xj j‖ ≤ δ₁ + η := fun j => by
    have h2 := hηj j
    have h3 := hXjX j
    calc ‖Xj j‖ = ‖(Xj j - X) + X‖ := by rw [sub_add_cancel]
      _ ≤ ‖Xj j - X‖ + ‖X‖ := norm_add_le _ _
      _ ≤ δ₁ + η := by linarith
  have hXjtend : Tendsto Xj atTop (𝓝 X) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j => norm_nonneg _) hXjX ?_
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hxR : ∀ j, ∀ y : Site d, ‖toE y - toE (xj j)‖ < 6 * η * n (kj j) →
      y ∈ ballZ0 (d := d) (n (kj j) : ℝ) := by
    intro j y hy
    rw [mem_ballZ0]
    have hx : ‖toE (xj j)‖ ≤ (n (kj j) : ℝ) * (δ₁ + η) := by
      have h := hXjn j
      simp only [Xj] at h
      rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_le_iff₀ (hnk0 j)] at h
      exact h
    have h7 : δ₁ + 7 * η < 1 := by rw [hη_def]; linarith
    have h8 : (n (kj j) : ℝ) * (δ₁ + η) + 6 * η * n (kj j) < n (kj j) := by nlinarith [hnk0 j]
    calc ‖toE y‖ = ‖(toE y - toE (xj j)) + toE (xj j)‖ := by rw [sub_add_cancel]
      _ ≤ ‖toE y - toE (xj j)‖ + ‖toE (xj j)‖ := norm_add_le _ _
      _ < n (kj j) := by linarith
  have hxB : ∀ j, xj j ∈ ballZ0 (d := d) (n (kj j) : ℝ) := fun j =>
    hxR j _ (by rw [sub_self, norm_zero]; have := hnk0 j; positivity)
  have hgapj : ∀ j, ∀ y : Site d, ‖toE y - toE (xj j)‖ < 3 * η * n (kj j) →
      y ∈ ballZ0 (d := d) (n (kj j) : ℝ) ∧
      w (n (kj j)) (xj j) + inner ℝ (pj j) (toE y - toE (xj j)) - w (n (kj j)) y ≤
        Λ * ‖toE y - toE (xj j)‖ ^ 2 := by
    intro j y hy
    have hpos : 0 < η * (n (kj j) : ℝ) := mul_pos hη (hnk0 j)
    have h6 : ‖toE y - toE (xj j)‖ < 6 * η * n (kj j) := by nlinarith
    refine ⟨hxR j y h6, ?_⟩
    have hq := gap_le_quadratic (R := 6 * η * n (kj j)) hC (hlap (n (kj j))) (hpj j) (hxR j)
      (by nlinarith : ‖toE y - toE (xj j)‖ < 1 / 2 * (6 * η * n (kj j)))
    exact hq.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have hqbd : ∀ j, ‖qj j‖ ≤ L.toNNReal := by
    intro j
    have hXjC : closedBall (Xj j) η ⊆ closedBall (0 : Rd d) δ₂ := by
      intro Y hY
      rw [mem_closedBall_zero_iff]
      have h1 := mem_closedBall.1 hY
      rw [dist_eq_norm] at h1
      have h2 := hXjn j
      calc ‖Y‖ = ‖(Y - Xj j) + Xj j‖ := by rw [sub_add_cancel]
        _ ≤ ‖Y - Xj j‖ + ‖Xj j‖ := norm_add_le _ _
        _ ≤ δ₂ := by linarith
    refine norm_le_of_supergrad (hLip _ (hkj₀ j)) hη hXjC (fun Y hY => ?_)
    exact rescaled_le_affine (hn1 _ (hkj1 j)) (mem_dClosure_of_mem (hxB j)) (hpj j)
      (hkjhull j Y (hXjC hY))
  obtain ⟨qs, -, χ, hχ, hqlim⟩ :=
    (isCompact_closedBall (0 : Rd d) (L.toNNReal : ℝ)).tendsto_subseq
      (fun j => mem_closedBall_zero_iff.2 (hqbd j))
  have hkχ : Tendsto (fun j => kj (χ j)) atTop atTop :=
    tendsto_atTop_mono (fun j => (hχ.id_le j).trans (hkj (χ j))) tendsto_id
  have hnχ : Tendsto (fun j => (n (kj (χ j)) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hntend.comp hkχ)
  have hXχ : Tendsto (fun j => Xj (χ j)) atTop (𝓝 X) := hXjtend.comp hχ.tendsto_atTop
  have hqχ : Tendsto (fun j => qj (χ j)) atTop (𝓝 qs) := hqlim
  have hFX : Tendsto (fun j => F (kj (χ j)) (Xj (χ j))) atTop (𝓝 (V X)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hA : Tendsto (fun j => (L.toNNReal : ℝ) * dist (Xj (χ j)) X) atTop (𝓝 0) := by
      have := (tendsto_iff_dist_tendsto_zero.1 hXχ).const_mul (L.toNNReal : ℝ)
      rwa [mul_zero] at this
    have hB : Tendsto (fun j => dist (F (kj (χ j)) X) (V X)) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 ((hpt X hXX).comp hkχ)
    have hAB := hA.add hB
    rw [add_zero] at hAB
    refine squeeze_zero' (Eventually.of_forall fun j => dist_nonneg) ?_ hAB
    refine Eventually.of_forall fun j => ?_
    have hXj2 : Xj (χ j) ∈ closedBall (0 : Rd d) δ₂ :=
      mem_closedBall_zero_iff.2 (by linarith [hXjn (χ j)])
    calc dist (F (kj (χ j)) (Xj (χ j))) (V X)
        ≤ dist (F (kj (χ j)) (Xj (χ j))) (F (kj (χ j)) X) + dist (F (kj (χ j)) X) (V X) :=
          dist_triangle _ _ _
      _ ≤ (L.toNNReal : ℝ) * dist (Xj (χ j)) X + dist (F (kj (χ j)) X) (V X) := by
          gcongr
          exact (hLip _ (hkj₀ (χ j))).dist_le_mul _ hXj2 _ hX2
  -- the discrete lower bounds
  have hlow : ∀ Y ∈ ball X η, ∀ j, F (kj j) (Xj j) + inner ℝ (qj j) (Y - Xj j) -
      Λ * (‖Y - Xj j‖ + ρ / n (kj j)) ^ 2 ≤ F (kj j) Y := by
    intro Y hY j
    obtain ⟨ι, hι, zz, lam, h0, h1, hs, hdz⟩ := hcomb ((n (kj j) : ℝ) • Y)
    have hYX : ‖Y - Xj j‖ < 2 * η := by
      have h1 := mem_ball.1 hY
      rw [dist_eq_norm] at h1
      have h2 := hXjX j
      have h3 := hηj j
      calc ‖Y - Xj j‖ = ‖(Y - X) + (X - Xj j)‖ := by congr 1; abel
        _ ≤ ‖Y - X‖ + ‖X - Xj j‖ := norm_add_le _ _
        _ < 2 * η := by rw [norm_sub_rev X]; linarith
    have hcond : (n (kj j) : ℝ) * ‖Y - Xj j‖ + ρ < 3 * η * n (kj j) := by
      have := mul_lt_mul_of_pos_left hYX (hnk0 j)
      have := hkjρ j
      nlinarith
    exact rescaled_lower (hn1 _ (hkj1 j)) (mem_dClosure_of_mem (hxB j)) (hpj j) hΛ0 (hgapj j)
      h0 h1 hs hdz hcond
  -- the limit paraboloid
  have hstar : ∀ Y ∈ ball X η, V X + inner ℝ qs (Y - X) - Λ * ‖Y - X‖ ^ 2 ≤ V Y := by
    intro Y hY
    have hY1 : Y ∈ ball (0 : Rd d) 1 := by
      rw [mem_ball_zero_iff]
      have h1 := mem_ball.1 hY
      rw [dist_eq_norm] at h1
      calc ‖Y‖ = ‖(Y - X) + X‖ := by rw [sub_add_cancel]
        _ ≤ ‖Y - X‖ + ‖X‖ := norm_add_le _ _
        _ < 1 := by linarith
    have hlimY : Tendsto (fun j => F (kj (χ j)) Y) atTop (𝓝 (V Y)) := (hpt Y hY1).comp hkχ
    have hρn : Tendsto (fun j => ρ / (n (kj (χ j)) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnχ
    have hlimL : Tendsto (fun j => F (kj (χ j)) (Xj (χ j)) + inner ℝ (qj (χ j)) (Y - Xj (χ j)) -
        Λ * (‖Y - Xj (χ j)‖ + ρ / n (kj (χ j))) ^ 2) atTop
        (𝓝 (V X + inner ℝ qs (Y - X) - Λ * (‖Y - X‖ + 0) ^ 2)) := by
      refine (hFX.add (hqχ.inner (tendsto_const_nhds.sub hXχ))).sub (tendsto_const_nhds.mul ?_)
      exact (((tendsto_const_nhds.sub hXχ).norm).add hρn).pow 2
    rw [add_zero] at hlimL
    exact le_of_tendsto_of_tendsto hlimL hlimY (Eventually.of_forall fun j => hlow Y hY (χ j))
  -- uniqueness of the slope
  have hqeq : q = qs := by
    by_contra hne
    obtain ⟨D, hD⟩ : ∃ D, D = q - qs := ⟨_, rfl⟩
    have hD0 : 0 < ‖D‖ := norm_pos_iff.2 (by rw [hD]; exact sub_ne_zero.2 hne)
    set t := min (η / (2 * ‖D‖)) (1 / (2 * (Λ + 1))) with ht
    have ht0 : 0 < t := lt_min (by positivity) (by positivity)
    have htD : t * ‖D‖ ≤ η / 2 := by
      have := min_le_left (η / (2 * ‖D‖)) (1 / (2 * (Λ + 1)))
      calc t * ‖D‖ ≤ η / (2 * ‖D‖) * ‖D‖ := mul_le_mul_of_nonneg_right this hD0.le
        _ = η / 2 := by field_simp
    have htΛ : Λ * t < 1 := by
      have := min_le_right (η / (2 * ‖D‖)) (1 / (2 * (Λ + 1)))
      calc Λ * t ≤ Λ * (1 / (2 * (Λ + 1))) := mul_le_mul_of_nonneg_left this hΛ0
        _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
    set Y₁ := X - t • D with hY₁
    have hY₁X : Y₁ - X = -(t • D) := by rw [hY₁]; abel
    have hnY₁ : ‖Y₁ - X‖ = t * ‖D‖ := by
      rw [hY₁X, norm_neg, norm_smul, Real.norm_of_nonneg ht0.le]
    have hY₁b : Y₁ ∈ ball X η := by rw [mem_ball, dist_eq_norm, hnY₁]; linarith
    have hY₁1 : Y₁ ∈ ball (0 : Rd d) 1 := by
      rw [mem_ball_zero_iff]
      calc ‖Y₁‖ = ‖(Y₁ - X) + X‖ := by rw [sub_add_cancel]
        _ ≤ ‖Y₁ - X‖ + ‖X‖ := norm_add_le _ _
        _ < 1 := by rw [hnY₁]; linarith
    have hup := hq Y₁ hY₁1
    have hlo := hstar Y₁ hY₁b
    rw [hY₁X, inner_neg_right, real_inner_smul_right] at hup
    rw [hnY₁, hY₁X, inner_neg_right, real_inner_smul_right] at hlo
    have hDD : inner ℝ q D - inner ℝ qs D = ‖D‖ ^ 2 := by
      rw [← inner_sub_left, ← hD, real_inner_self_eq_norm_sq]
    have h6 : t * inner ℝ q D - t * inner ℝ qs D = t * ‖D‖ ^ 2 := by rw [← mul_sub, hDD]
    have hkey : t * ‖D‖ ^ 2 ≤ Λ * (t * ‖D‖) ^ 2 := by linarith
    have h7 : Λ * (t * ‖D‖) ^ 2 = Λ * t * (t * ‖D‖ ^ 2) := by ring
    have hpos : 0 < t * ‖D‖ ^ 2 * (1 - Λ * t) := by
      have : 0 < 1 - Λ * t := by linarith
      positivity
    have h8 : t * ‖D‖ ^ 2 * (1 - Λ * t) = t * ‖D‖ ^ 2 - Λ * t * (t * ‖D‖ ^ 2) := by ring
    linarith
  intro Y hY
  rw [hqeq]
  exact hstar Y hY

end RandomSandpile

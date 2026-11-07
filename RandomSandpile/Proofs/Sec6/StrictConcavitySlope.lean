import RandomSandpile.Proofs.Sec6.StrictConcavityLimit

/-! # Lemma 6.2', step L2-B: slope mass of limits of rescaled envelopes

`limitSlopeMass : LimitSlopeMassStmt`. Fix a closed ball `K = B̄(c, r) ⊆ B_1`.
* Mass: by near-maximality and the bound on the complement `B_1 \ K`, the discrete slopes at points
  of `nK` have volume `≥ (α r^d - 2ε) |B_n|` for large `n` (`mass_closedBall_lower`).
* Rescaling: the slopes `q = (p' - p_n)/n` are supergradients of the rescaled envelope `V_n`
  (`rescaled_le_affine`), bounded by the Lipschitz constant of `V_n` (`norm_le_of_supergrad`); the
  rescaled slope set has volume `n^{-d}` times the discrete one, and `|B_n|/n^d → |B_1|`
  (`tendsto_ncard_ball_div_pow`, with `covolume_intLattice`).
* Reverse Fatou: every slope lying in infinitely many rescaled slope sets is a slope of `V` over
  `K` (compactness of `K` and locally uniform convergence), so `|slopes of V over K| ≥ α |K|`. -/

open MeasureTheory LatticeProb Filter Metric Module
open scoped Topology ENNReal Pointwise

namespace RandomSandpile

namespace LimitSlopeMass

open MuLipschitz EnvelopeCompactness BallCount

variable {d : ℕ}

/-- The integer lattice `ℤ^d ⊂ ℝ^d` has covolume `1`. -/
theorem covolume_intLattice : ZLattice.covolume (intLattice d) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (intLattice d) volume
    (ZSpan.isAddFundamentalDomain (PiLp.basisFun 2 ℝ (Fin d)) volume),
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume)]
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).volume_parallelepiped
  rw [← OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_toBasis] at h
  rw [measureReal_def, h, ENNReal.toReal_one]

/-- `|B_n| / n^d → |B_1|`. -/
theorem tendsto_ncard_ball_div_pow (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ => ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) / (n : ℝ) ^ d) atTop
      (𝓝 (volume.real (ball (0 : Rd d) 1))) := by
  have h := tendsto_ncard_div_pow (d := d) hd one_pos
  rw [covolume_intLattice, div_one] at h
  simpa only [one_mul] using h

theorem mem_discretize_iff {W : Set (Rd d)} {n : ℕ} (hn : 1 ≤ n) {x : Site d} :
    x ∈ discretize W n ↔ (n : ℝ)⁻¹ • toE x ∈ W := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  exact Set.mem_smul_set_iff_inv_smul_mem₀ hn0 _ _

/-- A closed ball inside `B_1` lies in `B̄_{‖c‖ + r}` with `‖c‖ + r < 1`. -/
theorem norm_add_lt_one (hd : 1 ≤ d) {c : Rd d} {r : ℝ} (hr : 0 ≤ r)
    (hK : closedBall c r ⊆ ball (0 : Rd d) 1) : ‖c‖ + r < 1 := by
  by_cases hc : c = 0
  · subst hc
    set u : Rd d := EuclideanSpace.single (⟨0, by omega⟩ : Fin d) 1
    have hu : ‖u‖ = 1 := by simp [u]
    have hmem : r • u ∈ closedBall (0 : Rd d) r := by
      rw [mem_closedBall_zero_iff, norm_smul, hu, Real.norm_of_nonneg hr, mul_one]
    have := mem_ball_zero_iff.1 (hK hmem)
    rw [norm_smul, hu, Real.norm_of_nonneg hr, mul_one] at this
    simpa using this
  · have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
    set u : Rd d := ‖c‖⁻¹ • c
    have hu : ‖u‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc0.ne']
    have hmem : c + r • u ∈ closedBall c r := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hu,
        Real.norm_of_nonneg hr, mul_one]
    have := mem_ball_zero_iff.1 (hK hmem)
    have heq : c + r • u = (1 + r / ‖c‖) • c := by
      simp only [u, smul_smul, add_smul, one_smul]
      congr 2
    rw [heq, norm_smul, Real.norm_of_nonneg (by positivity)] at this
    have : (1 + r / ‖c‖) * ‖c‖ = ‖c‖ + r := by field_simp
    linarith

/-- For `δ < 1` and large `n`, `n B̄_δ` lies in the convex hull of `B̄_n`. -/
theorem hull_eventually (hd : 1 ≤ d) {δ : ℝ} (hδ : δ < 1) : ∀ᶠ n : ℕ in atTop,
    ∀ X ∈ closedBall (0 : Rd d) δ,
      (n : ℝ) • X ∈ convexHull ℝ (toE '' dClosure (ballZ0 (d := d) (n : ℝ))) := by
  obtain ⟨ρ, hρ, hcomb⟩ := localConvexComb d hd
  obtain ⟨N, hN⟩ := exists_nat_gt ((ρ + 1) / (1 - δ))
  filter_upwards [eventually_ge_atTop N] with n hn X hX
  obtain ⟨ι, hι, z, lam, h0, h1, hs, hdist⟩ := hcomb ((n : ℝ) • X)
  rw [← hs]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => h0 i) h1
    (fun i _ => subset_convexHull ℝ _ ⟨z i, Or.inl (mem_ballZ0.2 ?_), rfl⟩)
  have hXn : ‖(n : ℝ) • X‖ ≤ n * δ := by
    rw [norm_smul, Real.norm_natCast]
    exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hX) (Nat.cast_nonneg _)
  have h1δ : 0 < 1 - δ := by linarith
  have hn' : (ρ + 1) / (1 - δ) < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
  rw [div_lt_iff₀ h1δ] at hn'
  calc ‖toE (z i)‖ = ‖(toE (z i) - (n : ℝ) • X) + (n : ℝ) • X‖ := by rw [sub_add_cancel]
    _ ≤ ‖toE (z i) - (n : ℝ) • X‖ + ‖(n : ℝ) • X‖ := norm_add_le _ _
    _ < n := by nlinarith [hdist i]

/-- Discrete supergradients rescale to supergradients of the rescaled envelope: at a contact point
`x` with slope `p'`, `V_n(Y) ≤ V_n(x/n) + ((p' - p)/n) · (Y - x/n)` wherever `nY` lies in the hull. -/
theorem rescaled_le_affine {w : Site d → ℝ} {n : ℕ} (hn : 1 ≤ n) {x₀ x : Site d} {p p' : Rd d}
    (hx : x ∈ dClosure (ballZ0 (d := d) (n : ℝ))) (hp' : p' ∈ supGrad w x (ballZ0 (n : ℝ)))
    {Y : Rd d}
    (hY : (n : ℝ) • Y ∈ convexHull ℝ (toE '' dClosure (ballZ0 (d := d) (n : ℝ)))) :
    rescaledEnvelope w n x₀ p Y ≤ rescaledEnvelope w n x₀ p ((n : ℝ)⁻¹ • toE x) +
      inner ℝ ((n : ℝ)⁻¹ • (p' - p)) (Y - (n : ℝ)⁻¹ • toE x) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle := concaveEnvelopeOn_le_of_mem_supGrad (ballZ0_finite _) hx hp' hY
  have heq := concaveEnvelopeOn_eq_of_mem_supGrad (ballZ0_finite (d := d) (n : ℝ)) hx hp'
  unfold rescaledEnvelope
  rw [smul_smul, mul_inv_cancel₀ hn0.ne', one_smul, heq]
  have hv : Y - (n : ℝ)⁻¹ • toE x = (n : ℝ)⁻¹ • ((n : ℝ) • Y - toE x) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hn0.ne', one_smul]
  have key : inner ℝ ((n : ℝ)⁻¹ • (p' - p)) (Y - (n : ℝ)⁻¹ • toE x) =
      (inner ℝ p' ((n : ℝ) • Y - toE x) - inner ℝ p ((n : ℝ) • Y - toE x)) / (n : ℝ) ^ 2 := by
    rw [hv, real_inner_smul_left, real_inner_smul_right, inner_sub_left]
    field_simp
  have h3 : inner ℝ p ((n : ℝ) • Y - toE x₀) =
      inner ℝ p ((n : ℝ) • Y - toE x) + inner ℝ p (toE x - toE x₀) := by
    rw [← inner_add_right]; congr 1; abel
  rw [key, ← add_div, div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- A supergradient at `X` of a function that is `L`-Lipschitz on `B̄(X, s)` has norm `≤ L`. -/
theorem norm_le_of_supergrad {f : Rd d → ℝ} {S : Set (Rd d)} {L : NNReal}
    (hL : LipschitzOnWith L f S) {X q : Rd d} {s : ℝ} (hs : 0 < s)
    (hball : closedBall X s ⊆ S)
    (hsup : ∀ Y ∈ closedBall X s, f Y ≤ f X + inner ℝ q (Y - X)) : ‖q‖ ≤ L := by
  by_cases hq : q = 0
  · rw [hq, norm_zero]; exact L.2
  have hq0 : 0 < ‖q‖ := norm_pos_iff.2 hq
  set Y : Rd d := X - (s / ‖q‖) • q
  have hYX : Y - X = -((s / ‖q‖) • q) := by simp only [Y]; abel
  have hnorm : ‖Y - X‖ = s := by
    rw [hYX, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hYmem : Y ∈ closedBall X s := by rw [mem_closedBall, dist_eq_norm, hnorm]
  have hXmem : X ∈ closedBall X s := mem_closedBall_self hs.le
  have h1 := hsup Y hYmem
  rw [hYX, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
  have h2 := hL.dist_le_mul Y (hball hYmem) X (hball hXmem)
  rw [Real.dist_eq, dist_eq_norm, hnorm] at h2
  have h3 : f X - f Y ≤ L * s := by linarith [neg_abs_le (f Y - f X)]
  have h4 : s / ‖q‖ * ‖q‖ ^ 2 = s * ‖q‖ := by field_simp
  have : s * ‖q‖ ≤ L * s := by linarith
  nlinarith

/-- Mass of the discrete slopes over `nK`, `K = B̄(c, r) ⊆ B_1`: near-maximality and the bound
on the complement give `≥ (α r^d - 2ε) |B_n|` for large `n`. -/
theorem mass_closedBall_lower (hd : 1 ≤ d) {w : ℕ → Site d → ℝ} {α : ℝ}
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
        volume (supGradSet (w n) (ballZ0 (n : ℝ))))
    (hann : ∀ (c : Rd d) (ρ : ℝ), 0 < ρ → closedBall c ρ ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        volume (⋃ x ∈ discretize (ball (0 : Rd d) 1 \ closedBall c ρ) n,
            supGrad (w n) x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal ((α * (1 - ρ ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)))
    (hα : 0 ≤ α) {c : Rd d} {r : ℝ} (hr : 0 < r) (hK : closedBall c r ⊆ ball 0 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ((α * r ^ d - 2 * ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
        volume (⋃ x ∈ discretize (closedBall c r) n, supGrad (w n) x (ballZ0 (n : ℝ))) := by
  have hr1 : r < 1 := by have := norm_add_lt_one hd hr.le hK; linarith [norm_nonneg c]
  have hrd : r ^ d ≤ 1 := pow_le_one₀ hr.le hr1.le
  filter_upwards [hnear ε hε, hann c r hr hK ε hε, eventually_ge_atTop 1] with n h1 h2 hn
  set A := ⋃ x ∈ discretize (ball (0 : Rd d) 1 \ closedBall c r) n,
    supGrad (w n) x (ballZ0 (n : ℝ))
  set B := ⋃ x ∈ discretize (closedBall c r) n, supGrad (w n) x (ballZ0 (n : ℝ))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub : supGradSet (w n) (ballZ0 (n : ℝ)) ⊆ A ∪ B := by
    intro q hq
    simp only [supGradSet, Set.mem_iUnion] at hq
    obtain ⟨x, hx, hqx⟩ := hq
    by_cases hxK : (n : ℝ)⁻¹ • toE x ∈ closedBall c r
    · exact Or.inr (Set.mem_biUnion ((mem_discretize_iff hn).2 hxK) hqx)
    · refine Or.inl (Set.mem_biUnion ((mem_discretize_iff hn).2 ⟨?_, hxK⟩) hqx)
      rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hn0,
        mul_one]
      exact mem_ballZ0.1 hx
  have htot := h1.trans ((measure_mono hsub).trans (measure_union_le A B))
  have hN : (0 : ℝ) ≤ ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := Nat.cast_nonneg _
  have hy : 0 ≤ (α * (1 - r ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
    have : 0 ≤ α * (1 - r ^ d) := mul_nonneg hα (by linarith)
    positivity
  have hsplit : ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) =
      ENNReal.ofReal ((α * r ^ d - 2 * ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) +
        (α * (1 - r ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
    congr 1; ring
  by_cases hneg : (α * r ^ d - 2 * ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) ≤ 0
  · rw [ENNReal.ofReal_of_nonpos hneg]; exact bot_le
  rw [not_le] at hneg
  rw [hsplit, ENNReal.ofReal_add hneg.le hy] at htot
  have h4 : ENNReal.ofReal ((α * r ^ d - 2 * ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) +
      ENNReal.ofReal ((α * (1 - r ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
      volume B + ENNReal.ofReal ((α * (1 - r ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) :=
    calc _ ≤ volume A + volume B := htot
      _ ≤ ENNReal.ofReal ((α * (1 - r ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) +
          volume B := by gcongr
      _ = _ := add_comm _ _
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h4

end LimitSlopeMass

open MuLipschitz EnvelopeCompactness LimitSlopeMass in
/-- **Step L2-B** (`LimitSlopeMassStmt`): for every closed ball `K ⊆ B_1`, the slopes of the limit
`V` over `K` have volume `≥ α |K|`. -/
theorem limitSlopeMass : LimitSlopeMassStmt := by
  intro d hd K hK α hα w hlap hnear hballs hann β hβ0 hβ1 m hm x₀ p hx₀ hp φ V z hφ hz hconv
    c r hr hKsub
  have hd1 : 1 ≤ d := by omega
  set n : ℕ → ℕ := fun k => m (φ k) with hn_def
  have hnmono : StrictMono n := hm.comp hφ
  have hntend : Tendsto n atTop atTop := hnmono.tendsto_atTop
  have hn1 : ∀ k, 1 ≤ k → 1 ≤ n k := fun k hk => hk.trans (hnmono.id_le k)
  set F : ℕ → Rd d → ℝ := fun k =>
    rescaledEnvelope (w (n k)) (n k) (x₀ (φ k)) (p (φ k)) with hF_def
  set Kb : Set (Rd d) := closedBall c r with hKb
  have hδ₀ : ‖c‖ + r < 1 := norm_add_lt_one hd1 hr.le hKsub
  set δ := (‖c‖ + r + 1) / 2 with hδ_def
  have hδ1 : δ < 1 := by simp only [δ]; linarith
  set s := (1 - (‖c‖ + r)) / 2 with hs_def
  have hs : 0 < s := by simp only [s]; linarith
  have hKδ : ∀ X ∈ Kb, closedBall X s ⊆ closedBall (0 : Rd d) δ := by
    intro X hX Y hY
    rw [mem_closedBall_zero_iff]
    have h1 : ‖X‖ ≤ ‖c‖ + r := by
      have := mem_closedBall.1 hX
      rw [dist_eq_norm] at this
      calc ‖X‖ = ‖(X - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖X - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have h2 := mem_closedBall.1 hY
    rw [dist_eq_norm] at h2
    calc ‖Y‖ = ‖(Y - X) + X‖ := by rw [sub_add_cancel]
      _ ≤ ‖Y - X‖ + ‖X‖ := norm_add_le _ _
      _ ≤ δ := by simp only [δ, s] at h2 ⊢; linarith
  have hKsubδ : Kb ⊆ closedBall (0 : Rd d) δ := fun X hX => hKδ X hX (mem_closedBall_self hs.le)
  obtain ⟨M, L, δ', k₀, -, -, hk⟩ := LimitBasic.rescaled_eventually_bounds hd hK hlap hβ0 hβ1
    hnmono (x₀ := fun k => x₀ (φ k)) (p := fun k => p (φ k)) (fun k => hx₀ (φ k))
    (fun k => hp (φ k)) δ hδ1
  have hLip : ∀ k, k₀ ≤ k → LipschitzOnWith L.toNNReal (F k) (closedBall (0 : Rd d) δ) :=
    fun k hk' => (hk k hk').2.1
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 ((hntend.eventually (hull_eventually hd1 hδ1)).and
    (eventually_ge_atTop (max k₀ 1)))
  -- the rescaled slope sets
  set U : ℕ → Set (Rd d) := fun k =>
    ⋃ x ∈ discretize Kb (n k), supGrad (w (n k)) x (ballZ0 (n k : ℝ)) with hU
  set S : ℕ → Set (Rd d) := fun k => (fun q => p (φ k) + (n k : ℝ) • q) ⁻¹' U k with hS
  have hdiscr : ∀ k, 1 ≤ k → ∀ x ∈ discretize Kb (n k), (n k : ℝ)⁻¹ • toE x ∈ Kb ∧
      x ∈ ballZ0 (d := d) (n k : ℝ) := by
    intro k hk1 x hx
    have hX := (mem_discretize_iff (hn1 k hk1)).1 hx
    refine ⟨hX, mem_ballZ0.2 ?_⟩
    have hn0 : (0 : ℝ) < n k := by exact_mod_cast hn1 k hk1
    have h1 := mem_ball_zero_iff.1 (hKsub hX)
    rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hn0, mul_one] at h1
    exact h1
  have hS_aff : ∀ k, 1 ≤ k → ∀ q ∈ S k, ∃ X ∈ Kb, ∀ Y : Rd d,
      (n k : ℝ) • Y ∈ convexHull ℝ (toE '' dClosure (ballZ0 (d := d) (n k : ℝ))) →
      F k Y ≤ F k X + inner ℝ q (Y - X) := by
    intro k hk1 q hq
    have hq' : p (φ k) + (n k : ℝ) • q ∈ U k := hq
    simp only [U, Set.mem_iUnion] at hq'
    obtain ⟨x, hx, hpx⟩ := hq'
    obtain ⟨hX, hxB⟩ := hdiscr k hk1 x hx
    have hn0 : (0 : ℝ) < n k := by exact_mod_cast hn1 k hk1
    refine ⟨_, hX, fun Y hY => ?_⟩
    have h := rescaled_le_affine (x₀ := x₀ (φ k)) (p := p (φ k)) (hn1 k hk1) (Or.inl hxB) hpx hY
    rwa [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hn0.ne', one_smul] at h
  have hSbdd : ∀ k, k₁ ≤ k → S k ⊆ closedBall (0 : Rd d) (L.toNNReal : ℝ) := by
    intro k hk q hq
    obtain ⟨hhull, hkk⟩ := hk₁ k hk
    have hk1 : 1 ≤ k := le_of_max_le_right hkk
    obtain ⟨X, hX, haff⟩ := hS_aff k hk1 q hq
    rw [mem_closedBall_zero_iff]
    exact norm_le_of_supergrad (hLip k (le_of_max_le_left hkk)) hs (hKδ X hX)
      (fun Y hY => haff Y (hhull Y (hKδ X hX hY)))
  have hSclosed : ∀ k, 1 ≤ k → IsClosed (S k) := by
    intro k hk1
    have hcont : Continuous (fun q : Rd d => p (φ k) + (n k : ℝ) • q) :=
      continuous_const.add (continuous_const_smul _)
    refine IsClosed.preimage hcont ?_
    have hfin : (discretize Kb (n k)).Finite :=
      (ballZ0_finite (d := d) (n k : ℝ)).subset fun x hx => (hdiscr k hk1 x hx).2
    exact hfin.isClosed_biUnion fun x _ => isClosed_supGrad _ _ _
  have hvolS : ∀ k, 1 ≤ k →
      volume (S k) = ENNReal.ofReal |((n k : ℝ) ^ d)⁻¹| * volume (U k) := by
    intro k hk1
    have hn0 : (n k : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n k := by exact_mod_cast hn1 k hk1
      exact this.ne'
    have hpre : S k = (fun q => (n k : ℝ) • q) ⁻¹' ((fun h => p (φ k) + h) ⁻¹' U k) := rfl
    rw [hpre, Measure.addHaar_preimage_smul volume hn0, measure_preimage_add,
      finrank_euclideanSpace_fin]
  -- tails of the sequence of slope sets
  set T : ℕ → Set (Rd d) := fun N => ⋃ k, ⋃ (_ : N + 1 ≤ k), S k with hT
  have hT_anti : Antitone T := by
    intro N N' hNN' q hq
    simp only [T, Set.mem_iUnion] at hq ⊢
    obtain ⟨k, hk, hqk⟩ := hq
    exact ⟨k, by omega, hqk⟩
  have hT_meas : ∀ N, NullMeasurableSet (T N) volume := fun N =>
    (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk =>
      (hSclosed k (by omega)).measurableSet).nullMeasurableSet
  have hT_fin : ∃ N, volume (T N) ≠ ∞ := by
    refine ⟨k₁, ne_of_lt (lt_of_le_of_lt (measure_mono (t := closedBall (0 : Rd d)
      (L.toNNReal : ℝ)) ?_) measure_closedBall_lt_top)⟩
    intro q hq
    simp only [T, Set.mem_iUnion] at hq
    obtain ⟨k, hk, hqk⟩ := hq
    exact hSbdd k (by omega) hqk
  have hInter := hT_anti.measure_iInter hT_meas hT_fin
  -- every slope in infinitely many `S k` is a slope of `V` over `K`
  have hpt : ∀ Y ∈ ball (0 : Rd d) 1, Tendsto (fun k => F k Y) atTop (𝓝 (V Y)) := fun Y hY =>
    (hconv ‖Y‖ (mem_ball_zero_iff.1 hY)).tendsto_at (mem_closedBall_zero_iff.2 le_rfl)
  have hlimsup : (⋂ N, T N) ⊆ slopeSet V Kb := by
    intro q hq
    have hfreq : ∃ᶠ k in atTop, 1 ≤ k ∧ q ∈ S k := by
      rw [Filter.frequently_atTop]
      intro N
      have := Set.mem_iInter.1 hq N
      simp only [T, Set.mem_iUnion] at this
      obtain ⟨k, hk, hqk⟩ := this
      exact ⟨k, by omega, by omega, hqk⟩
    obtain ⟨ψ, hψ, hψq⟩ := Filter.extraction_of_frequently_atTop hfreq
    choose X hXK hXaff using fun j => hS_aff (ψ j) (hψq j).1 q (hψq j).2
    obtain ⟨X₀, hX₀K, χ, hχ, hXlim⟩ := (isCompact_closedBall c r).tendsto_subseq hXK
    refine ⟨X₀, hX₀K, fun Y hY => ?_⟩
    have hkk : StrictMono (fun j => ψ (χ j)) := hψ.comp hχ
    have hkkt : Tendsto (fun j => ψ (χ j)) atTop atTop := hkk.tendsto_atTop
    have hY1 : Tendsto (fun j => F (ψ (χ j)) Y) atTop (𝓝 (V Y)) := (hpt Y hY).comp hkkt
    have hXlim' : Tendsto (fun j => X (χ j)) atTop (𝓝 X₀) := hXlim
    have hX1 : Tendsto (fun j => F (ψ (χ j)) (X (χ j))) atTop (𝓝 (V X₀)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have hA : Tendsto (fun j => (L.toNNReal : ℝ) * dist (X (χ j)) X₀) atTop (𝓝 0) := by
        have := (tendsto_iff_dist_tendsto_zero.1 hXlim').const_mul (L.toNNReal : ℝ)
        rwa [mul_zero] at this
      have hB : Tendsto (fun j => dist (F (ψ (χ j)) X₀) (V X₀)) atTop (𝓝 0) :=
        tendsto_iff_dist_tendsto_zero.1 ((hpt X₀ (hKsub hX₀K)).comp hkkt)
      have hAB := hA.add hB
      rw [add_zero] at hAB
      refine squeeze_zero' (Eventually.of_forall fun j => dist_nonneg) ?_ hAB
      filter_upwards [hkkt.eventually (eventually_ge_atTop k₀)] with j hj
      calc dist (F (ψ (χ j)) (X (χ j))) (V X₀)
          ≤ dist (F (ψ (χ j)) (X (χ j))) (F (ψ (χ j)) X₀) + dist (F (ψ (χ j)) X₀) (V X₀) :=
            dist_triangle _ _ _
        _ ≤ (L.toNNReal : ℝ) * dist (X (χ j)) X₀ + dist (F (ψ (χ j)) X₀) (V X₀) := by
            gcongr
            exact (hLip _ hj).dist_le_mul _ (hKsubδ (hXK (χ j))) _ (hKsubδ hX₀K)
    have hδY : max ‖Y‖ δ < 1 := max_lt (mem_ball_zero_iff.1 hY) hδ1
    have hhY : ∀ᶠ j in atTop, (n (ψ (χ j)) : ℝ) • Y ∈
        convexHull ℝ (toE '' dClosure (ballZ0 (d := d) (n (ψ (χ j)) : ℝ))) :=
      ((hntend.comp hkkt).eventually (hull_eventually hd1 hδY)).mono fun j hj =>
        hj Y (mem_closedBall_zero_iff.2 (le_max_left _ _))
    have hineq : ∀ᶠ j in atTop,
        F (ψ (χ j)) Y ≤ F (ψ (χ j)) (X (χ j)) + inner ℝ q (Y - X (χ j)) :=
      hhY.mono fun j hj => hXaff (χ j) Y hj
    have hlim2 : Tendsto (fun j => F (ψ (χ j)) (X (χ j)) + inner ℝ q (Y - X (χ j))) atTop
        (𝓝 (V X₀ + inner ℝ q (Y - X₀))) :=
      hX1.add (tendsto_const_nhds.inner (tendsto_const_nhds.sub hXlim'))
    exact le_of_tendsto_of_tendsto hY1 hlim2 hineq
  -- lower bound on the tails
  set ω := volume.real (ball (0 : Rd d) 1) with hω
  have hcount := (tendsto_ncard_ball_div_pow (d := d) hd1).comp hntend
  have hTlow : ∀ N, ∀ ε : ℝ, 0 < ε →
      ENNReal.ofReal ((α * r ^ d - 2 * ε) * ω) ≤ volume (T N) := by
    intro N ε hε
    have hmass := hntend.eventually (mass_closedBall_lower hd1 hnear hann hα.le hr hKsub hε)
    have hev : ∀ᶠ k in atTop, ENNReal.ofReal ((α * r ^ d - 2 * ε) *
        (((ballZ0 (d := d) (n k : ℝ)).ncard : ℝ) / (n k : ℝ) ^ d)) ≤ volume (T N) := by
      filter_upwards [hmass, eventually_ge_atTop (N + 1)] with k hk hkN
      have hk1 : 1 ≤ k := by omega
      have hnk : (0 : ℝ) < n k := by exact_mod_cast hn1 k hk1
      calc ENNReal.ofReal ((α * r ^ d - 2 * ε) *
              (((ballZ0 (d := d) (n k : ℝ)).ncard : ℝ) / (n k : ℝ) ^ d))
          = ENNReal.ofReal |((n k : ℝ) ^ d)⁻¹| *
              ENNReal.ofReal ((α * r ^ d - 2 * ε) * ((ballZ0 (d := d) (n k : ℝ)).ncard : ℝ)) := by
            rw [← ENNReal.ofReal_mul (abs_nonneg _),
              abs_of_pos (by positivity : (0 : ℝ) < ((n k : ℝ) ^ d)⁻¹)]
            congr 1; ring
        _ ≤ ENNReal.ofReal |((n k : ℝ) ^ d)⁻¹| * volume (U k) := by gcongr
        _ = volume (S k) := (hvolS k hk1).symm
        _ ≤ volume (T N) := measure_mono fun q hq => Set.mem_iUnion₂.2 ⟨k, hkN, hq⟩
    have hlimit : Tendsto (fun k => ENNReal.ofReal ((α * r ^ d - 2 * ε) *
        (((ballZ0 (d := d) (n k : ℝ)).ncard : ℝ) / (n k : ℝ) ^ d))) atTop
        (𝓝 (ENNReal.ofReal ((α * r ^ d - 2 * ε) * ω))) :=
      ENNReal.tendsto_ofReal (hcount.const_mul _)
    exact le_of_tendsto hlimit hev
  have hall : ∀ ε : ℝ, 0 < ε →
      ENNReal.ofReal ((α * r ^ d - 2 * ε) * ω) ≤ volume (slopeSet V Kb) := by
    intro ε hε
    calc _ ≤ ⨅ N, volume (T N) := le_iInf fun N => hTlow N ε hε
      _ = volume (⋂ N, T N) := hInter.symm
      _ ≤ _ := measure_mono hlimsup
  have hvolK : ENNReal.ofReal α * volume Kb = ENNReal.ofReal (α * (r ^ d * ω)) := by
    have hB1 : volume (ball (0 : Rd d) 1) = ENNReal.ofReal ω := by
      rw [hω, measureReal_def, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
    rw [hKb, Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, hB1,
      ← ENNReal.ofReal_mul (pow_nonneg hr.le d), ← ENNReal.ofReal_mul hα.le]
  rw [hvolK]
  have htend : Tendsto (fun ε : ℝ => ENNReal.ofReal ((α * r ^ d - 2 * ε) * ω)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (α * (r ^ d * ω)))) := by
    apply ENNReal.tendsto_ofReal
    have h : Tendsto (fun ε : ℝ => (α * r ^ d - 2 * ε) * ω) (𝓝 0)
        (𝓝 ((α * r ^ d - 2 * 0) * ω)) :=
      ((continuous_const.sub (continuous_const.mul continuous_id)).mul continuous_const).tendsto 0
    rw [show (α * r ^ d - 2 * 0) * ω = α * (r ^ d * ω) by ring] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  exact le_of_tendsto htend (eventually_nhdsWithin_of_forall fun ε hε => hall ε hε)

end RandomSandpile

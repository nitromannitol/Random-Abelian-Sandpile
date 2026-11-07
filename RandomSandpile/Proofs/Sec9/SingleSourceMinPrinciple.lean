import RandomSandpile.Proofs.Sec9.OpenBoundaryMaxPrinciple
import RandomSandpile.Proofs.Sec9.SingleSource
import RandomSandpile.Proofs.Sec7.MainTheoremUInterior

/-! # Theorem 9.2, step: the minimum principle off the origin

`ssInteriorMinPrinciple_of_compactness : MuConvergenceStmt → SSCompactnessStmt →
SSInteriorMinPrincipleStmt`, the argument of Theorem 9.1's `openInteriorMinPrinciple_of_muConvergence`
for the single-source odometers `v_n` (least stabilizing toppling of `η + n δ_0` on `ℤ^d`):

* the rescaling `v̄_n(x) = n^{-2/d} v_n([n^{1/d} x])` is compared with the integer-scale rescaling
  `m^{-2} v_n([m x])`, `m = ⌊n^{1/d}⌋` (`rescaleOdo_eq`); since `m / n^{1/d} → 1` and the limit is
  continuous, the integer-scale rescalings converge uniformly on a slightly smaller ball
  (`tendstoUniformlyOn_rescale`);
* the restriction of `v_n` to `mB_r(a) ∩ ℤ^d`, a set avoiding the origin, is a stabilizing
  toppling for `η` there, so its perturbed supergradient mass is at most `μ*`
  (`volume_le_muStar_of_restrict`), and `μ*(l, M) = 0` with Lemma 5.5 makes it `o(m^d)`;
* the rescaled ABP estimate (`principle_generic_on`, the core `principle_generic` of Theorem 9.1
  with uniform convergence and continuity only on a closed ball) concludes.

Continuity of the limit off the origin comes from step, `SSCompactnessStmt`: a further
subsequence converges to `v + G` with `v` continuous.
-/

open MeasureTheory LatticeProb Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

namespace SingleSourceMin

open OpenMaxPrinciple

variable {d : ℕ}

/-- `principle_generic` (`Proofs/Sec9/OpenBoundaryMaxPrincipleCore.lean`) with uniform convergence
and continuity of the limit only on a closed ball `B̄_{r'}(a)`, `r' > r`, and scales `n_k → ∞`. -/
theorem principle_generic_on (hd : 1 ≤ d) {σ : ℝ} {Q v : Rd d → ℝ} (hQ : Continuous Q)
    {a : Rd d} {r r' : ℝ} (hr : 0 < r) (hrr' : r < r')
    (hv : ContinuousOn v (closedBall a r')) {nk : ℕ → ℕ} (hnk : Tendsto nk atTop atTop)
    {vk : ℕ → Site d → ℤ}
    (hconv : TendstoUniformlyOn (fun k => rescaleOdo (vk k) (nk k)) v atTop (closedBall a r'))
    {V : ℕ → ℝ≥0∞}
    (hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => σ * ((vk k z : ℝ) -
        (nk k : ℝ) ^ 2 * Q ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball a r) (nk k))) ≤ V k ∧
        V k ≠ ⊤)
    (hV : Tendsto (fun k => (V k).toReal / (nk k : ℝ) ^ d) atTop (𝓝 0))
    {x : Rd d} (hx : x ∈ ball a r) :
    ∃ y ∈ sphere a r, σ * (v x - Q x) ≤ σ * (v y - Q y) := by
  obtain ⟨c, hc, habp⟩ := abp_general (d := d) hd
  have hntop : Tendsto nk atTop atTop := hnk
  have hnt : Tendsto (fun k => (nk k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hntop
  set g : ℕ → Site d → ℝ := fun k z =>
    σ * ((vk k z : ℝ) - (nk k : ℝ) ^ 2 * Q ((nk k : ℝ)⁻¹ • toE z)) with hg
  set zk : ℕ → Site d := fun k => latticeRound ((nk k : ℝ) • x) with hzk
  set F : ℕ → Rd d → ℝ := fun k => rescaleOdo (vk k) (nk k) with hF
  -- rescaled lattice points converge to `x`
  have hz : Tendsto (fun k => (nk k : ℝ)⁻¹ • toE (zk k)) atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ k in atTop,
        ‖(nk k : ℝ)⁻¹ • toE (zk k) - x‖ ≤ ((d : ℝ) + 1) * (nk k : ℝ)⁻¹ := by
      filter_upwards [hntop.eventually (eventually_ge_atTop 1)] with k hk
      have hn0 : (nk k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hnpos : (0 : ℝ) < nk k := by exact_mod_cast hk
      have : (nk k : ℝ)⁻¹ • toE (zk k) - x = (nk k : ℝ)⁻¹ • (toE (zk k) - (nk k : ℝ) • x) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hn0, one_smul]
      rw [this, norm_smul, norm_inv, Real.norm_of_nonneg hnpos.le, mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_toE_latticeRound_sub_le _) (by positivity)
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) hb ?_
    have := (tendsto_inv_atTop_zero.comp hnt).const_mul ((d : ℝ) + 1)
    rwa [mul_zero] at this
  -- eventually the discrete ABP applies at `z_k`
  have hev : ∀ᶠ k in atTop, 1 ≤ nk k ∧ ∃ y ∈ bdry (discretize (ball a r) (nk k)),
      g k (zk k) ≤ g k y + c * ((2 * r + 1) * (nk k : ℝ)) * (V k).toReal ^ (1 / (d : ℝ)) := by
    have hzin : ∀ᶠ k in atTop, (nk k : ℝ)⁻¹ • toE (zk k) ∈ ball a r :=
      hz.eventually (isOpen_ball.mem_nhds hx)
    filter_upwards [hvol, hzin, hntop.eventually (eventually_ge_atTop 1)] with k hk hzk' hk1
    have hn0 : nk k ≠ 0 := by omega
    have hzD : zk k ∈ discretize (ball a r) (nk k) := (mem_discretize_iff' hn0).2 hzk'
    have hfin : (discretize (ball a r) (nk k)).Finite :=
      SubadditiveLipschitz.discretize_finite isBounded_ball (nk k)
    obtain ⟨y, hy, hymax⟩ := exists_bdry_max hd hfin ⟨_, hzD⟩ (g k)
    have hpos : 0 < (2 * r + 1) * (nk k : ℝ) :=
      mul_pos (by linarith) (by exact_mod_cast hk1)
    exact ⟨hk1, y, hy, habp _ hfin (g k) _ hpos (zk k) hzD
      (fun z hz => norm_sub_le_of_mem_dClosure hk1 hzD hz) (V k) hk.1 hk.2 (g k y) hymax⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  have hch : ∀ k, ∃ y : Site d, K ≤ k → y ∈ bdry (discretize (ball a r) (nk k)) ∧
      g k (zk k) ≤ g k y + c * ((2 * r + 1) * (nk k : ℝ)) * (V k).toReal ^ (1 / (d : ℝ)) :=
    fun k => by
      by_cases hk : K ≤ k
      · obtain ⟨-, y, hy, h⟩ := hK k hk; exact ⟨y, fun _ => ⟨hy, h⟩⟩
      · exact ⟨0, fun h => absurd h hk⟩
  choose yk hyk using hch
  set Y : ℕ → Rd d := fun k => (nk k : ℝ)⁻¹ • toE (yk k) with hY
  set err : ℕ → ℝ := fun k => c * (2 * r + 1) * ((V k).toReal / (nk k : ℝ) ^ d) ^ (1 / (d : ℝ))
    with herr
  -- the rescaled inequality
  have hres : ∀ k, K ≤ k → σ * (F k x - Q ((nk k : ℝ)⁻¹ • toE (zk k))) ≤
      σ * (F k (Y k) - Q (Y k)) + err k := by
    intro k hk
    have hk1 := (hK k hk).1
    have hn0 : nk k ≠ 0 := by omega
    have hnpos : (0 : ℝ) < nk k := by exact_mod_cast hk1
    have h := (hyk k hk).2
    have hFx : F k x = (vk k (zk k) : ℝ) / (nk k : ℝ) ^ 2 := rfl
    have hFy : F k (Y k) = (vk k (yk k) : ℝ) / (nk k : ℝ) ^ 2 := by
      simp only [F, Y, rescaleOdo, latticeRound_smul_inv_smul_toE hn0]
    have hV0 : 0 ≤ (V k).toReal := ENNReal.toReal_nonneg
    have herrk : err k * (nk k : ℝ) ^ 2 =
        c * ((2 * r + 1) * (nk k : ℝ)) * (V k).toReal ^ (1 / (d : ℝ)) := by
      have hd0 : d ≠ 0 := by omega
      have hroot : ((nk k : ℝ) ^ d) ^ (1 / (d : ℝ)) = nk k := by
        rw [one_div]; exact Real.pow_rpow_inv_natCast hnpos.le hd0
      simp only [err]
      rw [Real.div_rpow hV0 (by positivity), hroot]
      field_simp
    have hn2 : (0 : ℝ) < (nk k : ℝ) ^ 2 := by positivity
    rw [hFx, hFy]
    have key : g k (zk k) / (nk k : ℝ) ^ 2 ≤ g k (yk k) / (nk k : ℝ) ^ 2 + err k := by
      rw [div_add' _ _ _ hn2.ne', div_le_div_iff_of_pos_right hn2, herrk]
      exact h
    have e1 : g k (zk k) / (nk k : ℝ) ^ 2 =
        σ * ((vk k (zk k) : ℝ) / (nk k : ℝ) ^ 2 - Q ((nk k : ℝ)⁻¹ • toE (zk k))) := by
      simp only [g]; field_simp
    have e2 : g k (yk k) / (nk k : ℝ) ^ 2 =
        σ * ((vk k (yk k) : ℝ) / (nk k : ℝ) ^ 2 - Q (Y k)) := by
      simp only [g, Y]; field_simp
    rw [e1, e2] at key
    exact key
  -- the boundary points lie in shrinking annuli
  have hann : ∀ k, K ≤ k → r ≤ ‖Y k - a‖ ∧ ‖Y k - a‖ < r + 1 / (nk k : ℝ) := fun k hk =>
    bdry_rescaled (hK k hk).1 (hyk k hk).1
  have hmem : ∀ j, Y (j + K) ∈ closedBall a (r + 1) := by
    intro j
    obtain ⟨-, h2⟩ := hann (j + K) (by omega)
    have hk1 := (hK (j + K) (by omega)).1
    have : 1 / (nk (j + K) : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hk1)]; exact_mod_cast hk1
    rw [mem_closedBall, dist_eq_norm]; linarith
  obtain ⟨y, -, ψ, hψ, hYlim⟩ := (isCompact_closedBall a (r + 1)).tendsto_subseq hmem
  set kj : ℕ → ℕ := fun j => ψ j + K with hkj
  have hkjt : Tendsto kj atTop atTop :=
    tendsto_atTop_mono (fun j => (hψ.id_le j).trans (Nat.le_add_right _ _)) tendsto_id
  have hYlim' : Tendsto (fun j => Y (kj j)) atTop (𝓝 y) := hYlim
  have hnkj : Tendsto (fun j => (nk (kj j) : ℝ)) atTop atTop := hnt.comp hkjt
  -- the limit point is on the sphere
  have hysph : y ∈ sphere a r := by
    have hnorm : Tendsto (fun j => ‖Y (kj j) - a‖) atTop (𝓝 ‖y - a‖) :=
      (hYlim'.sub_const a).norm
    have hlo : r ≤ ‖y - a‖ :=
      ge_of_tendsto hnorm (Eventually.of_forall fun j => (hann (kj j) (Nat.le_add_left _ _)).1)
    have hup : ‖y - a‖ ≤ r := by
      have hb : Tendsto (fun j => r + 1 / (nk (kj j) : ℝ)) atTop (𝓝 (r + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hnkj)
      rw [add_zero] at hb
      exact le_of_tendsto_of_tendsto hnorm hb
        (Eventually.of_forall fun j => (hann (kj j) (Nat.le_add_left _ _)).2.le)
    rw [mem_sphere, dist_eq_norm]; exact le_antisymm hup hlo
  refine ⟨y, hysph, ?_⟩
  -- pass to the limit along `kj`
  have hFunif : TendstoUniformlyOn (fun j => F (kj j)) v atTop (closedBall a r') := fun u hu =>
    hkjt.eventually (hconv u hu)
  have hys' : y ∈ closedBall a r' := by
    rw [mem_sphere] at hysph; rw [mem_closedBall]; linarith
  have hYs : Tendsto (fun j => Y (kj j)) atTop (𝓝[closedBall a r'] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hYlim', ?_⟩
    have hsmall : ∀ᶠ j in atTop, 1 / (nk (kj j) : ℝ) < r' - r :=
      (tendsto_const_nhds.div_atTop hnkj).eventually (gt_mem_nhds (by linarith))
    filter_upwards [hsmall] with j hj
    have := (hann (kj j) (Nat.le_add_left _ _)).2
    rw [mem_closedBall, dist_eq_norm]; linarith
  have hL : Tendsto (fun j => σ * (F (kj j) x - Q ((nk (kj j) : ℝ)⁻¹ • toE (zk (kj j)))))
      atTop (𝓝 (σ * (v x - Q x))) :=
    (((hconv.tendsto_at (ball_subset_closedBall.trans (closedBall_subset_closedBall hrr'.le) hx)).comp hkjt).sub ((hQ.tendsto x).comp (hz.comp hkjt))).const_mul σ
  have herr0 : Tendsto (fun j => err (kj j)) atTop (𝓝 0) := by
    have hdpos : (0 : ℝ) < 1 / (d : ℝ) := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    have h1 := ((Real.continuousAt_rpow_const 0 (1 / (d : ℝ)) (Or.inr hdpos.le)).tendsto.comp
      (hV.comp hkjt)).const_mul (c * (2 * r + 1))
    rw [Real.zero_rpow hdpos.ne', mul_zero] at h1
    exact h1
  have hR : Tendsto (fun j => σ * (F (kj j) (Y (kj j)) - Q (Y (kj j))) + err (kj j)) atTop
      (𝓝 (σ * (v y - Q y) + 0)) :=
    (((hFunif.tendsto_comp (hv.continuousWithinAt hys') hYs).sub
      ((hQ.tendsto y).comp hYlim')).const_mul σ).add herr0
  rw [add_zero] at hR
  exact le_of_tendsto_of_tendsto hL hR (Eventually.of_forall fun j => hres (kj j) (Nat.le_add_left _ _))



/-- The fundamental solution is continuous off the origin. -/
theorem continuousOn_fundamentalSolution (d : ℕ) :
    ContinuousOn (fundamentalSolution d) {x : Rd d | x ≠ 0} := by
  intro x hx
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  refine ContinuousAt.continuousWithinAt ?_
  by_cases h2 : d = 2
  · have e : fundamentalSolution d = fun y : Rd d => -(1 / (2 * Real.pi)) * Real.log ‖y‖ := by
      funext y; simp only [fundamentalSolution, if_pos h2]
    rw [e]
    exact continuousAt_const.mul ((Real.continuousAt_log hx0).comp continuous_norm.continuousAt)
  · have e : fundamentalSolution d = fun y : Rd d =>
        ‖y‖ ^ (2 - (d : ℝ)) / ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d) := by
      funext y; simp only [fundamentalSolution, if_neg h2]
    rw [e]
    exact ((Real.continuousAt_rpow_const ‖x‖ (2 - (d : ℝ)) (Or.inl hx0)).comp
      continuous_norm.continuousAt).div_const _

/-- The single-source rescaling at scale `n^{1/d}` against the integer scale `m`. -/
theorem rescaleOdo_eq (v : Site d → ℤ) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (y : Rd d) :
    rescaleOdo v m y = ((n : ℝ) ^ (1 / (d : ℝ)) / m) ^ 2 *
      rescaleSingleSource v n (((m : ℝ) / (n : ℝ) ^ (1 / (d : ℝ))) • y) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hhpos : 0 < (n : ℝ) ^ (1 / (d : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hsm : (n : ℝ) ^ (1 / (d : ℝ)) • (((m : ℝ) / (n : ℝ) ^ (1 / (d : ℝ))) • y) =
      (m : ℝ) • y := by
    rw [smul_smul, mul_div_cancel₀ _ hhpos.ne']
  have hpow : (n : ℝ) ^ (-(2 / (d : ℝ))) = (((n : ℝ) ^ (1 / (d : ℝ))) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hnpos.le, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    congr 2
    push_cast
    ring
  simp only [rescaleOdo, rescaleSingleSource, hsm, hpow]
  have hh0 := hhpos.ne'
  field_simp

/-- Uniform convergence survives a rescaling of the argument and of the values by factors
tending to `1`, on a smaller closed ball, when the limit is continuous. -/
theorem tendstoUniformlyOn_rescale {F : ℕ → Rd d → ℝ} {u : Rd d → ℝ} {a : Rd d} {r₁ r₂ : ℝ}
    (h12 : r₁ < r₂) (hu : ContinuousOn u (closedBall a r₂))
    (hF : TendstoUniformlyOn F u atTop (closedBall a r₂))
    {c t : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 1)) (ht : Tendsto t atTop (𝓝 1)) :
    TendstoUniformlyOn (fun k y => c k * F k (t k • y)) u atTop (closedBall a r₁) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hK := isCompact_closedBall a r₂
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hu
  set B' := max B 0 with hB'
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hu) (ε / 3) (by positivity)
  set R := ‖a‖ + |r₁| + 1 with hR
  have hRpos : 0 < R := by positivity
  have hmin : 0 < min δ (r₂ - r₁) := lt_min hδ (by linarith)
  have ht' : ∀ᶠ k in atTop, |t k - 1| * R < min δ (r₂ - r₁) := by
    have h := ((ht.sub_const 1).abs.mul_const R)
    rw [sub_self, abs_zero, zero_mul] at h
    exact h.eventually (gt_mem_nhds hmin)
  have hc' : ∀ᶠ k in atTop, |c k - 1| * (B' + 1) < ε / 3 := by
    have h := ((hc.sub_const 1).abs.mul_const (B' + 1))
    rw [sub_self, abs_zero, zero_mul] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  have hF' := Metric.tendstoUniformlyOn_iff.1 hF (min (ε / 3) 1) (by positivity)
  filter_upwards [ht', hc', hF'] with k htk hck hFk y hy
  have hyn : ‖y‖ ≤ R := by
    have h1 : ‖y‖ ≤ ‖a‖ + dist y a := by
      rw [dist_eq_norm]
      calc ‖y‖ = ‖a + (y - a)‖ := by rw [add_sub_cancel]
        _ ≤ ‖a‖ + ‖y - a‖ := norm_add_le _ _
    have h2 : dist y a ≤ r₁ := hy
    have h3 := le_abs_self r₁
    linarith
  have hty : dist (t k • y) y < min δ (r₂ - r₁) := by
    rw [dist_eq_norm, show t k • y - y = (t k - 1) • y by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs]
    calc |t k - 1| * ‖y‖ ≤ |t k - 1| * R := mul_le_mul_of_nonneg_left hyn (abs_nonneg _)
      _ < _ := htk
  have hts : t k • y ∈ closedBall a r₂ := by
    have hy' : dist y a ≤ r₁ := hy
    rw [mem_closedBall]
    calc dist (t k • y) a ≤ dist (t k • y) y + dist y a := dist_triangle _ _ _
      _ ≤ (r₂ - r₁) + r₁ := add_le_add (hty.le.trans (min_le_right _ _)) hy'
      _ = r₂ := by ring
  have hys : y ∈ closedBall a r₂ := closedBall_subset_closedBall h12.le hy
  have h1 := hFk _ hts
  have h2 := hδu _ hts _ hys (hty.trans_le (min_le_left _ _))
  have h3 := hB _ hts
  rw [Real.dist_eq] at h1 h2 ⊢
  rw [Real.norm_eq_abs] at h3
  have h1a : |u (t k • y) - F k (t k • y)| < ε / 3 := h1.trans_le (min_le_left _ _)
  have h1b : |u (t k • y) - F k (t k • y)| < 1 := h1.trans_le (min_le_right _ _)
  have hFb : |F k (t k • y)| ≤ B' + 1 := by
    have e : F k (t k • y) = u (t k • y) - (u (t k • y) - F k (t k • y)) := by ring
    rw [e]
    calc |u (t k • y) - (u (t k • y) - F k (t k • y))|
        ≤ |u (t k • y)| + |u (t k • y) - F k (t k • y)| := abs_sub _ _
      _ ≤ B' + 1 := add_le_add (h3.trans (le_max_left _ _)) h1b.le
  have h4 : |(1 - c k) * F k (t k • y)| ≤ |c k - 1| * (B' + 1) := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hFb (abs_nonneg _)
  have h2' : |u y - u (t k • y)| < ε / 3 := by rw [abs_sub_comm]; exact h2
  have e : u y - c k * F k (t k • y) =
      (u y - u (t k • y)) + (u (t k • y) - F k (t k • y)) + (1 - c k) * F k (t k • y) := by ring
  rw [e]
  calc _ ≤ |u y - u (t k • y)| + |u (t k • y) - F k (t k • y)| +
        |(1 - c k) * F k (t k • y)| := abs_add_three _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- The mass of the negated perturbed function of a stabilizing toppling of `B` is at most
`μ*` (`volume_le_muStar` with the restriction given directly). -/
theorem volume_le_muStar_of_restrict {η : Site d → ℤ} {B : Set (Site d)} {v : Site d → ℤ}
    (hv : (dClosure B).indicator v ∈ stabilizing η B) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    {g : Site d → ℝ} (c : Rd d) (c0 : ℝ)
    (hg : ∀ z ∈ dClosure B,
      g z = -((v z : ℝ) - (qlZ l z + qMZ M z)) + inner ℝ c (toE z) + c0) :
    volume (supGradSet g B) ≤ muStar B η l M := by
  set w' : Site d → ℝ := fun z => (((dClosure B).indicator v z : ℤ) : ℝ) - (qlZ l z + qMZ M z)
  have hw' : w' ∈ perturbedSuper B η l M := mem_perturbedSuper.2 ⟨_, hv, rfl⟩
  rw [volume_supGradSet_affine (w₂ := fun z => -w' z) c c0 (fun z hz => by
    rw [hg z hz]; simp only [w', Set.indicator_of_mem hz]), ← subGradNegVolume d w' B]
  exact le_iSup₂_of_le w' hw' le_rfl

end SingleSourceMin

open SingleSourceMin OpenMaxPrinciple

/-- **Step of Theorem 9.2** (`SSInteriorMinPrincipleStmt`) from Lemma 5.5 and step. -/
theorem ssInteriorMinPrinciple_of_compactness (hconv : MuConvergenceStmt)
    (hComp : SSCompactnessStmt) : SSInteriorMinPrincipleStmt := by
  intro d hd E hE l M hM hμ
  have hd1 : 1 ≤ d := by omega
  filter_upwards [(hconv d hd).1 E M hM l, ae_all_iff.2 E.bounded] with η hη hbd
  rintro u ⟨nk, hnk, hconvu⟩ a p r hr hball x hx
  have hbd' : ∀ z, E.ηmin ≤ η z ∧ η z ≤ 2 * (d : ℤ) - 2 := fun z =>
    ⟨(hbd z).1, (hbd z).2.trans hE.le⟩
  obtain ⟨φ, hφ, v, hvc, hconvφ⟩ := hComp d hd E.ηmin η hbd' nk hnk
  have hopen : IsOpen {x : Rd d | x ≠ 0} := isOpen_ne
  have huv : Set.EqOn u (fun y => v y + fundamentalSolution d y) {x : Rd d | x ≠ 0} :=
    fun y hy =>
      tendsto_nhds_unique ((hconvu.tendsto_at hy).comp hφ.tendsto_atTop) (hconvφ.tendsto_at hy)
  have hucont : ContinuousOn u {x : Rd d | x ≠ 0} :=
    (hvc.continuousOn.add (continuousOn_fundamentalSolution d)).congr huv
  by_cases hxs : x ∈ sphere a r
  · exact ⟨x, hxs, le_rfl⟩
  have hxb : x ∈ ball a r := by
    rw [mem_closedBall] at hx; rw [mem_sphere] at hxs; rw [mem_ball]; exact lt_of_le_of_ne hx hxs
  -- radii `r < r₁ < r₂ < ‖a‖`
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
  -- the integer scales `m_k = ⌊n_k^{1/d}⌋`
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
  -- Lemma 5.5 on the ball: `μ* / m^d → 0`
  obtain ⟨hfinμ, -, hlimμ⟩ := hη (ball a r) (StrictConcavityBall.isLipschitzDomain_ball a hr)
  rw [hμ] at hlimμ
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
    have hne := ssNonempty d hd1 η (fun z => (hbd' z).2) (nk k)
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
    refine ⟨volume_le_muStar_of_restrict hres' l M c c0 (fun z _ => ?_), (hfinμ (mk k)).2⟩
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

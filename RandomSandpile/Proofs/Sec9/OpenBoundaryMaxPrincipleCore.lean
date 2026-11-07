import RandomSandpile.Proofs.Sec9.OpenBoundary
import RandomSandpile.Proofs.Sec5.ABP
import RandomSandpile.Infra.SubadditiveLipschitz
import RandomSandpile.Defs.Divisible

/-! # Interior maximum principles: the deterministic core

`principle_generic`: the rescaled form of Lemma 5.2. Let `v_k : ℤ^d → ℤ` with rescalings
`v̄_k = n_k⁻² v_k([n_k ·])` converging uniformly to a continuous `v`, let `Q` be continuous and
`σ ∈ ℝ`. If the functions `g_k = σ (v_k - n_k² Q(·/n_k))` on `D_k = n_k B_r(a) ∩ ℤ^d` have
supergradient mass `V_k` with `V_k / n_k^d → 0`, then for every `x ∈ B_r(a)` some `y ∈ ∂B_r(a)` has
`σ (v - Q)(x) ≤ σ (v - Q)(y)`.

Ingredients: the ABP estimate on an arbitrary finite set (`abp_general`, from the proved steps
`tiltedPlaneAbove`, `slidePlane`, `ballVolumeRadius` of Lemma 5.2), a maximizing boundary point
(`exists_bdry_max`), rescaling, and compactness of the shrinking annuli. -/

open MeasureTheory LatticeProb Filter Metric
open scoped Topology ENNReal

namespace RandomSandpile

namespace OpenMaxPrinciple

variable {d : ℕ}

/-- The ABP estimate on an arbitrary finite set `A` of diameter `≤ D` around `x`. -/
theorem abp_general (hd : 1 ≤ d) : ∃ c : ℝ, 0 < c ∧ ∀ (A : Set (Site d)), A.Finite →
    ∀ (w : Site d → ℝ) (D : ℝ), 0 < D → ∀ x ∈ A, (∀ z ∈ dClosure A, ‖toE z - toE x‖ ≤ D) →
      ∀ V : ℝ≥0∞, volume (supGradSet w A) ≤ V → V ≠ ⊤ →
        ∀ S : ℝ, (∀ z ∈ bdry A, w z ≤ S) → w x ≤ S + c * D * V.toReal ^ (1 / (d : ℝ)) := by
  obtain ⟨c, hc, hrad⟩ := ballVolumeRadius d hd
  refine ⟨c, hc, fun A hA w D hD x hx hdiam V hV hVt S hSb => ?_⟩
  have hpow : 0 ≤ V.toReal ^ (1 / (d : ℝ)) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  by_cases ha : w x ≤ S
  · have : 0 ≤ c * D * V.toReal ^ (1 / (d : ℝ)) := by positivity
    linarith
  rw [not_le] at ha
  set r : ℝ := (w x - S) / D with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hD.le
  have hball : ball (0 : Rd d) r ⊆ supGradSet w A := by
    intro p hp
    rw [mem_ball_zero_iff] at hp
    have hpD : ‖p‖ * D < w x - S := by
      rw [hr, lt_div_iff₀ hD] at hp
      exact hp
    exact slidePlane d w A hA x hx p (tiltedPlaneAbove d w A x hx S D p hSb hdiam hpD)
  have hVle : (volume (supGradSet w A)).toReal ≤ V.toReal := ENNReal.toReal_mono hVt hV
  have hrle := hrad r hr0 _ hball (ne_top_of_le_ne_top hVt hV)
  have hmono : (volume (supGradSet w A)).toReal ^ (1 / (d : ℝ)) ≤ V.toReal ^ (1 / (d : ℝ)) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hVle (by positivity)
  have hrV : r ≤ c * V.toReal ^ (1 / (d : ℝ)) := hrle.trans (mul_le_mul_of_nonneg_left hmono hc.le)
  have hwx : w x - S = r * D := by rw [hr]; field_simp
  have : r * D ≤ c * V.toReal ^ (1 / (d : ℝ)) * D := mul_le_mul_of_nonneg_right hrV hD.le
  nlinarith

/-- Lattice neighbours are at Euclidean distance `1`. -/
theorem norm_toE_sub_of_adj {x y : Site d} (h : Adj y x) : ‖toE y - toE x‖ = 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [hi, ABP.toE_add]
    have : toE y - (toE y + toE (unit i)) = -toE (unit i) := by abel
    rw [this, norm_neg, ABP.norm_toE_unit]
  · rw [hi, ABP.toE_add, add_sub_cancel_left, ABP.norm_toE_unit]

/-- A finite nonempty set has a nonempty outer boundary, and a boundary point maximizing `w`. -/
theorem exists_bdry_max (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) (hne : A.Nonempty)
    (w : Site d → ℝ) : ∃ y ∈ bdry A, ∀ z ∈ bdry A, w z ≤ w y := by
  set i₀ : Fin d := ⟨0, by omega⟩
  obtain ⟨x, hx, hxmax⟩ := Set.exists_max_image A (fun z : Site d => z i₀) hA hne
  have hb : x + unit i₀ ∈ bdry A := by
    refine mem_bdry.2 ⟨fun hmem => ?_, x, hx, adj_add_unit x i₀⟩
    have h1 := hxmax _ hmem
    have h2 : (x + unit i₀) i₀ = x i₀ + 1 := by simp [unit]
    rw [h2] at h1
    omega
  have hfin : (bdry A).Finite := (dClosure_finite hA).subset fun z hz => by
    rw [dClosure_eq]; exact Or.inr hz
  exact Set.exists_max_image (bdry A) w hfin ⟨_, hb⟩

theorem mem_discretize_iff' {W : Set (Rd d)} {n : ℕ} (hn : n ≠ 0) {x : Site d} :
    x ∈ discretize W n ↔ (n : ℝ)⁻¹ • toE x ∈ W :=
  Set.mem_smul_set_iff_inv_smul_mem₀ (Nat.cast_ne_zero.2 hn) _ _

/-- Points of `D = nB_r(a) ∩ ℤ^d` and of its discrete closure: distances. -/
theorem norm_sub_le_of_mem_dClosure {a : Rd d} {r : ℝ} {n : ℕ} (hn : 1 ≤ n) {x z : Site d}
    (hx : x ∈ discretize (ball a r) n) (hz : z ∈ dClosure (discretize (ball a r) n)) :
    ‖toE z - toE x‖ ≤ (2 * r + 1) * n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hball : ∀ y ∈ discretize (ball a r) n, ‖toE y - (n : ℝ) • a‖ < r * n := by
    intro y hy
    have h := (mem_discretize_iff' (by omega : n ≠ 0)).1 hy
    rw [mem_ball, dist_eq_norm] at h
    have : toE y - (n : ℝ) • a = (n : ℝ) • ((n : ℝ)⁻¹ • toE y - a) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hn0, one_smul]
    rw [this, norm_smul, Real.norm_of_nonneg hnpos.le, mul_comm]
    exact mul_lt_mul_of_pos_right h hnpos
  have hxb := hball x hx
  rw [dClosure_eq] at hz
  rcases hz with hz | hz
  · have hzb := hball z hz
    calc ‖toE z - toE x‖ = ‖(toE z - (n : ℝ) • a) - (toE x - (n : ℝ) • a)‖ := by congr 1; abel
      _ ≤ ‖toE z - (n : ℝ) • a‖ + ‖toE x - (n : ℝ) • a‖ := norm_sub_le _ _
      _ ≤ (2 * r + 1) * n := by nlinarith
  · obtain ⟨-, z', hz', hadj⟩ := mem_bdry.1 hz
    have hzb := hball z' hz'
    have h1 := norm_toE_sub_of_adj hadj
    calc ‖toE z - toE x‖ = ‖(toE z - toE z') + (toE z' - (n : ℝ) • a) - (toE x - (n : ℝ) • a)‖ := by
          congr 1; abel
      _ ≤ ‖toE z - toE z'‖ + ‖toE z' - (n : ℝ) • a‖ + ‖toE x - (n : ℝ) • a‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ (2 * r + 1) * n := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith

/-- Boundary points of `nB_r(a) ∩ ℤ^d`, rescaled, lie in the annulus `r ≤ |Y - a| < r + 1/n`. -/
theorem bdry_rescaled {a : Rd d} {r : ℝ} {n : ℕ} (hn : 1 ≤ n) {y : Site d}
    (hy : y ∈ bdry (discretize (ball a r) n)) :
    r ≤ ‖(n : ℝ)⁻¹ • toE y - a‖ ∧ ‖(n : ℝ)⁻¹ • toE y - a‖ < r + 1 / n := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hyn, z, hz, hadj⟩ := mem_bdry.1 hy
  refine ⟨?_, ?_⟩
  · by_contra h
    rw [not_le] at h
    exact hyn ((mem_discretize_iff' hn0).2 (by rw [mem_ball, dist_eq_norm]; exact h))
  · have hz' := (mem_discretize_iff' hn0).1 hz
    rw [mem_ball, dist_eq_norm] at hz'
    have h1 := norm_toE_sub_of_adj hadj
    have h2 : ‖(n : ℝ)⁻¹ • toE y - (n : ℝ)⁻¹ • toE z‖ = 1 / n := by
      rw [← smul_sub, norm_smul, h1, norm_inv, Real.norm_natCast, mul_one, one_div]
    calc ‖(n : ℝ)⁻¹ • toE y - a‖ = ‖((n : ℝ)⁻¹ • toE y - (n : ℝ)⁻¹ • toE z) +
          ((n : ℝ)⁻¹ • toE z - a)‖ := by congr 1; abel
      _ ≤ ‖(n : ℝ)⁻¹ • toE y - (n : ℝ)⁻¹ • toE z‖ + ‖(n : ℝ)⁻¹ • toE z - a‖ := norm_add_le _ _
      _ < r + 1 / n := by rw [h2]; linarith

/-- **Rescaled ABP**, generic form (see the module docstring). -/
theorem principle_generic (hd : 1 ≤ d) {σ : ℝ} {Q v : Rd d → ℝ} (hQ : Continuous Q)
    (hv : Continuous v) {nk : ℕ → ℕ} (hnk : StrictMono nk) {vk : ℕ → Site d → ℤ}
    (hconv : TendstoUniformly (fun k => rescaleOdo (vk k) (nk k)) v atTop)
    {a : Rd d} {r : ℝ} (hr : 0 < r) {V : ℕ → ℝ≥0∞}
    (hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => σ * ((vk k z : ℝ) -
        (nk k : ℝ) ^ 2 * Q ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball a r) (nk k))) ≤ V k ∧
        V k ≠ ⊤)
    (hV : Tendsto (fun k => (V k).toReal / (nk k : ℝ) ^ d) atTop (𝓝 0))
    {x : Rd d} (hx : x ∈ ball a r) :
    ∃ y ∈ sphere a r, σ * (v x - Q x) ≤ σ * (v y - Q y) := by
  obtain ⟨c, hc, habp⟩ := abp_general (d := d) hd
  have hntop : Tendsto nk atTop atTop := hnk.tendsto_atTop
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
  have hFunif : TendstoUniformly (fun j => F (kj j)) v atTop := fun u hu =>
    hkjt.eventually (hconv u hu)
  have hL : Tendsto (fun j => σ * (F (kj j) x - Q ((nk (kj j) : ℝ)⁻¹ • toE (zk (kj j)))))
      atTop (𝓝 (σ * (v x - Q x))) :=
    (((hconv.tendsto_at x).comp hkjt).sub ((hQ.tendsto x).comp (hz.comp hkjt))).const_mul σ
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
    (((hFunif.tendsto_comp hv.continuousAt hYlim').sub
      ((hQ.tendsto y).comp hYlim')).const_mul σ).add herr0
  rw [add_zero] at hR
  exact le_of_tendsto_of_tendsto hL hR (Eventually.of_forall fun j => hres (kj j) (Nat.le_add_left _ _))

end OpenMaxPrinciple

end RandomSandpile

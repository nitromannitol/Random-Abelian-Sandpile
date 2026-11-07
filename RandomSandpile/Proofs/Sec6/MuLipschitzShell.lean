import RandomSandpile.Proofs.Sec6.StrictConcavity
import RandomSandpile.Proofs.Sec5.MuConvergenceRestrict
import RandomSandpile.Proofs.Sec6.MuLipschitz
import RandomSandpile.Proofs.Sec6.MuLipschitzAnnulus

/-! # The shell estimate from Lemma 5.5

`ShellBoundStmt` (Steps/Sec6/MuLipschitz.lean) from Lemma 5.5 (`MuConvergenceStmt`), applied on the
annulus `W = B_1 \ B̄_ρ`, `ρ < 1 - τ` close to `1 - τ`.

* Restriction. The shell `B_n \ B_{(1-τ)n}` lies in `D_n = nW ∩ ℤ^d ⊆ B_n`. Restricting
  `u ∈ 𝓛(η, B_n)` to `D̄_n` gives an element of `𝓛(η, D_n)` (`locLegalRestrict`), and testing on the
  smaller set `D̄_n` enlarges supergradients. So the supergradients of `w ∈ S(B_n, η, l, M)` at the
  shell have measure at most `μ(D_n, η, l, M)`. Dually for `S*`, by `stabilizingRestrict`.
* Lemma 5.5. `μ(D_n) / |D_n| → μ(l, M)`. The lemma is stated for symmetric `M`, and `q_M` only sees
  the symmetric part `(M + Mᵀ)/2` (`qMZ_symmPart`), so `μ` and `μ̄` do not change when `M` is
  replaced by its symmetric part.
* Counting. `|D_n| / |B_n| → |W| / |B_1| = 1 - ρ^d`, by `ZLattice.covolume.tendsto_card_div_pow'`;
  the frontier of `W` lies in two spheres, which are null.

The annulus is a bounded Lipschitz domain for `d ≥ 2` (`MuLipschitzAnnulus.annulus_isLipschitzDomain`).

Consequences: Lemma 6.3 (`muLipschitz_of_bending_of_muConvergence`) and the `β`-dependent Lemma 6.2
(`strictConcavityBeta_of_bending_of_muConvergence`) follow from Lemma 6.2' (`NearMaxBendingStmt`)
and Lemma 5.5 (`MuConvergenceStmt`). -/

open MeasureTheory LatticeProb Filter Metric Module
open scoped Topology Pointwise ENNReal Matrix

namespace RandomSandpile

namespace MuLipschitzShell

open MuLipschitz BallCount

variable {d : ℕ}

/-! ### Counting the lattice points of `nW` -/

/-- The lattice points of `W` at scale `1/n` are the rescaled points of `nW ∩ ℤ^d`. -/
theorem card_inter_eq_discretize (W : Set (Rd d)) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card ↥(W ∩ (n : ℝ)⁻¹ • (intLattice d : Set (Rd d))) = (discretize W n).ncard := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.card_coe_set_eq]
  have hset : W ∩ (n : ℝ)⁻¹ • (intLattice d : Set (Rd d)) =
      (fun z : Site d => (n : ℝ)⁻¹ • toE z) '' discretize W n := by
    ext v
    rw [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hn0.ne'), inv_inv,
      SetLike.mem_coe, mem_intLattice]
    constructor
    · rintro ⟨hv, hL⟩
      choose k hk using hL
      have hz : toE k = (n : ℝ) • v := by
        ext i
        simp [toE_apply, hk i]
      refine ⟨k, ?_, ?_⟩
      · show toE k ∈ (n : ℝ) • W
        rw [hz]
        exact Set.smul_mem_smul_set hv
      · simp only [hz, smul_smul, inv_mul_cancel₀ hn0.ne', one_smul]
    · rintro ⟨z, hz, rfl⟩
      have hz' : toE z ∈ (n : ℝ) • W := hz
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hn0.ne'] at hz'
      refine ⟨hz', fun i => ⟨z i, ?_⟩⟩
      simp [smul_smul, mul_inv_cancel₀ hn0.ne', toE_apply]
  rw [hset]
  exact Set.ncard_image_of_injective _
    ((smul_right_injective _ (inv_ne_zero hn0.ne')).comp toE_injective')

/-- `|nW ∩ ℤ^d| / n^d → |W| / covol(ℤ^d)` for bounded measurable `W` with null frontier. -/
theorem tendsto_ncard_discretize {W : Set (Rd d)} (hb : Bornology.IsBounded W)
    (hm : MeasurableSet W) (hf : volume (frontier W) = 0) :
    Tendsto (fun n : ℕ => ((discretize W n).ncard : ℝ) / (n : ℝ) ^ d) atTop
      (𝓝 (volume.real W / ZLattice.covolume (intLattice d))) := by
  have h := ZLattice.covolume.tendsto_card_div_pow' (intLattice d) hb hm hf
  rw [finrank_euclideanSpace_fin] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [card_inter_eq_discretize W hn]

/-- `|nW ∩ ℤ^d| / |B_n| → |W| / |B_1|`. -/
theorem tendsto_ncard_discretize_div_ball (hd : 1 ≤ d) {W : Set (Rd d)}
    (hb : Bornology.IsBounded W) (hm : MeasurableSet W) (hf : volume (frontier W) = 0) :
    Tendsto (fun n : ℕ => ((discretize W n).ncard : ℝ) / (ballZ0 (d := d) (n : ℝ)).ncard) atTop
      (𝓝 (volume.real W / volume.real (ball (0 : Rd d) 1))) := by
  haveI : NeZero d := ⟨by omega⟩
  have h1 := tendsto_ncard_discretize hb hm hf
  have h2 := tendsto_ncard_div_pow hd one_pos
  simp only [one_mul] at h2
  have hcov := ZLattice.covolume_pos (intLattice d)
  have hvol1 : 0 < volume.real (ball (0 : Rd d) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hlim := h1.div h2 (div_pos hvol1 hcov).ne'
  have heq : volume.real W / ZLattice.covolume (intLattice d) /
      (volume.real (ball (0 : Rd d) 1) / ZLattice.covolume (intLattice d)) =
      volume.real W / volume.real (ball (0 : Rd d) 1) := by
    field_simp
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnd : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (by exact_mod_cast hn) d
  simp only [Pi.div_apply]
  field_simp

/-! ### The annulus -/

/-- The open annulus `B_1 \ B̄_ρ`. -/
abbrev annulus (d : ℕ) (ρ : ℝ) : Set (Rd d) := ball (0 : Rd d) 1 \ closedBall 0 ρ

theorem volume_real_annulus {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    volume.real (annulus d ρ) = (1 - ρ ^ d) * volume.real (ball (0 : Rd d) 1) := by
  have hsub : closedBall (0 : Rd d) ρ ⊆ ball 0 1 := closedBall_subset_ball hρ1
  rw [measureReal_def, measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet
      measure_closedBall_lt_top.ne,
    ENNReal.toReal_sub_of_le (measure_mono hsub) measure_ball_lt_top.ne,
    Measure.addHaar_closedBall _ _ hρ0, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hρ0 d), measureReal_def]
  ring

theorem volume_frontier_annulus (hd : 1 ≤ d) (ρ : ℝ) :
    volume (frontier (annulus d ρ)) = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hopen : IsOpen (annulus d ρ) := isOpen_ball.sdiff isClosed_closedBall
  have hcl : closure (annulus d ρ) ⊆ closedBall 0 1 \ ball 0 ρ :=
    closure_minimal (Set.sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall)
      (isClosed_closedBall.sdiff isOpen_ball)
  refine measure_mono_null (t := sphere 0 1 ∪ sphere 0 ρ) ?_
    (measure_union_null (Measure.addHaar_sphere _ _ _) (Measure.addHaar_sphere _ _ _))
  intro x hx
  rw [hopen.frontier_eq] at hx
  obtain ⟨h1, h2⟩ := hcl hx.1
  have h3 := hx.2
  rw [mem_closedBall_zero_iff] at h1
  rw [mem_ball_zero_iff, not_lt] at h2
  simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_and, not_not] at h3
  rcases lt_or_eq_of_le h1 with h | h
  · exact Or.inr (mem_sphere_zero_iff_norm.2 (le_antisymm (h3 h) h2))
  · exact Or.inl (mem_sphere_zero_iff_norm.2 h)

/-! ### Symmetrization of `M` -/

/-- The symmetric part `(M + Mᵀ)/2` of `M`. -/
noncomputable def symmPart (M : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := (1 / 2 : ℝ) • (M + Mᵀ)

theorem symmPart_isSymm (M : Matrix (Fin d) (Fin d) ℝ) : (symmPart M).IsSymm := by
  unfold symmPart Matrix.IsSymm
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

/-- `q_M` only sees the symmetric part of `M`. -/
theorem qMZ_symmPart (M : Matrix (Fin d) (Fin d) ℝ) : qMZ (symmPart M) = qMZ M := by
  funext x
  have hT : WithLp.ofLp (toE x) ⬝ᵥ Mᵀ *ᵥ WithLp.ofLp (toE x) =
      WithLp.ofLp (toE x) ⬝ᵥ M *ᵥ WithLp.ofLp (toE x) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  simp only [qMZ, qM, symmPart, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul,
    dotProduct_add, smul_eq_mul, hT]
  ring

theorem mu_symmPart (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    mu A η l (symmPart M) = mu A η l M := by
  simp only [mu, perturbedSub, qMZ_symmPart]

theorem muStar_symmPart (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : muStar A η l (symmPart M) = muStar A η l M := by
  simp only [muStar, perturbedSuper, qMZ_symmPart]

theorem muBar_symmPart (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muBar E l (symmPart M) = muBar E l M := by
  simp only [muBar, mu_symmPart]

theorem muStarBar_symmPart (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStarBar E l (symmPart M) = muStarBar E l M := by
  simp only [muStarBar, muStar_symmPart]

/-! ### Restriction to a sub-domain -/

/-- Supergradients of `w ∈ S(B_n, η, l, M)` at points of `S ⊆ D ⊆ B_n` have measure at most
`μ(D, η, l, M)`. -/
theorem volume_supGrad_le_mu {η : Site d → ℤ} {l : ℝ} {M : Matrix (Fin d) (Fin d) ℝ}
    {A D S : Set (Site d)} (hD : D ⊆ A) (hS : S ⊆ D) {w : Site d → ℝ}
    (hw : w ∈ perturbedSub A η l M) :
    volume (⋃ x ∈ S, supGrad w x A) ≤ mu D η l M := by
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.1 hw
  have hw' : (fun x => (((dClosure D).indicator u x : ℤ) : ℝ) - (qlZ l x + qMZ M x)) ∈
      perturbedSub D η l M :=
    mem_perturbedSub.2 ⟨_, locLegalRestrict d η A D u hD hu, rfl⟩
  refine le_trans (measure_mono ?_) (le_iSup₂
    (f := fun w (_ : w ∈ perturbedSub D η l M) => volume (supGradSet w D)) _ hw')
  intro p hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨x, hx, hp⟩ := hp
  refine Set.mem_biUnion (hS hx) fun y hy => ?_
  have h := hp y (dClosure_mono hD hy)
  have hxD : x ∈ dClosure D := Or.inl (hS hx)
  simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hxD]
  exact h

/-- Dual of `volume_supGrad_le_mu`, by `stabilizingRestrict`. -/
theorem volume_subGrad_le_muStar {η : Site d → ℤ} {l : ℝ} {M : Matrix (Fin d) (Fin d) ℝ}
    {A D S : Set (Site d)} (hD : D ⊆ A) (hS : S ⊆ D) {w : Site d → ℝ}
    (hw : w ∈ perturbedSuper A η l M) :
    volume (⋃ x ∈ S, subGrad w x A) ≤ muStar D η l M := by
  obtain ⟨v, hv, rfl⟩ := mem_perturbedSuper.1 hw
  have hw' : (fun x => (((dClosure D).indicator v x : ℤ) : ℝ) - (qlZ l x + qMZ M x)) ∈
      perturbedSuper D η l M :=
    mem_perturbedSuper.2 ⟨_, stabilizingRestrict d η A D v hD hv, rfl⟩
  refine le_trans (measure_mono ?_) (le_iSup₂
    (f := fun w (_ : w ∈ perturbedSuper D η l M) => volume (subGradSet w D)) _ hw')
  intro p hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨x, hx, hp⟩ := hp
  refine Set.mem_biUnion (hS hx) fun y hy => ?_
  have h := hp y (dClosure_mono hD hy)
  have hxD : x ∈ dClosure D := Or.inl (hS hx)
  simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hxD]
  exact h

/-! ### Geometry of the shell -/

theorem shell_subset_discretize {τ ρ : ℝ} {n : ℕ} (hn : 1 ≤ n) (hρ : ρ < 1 - τ) :
    ballZ0 (d := d) (n : ℝ) \ ballZ0 ((1 - τ) * n) ⊆ discretize (annulus d ρ) n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  intro x ⟨hx1, hx2⟩
  have h1 := mem_ballZ0.1 hx1
  have h2 : (1 - τ) * n ≤ ‖toE x‖ := not_lt.1 fun h => hx2 (mem_ballZ0.2 h)
  show toE x ∈ (n : ℝ) • annulus d ρ
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hn0.ne']
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hn0]
    linarith
  · rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_natCast, not_le,
      lt_inv_mul_iff₀ hn0]
    nlinarith

theorem discretize_annulus_subset {ρ : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    discretize (annulus d ρ) n ⊆ ballZ0 (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  intro x hx
  have hx' : toE x ∈ (n : ℝ) • annulus d ρ := hx
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hn0.ne'] at hx'
  have h := hx'.1
  rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hn0] at h
  exact mem_ballZ0.2 (by linarith)

/-- Choice of the inner radius: `0 < ρ < 1 - τ` with `(1 - τ)^d - ρ^d ≤ δ`. -/
theorem exists_radius (hd : 1 ≤ d) {τ δ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 - τ ∧ 1 - ρ ^ d ≤ 1 - (1 - τ) ^ d + δ := by
  set θ := min (1 / 2 : ℝ) (δ / d)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hθ0 : 0 < θ := lt_min (by norm_num) (div_pos hδ hdpos)
  have hθ1 : θ ≤ 1 / 2 := min_le_left _ _
  have hθ2 : θ ≤ δ / d := min_le_right _ _
  refine ⟨(1 - τ) * (1 - θ), by nlinarith, by nlinarith, ?_⟩
  have hbern : 1 - d * θ ≤ (1 - θ) ^ d := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -θ by linarith) d
    rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
    exact this
  have hpow : (1 - τ) ^ d ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hpow0 : 0 ≤ (1 - τ) ^ d := pow_nonneg (by linarith) d
  have hdθ : d * θ ≤ δ := by rw [le_div_iff₀ hdpos] at hθ2; linarith
  rw [mul_pow]
  nlinarith

end MuLipschitzShell

open MuLipschitz MuLipschitzShell in
/-- **The shell estimate from Lemma 5.5**, given that annuli are Lipschitz domains. -/
theorem shellBound_of_muConvergence_of_annulus (hconv : MuConvergenceStmt)
    (hann : ∀ d : ℕ, 2 ≤ d → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → IsLipschitzDomain (annulus d ρ)) :
    ShellBoundStmt := by
  intro d hd E l M
  have hd1 : 1 ≤ d := by omega
  filter_upwards [(hconv d hd).1 E (symmPart M) (symmPart_isSymm M) l] with η hη
  intro τ hτ0 hτ1 ε hε
  set α := muBar E l M with hαdef
  set α' := muStarBar E l M with hα'def
  have hα0 : 0 ≤ α := ENNReal.toReal_nonneg
  have hα'0 : 0 ≤ α' := ENNReal.toReal_nonneg
  set K := α + α' + 1 with hK
  have hK1 : 1 ≤ K := by linarith
  set δ := min 1 ε / (4 * K) with hδdef
  have hmin0 : 0 < min 1 ε := lt_min one_pos hε
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 4 := by
    rw [hδdef, div_le_iff₀ (by positivity)]
    nlinarith [min_le_left (1 : ℝ) ε]
  have hδε : 4 * K * δ ≤ ε := by
    rw [hδdef, mul_div_cancel₀ _ (by positivity)]
    exact min_le_right _ _
  obtain ⟨ρ, hρ0, hρ1, hρδ⟩ := exists_radius hd1 hτ0 hτ1 hδ0
  have hρ1' : ρ < 1 := by linarith
  have hW := hann d hd ρ hρ0 hρ1'
  obtain ⟨hfin, hconvμ, hconvμ'⟩ := hη _ hW
  rw [muBar_symmPart] at hconvμ
  rw [muStarBar_symmPart] at hconvμ'
  have hcnt := tendsto_ncard_discretize_div_ball hd1 hW.1
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet (volume_frontier_annulus hd1 ρ)
  have hvol1 : 0 < volume.real (ball (0 : Rd d) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  rw [volume_real_annulus hρ0.le hρ1', mul_div_cancel_right₀ _ hvol1.ne'] at hcnt
  have e1 := hconvμ.eventually (gt_mem_nhds (show α < α + ε / 4 by linarith))
  have e2 := hconvμ'.eventually (gt_mem_nhds (show α' < α' + ε / 4 by linarith))
  have e3 := hcnt.eventually (gt_mem_nhds (show 1 - ρ ^ d < 1 - ρ ^ d + δ by linarith))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (eventually_ge_atTop 1))))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3, hn1⟩ := hn₀ n hn
  set D := discretize (annulus d ρ) n
  set N : ℝ := ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)
  have hDsub := discretize_annulus_subset (d := d) (ρ := ρ) hn1
  have hshell := shell_subset_discretize (d := d) hn1 hρ1
  have hNpos : 0 < N := Nat.cast_pos.2 (ncard_ballZ0_pos hn1)
  have ha0 : 0 ≤ 1 - (1 - τ) ^ d := by
    have : (1 - τ) ^ d ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  have ha1 : 1 - (1 - τ) ^ d ≤ 1 := by
    have : 0 ≤ (1 - τ) ^ d := pow_nonneg (by linarith) d
    linarith
  -- the count `|D| ≤ (1 - (1-τ)^d + 2δ) N`
  have hDcnt : (D.ncard : ℝ) ≤ (1 - (1 - τ) ^ d + 2 * δ) * N := by
    have := (div_lt_iff₀ hNpos).1 h3
    nlinarith
  -- the arithmetic `(β + ε/4)(a + 2δ) ≤ a β + ε` for `0 ≤ β ≤ K`
  have harith : ∀ β : ℝ, 0 ≤ β → β ≤ K →
      (β + ε / 4) * (1 - (1 - τ) ^ d + 2 * δ) ≤ (1 - (1 - τ) ^ d) * β + ε := by
    intro β hβ0 hβK
    have hβδ : β * δ ≤ K * δ := mul_le_mul_of_nonneg_right hβK hδ0.le
    nlinarith
  -- a bound of the restricted `μ` by the count
  have hbound : ∀ (m : ℝ≥0∞) (β : ℝ), 0 ≤ β → β ≤ K → m ≠ ⊤ →
      m.toReal / (D.ncard : ℝ) < β + ε / 4 →
      m ≤ ENNReal.ofReal (((1 - (1 - τ) ^ d) * β + ε) * N) ∨ D = ∅ := by
    intro m β hβ0 hβK hm hlt
    by_cases hD0 : (D.ncard : ℝ) = 0
    · right
      have hfinD : D.Finite := (ballZ0_finite _).subset hDsub
      exact (Set.ncard_eq_zero hfinD).1 (by exact_mod_cast hD0)
    · left
      have hDpos : 0 < (D.ncard : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hD0)
      rw [← ENNReal.ofReal_toReal hm]
      refine ENNReal.ofReal_le_ofReal ?_
      have hm1 := (div_lt_iff₀ hDpos).1 hlt
      have hm2 : (β + ε / 4) * D.ncard ≤ (β + ε / 4) * ((1 - (1 - τ) ^ d + 2 * δ) * N) :=
        mul_le_mul_of_nonneg_left hDcnt (by linarith)
      have hm3 := mul_le_mul_of_nonneg_right (harith β hβ0 hβK) hNpos.le
      nlinarith
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have hv := volume_supGrad_le_mu hDsub hshell hw
    rw [← mu_symmPart] at hv
    rcases hbound _ α hα0 (by linarith) (hfin n).1 h1 with hb | hb
    · exact hv.trans hb
    · have : ballZ0 (d := d) (n : ℝ) \ ballZ0 ((1 - τ) * n) = ∅ :=
        Set.subset_eq_empty hshell hb
      rw [this]
      simp
  · have hv := volume_subGrad_le_muStar hDsub hshell hw
    rw [← muStar_symmPart] at hv
    rcases hbound _ α' hα'0 (by linarith) (hfin n).2 h2 with hb | hb
    · exact hv.trans hb
    · have : ballZ0 (d := d) (n : ℝ) \ ballZ0 ((1 - τ) * n) = ∅ :=
        Set.subset_eq_empty hshell hb
      rw [this]
      simp

/-- **The shell estimate from Lemma 5.5** (`ShellBoundStmt`). -/
theorem shellBound_of_muConvergence (hconv : MuConvergenceStmt) : ShellBoundStmt :=
  shellBound_of_muConvergence_of_annulus hconv fun _ hd _ hρ0 hρ1 =>
    MuLipschitzAnnulus.annulus_isLipschitzDomain hd hρ0 hρ1

/-- **Lemma 6.3 from Lemma 6.2' and Lemma 5.5** (repaired proof). -/
theorem muLipschitz_of_bending_of_muConvergence (hbend : NearMaxBendingStmt)
    (hconv : MuConvergenceStmt) : MuLipschitzStmt :=
  muLipschitz_of_bending hbend (shellBound_of_muConvergence hconv)

/-- **Lemma 6.2 with `C = C(β) = c (1-β)²`, from Lemma 6.2' and Lemma 5.5.** -/
theorem strictConcavityBeta_of_bending_of_muConvergence (hbend : NearMaxBendingStmt)
    (hconv : MuConvergenceStmt) : StrictConcavityBetaStmt :=
  strictConcavityBeta_of_bending hbend (shellBound_of_muConvergence hconv)

end RandomSandpile

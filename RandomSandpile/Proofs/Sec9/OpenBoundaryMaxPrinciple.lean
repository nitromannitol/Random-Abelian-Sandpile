import RandomSandpile.Proofs.Sec9.OpenBoundaryMaxPrincipleCore
import RandomSandpile.Proofs.Sec3.LeastAction
import RandomSandpile.Proofs.Sec5.MuConvergenceRestrict
import RandomSandpile.Proofs.Sec6.StrictConcavityBall
import RandomSandpile.Proofs.Sec6.StrictConcavity

/-! # Theorem 9.1, steps and: interior maximum and minimum principles

`openInteriorMaxPrinciple_of_muConvergence`, `openInteriorMinPrinciple_of_muConvergence`: from
Lemma 5.5 (`MuConvergenceStmt`) and the compactness step (`OpenCompactnessStmt`), which supplies
the continuity of the subsequential limits. Route: `principle_generic` (rescaled ABP on
`nB_r(a) ∩ ℤ^d`), applied to the open odometers.
* The open odometer is legal (`openOdometer_isLegal`: the least stabilizing toppling vanishing on
  `∂A` is the legal stabilizing one of Proposition 3.1, no connectivity needed) and stabilizing.
  Its restriction to `nB_r(a)` is locally legal, resp. stabilizing, there (Lemma 5.5's restriction
  steps).
* `n² Q(·/n) = q_l + q_M + affine` (`rescaled_quad_affine`), and supergradient masses are invariant
  under adding affine functions (`volume_supGradSet_affine`). Hence the mass is at most
  `μ(nB_r(a) ∩ ℤ^d, η, l, M)` (resp. `μ*`).
* Lemma 5.5 on the ball `B_r(a)`: `μ / |nB_r(a) ∩ ℤ^d| → μ(l, M) = 0`, so `μ / n^d → 0`.

Continuity of the limit is needed: the maximum over the discrete boundary converges to a value on
the sphere only for a continuous limit. It comes from compactness: a further subsequence converges to a
continuous function. -/

open MeasureTheory LatticeProb Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

namespace OpenMaxPrinciple

variable {d : ℕ}

/-- The open odometer is legal (Proposition 3.1, without connectivity). -/
theorem openOdometer_isLegal (hd : 0 < d) {A : Set (Site d)} (hA : A.Finite) (η : Site d → ℤ) :
    IsLegal η A (openOdometer η A) := by
  obtain ⟨v, hvL, hvS⟩ := existsLegalStabilizing d hd A hA η
  have hvO : v ∈ stabilizingOpen η A :=
    ⟨hvS, fun y hy => hvL.eq_zero_of_notMem (Set.disjoint_right.1 (bdry_disjoint A) hy)⟩
  have hL := isLeast_openOdometer ⟨v, hvO⟩
  have h1 : openOdometer η A ≤ v := hL.2 hvO
  have h2 : v ≤ openOdometer η A :=
    legalLeStabilizing d A η v _ hvL (stabilizingOpen_subset η A hL.1)
  rw [le_antisymm h1 h2]; exact hvL

theorem openOdometer_mem_stabilizing (hd : 0 < d) {A : Set (Site d)} (hA : A.Finite)
    (η : Site d → ℤ) : openOdometer η A ∈ stabilizing η A := by
  obtain ⟨v, hvL, hvS⟩ := existsLegalStabilizing d hd A hA η
  have hvO : v ∈ stabilizingOpen η A :=
    ⟨hvS, fun y hy => hvL.eq_zero_of_notMem (Set.disjoint_right.1 (bdry_disjoint A) hy)⟩
  exact stabilizingOpen_subset η A (isLeast_openOdometer ⟨v, hvO⟩).1

/-- Supergradient masses are invariant under adding affine functions. -/
theorem volume_supGradSet_affine {A : Set (Site d)} {w₁ w₂ : Site d → ℝ} (c : Rd d) (c0 : ℝ)
    (h : ∀ z ∈ dClosure A, w₁ z = w₂ z + inner ℝ c (toE z) + c0) :
    volume (supGradSet w₁ A) = volume (supGradSet w₂ A) := by
  have hset : supGradSet w₁ A = (fun q => q + (-c)) ⁻¹' supGradSet w₂ A := by
    ext q
    simp only [supGradSet, Set.mem_iUnion, Set.mem_preimage, exists_prop]
    constructor
    · rintro ⟨x, hx, hq⟩
      refine ⟨x, hx, fun y hy => ?_⟩
      have h1 := hq y hy
      rw [h y hy, h x (mem_dClosure_of_mem hx)] at h1
      simp only [inner_add_left, inner_neg_left, inner_sub_right] at h1 ⊢
      linarith
    · rintro ⟨x, hx, hq⟩
      refine ⟨x, hx, fun y hy => ?_⟩
      have h1 := hq y hy
      rw [h y hy, h x (mem_dClosure_of_mem hx)]
      simp only [inner_add_left, inner_neg_left, inner_sub_right] at h1 ⊢
      linarith
  rw [hset]; exact measure_preimage_add_right volume (-c) _

theorem qM_smul' (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (X : Rd d) :
    qM M (t • X) = t ^ 2 * qM M X := by
  simp only [qM, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

theorem ql_smul' (l t : ℝ) (X : Rd d) : ql l (t • X) = t ^ 2 * ql l X := by
  simp only [ql, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem qM_sub' {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (Z B : Rd d) :
    qM M (Z - B) =
      qM M Z - inner ℝ (WithLp.toLp 2 (M *ᵥ WithLp.ofLp B)) Z + qM M B := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, WithLp.ofLp_toLp]
  have hsym : WithLp.ofLp B ⬝ᵥ (M *ᵥ WithLp.ofLp Z) =
      WithLp.ofLp Z ⬝ᵥ (M *ᵥ WithLp.ofLp B) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, dotProduct_comm]
  simp only [qM, WithLp.ofLp_sub, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hsym]; ring

theorem ql_sub' (l : ℝ) (Z B : Rd d) :
    ql l (Z - B) = ql l Z - l / d * inner ℝ B Z + ql l B := by
  simp only [ql]
  rw [norm_sub_sq_real, real_inner_comm]
  ring

/-- `n² Q(·/n) = q_l + q_M + affine` for `Q(X) = p·(X - a) + q_M(X - a) + q_l(X - a)`. -/
theorem rescaled_quad_affine {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (p a : Rd d)
    (l : ℝ) {n : ℝ} (hn : n ≠ 0) : ∃ (c : Rd d) (c0 : ℝ), ∀ Z : Rd d,
      n ^ 2 * (inner ℝ p (n⁻¹ • Z - a) + qM M (n⁻¹ • Z - a) + ql l (n⁻¹ • Z - a)) =
        ql l Z + qM M Z + inner ℝ c Z + c0 := by
  set B : Rd d := n • a
  refine ⟨n • p - WithLp.toLp 2 (M *ᵥ WithLp.ofLp B) - (l / d) • B,
    qM M B + ql l B - n ^ 2 * inner ℝ p a, fun Z => ?_⟩
  have h1 : n⁻¹ • Z - a = n⁻¹ • (Z - B) := by
    simp only [B, smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [h1, qM_smul', ql_smul', qM_sub' hM, ql_sub']
  simp only [B, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  field_simp
  ring

/-- The mass of a perturbed restriction of a locally legal toppling is at most `μ`. -/
theorem volume_le_mu {η : Site d → ℤ} {B A : Set (Site d)} (hBA : B ⊆ A) {u : Site d → ℤ}
    (hu : u ∈ locLegal η A) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {g : Site d → ℝ}
    (c : Rd d) (c0 : ℝ)
    (hg : ∀ z ∈ dClosure B, g z = ((u z : ℝ) - (qlZ l z + qMZ M z)) + inner ℝ c (toE z) + c0) :
    volume (supGradSet g B) ≤ mu B η l M := by
  set w' : Site d → ℝ := fun z => (((dClosure B).indicator u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)
  have hw' : w' ∈ perturbedSub B η l M :=
    mem_perturbedSub.2 ⟨_, locLegalRestrict d η A B u hBA hu, rfl⟩
  rw [volume_supGradSet_affine (w₂ := w') c c0 (fun z hz => by
    rw [hg z hz]; simp only [w', Set.indicator_of_mem hz])]
  exact le_iSup₂_of_le w' hw' le_rfl

/-- The mass of the negated perturbed restriction of a stabilizing toppling is at most `μ*`. -/
theorem volume_le_muStar {η : Site d → ℤ} {B A : Set (Site d)} (hBA : B ⊆ A) {v : Site d → ℤ}
    (hv : v ∈ stabilizing η A) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {g : Site d → ℝ}
    (c : Rd d) (c0 : ℝ)
    (hg : ∀ z ∈ dClosure B,
      g z = -((v z : ℝ) - (qlZ l z + qMZ M z)) + inner ℝ c (toE z) + c0) :
    volume (supGradSet g B) ≤ muStar B η l M := by
  set w' : Site d → ℝ := fun z => (((dClosure B).indicator v z : ℤ) : ℝ) - (qlZ l z + qMZ M z)
  have hw' : w' ∈ perturbedSuper B η l M :=
    mem_perturbedSuper.2 ⟨_, stabilizingRestrict d η A B v hBA hv, rfl⟩
  rw [volume_supGradSet_affine (w₂ := fun z => -w' z) c c0 (fun z hz => by
    rw [hg z hz]; simp only [w', Set.indicator_of_mem hz]), ← subGradNegVolume d w' B]
  exact le_iSup₂_of_le w' hw' le_rfl

/-- `f(nB_r(a) ∩ ℤ^d) / |nB_r(a) ∩ ℤ^d| → 0` implies `f(n_k B_r(a) ∩ ℤ^d) / n_k^d → 0`. -/
theorem div_pow_tendsto_zero (hd : 1 ≤ d) {a : Rd d} {r : ℝ} (hr : 0 < r)
    (f : Set (Site d) → ℝ≥0∞) (hf0 : f ∅ = 0)
    (hlim : Tendsto (fun n : ℕ => (f (discretize (ball a r) n)).toReal /
      ((discretize (ball a r) n).ncard : ℝ)) atTop (𝓝 0))
    {nk : ℕ → ℕ} (hnk : StrictMono nk) :
    Tendsto (fun k => (f (discretize (ball a r) (nk k))).toReal / (nk k : ℝ) ^ d) atTop
      (𝓝 0) := by
  set ρ := ‖a‖ + r
  have hρ : 0 < ρ := by positivity
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (fun n : ℕ => ((ballZ0 (d := d) (ρ * n)).ncard : ℝ) /
      (n : ℝ) ^ d) atTop (𝓝 L) := ⟨_, BallCount.tendsto_ncard_div_pow hd hρ⟩
  have hB : ∀ᶠ n : ℕ in atTop,
      ((ballZ0 (d := d) (ρ * n)).ncard : ℝ) / (n : ℝ) ^ d ≤ L + 1 :=
    (hL.eventually (Iio_mem_nhds (lt_add_one L))).mono fun _ h => h.le
  have hall : Tendsto (fun n : ℕ => (f (discretize (ball a r) n)).toReal / (n : ℝ) ^ d) atTop
      (𝓝 0) := by
    have hR : Tendsto (fun n : ℕ => (f (discretize (ball a r) n)).toReal /
        ((discretize (ball a r) n).ncard : ℝ) * (L + 1)) atTop (𝓝 0) := by
      have := hlim.mul_const (L + 1); rwa [zero_mul] at this
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hR
    filter_upwards [hB, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < (n : ℝ) ^ d := by
      have : (0 : ℝ) < n := by exact_mod_cast hn1
      positivity
    have hfin : (discretize (ball a r) n).Finite :=
      SubadditiveLipschitz.discretize_finite isBounded_ball n
    have hsub : discretize (ball a r) n ⊆ ballZ0 (ρ * n) := by
      intro z hz
      have h := (mem_discretize_iff' (by omega : n ≠ 0)).1 hz
      rw [mem_ball, dist_eq_norm] at h
      rw [ABP.mem_ballZ0]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have h2 : ‖(n : ℝ)⁻¹ • toE z‖ < ρ := by
        calc ‖(n : ℝ)⁻¹ • toE z‖ = ‖((n : ℝ)⁻¹ • toE z - a) + a‖ := by rw [sub_add_cancel]
          _ ≤ ‖(n : ℝ)⁻¹ • toE z - a‖ + ‖a‖ := norm_add_le _ _
          _ < ρ := by simp only [ρ]; linarith
      rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hnpos] at h2
      linarith
    have hcard : ((discretize (ball a r) n).ncard : ℝ) ≤ (ballZ0 (d := d) (ρ * n)).ncard := by
      exact_mod_cast Set.ncard_le_ncard hsub (ABP.ballZ0_finite _)
    have hnn : 0 ≤ (f (discretize (ball a r) n)).toReal := ENNReal.toReal_nonneg
    by_cases h0 : ((discretize (ball a r) n).ncard : ℝ) = 0
    · have hemp : discretize (ball a r) n = ∅ :=
        (Set.ncard_eq_zero hfin).1 (by exact_mod_cast h0)
      rw [hemp, hf0]; simp
    · have hD : ((discretize (ball a r) n).ncard : ℝ) / (n : ℝ) ^ d ≤ L + 1 :=
        le_trans (div_le_div_of_nonneg_right hcard hn0.le) hn
      calc (f (discretize (ball a r) n)).toReal / (n : ℝ) ^ d
          = (f (discretize (ball a r) n)).toReal / ((discretize (ball a r) n).ncard : ℝ) *
              (((discretize (ball a r) n).ncard : ℝ) / (n : ℝ) ^ d) := by
            rw [div_mul_div_cancel₀ h0]
        _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)
  exact hall.comp hnk.tendsto_atTop

theorem mu_empty (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    mu (∅ : Set (Site d)) η l M = 0 := by
  simp [mu, supGradSet]

theorem muStar_empty (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStar (∅ : Set (Site d)) η l M = 0 := by
  simp [muStar, subGradSet]

theorem continuous_quadratic (p a : Rd d) (M : Matrix (Fin d) (Fin d) ℝ) (l : ℝ) :
    Continuous (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a)) := by
  have hqM : Continuous (qM M) := (contDiff_qM (n := 0) M).continuous
  have hql : Continuous (ql (d := d) l) := by
    unfold ql; exact ((continuous_const.mul (continuous_norm.pow 2)).div_const _)
  have hs : Continuous (fun X : Rd d => X - a) := continuous_id.sub continuous_const
  exact ((continuous_const.inner hs).add (hqM.comp hs)).add (hql.comp hs)

end OpenMaxPrinciple

open OpenMaxPrinciple in
/-- **Step** (`OpenInteriorMaxPrincipleStmt`) from Lemma 5.5 and the compactness step. -/
theorem openInteriorMaxPrinciple_of_muConvergence (hconv : MuConvergenceStmt)
    (hComp : OpenCompactnessStmt) : OpenInteriorMaxPrincipleStmt := by
  intro d hd E W hW l M hM hμ
  have hd1 : 1 ≤ d := by omega
  filter_upwards [(hconv d hd).1 E M hM l, ae_all_iff.2 E.bounded] with η hη hbd
  rintro v ⟨nk, hnk, hvconv⟩ a p r hr hball x hx
  have hvc : Continuous v := by
    obtain ⟨φ, hφ, vbar, hvbar, hconvφ⟩ := hComp d hd W hW E.ηmin E.ηmax η hbd nk hnk
    have : v = vbar := funext fun X =>
      tendsto_nhds_unique ((hvconv.tendsto_at X).comp hφ.tendsto_atTop) (hconvφ.tendsto_at X)
    rw [this]; exact hvbar
  by_cases hxs : x ∈ sphere a r
  · exact ⟨x, hxs, le_rfl⟩
  have hxb : x ∈ ball a r := by
    rw [mem_closedBall] at hx; rw [mem_sphere] at hxs; rw [mem_ball]; exact lt_of_le_of_ne hx hxs
  obtain ⟨hfinμ, hlimμ, -⟩ := hη (ball a r) (StrictConcavityBall.isLipschitzDomain_ball a hr)
  rw [hμ] at hlimμ
  have hV := div_pow_tendsto_zero hd1 hr (fun A => mu A η l M) (mu_empty η l M) hlimμ hnk
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (1 : ℝ) *
      ((openOdometer η (discretize W (nk k)) z : ℝ) - (nk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a))
          ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball a r) (nk k))) ≤
        mu (discretize (ball a r) (nk k)) η l M ∧
      mu (discretize (ball a r) (nk k)) η l M ≠ ⊤ := by
    filter_upwards [hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : (nk k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨c, c0, hcq⟩ := rescaled_quad_affine hM p a l hn0
    have hWfin : (discretize W (nk k)).Finite :=
      SubadditiveLipschitz.discretize_finite hW.1 (nk k)
    have hDW : discretize (ball a r) (nk k) ⊆ discretize W (nk k) :=
      fun z hz => Set.smul_set_mono (ball_subset_closedBall.trans hball) hz
    refine ⟨volume_le_mu hDW (mem_locLegal_of_isLegal (openOdometer_isLegal (by omega) hWfin η))
      l M (-c) (-c0) (fun z _ => ?_), (hfinμ (nk k)).1⟩
    have h1 := hcq (toE z)
    simp only [qlZ, qMZ, inner_neg_left]
    rw [h1]
    ring
  obtain ⟨y, hy, h⟩ := principle_generic hd1 (σ := 1) (continuous_quadratic p a M l) hvc hnk
    hvconv hr hvol hV hxb
  exact ⟨y, hy, by simpa using h⟩

open OpenMaxPrinciple in
/-- **Step** (`OpenInteriorMinPrincipleStmt`) from Lemma 5.5 and the compactness step. -/
theorem openInteriorMinPrinciple_of_muConvergence (hconv : MuConvergenceStmt)
    (hComp : OpenCompactnessStmt) : OpenInteriorMinPrincipleStmt := by
  intro d hd E W hW l M hM hμ
  have hd1 : 1 ≤ d := by omega
  filter_upwards [(hconv d hd).1 E M hM l, ae_all_iff.2 E.bounded] with η hη hbd
  rintro v ⟨nk, hnk, hvconv⟩ a p r hr hball x hx
  have hvc : Continuous v := by
    obtain ⟨φ, hφ, vbar, hvbar, hconvφ⟩ := hComp d hd W hW E.ηmin E.ηmax η hbd nk hnk
    have : v = vbar := funext fun X =>
      tendsto_nhds_unique ((hvconv.tendsto_at X).comp hφ.tendsto_atTop) (hconvφ.tendsto_at X)
    rw [this]; exact hvbar
  by_cases hxs : x ∈ sphere a r
  · exact ⟨x, hxs, le_rfl⟩
  have hxb : x ∈ ball a r := by
    rw [mem_closedBall] at hx; rw [mem_sphere] at hxs; rw [mem_ball]; exact lt_of_le_of_ne hx hxs
  obtain ⟨hfinμ, -, hlimμ⟩ := hη (ball a r) (StrictConcavityBall.isLipschitzDomain_ball a hr)
  rw [hμ] at hlimμ
  have hV := div_pow_tendsto_zero hd1 hr (fun A => muStar A η l M) (muStar_empty η l M)
    hlimμ hnk
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (-1 : ℝ) *
      ((openOdometer η (discretize W (nk k)) z : ℝ) - (nk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a))
          ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball a r) (nk k))) ≤
        muStar (discretize (ball a r) (nk k)) η l M ∧
      muStar (discretize (ball a r) (nk k)) η l M ≠ ⊤ := by
    filter_upwards [hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : (nk k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨c, c0, hcq⟩ := rescaled_quad_affine hM p a l hn0
    have hWfin : (discretize W (nk k)).Finite :=
      SubadditiveLipschitz.discretize_finite hW.1 (nk k)
    have hDW : discretize (ball a r) (nk k) ⊆ discretize W (nk k) :=
      fun z hz => Set.smul_set_mono (ball_subset_closedBall.trans hball) hz
    refine ⟨volume_le_muStar hDW (openOdometer_mem_stabilizing (by omega) hWfin η)
      l M c c0 (fun z _ => ?_), (hfinμ (nk k)).2⟩
    have h1 := hcq (toE z)
    simp only [qlZ, qMZ]
    rw [h1]
    ring
  obtain ⟨y, hy, h⟩ := principle_generic hd1 (σ := -1) (continuous_quadratic p a M l) hvc hnk
    hvconv hr hvol hV hxb
  refine ⟨y, hy, ?_⟩
  simp only [neg_mul, one_mul, neg_le_neg_iff] at h
  exact h

end RandomSandpile

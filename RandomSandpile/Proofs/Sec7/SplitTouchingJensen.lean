import RandomSandpile.Proofs.Sec9.OpenBoundaryComparison
import RandomSandpile.Proofs.Sec9.OpenBoundaryMaxPrinciple
import RandomSandpile.Proofs.Sec7.MainTheoremUniqueness
import RandomSandpile.Proofs.Sec7.LimitObstacleGamma
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTranslates

/-! # Jensen's lemma with a measure bound

The quantitative form of Jensen's lemma (Crandall-Ishii-Lions, *User's guide*, Lemma A.3) used for
`SplitTouchingStmt`: the set of maximum points of `Z - p·(·)`, `|p| ≤ r`, of a semiconvex `Z` has
measure at least `|B_r| / B` when `|det D²Z| ≤ B` at its points of second-order expansion off a null
set (`jensen_volume`).

* `slope_taylor`: at a point `x` of second-order expansion `(P, H)` of `Z`, the slope `p` of an
  affine function touching `Z` from above at a nearby `y` is `P + H(y - x) + o(|y - x|)`. Hence the
  slope map of the maximum points is differentiable within that set, with derivative `H`.
* `abs_entry_le_of_nonpos`: if `q_H ≤ 0` and `tr H ≥ -T` then `|H_ij| ≤ T`; with Hadamard's bound
  (`Matrix.det_le`), `|det H| ≤ d! T^d` (`abs_det_le_of_nonpos`).
* `jensen_volume`: the slope map sends the maximum points onto `B_r`; off a measurable null set
  the area inequality `addHaar_image_le_lintegral_abs_det_fderiv` applies, and the null part has
  null image (Lipschitz on small pieces, as in `OpenComparison.jensen_exists`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Matrix

namespace RandomSandpile

namespace SplitJensen

variable {d : ℕ}

open OpenComparison

/-- `q_H(k + h) = q_H(k) + (Hk)·h + q_H(h)` for symmetric `H`. -/
theorem qM_add_sym {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsSymm) (h k : Rd d) :
    qM H (k + h) = qM H k + inner ℝ (WithLp.toLp 2 (H *ᵥ WithLp.ofLp k)) h + qM H h := by
  have e : k + h = h - (-k) := by abel
  rw [e, OpenMaxPrinciple.qM_sub' hH]
  have h1 : qM H (-k) = qM H k := by
    rw [show -k = (-1 : ℝ) • k by simp, OpenMaxPrinciple.qM_smul']; ring
  have h2 : WithLp.toLp 2 (H *ᵥ WithLp.ofLp (-k)) = -(WithLp.toLp 2 (H *ᵥ WithLp.ofLp k)) := by
    simp [Matrix.mulVec_neg]
  rw [h1, h2, inner_neg_left]; ring

/-- Arithmetic of `slope_taylor`. -/
theorem slope_arith {Λ θ lam θ₁ a : ℝ} (hΛ : 0 ≤ Λ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamΛ : Λ * lam ≤ θ / 4) (hθ₁0 : 0 ≤ θ₁) (hθ₁ : θ₁ ≤ θ * lam / 12) :
    Λ * (lam * a) ^ 2 + θ₁ * ((a + lam * a) ^ 2 + a ^ 2) ≤ lam * a * (θ * a) := by
  have h1 : Λ * lam ^ 2 ≤ θ / 4 * lam := by
    have := mul_le_mul_of_nonneg_right hlamΛ hlam0.le; nlinarith
  have h2 : (1 + lam) ^ 2 + 1 ≤ 5 := by nlinarith
  have h3 : θ₁ * ((1 + lam) ^ 2 + 1) ≤ θ * lam / 12 * 5 := by
    have hp : 0 ≤ (1 + lam) ^ 2 + 1 := by positivity
    calc θ₁ * ((1 + lam) ^ 2 + 1) ≤ θ * lam / 12 * ((1 + lam) ^ 2 + 1) :=
          mul_le_mul_of_nonneg_right hθ₁ hp
      _ ≤ θ * lam / 12 * 5 := by
          apply mul_le_mul_of_nonneg_left h2
          have : 0 ≤ θ := by nlinarith
          positivity
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have e : Λ * (lam * a) ^ 2 + θ₁ * ((a + lam * a) ^ 2 + a ^ 2) =
      a ^ 2 * (Λ * lam ^ 2 + θ₁ * ((1 + lam) ^ 2 + 1)) := by ring
  rw [e]
  have : a ^ 2 * (Λ * lam ^ 2 + θ₁ * ((1 + lam) ^ 2 + 1)) ≤
      a ^ 2 * (θ / 4 * lam + θ * lam / 12 * 5) :=
    mul_le_mul_of_nonneg_left (by linarith) ha2
  have hθ0 : 0 ≤ θ * lam := by nlinarith
  nlinarith

/-- **Slopes at nearby touching points** (the derivative of the slope map). -/
theorem slope_taylor {Z : Rd d → ℝ} {x P : Rd d} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsSymm) (hT : HasSecondOrderTaylorAt Z x P H) {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ y p : Rd d, ‖y - x‖ < δ →
      (∀ z, ‖z - y‖ < ρ → Z z ≤ Z y + inner ℝ p (z - y)) →
      ‖p - P - WithLp.toLp 2 (H *ᵥ WithLp.ofLp (y - x))‖ ≤ θ * ‖y - x‖ := by
  obtain ⟨c, hc, hcH⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ i j, |H i j| ≤ c :=
    ⟨∑ i, ∑ j, |H i j|, by positivity, fun i j => PegdenSmartRegularity.abs_entry_le_sum H i j⟩
  set Λ : ℝ := (d : ℝ) ^ 2 * c with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hqH : ∀ h : Rd d, |qM H h| ≤ Λ * ‖h‖ ^ 2 := fun h => abs_qM_le H hc hcH h
  set lam : ℝ := min 1 (θ / (4 * (Λ + 1))) with hlam
  have hlam0 : 0 < lam := lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamΛ : Λ * lam ≤ θ / 4 := by
    have h1 : lam ≤ θ / (4 * (Λ + 1)) := min_le_right _ _
    have h2 : Λ * (θ / (4 * (Λ + 1))) ≤ θ / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    calc Λ * lam ≤ Λ * (θ / (4 * (Λ + 1))) := mul_le_mul_of_nonneg_left h1 hΛ0
      _ ≤ θ / 4 := h2
  set θ₁ : ℝ := min (1 / 2) (θ * lam / 12) with hθ₁
  have hθ₁0 : 0 < θ₁ := lt_min (by norm_num) (by positivity)
  obtain ⟨δ₁, hδ₁, hb⟩ := hT.bound hθ₁0
  -- the core inequality
  have core : ∀ y p : Rd d, (∀ z, ‖z - y‖ < ρ → Z z ≤ Z y + inner ℝ p (z - y)) →
      ∀ t : ℝ, 0 < t → t < ρ → ‖y - x‖ + t < δ₁ →
      t * ‖p - P - WithLp.toLp 2 (H *ᵥ WithLp.ofLp (y - x))‖ ≤
        Λ * t ^ 2 + θ₁ * ((‖y - x‖ + t) ^ 2 + ‖y - x‖ ^ 2) := by
    intro y p hup t ht htρ htδ
    set k := y - x with hk
    set V := p - P - WithLp.toLp 2 (H *ᵥ WithLp.ofLp k) with hV
    by_cases hV0 : V = 0
    · rw [hV0, norm_zero, mul_zero]; positivity
    have hVn : 0 < ‖V‖ := norm_pos_iff.2 hV0
    set h : Rd d := -((t / ‖V‖) • V) with hh
    have hhn : ‖h‖ = t := by
      rw [hh, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp
    have hVh : inner ℝ V h = -(t * ‖V‖) := by
      rw [hh, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
    have hz := hup (y + h) (by rw [add_sub_cancel_left, hhn]; exact htρ)
    rw [add_sub_cancel_left] at hz
    have hkn : ‖k‖ < δ₁ := by linarith
    have hkh : ‖k + h‖ ≤ ‖k‖ + t := (norm_add_le _ _).trans (by rw [hhn])
    have e1 : y + h - x = k + h := by rw [hk]; abel
    have hb1 := hb (y + h) (by rw [e1]; linarith)
    have hb2 := hb y hkn
    rw [e1] at hb1
    have hb1' := (abs_le.1 hb1).1
    have hb2' := (abs_le.1 hb2).2
    have hq := qM_add_sym hH h k
    have hqh := (abs_le.1 (hqH h)).1
    rw [hhn] at hqh
    have hkh2 : ‖k + h‖ ^ 2 ≤ (‖k‖ + t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hkh 2
    have hkh3 : θ₁ * ‖k + h‖ ^ 2 ≤ θ₁ * (‖k‖ + t) ^ 2 := mul_le_mul_of_nonneg_left hkh2 hθ₁0.le
    have hexp : inner ℝ V h = inner ℝ p h - inner ℝ P h -
        inner ℝ (WithLp.toLp 2 (H *ᵥ WithLp.ofLp k)) h := by
      rw [hV, inner_sub_left, inner_sub_left]
    have hPkh : inner ℝ P (k + h) = inner ℝ P k + inner ℝ P h := inner_add_right _ _ _
    linarith
  refine ⟨min (δ₁ / (2 * (1 + lam))) (ρ / (2 * (lam + 1))), by positivity, fun y p hy hup => ?_⟩
  have hy1 : ‖y - x‖ < δ₁ / (2 * (1 + lam)) := hy.trans_le (min_le_left _ _)
  have hy2 : ‖y - x‖ < ρ / (2 * (lam + 1)) := hy.trans_le (min_le_right _ _)
  by_cases hk0 : ‖y - x‖ = 0
  · rw [hk0, mul_zero]
    by_contra hpos
    push Not at hpos
    set Vn := ‖p - P - WithLp.toLp 2 (H *ᵥ WithLp.ofLp (y - x))‖ with hVn
    set t : ℝ := min (min (ρ / 2) (δ₁ / 2)) (Vn / (2 * (Λ + 1))) with ht
    have ht0 : 0 < t := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
    have htρ : t < ρ := by
      have := min_le_left (min (ρ / 2) (δ₁ / 2)) (Vn / (2 * (Λ + 1)))
      have := min_le_left (ρ / 2) (δ₁ / 2); linarith
    have htδ : ‖y - x‖ + t < δ₁ := by
      have := min_le_left (min (ρ / 2) (δ₁ / 2)) (Vn / (2 * (Λ + 1)))
      have := min_le_right (ρ / 2) (δ₁ / 2); rw [hk0]; linarith
    have htV : t ≤ Vn / (2 * (Λ + 1)) := min_le_right _ _
    have hc := core y p hup t ht0 htρ htδ
    rw [hk0] at hc
    have hθ₁h : θ₁ ≤ 1 / 2 := min_le_left _ _
    have h1 : t * Vn ≤ (Λ + 1) * t ^ 2 := by
      have : θ₁ * ((0 + t) ^ 2 + 0 ^ 2) ≤ 1 / 2 * t ^ 2 := by
        have : (0 + t) ^ 2 + 0 ^ 2 = t ^ 2 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right hθ₁h (sq_nonneg t)
      nlinarith
    have h2 : Vn ≤ (Λ + 1) * t := by
      have : t * Vn ≤ t * ((Λ + 1) * t) := by nlinarith
      exact le_of_mul_le_mul_left this ht0
    have h3 : (Λ + 1) * t ≤ Vn / 2 := by
      have := mul_le_mul_of_nonneg_left htV (by positivity : (0 : ℝ) ≤ Λ + 1)
      have e : (Λ + 1) * (Vn / (2 * (Λ + 1))) = Vn / 2 := by field_simp
      linarith
    linarith
  · have hkpos : 0 < ‖y - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk0)
    set a := ‖y - x‖ with ha
    have hc := core y p hup (lam * a) (by positivity)
      (by
        have : lam * a ≤ 1 * a := mul_le_mul_of_nonneg_right hlam1 hkpos.le
        have h2 : a * (2 * (lam + 1)) < ρ := by rwa [lt_div_iff₀ (by positivity)] at hy2
        nlinarith)
      (by
        have h2 : a * (2 * (1 + lam)) < δ₁ := by rwa [lt_div_iff₀ (by positivity)] at hy1
        nlinarith)
    have hA := slope_arith hΛ0 hlam0 hlam1 hlamΛ hθ₁0.le (min_le_right _ _) (a := a)
    have hpos : 0 < lam * a := by positivity
    exact le_of_mul_le_mul_left (hc.trans hA) hpos

/-- `q_H ≤ 0` and `tr H ≥ -T` bound the entries of `H` by `T`. -/
theorem abs_entry_le_of_nonpos {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsSymm)
    (hneg : ∀ h : Rd d, qM H h ≤ 0) {T : ℝ} (htr : -T ≤ H.trace) : ∀ i j, |H i j| ≤ T := by
  classical
  set e : Fin d → Rd d := fun i => WithLp.toLp 2 (Pi.single i (1 : ℝ)) with he
  have hqe : ∀ i, qM H (e i) = H i i / 2 := fun i => qM_toLp_single H i
  have hdiag : ∀ i, H i i ≤ 0 := fun i => by have := hneg (e i); rw [hqe] at this; linarith
  have hinner : ∀ i j, inner ℝ (WithLp.toLp 2 (H *ᵥ WithLp.ofLp (e i))) (e j) = H j i := by
    intro i j
    simp [he, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec_single]
  have hsum2 : ∀ i j, i ≠ j → -T ≤ H i i + H j j := by
    intro i j hij
    have h1 : H.trace = H i i + ∑ k ∈ Finset.univ.erase i, H k k := by
      rw [Matrix.trace, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; rfl
    have h2 : ∑ k ∈ Finset.univ.erase i, H k k =
        H j j + ∑ k ∈ (Finset.univ.erase i).erase j, H k k :=
      (Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩)).symm
    have h3 : ∑ k ∈ (Finset.univ.erase i).erase j, H k k ≤ 0 :=
      Finset.sum_nonpos fun k _ => hdiag k
    linarith
  have hsum1 : ∀ i, -T ≤ H i i := by
    intro i
    have h1 : H.trace = H i i + ∑ k ∈ Finset.univ.erase i, H k k := by
      rw [Matrix.trace, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; rfl
    have h3 : ∑ k ∈ Finset.univ.erase i, H k k ≤ 0 := Finset.sum_nonpos fun k _ => hdiag k
    linarith
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [abs_of_nonpos (hdiag i)]; linarith [hsum1 i]
  · have hp := hneg (e i + e j)
    have hm := hneg (e i + (-1 : ℝ) • e j)
    rw [qM_add_sym hH, hqe, hqe, hinner] at hp
    rw [qM_add_sym hH, OpenMaxPrinciple.qM_smul', hqe, hqe, inner_smul_right, hinner] at hm
    have hs : H j i = H i j := by
      have := congrFun (congrFun hH i) j
      simpa [Matrix.transpose_apply] using this
    rw [hs] at hp hm
    have := hsum2 i j hij
    rw [abs_le]; constructor <;> nlinarith

/-- `|det H| ≤ d! T^d` when `q_H ≤ 0` and `tr H ≥ -T`. -/
theorem abs_det_le_of_nonpos {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsSymm)
    (hneg : ∀ h : Rd d, qM H h ≤ 0) {T : ℝ} (htr : -T ≤ H.trace) :
    |H.det| ≤ (d.factorial : ℝ) * T ^ d := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (abs_entry_le_of_nonpos hH hneg htr)
  simpa [AbsoluteValue.abs_apply, nsmul_eq_mul, Fintype.card_fin] using h

/-- The matrix `H` as a continuous linear map of `ℝ^d`. -/
def toCLM (H : Matrix (Fin d) (Fin d) ℝ) : Rd d →L[ℝ] Rd d :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin H)

set_option linter.deprecated false in
theorem toCLM_apply (H : Matrix (Fin d) (Fin d) ℝ) (v : Rd d) :
    toCLM H v = WithLp.toLp 2 (H *ᵥ WithLp.ofLp v) := by
  simp [toCLM, Matrix.toEuclideanLin_apply]

theorem toCLM_det (H : Matrix (Fin d) (Fin d) ℝ) : (toCLM H).det = H.det := by
  rw [toCLM, LinearMap.det_toContinuousLinearMap]
  simp [Matrix.toEuclideanLin]

/-- **Jensen's lemma with a measure bound.** -/
theorem jensen_volume {Z : Rd d → ℝ} (hZc : Continuous Z) {S A Bad : Set (Rd d)} {c ρ r B : ℝ}
    (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hconv : ConvexOn ℝ univ (fun z => Z z + c * ‖z‖ ^ 2)) (hA : IsCompact A)
    (hball : ∀ x ∈ A, ball x ρ ⊆ S)
    (hmax : ∀ p ∈ closedBall (0 : Rd d) r, ∃ x ∈ A, IsMaxSlope Z S x p)
    (hBad : volume Bad = 0)
    (hgood : ∀ x ∈ A, x ∉ Bad → ∀ p, IsMaxSlope Z S x p →
      ∃ (P : Rd d) (H : Matrix (Fin d) (Fin d) ℝ), H.IsSymm ∧ HasSecondOrderTaylorAt Z x P H ∧
        |H.det| ≤ B) :
    volume (ball (0 : Rd d) r) ≤
      ENNReal.ofReal B * volume {x | x ∈ A ∧ ∃ p ∈ closedBall (0 : Rd d) r, IsMaxSlope Z S x p} := by
  classical
  set K : Set (Rd d) := {x | x ∈ A ∧ ∃ p ∈ closedBall (0 : Rd d) r, IsMaxSlope Z S x p} with hK
  -- `K` is compact
  have hKc : IsCompact K := by
    set R : Set (Rd d × Rd d) :=
      (A ×ˢ closedBall (0 : Rd d) r) ∩ {q | IsMaxSlope Z S q.1 q.2} with hR
    have hRcl : IsClosed {q : Rd d × Rd d | IsMaxSlope Z S q.1 q.2} := by
      simp only [IsMaxSlope, setOf_forall]
      refine isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_le ?_ ?_
      · exact continuous_const.sub (continuous_snd.inner continuous_const)
      · exact (hZc.comp continuous_fst).sub (continuous_snd.inner continuous_fst)
    have hRc : IsCompact R :=
      (hA.prod (isCompact_closedBall _ _)).inter_right hRcl
    have : K = Prod.fst '' R := by
      ext x
      simp only [hK, hR, mem_setOf_eq, mem_image, mem_inter_iff, mem_prod, Prod.exists,
        exists_and_right, exists_eq_right]
      constructor
      · rintro ⟨hxA, p, hp, hxp⟩; exact ⟨p, ⟨hxA, hp⟩, hxp⟩
      · rintro ⟨p, ⟨hxA, hp⟩, hxp⟩; exact ⟨hxA, p, hp, hxp⟩
    rw [this]; exact hRc.image continuous_fst
  -- the slope map
  set Pm : Rd d → Rd d := fun x => if h : x ∈ K then Classical.choose h.2 else 0 with hPm
  have hPmax : ∀ x ∈ K, IsMaxSlope Z S x (Pm x) := by
    intro x hx
    have := (Classical.choose_spec hx.2).2
    simp only [hPm, dif_pos hx]; exact this
  have himg : ball (0 : Rd d) r ⊆ Pm '' K := by
    intro p hp
    obtain ⟨x, hxA, hxp⟩ := hmax p (ball_subset_closedBall hp)
    have hxK : x ∈ K := ⟨hxA, p, ball_subset_closedBall hp, hxp⟩
    exact ⟨x, hxK, (slope_unique hc hρ hconv (hball x hxA) hxp (hPmax x hxK)).symm⟩
  -- the null part
  set M := toMeasurable volume Bad with hM
  have hM0 : volume M = 0 := by rw [hM, measure_toMeasurable]; exact hBad
  have hnullimg : volume (Pm '' (K ∩ M)) = 0 := by
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rd d)
    have hcover : Pm '' (K ∩ M) ⊆ ⋃ a ∈ D, Pm '' (K ∩ M ∩ ball a (ρ / 4)) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, haD, hxa⟩ := hDd.exists_dist_lt x (by positivity : (0 : ℝ) < ρ / 4)
      exact mem_biUnion haD ⟨x, ⟨hx, by rw [mem_ball]; exact hxa⟩, rfl⟩
    have hpiece : ∀ a ∈ D, volume (Pm '' (K ∩ M ∩ ball a (ρ / 4))) = 0 := by
      intro a _
      refine UniformConcavity.volume_image_eq_zero_of_lipschitzOnWith (K := (4 * c).toNNReal) ?_
        (measure_mono_null (inter_subset_left.trans inter_subset_right) hM0)
      refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
      have hxx : ‖x - x'‖ < ρ / 2 := by
        have h1 := mem_ball.1 hx.2
        have h2 := mem_ball.1 hx'.2
        rw [← dist_eq_norm]
        calc dist x x' ≤ dist x a + dist a x' := dist_triangle _ _ _
          _ < ρ / 4 + ρ / 4 := by rw [dist_comm a x']; linarith
          _ = ρ / 2 := by ring
      have := slope_lipschitz hc hρ hconv (hball x hx.1.1.1) (hball x' hx'.1.1.1)
        (hPmax x hx.1.1) (hPmax x' hx'.1.1) hxx
      rw [norm_sub_rev]; exact this
    exact measure_mono_null hcover ((measure_biUnion_null_iff hDc).2 hpiece)
  -- the good part
  set s := K \ M with hs
  have hsm : MeasurableSet s := hKc.isClosed.measurableSet.diff (measurableSet_toMeasurable _ _)
  have hgood' : ∀ x ∈ s, ∃ (P : Rd d) (H : Matrix (Fin d) (Fin d) ℝ), H.IsSymm ∧
      HasSecondOrderTaylorAt Z x P H ∧ |H.det| ≤ B := fun x hx =>
    hgood x hx.1.1 (fun h => hx.2 (subset_toMeasurable _ _ h)) (Pm x) (hPmax x hx.1)
  set Hm : Rd d → Matrix (Fin d) (Fin d) ℝ := fun x =>
    if h : x ∈ s then Classical.choose (Classical.choose_spec (hgood' x h)) else 0 with hHm
  have hHm : ∀ x (hx : x ∈ s), (Hm x).IsSymm ∧
      HasSecondOrderTaylorAt Z x (Classical.choose (hgood' x hx)) (Hm x) ∧ |(Hm x).det| ≤ B := by
    intro x hx
    simp only [hHm, dif_pos hx]
    exact Classical.choose_spec (Classical.choose_spec (hgood' x hx))
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt Pm (toCLM (Hm x)) s x := by
    intro x hx
    obtain ⟨hHs, hHT, -⟩ := hHm x hx
    set P := Classical.choose (hgood' x hx)
    have hup : ∀ y ∈ K, ∀ z, ‖z - y‖ < ρ → Z z ≤ Z y + inner ℝ (Pm y) (z - y) := by
      intro y hy z hz
      exact (hPmax y hy).upper (hball y hy.1 (by rw [mem_ball, dist_eq_norm]; exact hz))
    have hPx : Pm x = P := by
      obtain ⟨δ, hδ, hsl⟩ := slope_taylor hHs hHT hρ (θ := 1) one_pos
      have := hsl x (Pm x) (by rw [sub_self, norm_zero]; exact hδ) (hup x hx.1)
      rw [sub_self, norm_zero, mul_zero] at this
      have h0 : WithLp.toLp 2 (Hm x *ᵥ WithLp.ofLp (0 : Rd d)) = 0 := by simp
      rw [h0, sub_zero] at this
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    refine HasFDerivWithinAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun θ hθ => ?_)
    obtain ⟨δ, hδ, hsl⟩ := slope_taylor hHs hHT hρ hθ
    filter_upwards [inter_mem_nhdsWithin s (ball_mem_nhds x hδ)] with y hy
    rw [toCLM_apply, hPx]
    exact hsl y (Pm y) (by rw [← dist_eq_norm]; exact hy.2) (hup y hy.1.1)
  have harea := addHaar_image_le_lintegral_abs_det_fderiv volume hsm hderiv
  have hbound : ∫⁻ x in s, ENNReal.ofReal |(toCLM (Hm x)).det| ≤ ENNReal.ofReal B * volume s := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun x hx => ?_
    rw [toCLM_det]
    exact ENNReal.ofReal_le_ofReal (hHm x hx).2.2
  have hsplit : Pm '' K ⊆ Pm '' s ∪ Pm '' (K ∩ M) := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxM : x ∈ M
    · exact Or.inr ⟨x, ⟨hx, hxM⟩, rfl⟩
    · exact Or.inl ⟨x, ⟨hx, hxM⟩, rfl⟩
  calc volume (ball (0 : Rd d) r) ≤ volume (Pm '' K) := measure_mono himg
    _ ≤ volume (Pm '' s) + volume (Pm '' (K ∩ M)) := (measure_mono hsplit).trans (measure_union_le _ _)
    _ = volume (Pm '' s) := by rw [hnullimg, add_zero]
    _ ≤ ENNReal.ofReal B * volume s := harea.trans hbound
    _ ≤ ENNReal.ofReal B * volume K := by gcongr; exact sdiff_subset

end SplitJensen

end RandomSandpile

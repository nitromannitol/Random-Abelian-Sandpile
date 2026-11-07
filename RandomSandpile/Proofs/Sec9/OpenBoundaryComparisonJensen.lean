import RandomSandpile.Proofs.Sec9.OpenBoundaryComparisonTouch
import RandomSandpile.Proofs.Sec6.StrictConcavityUniformDet

/-! # Comparison principle (Theorem 9.1): Jensen's lemma

`jensen_exists`: let `Z + c|·|²` be convex on `ℝ^d` (`Z` semiconvex). Suppose that for every slope
`p` in a ball `B_r` the function `Z - p·(·)` attains its maximum over a compact `S` at a point of
`A`, where `A` lies at distance `ρ` inside `S`. Then the set of such maximum points is not null.
In particular it is not contained in a given null set `N`.

Proof:
* At a maximum point `x` with slope `p`, convexity gives `Z ≥ Z(x) + p·(· - x) - 2c|· - x|²`
  (`lower_of_max`). Hence the slope is unique (`slope_unique`), and the slope map is
  `4c`-Lipschitz on pairs closer than `ρ/2` (`slope_lipschitz`).
* The slope map sends the maximum points onto `B_r`. A Lipschitz image of a null set is null
  (`volume_image_eq_zero_of_lipschitzOnWith`), applied on countably many small pieces.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set

namespace RandomSandpile

namespace OpenComparison

variable {d : ℕ}

/-- `x` maximizes `Z - p·(·)` over `S`. -/
def IsMaxSlope (Z : Rd d → ℝ) (S : Set (Rd d)) (x p : Rd d) : Prop :=
  ∀ y ∈ S, Z y - inner ℝ p y ≤ Z x - inner ℝ p x

theorem IsMaxSlope.upper {Z : Rd d → ℝ} {S : Set (Rd d)} {x p : Rd d} (h : IsMaxSlope Z S x p)
    {y : Rd d} (hy : y ∈ S) : Z y ≤ Z x + inner ℝ p (y - x) := by
  have := h y hy
  rw [inner_sub_right]; linarith

/-- **Semiconvexity at a maximum point.** -/
theorem lower_of_max {Z : Rd d → ℝ} {S : Set (Rd d)} {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hconv : ConvexOn ℝ univ (fun z => Z z + c * ‖z‖ ^ 2)) {x p : Rd d}
    (hball : ball x ρ ⊆ S) (hmax : IsMaxSlope Z S x p) (y : Rd d) :
    Z x + inner ℝ p (y - x) - 2 * c * ‖y - x‖ ^ 2 ≤ Z y := by
  set v := y - x with hv
  set s₀ := ρ / (2 * (‖v‖ + ρ)) with hs₀
  have hs0 : 0 < s₀ := by positivity
  have hs1 : s₀ ≤ 1 := by
    rw [hs₀, div_le_one (by positivity)]; nlinarith [norm_nonneg v]
  have hsv : s₀ * ‖v‖ < ρ := by
    rw [hs₀, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg v]
  -- the upper bound at `x - s₀ v`
  have hmem : x - s₀ • v ∈ S := hball (by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg hs0.le]; exact hsv)
  have hU := hmax.upper hmem
  rw [show x - s₀ • v - x = -(s₀ • v) by abel, inner_neg_right, real_inner_smul_right] at hU
  -- convexity on the three points `x - s₀ v`, `x`, `y`
  have ha : (0 : ℝ) ≤ 1 / (1 + s₀) := by positivity
  have hb : (0 : ℝ) ≤ s₀ / (1 + s₀) := by positivity
  have hab : 1 / (1 + s₀) + s₀ / (1 + s₀) = 1 := by field_simp
  have hpt : (1 / (1 + s₀)) • (x - s₀ • v) + (s₀ / (1 + s₀)) • y = x := by
    have hy : y = x + v := by rw [hv]; abel
    rw [hy, smul_sub, smul_add, smul_smul]
    have h1 : (1 / (1 + s₀)) • x + (s₀ / (1 + s₀)) • x = x := by
      rw [← add_smul, hab, one_smul]
    have h2 : 1 / (1 + s₀) * s₀ = s₀ / (1 + s₀) := by ring
    rw [h2]
    calc (1 / (1 + s₀)) • x - (s₀ / (1 + s₀)) • v + ((s₀ / (1 + s₀)) • x + (s₀ / (1 + s₀)) • v)
        = (1 / (1 + s₀)) • x + (s₀ / (1 + s₀)) • x := by abel
      _ = x := h1
  have hC := hconv.2 (mem_univ (x - s₀ • v)) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hC
  rw [hpt] at hC
  have hC' : (1 + s₀) * (Z x + c * ‖x‖ ^ 2) ≤
      (Z (x - s₀ • v) + c * ‖x - s₀ • v‖ ^ 2) + s₀ * (Z y + c * ‖y‖ ^ 2) := by
    have h1s : (0 : ℝ) < 1 + s₀ := by positivity
    have := mul_le_mul_of_nonneg_left hC h1s.le
    have e : (1 + s₀) * (1 / (1 + s₀) * (Z (x - s₀ • v) + c * ‖x - s₀ • v‖ ^ 2) +
        s₀ / (1 + s₀) * (Z y + c * ‖y‖ ^ 2)) =
        (Z (x - s₀ • v) + c * ‖x - s₀ • v‖ ^ 2) + s₀ * (Z y + c * ‖y‖ ^ 2) := by
      field_simp
    linarith
  -- norm expansions
  have n1 : ‖x - s₀ • v‖ ^ 2 = ‖x‖ ^ 2 - 2 * s₀ * inner ℝ x v + s₀ ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hs0.le]; ring
  have n2 : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x v + ‖v‖ ^ 2 := by
    have hy : y = x + v := by rw [hv]; abel
    rw [hy, norm_add_sq_real]
  have n1c : c * ‖x - s₀ • v‖ ^ 2 = c * ‖x‖ ^ 2 - 2 * s₀ * c * inner ℝ x v +
      c * s₀ ^ 2 * ‖v‖ ^ 2 := by rw [n1]; ring
  have n2c : s₀ * (c * ‖y‖ ^ 2) = s₀ * c * ‖x‖ ^ 2 + 2 * s₀ * c * inner ℝ x v +
      s₀ * c * ‖v‖ ^ 2 := by rw [n2]; ring
  have key : s₀ * (Z x + inner ℝ p v - c * (1 + s₀) * ‖v‖ ^ 2 - Z y) ≤ 0 := by
    nlinarith [hC', hU, n1c, n2c]
  have hE : Z x + inner ℝ p v - c * (1 + s₀) * ‖v‖ ^ 2 - Z y ≤ 0 := by
    by_contra h
    have := mul_pos hs0 (lt_of_not_ge h)
    linarith
  have : c * (1 + s₀) * ‖v‖ ^ 2 ≤ 2 * c * ‖v‖ ^ 2 := by
    have : c * (1 + s₀) ≤ 2 * c := by nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  linarith

/-- **Uniqueness of the slope** at a maximum point. -/
theorem slope_unique {Z : Rd d → ℝ} {S : Set (Rd d)} {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hconv : ConvexOn ℝ univ (fun z => Z z + c * ‖z‖ ^ 2)) {x p p' : Rd d}
    (hball : ball x ρ ⊆ S) (hmax : IsMaxSlope Z S x p) (hmax' : IsMaxSlope Z S x p') :
    p = p' := by
  by_contra hne
  set D := p - p' with hD
  have hD0 : 0 < ‖D‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set s := min (ρ / (2 * ‖D‖)) (1 / (4 * c + 1)) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  have hsD : s * ‖D‖ < ρ := by
    calc s * ‖D‖ ≤ ρ / (2 * ‖D‖) * ‖D‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hD0.le
      _ = ρ / 2 := by field_simp
      _ < ρ := by linarith
  have hsc : 2 * c * s < 1 := by
    have h1 : s ≤ 1 / (4 * c + 1) := min_le_right _ _
    have h2 : 2 * c * s ≤ 2 * c * (1 / (4 * c + 1)) := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : 2 * c * (1 / (4 * c + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]; linarith
    linarith
  set y := x + s • D
  have hy : y ∈ S := hball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le]
    exact hsD)
  have hlow := lower_of_max hc hρ hconv hball hmax y
  have hup := hmax'.upper hy
  have hyx : y - x = s • D := by simp only [y]; abel
  rw [hyx, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hs0.le] at hlow
  rw [hyx, real_inner_smul_right] at hup
  have hDD : inner ℝ p D - inner ℝ p' D = ‖D‖ ^ 2 := by
    rw [← inner_sub_left, ← hD, real_inner_self_eq_norm_sq]
  have hDD' : s * inner ℝ p D - s * inner ℝ p' D = s * ‖D‖ ^ 2 := by rw [← mul_sub, hDD]
  have h1 : s * ‖D‖ ^ 2 ≤ 2 * c * (s * ‖D‖) ^ 2 := by linarith
  have h2 : 2 * c * (s * ‖D‖) ^ 2 = (2 * c * s) * (s * ‖D‖ ^ 2) := by ring
  have h3 : 0 < s * ‖D‖ ^ 2 := by positivity
  have h4 := mul_pos (sub_pos.2 hsc) h3
  nlinarith

/-- **The slope map is Lipschitz** on pairs of maximum points closer than `ρ/2`. -/
theorem slope_lipschitz {Z : Rd d → ℝ} {S : Set (Rd d)} {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hconv : ConvexOn ℝ univ (fun z => Z z + c * ‖z‖ ^ 2)) {x x' p p' : Rd d}
    (hball : ball x ρ ⊆ S) (hball' : ball x' ρ ⊆ S) (hmax : IsMaxSlope Z S x p)
    (hmax' : IsMaxSlope Z S x' p') (hxx : ‖x - x'‖ < ρ / 2) :
    ‖p' - p‖ ≤ 4 * c * ‖x - x'‖ := by
  set s := ‖x - x'‖ with hs
  rcases eq_or_lt_of_le (norm_nonneg (x - x')) with h0 | hspos
  · have hx : x = x' := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    subst hx
    rw [slope_unique hc hρ hconv hball hmax' hmax, sub_self, norm_zero]
    positivity
  by_cases hh : p' - p = 0
  · rw [hh, norm_zero]; positivity
  set h := p' - p with hhdef
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  set u := ‖h‖⁻¹ • h with hu
  have hun : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hhn.ne']
  have hhu : inner ℝ h u = ‖h‖ := by
    rw [hu, real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  set Y := x' + s • u
  have hYx' : Y - x' = s • u := by simp only [Y]; abel
  have hYx : ‖Y - x‖ < ρ := by
    have : Y - x = (x' - x) + s • u := by simp only [Y]; abel
    rw [this]
    calc ‖(x' - x) + s • u‖ ≤ ‖x' - x‖ + ‖s • u‖ := norm_add_le _ _
      _ = s + s := by rw [norm_sub_rev, norm_smul, hun, Real.norm_of_nonneg hspos.le, mul_one]
      _ < ρ := by linarith
  have hYS : Y ∈ S := hball (by rw [mem_ball, dist_eq_norm]; exact hYx)
  have h1 := hmax.upper hYS
  have h2 := lower_of_max hc hρ hconv hball' hmax' Y
  have h3 := lower_of_max hc hρ hconv hball hmax x'
  rw [hYx', real_inner_smul_right, norm_smul, hun, Real.norm_of_nonneg hspos.le, mul_one] at h2
  have hsplit : inner ℝ p (Y - x) = inner ℝ p (x' - x) + s * inner ℝ p u := by
    rw [show Y - x = (x' - x) + s • u by simp only [Y]; abel, inner_add_right,
      real_inner_smul_right]
  rw [hsplit] at h1
  rw [norm_sub_rev x' x, ← hs] at h3
  have hpu : inner ℝ p' u - inner ℝ p u = ‖h‖ := by
    rw [← inner_sub_left, ← hhdef, hhu]
  have hpu' : s * inner ℝ p' u - s * inner ℝ p u = s * ‖h‖ := by rw [← mul_sub, hpu]
  have key : s * ‖h‖ ≤ 4 * c * s ^ 2 := by linarith
  have : ‖h‖ ≤ 4 * c * s := by
    by_contra hcon
    have := mul_lt_mul_of_pos_left (lt_of_not_ge hcon) hspos
    nlinarith
  exact this

/-- **Jensen's lemma.** -/
theorem jensen_exists {Z : Rd d → ℝ} {S A N : Set (Rd d)} {c ρ r : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hr : 0 < r) (hconv : ConvexOn ℝ univ (fun z => Z z + c * ‖z‖ ^ 2))
    (hball : ∀ x ∈ A, ball x ρ ⊆ S)
    (hmax : ∀ p ∈ ball (0 : Rd d) r, ∃ x ∈ A, IsMaxSlope Z S x p) (hN : volume N = 0) :
    ∃ x ∈ A, x ∉ N ∧ ∃ p, IsMaxSlope Z S x p := by
  set K : Set (Rd d) := {x | x ∈ A ∧ ∃ p ∈ ball (0 : Rd d) r, IsMaxSlope Z S x p} with hK
  by_contra hcon
  have hKN : K ⊆ N := by
    intro x hx
    by_contra hxN
    exact hcon ⟨x, hx.1, hxN, by obtain ⟨p, -, hp⟩ := hx.2; exact ⟨p, hp⟩⟩
  have hK0 : volume K = 0 := measure_mono_null hKN hN
  -- the slope map
  classical
  set P : Rd d → Rd d := fun x => if h : x ∈ K then Classical.choose h.2 else 0 with hP
  have hPmax : ∀ x ∈ K, IsMaxSlope Z S x (P x) := by
    intro x hx
    have := (Classical.choose_spec hx.2).2
    simp only [hP, dif_pos hx]; exact this
  have himg : ball (0 : Rd d) r ⊆ P '' K := by
    intro p hp
    obtain ⟨x, hxA, hxp⟩ := hmax p hp
    have hxK : x ∈ K := ⟨hxA, p, hp, hxp⟩
    exact ⟨x, hxK, (slope_unique hc hρ hconv (hball x hxA) hxp (hPmax x hxK)).symm⟩
  -- countably many pieces
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rd d)
  have hcover : P '' K ⊆ ⋃ a ∈ D, P '' (K ∩ ball a (ρ / 4)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, haD, hxa⟩ := hDd.exists_dist_lt x (by positivity : (0 : ℝ) < ρ / 4)
    exact mem_biUnion haD ⟨x, ⟨hx, by rw [mem_ball]; exact hxa⟩, rfl⟩
  have hpiece : ∀ a ∈ D, volume (P '' (K ∩ ball a (ρ / 4))) = 0 := by
    intro a _
    refine UniformConcavity.volume_image_eq_zero_of_lipschitzOnWith (K := (4 * c).toNNReal) ?_
      (measure_mono_null inter_subset_left hK0)
    refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    have hxx : ‖x - x'‖ < ρ / 2 := by
      have h1 := mem_ball.1 hx.2
      have h2 := mem_ball.1 hx'.2
      rw [← dist_eq_norm]
      calc dist x x' ≤ dist x a + dist a x' := dist_triangle _ _ _
        _ < ρ / 4 + ρ / 4 := by rw [dist_comm a x']; linarith
        _ = ρ / 2 := by ring
    have := slope_lipschitz hc hρ hconv (hball x hx.1.1) (hball x' hx'.1.1) (hPmax x hx.1)
      (hPmax x' hx'.1) hxx
    rw [norm_sub_rev]; exact this
  have hnull : volume (P '' K) = 0 :=
    measure_mono_null hcover ((measure_biUnion_null_iff hDc).2 hpiece)
  have := measure_mono_null himg hnull
  exact (measure_ball_pos volume (0 : Rd d) hr).ne' this

end OpenComparison

end RandomSandpile

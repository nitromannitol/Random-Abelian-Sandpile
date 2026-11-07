import RandomSandpile.Proofs.Sec9.SingleSourceD2TraceBounds
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTrace
import RandomSandpile.Proofs.Sec7.FlatBarrier
import RandomSandpile.Steps.Sec5.ABP

/-!
# Theorem 9.2 in dimension two: `f ≥ -2` for `F*`

SIMPLE-PROOF §6, (6.3). For trace-free `A` and `l < -2`, `α = (-2 - l)/4 > 0`: the integer function
`g = ⌈q_{A-I}⌉ + C` (on `B̄_n`, `0` outside) has `Δg < tr(A - I) + 4 = 2`, so `Δg ≤ 1` and `g`
stabilizes every background `η ≤ 2`; `w = g - q_l - q_A = α|x|² + e + C` with `0 ≤ e < 1`. For
`|p| ≤ αn/4` the minimum of `w - p·x` over `B̄_n` lies in `B_n` (for `n` large), so `p` is a
subgradient: the slope set contains the ball of radius `αn/4`, and `μ*(l, A) ≥ (α/4)² |B_1| / 9`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal

namespace RandomSandpile

open EffectiveOperatorBasic MuLipschitz

namespace SingleSourceD2

/-- `#B_n ≤ (2n + 1)²` in the plane. -/
theorem ncard_ballZ0_two_le (n : ℕ) : ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ) ≤ (2 * n + 1) ^ 2 := by
  classical
  set S : Finset (Site 2) := Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-(n : ℤ)) n
  have hsub : ballZ0 (d := 2) (n : ℝ) ⊆ (S : Set (Site 2)) := by
    intro x hx
    have hc := ABP.ballZ0_subset_cubeZ0 (d := 2) (n : ℝ) hx
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hi := hc i
    simp only [Pi.zero_apply, sub_zero] at hi
    rw [abs_lt] at hi
    constructor
    · have : (-(n : ℝ)) < (x i : ℝ) := hi.1
      exact_mod_cast this.le
    · have : (x i : ℝ) < n := hi.2
      exact_mod_cast this.le
  have h1 : (ballZ0 (d := 2) (n : ℝ)).ncard ≤ S.card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet S)
  have h2 : (S.card : ℝ) = (2 * n + 1) ^ 2 := by
    simp only [S, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    push_cast
    have : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
    rw [this]
    push_cast
    ring
  calc ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ) ≤ S.card := by exact_mod_cast h1
    _ = _ := h2

/-- The Laplacian of the ceiling of a quadratic of trace `-2`, restricted to `B̄`, is `≤ 1` on `B`. -/
theorem lap_ceil_le {B : Set (Site 2)} {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.trace = -2) (C : ℤ)
    {x : Site 2} (hx : x ∈ B) :
    lap ((dClosure B).indicator fun y => ⌈qMZ M y⌉ + C) x ≤ 1 := by
  have hg : ∀ y ∈ dClosure B,
      (((Set.indicator (dClosure B) (fun y => ⌈qMZ M y⌉ + C) y : ℤ)) : ℝ) =
        (⌈qMZ M y⌉ : ℝ) + C := by
    intro y hy
    rw [Set.indicator_of_mem hy]
    push_cast
    ring
  have hnb := fun i => Flat.mem_dClosure_of_nbr hx i
  have hreal : (lap ((dClosure B).indicator fun y => ⌈qMZ M y⌉ + C) x : ℝ) < 2 := by
    rw [← lapR_intCast]
    have hq := PegdenSmartRegularity.lapR_qMZ M x
    rw [hM] at hq
    simp only [lapR, nbrSum, Fin.sum_univ_two] at hq ⊢
    rw [hg _ (hnb 0).1, hg _ (hnb 0).2, hg _ (hnb 1).1, hg _ (hnb 1).2,
      hg _ (mem_dClosure_of_mem hx)]
    have c1 := Int.ceil_lt_add_one (qMZ M (x + unit 0))
    have c2 := Int.ceil_lt_add_one (qMZ M (x - unit 0))
    have c3 := Int.ceil_lt_add_one (qMZ M (x + unit 1))
    have c4 := Int.ceil_lt_add_one (qMZ M (x - unit 1))
    have c5 := Int.le_ceil (qMZ M x)
    push_cast at hq ⊢
    linarith
  have : lap ((dClosure B).indicator fun y => ⌈qMZ M y⌉ + C) x < 2 := by exact_mod_cast hreal
  omega

/-- The slope ball for the ceiling stabilizer. -/
theorem muStar_lower_ceil {z : Rd 2} {l : ℝ} (hl : l < -2) {n : ℕ} (hn : 1 ≤ n)
    (hnα : 1 ≤ 3 / 4 * ((-2 - l) / 4) * (n : ℝ) ^ 2) {η : Site 2 → ℤ}
    (hη : ∀ x ∈ ballZ0 (d := 2) (n : ℝ), η x ≤ 2) :
    volume (closedBall (0 : Rd 2) ((-2 - l) / 4 * n / 4)) ≤
      muStar (ballZ0 (n : ℝ)) η l (traceFreeMat z) := by
  set B := ballZ0 (d := 2) (n : ℝ)
  set A := traceFreeMat z
  set α := (-2 - l) / 4 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  set M : Matrix (Fin 2) (Fin 2) ℝ := A - 1
  have hM : M.trace = -2 := by
    simp only [M, A, Matrix.trace_sub, trace_traceFreeMat, Matrix.trace_one, Fintype.card_fin]
    norm_num
  have hfin : (dClosure B).Finite := dClosure_finite (ballZ0_finite _)
  obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ y ∈ dClosure B, -⌈qMZ M y⌉ ≤ C := by
    obtain ⟨C, hC⟩ := (hfin.image fun y => -⌈qMZ M y⌉).bddAbove
    exact ⟨C, fun y hy => hC ⟨y, hy, rfl⟩⟩
  set g : Site 2 → ℤ := (dClosure B).indicator fun y => ⌈qMZ M y⌉ + C
  have hgS : g ∈ stabilizing η B := by
    refine ⟨⟨fun y => ?_, fun y hy => Set.indicator_of_notMem hy _⟩, fun y hy => ?_⟩
    · by_cases hy : y ∈ dClosure B
      · simp only [g, Set.indicator_of_mem hy]
        linarith [hC y hy]
      · simp only [g, Set.indicator_of_notMem hy, le_refl]
    · have h1 : lap g y ≤ 1 := lap_ceil_le hM C (B := B) hy
      have h2 := hη y hy
      push_cast
      omega
  set w : Site 2 → ℝ := fun y => (g y : ℝ) - (qlZ l y + qMZ A y)
  have hwS : w ∈ perturbedSuper B η l A := Set.mem_image_of_mem _ hgS
  -- `w = α|x|² + e + C` on `B̄`
  have hwq : ∀ y ∈ dClosure B, α * ‖toE y‖ ^ 2 + C ≤ w y ∧ w y < α * ‖toE y‖ ^ 2 + C + 1 := by
    intro y hy
    have hceil1 := Int.le_ceil (qMZ M y)
    have hceil2 := Int.ceil_lt_add_one (qMZ M y)
    have hqM : qMZ M y = qMZ A y - 1 / 2 * ‖toE y‖ ^ 2 := by
      have e : M = A + (-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        simp only [M, neg_smul, one_smul, sub_eq_add_neg]
      simp only [qMZ, e, qM_add_smul_one]
      ring
    have hql : qlZ l y = l / 4 * ‖toE y‖ ^ 2 := by
      simp only [qlZ, ql]; push_cast; ring
    simp only [w, g, Set.indicator_of_mem hy]
    push_cast
    rw [hql, hα]
    constructor <;> linarith [hqM]
  -- the slope ball
  have hball : closedBall (0 : Rd 2) (α * n / 4) ⊆ subGradSet w B := by
    intro p hp
    rw [mem_closedBall, dist_zero_right] at hp
    have h0B : (0 : Site 2) ∈ B := by
      show ‖toE (0 : Site 2) - toE 0‖ < (n : ℝ)
      rw [sub_self, norm_zero]; exact_mod_cast hn
    obtain ⟨x, hxD, hxmin⟩ := Set.exists_min_image (dClosure B)
      (fun y => w y - inner ℝ p (toE y)) hfin ⟨0, mem_dClosure_of_mem h0B⟩
    have hxB : x ∈ B := by
      by_contra hxB
      have hxn : (n : ℝ) ≤ ‖toE x‖ := by
        by_contra h
        exact hxB (show ‖toE x - toE 0‖ < (n : ℝ) by
          rw [toE_zero, sub_zero]; exact not_le.mp h)
      have h1 := hxmin 0 (mem_dClosure_of_mem h0B)
      have h2 := (hwq x hxD).1
      have h3 := (hwq 0 (mem_dClosure_of_mem h0B)).2
      have h4 : inner ℝ p (toE x) ≤ ‖p‖ * ‖toE x‖ := real_inner_le_norm _ _
      have h5 : toE (0 : Site 2) = 0 := toE_zero
      simp only [h5, inner_zero_right, sub_zero, norm_zero] at h1 h3
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have h6 : ‖p‖ * ‖toE x‖ ≤ α * n / 4 * ‖toE x‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      have h7 : α * n * ‖toE x‖ ≤ α * ‖toE x‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hxn (mul_nonneg hα0.le (norm_nonneg (toE x)))
        nlinarith
      have h8 : α * n * n ≤ α * n * ‖toE x‖ :=
        mul_le_mul_of_nonneg_left hxn (mul_nonneg hα0.le hn0)
      nlinarith
    refine Set.mem_biUnion hxB fun y hy => ?_
    have := hxmin y hy
    rw [inner_sub_right]
    linarith
  calc volume (closedBall (0 : Rd 2) (α * n / 4)) ≤ volume (subGradSet w B) := measure_mono hball
    _ ≤ muStar B η l A := le_iSup₂_of_le w hwS le_rfl

/-- **, lower half**: `μ*(l, A_z) > 0` for `l < -2`. -/
theorem muStarBar_traceFree_pos (E : RandomEnvironment 2) (hE : E.ηmax ≤ 2) (z : Rd 2) {l : ℝ}
    (hl : l < -2) : 0 < muStarBar E l (traceFreeMat z) := by
  set α := (-2 - l) / 4 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  set V₁ := (volume (ball (0 : Rd 2) 1)).toReal
  have hV₁t : volume (ball (0 : Rd 2) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hV₁ : 0 < V₁ := ENNReal.toReal_pos (measure_ball_pos volume (0 : Rd 2) one_pos).ne' hV₁t
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, n₀ = ⌈2 / α⌉₊ + 1 := ⟨_, rfl⟩
  have hn₀1 : 1 ≤ n₀ := by rw [hn₀]; omega
  have hn₀α : 2 ≤ α * n₀ := by
    have h1 : 2 / α ≤ (⌈2 / α⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (n₀ : ℝ) = ⌈2 / α⌉₊ + 1 := by rw [hn₀]; push_cast; ring
    rw [div_le_iff₀ hα0] at h1
    rw [h2]; nlinarith
  set c := (α / 4) ^ 2 * V₁ / 9
  have hc : 0 < c := by positivity
  refine hc.trans_le (le_muStarBar_of_eventually (by norm_num) E hn₀1 ?_)
  filter_upwards [ae_all_iff.2 E.bounded] with η hη
  intro n hn
  have hn1 : 1 ≤ n := hn₀1.trans hn
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnα : 1 ≤ 3 / 4 * α * (n : ℝ) ^ 2 := by nlinarith
  have hmain := muStar_lower_ceil (z := z) hl hn1 hnα (η := η) fun x _ => (hη x).2.trans hE
  refine le_trans ?_ hmain
  rw [Measure.addHaar_closedBall _ _ (by positivity), finrank_euclideanSpace_fin,
    ← ENNReal.ofReal_toReal hV₁t, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard := ncard_ballZ0_two_le n
  have h9 : (2 * (n : ℝ) + 1) ^ 2 ≤ 9 * (n : ℝ) ^ 2 := by nlinarith
  have hcn : ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ) ≤ 9 * (n : ℝ) ^ 2 := hcard.trans h9
  calc c * ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ) ≤ c * (9 * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcn hc.le
    _ = (α * n / 4) ^ 2 * V₁ := by simp only [c]; ring

/-- **, lower half**: `f(z) = F*(A_z) ≥ -2`. -/
theorem effOpStarTraceLower : EffOpStarTraceLowerD2Stmt := by
  intro E hE z
  have hE2 : E.ηmax ≤ 2 := by rw [hE]; norm_num
  have hE1 : E.ηmax ≤ 2 * ((2 : ℕ) : ℤ) - 1 := by rw [hE]; norm_num
  unfold traceGraph effOpStar
  by_contra hlt
  set s := sSup {l : ℝ | 0 < muStarBar E l (traceFreeMat z)}
  have hlt' : s < -2 := not_le.mp hlt
  have hmem : (s + -2) / 2 ∈ {l : ℝ | 0 < muStarBar E l (traceFreeMat z)} :=
    muStarBar_traceFree_pos E hE2 z (by linarith)
  have := le_csSup (effOpStar_set_bddAbove (by norm_num) E (traceFreeMat z)) hmem
  linarith

/-- proved. -/
theorem effOpStarTraceBounds : EffOpStarTraceBoundsD2Stmt :=
  effOpStarTraceBounds_of_lower effOpStarTraceLower

end SingleSourceD2

end RandomSandpile

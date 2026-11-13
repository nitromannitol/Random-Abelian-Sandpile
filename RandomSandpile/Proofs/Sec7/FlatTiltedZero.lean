import RandomSandpile.Proofs.Sec7.FlatTilted
import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasicPos

/-!
# `F̄_η` is not flat for backgrounds `η ≤ d - 1`

 §2 (the same argument as).

* `le_muBar_of`, `le_muStarBar_of`: a lower bound for `μ(B_n, η, l, M) / |B_n|` valid almost surely
  and for every `n ≥ 1` passes to `μ(l, M)`, resp. `μ*(l, M)`.
* `mu_zero_lower`: for every `η` and `l > 0`, `u = 0` is locally legal and the supergradient set of
  `-q_l` at `x` contains `closedBall(-(l/d) x, l/(2d))`, so `μ(B_n, η, l, 0) ≥ |B_{l/(2d)}| |B_n|`.
* `muStar_zero_lower`: if `η ≤ d - 1` on `B_n` and `l < d`, then `v(x) = Σ_i x_i (x_i + 1) / 2`
  (cut off outside `B̄_n`) is stabilizing (`Δ v = d`), and the subgradient set of `v - q_l` at `x`
  contains `closedBall(s x + ½ 𝟙, s / 2)`, `s = 1 - l/d`, so `μ*(B_n, η, l, 0) ≥ |B_{s/2}| |B_n|`.
* `not_flatAt_zero`: for every environment with `η ≤ d - 1` almost surely, `μ(l, 0) > 0` for `l > 0`
  and `μ*(l, 0) > 0` for `l < d`, so no level makes both vanish: `F̄_η` is not flat at `0`.
* `zeroEnv d k`: the deterministic background `η ≡ 0`, with the bound field `η_max = k ≥ 0`.
* `not_flatEff_zeroEnv`: the flatness hypothesis of `SingleSourceTheoremFlatStmt` fails for
  `zeroEnv d (2d - 2)`, a background allowed by Theorem 9.2.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal

namespace RandomSandpile

open EffectiveOperatorBasic MuLipschitz

variable {d : ℕ}

/-! ### From lower bounds on balls to the deterministic limits -/

theorem ncard_ballZ0_ne_zero {n : ℕ} (hn : 1 ≤ n) : ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞) ≠ 0 := by
  have hmem : (0 : Site d) ∈ ballZ0 (n : ℝ) := by
    rw [mem_ballZ0, toE_zero, norm_zero]; exact_mod_cast hn
  have := (Set.ncard_pos (ballZ0_finite (d := d) (n : ℝ))).2 ⟨0, hmem⟩
  exact_mod_cast this.ne'

theorem ofReal_le_div_ncard {c : ℝ} (hc : 0 ≤ c) {m : ℝ≥0∞} {n : ℕ} (hn : 1 ≤ n)
    (h : ENNReal.ofReal (c * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ m) :
    ENNReal.ofReal c ≤ m / ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ncard_ballZ0_ne_zero hn)) (Or.inl (by simp))]
  rwa [ENNReal.ofReal_mul hc, ENNReal.ofReal_natCast] at h

theorem le_muBar_of (hd : 1 ≤ d) (E : RandomEnvironment d) {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {c : ℝ}
    (h : ∀ᵐ η ∂E.P, ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ mu (ballZ0 (n : ℝ)) η l M) :
    c ≤ muBar E l M := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (muBar_nonneg E l M)
  have hlim : ∀ᵐ η ∂E.P, ENNReal.ofReal c ≤ limsup (fun n : ℕ => mu (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop := by
    filter_upwards [h] with η hη
    exact le_limsup_of_frequently_le
      ((eventually_ge_atTop 1).mono fun n hn => ofReal_le_div_ncard hc.le hn (hη n hn)).frequently
  unfold muBar
  calc c = (∫⁻ _, ENNReal.ofReal c ∂E.P).toReal := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hc.le]
    _ ≤ _ := ENNReal.toReal_mono (lintegral_mu_ne_top hd E l M) (lintegral_mono_ae hlim)

theorem le_muStarBar_of (hd : 1 ≤ d) (E : RandomEnvironment d) {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {c : ℝ}
    (h : ∀ᵐ η ∂E.P, ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
        muStar (ballZ0 (n : ℝ)) η l M) :
    c ≤ muStarBar E l M := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (muStarBar_nonneg E l M)
  have hlim : ∀ᵐ η ∂E.P, ENNReal.ofReal c ≤
      limsup (fun n : ℕ => muStar (ballZ0 (n : ℝ)) η l M /
        ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop := by
    filter_upwards [h] with η hη
    exact le_limsup_of_frequently_le
      ((eventually_ge_atTop 1).mono fun n hn => ofReal_le_div_ncard hc.le hn (hη n hn)).frequently
  unfold muStarBar
  calc c = (∫⁻ _, ENNReal.ofReal c ∂E.P).toReal := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hc.le]
    _ ≤ _ := ENNReal.toReal_mono (lintegral_muStar_ne_top hd E l M) (lintegral_mono_ae hlim)

/-! ### Elementary lattice inequalities -/

/-- `|z| ≤ |z|²` for a lattice displacement `z = y - x`. -/
theorem norm_le_sq_toE_sub (x y : Site d) : ‖toE y - toE x‖ ≤ ‖toE y - toE x‖ ^ 2 := by
  by_cases hxy : y = x
  · subst hxy; simp
  · have h1 := one_le_norm_toE_sub hxy
    nlinarith

theorem qlZ_sub_eq_inner (hd : 1 ≤ d) (l : ℝ) (x y : Site d) :
    qlZ l y - qlZ l x - inner ℝ ((l / d) • toE x) (toE y - toE x) =
      l / (2 * d) * ‖toE y - toE x‖ ^ 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [qlZ, ql, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, real_inner_comm]
  field_simp
  ring

@[simp] theorem qMZ_zero (x : Site d) : qMZ (0 : Matrix (Fin d) (Fin d) ℝ) x = 0 := by
  simp [qMZ, qM]

/-! ### `μ(l, 0) > 0` for `l > 0` (`u = 0`) -/

theorem mu_zero_lower (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) (η : Site d → ℤ) (n : ℕ) :
    ENNReal.ofReal ((volume (closedBall (0 : Rd d) (l / (2 * d)))).toReal *
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ mu (ballZ0 (n : ℝ)) η l 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : 0 ≤ l / (2 * d) := by positivity
  set V := volume (closedBall (0 : Rd d) (l / (2 * d)))
  have hV : V ≠ ⊤ := measure_closedBall_lt_top.ne
  set B : Set (Site d) := ballZ0 (n : ℝ)
  set w : Site d → ℝ := fun x => ((0 : Site d → ℤ) x : ℝ) - (qlZ l x + qMZ 0 x) with hw
  have hwS : w ∈ perturbedSub B η l 0 := Set.mem_image_of_mem _ (zero_mem_locLegal η B)
  have hball : ∀ x : Site d, closedBall (-((l / d) • toE x)) (l / (2 * d)) ⊆ supGrad w x B := by
    intro x p hp y _
    have he : ‖p + (l / d) • toE x‖ ≤ l / (2 * d) := by
      rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add] at hp; exact hp
    have hcs := abs_real_inner_le_norm (p + (l / d) • toE x) (toE y - toE x)
    have hz := norm_le_sq_toE_sub x y
    have hq := qlZ_sub_eq_inner hd l x y
    have h1 : ‖p + (l / d) • toE x‖ * ‖toE y - toE x‖ ≤ l / (2 * d) * ‖toE y - toE x‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg _)
    have h2 : l / (2 * d) * ‖toE y - toE x‖ ≤ l / (2 * d) * ‖toE y - toE x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hz hr
    have hinner : inner ℝ (p + (l / d) • toE x) (toE y - toE x) =
        inner ℝ p (toE y - toE x) + inner ℝ ((l / d) • toE x) (toE y - toE x) :=
      inner_add_left _ _ _
    simp only [w, Pi.zero_apply, Int.cast_zero, zero_sub, qMZ_zero, add_zero]
    linarith [neg_abs_le (inner ℝ (p + (l / d) • toE x) (toE y - toE x))]
  have hfin : B.Finite := ballZ0_finite _
  calc ENNReal.ofReal (V.toReal * (B.ncard : ℝ))
      = (B.ncard : ℝ≥0∞) * V := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hV,
          ENNReal.ofReal_natCast, mul_comm]
    _ = ∑' _ : B, V := by
        rw [ENNReal.tsum_set_const, ← hfin.cast_ncard_eq]
        simp
    _ ≤ ∑' x : B, volume (supGrad w x B) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        calc V = volume (closedBall (-((l / d) • toE (x : Site d))) (l / (2 * d))) := by
              simp only [V, Measure.addHaar_closedBall _ _ hr]
          _ ≤ _ := measure_mono (hball x)
    _ = volume (supGradSet w B) := ((supGradSetVolume d w B).1).symm
    _ ≤ mu B η l 0 := le_iSup₂_of_le w hwS le_rfl

/-! ### `μ*(l, 0) > 0` for `l < d` when `η ≤ d - 1` (`v = Σ_i x_i (x_i + 1) / 2`) -/

/-- Triangular numbers on `ℤ`: `tri t = t (t + 1) / 2`. -/
def tri (t : ℤ) : ℤ := t * (t + 1) / 2

theorem two_mul_tri (t : ℤ) : 2 * tri t = t * (t + 1) :=
  Int.mul_ediv_cancel' (Int.even_mul_succ_self t).two_dvd

theorem tri_nonneg (t : ℤ) : 0 ≤ tri t := by
  have h := two_mul_tri t
  have : 0 ≤ t * (t + 1) := by
    rcases le_or_gt 0 t with ht | ht
    · positivity
    · nlinarith
  omega

theorem tri_secondDiff (t : ℤ) : -2 * tri t + tri (t + 1) + tri (t - 1) = 1 := by
  have h0 := two_mul_tri t
  have h1 := two_mul_tri (t + 1)
  have h2 := two_mul_tri (t - 1)
  nlinarith

theorem tri_cast (t : ℤ) : ((tri t : ℤ) : ℝ) = (t : ℝ) * ((t : ℝ) + 1) / 2 := by
  have h := two_mul_tri t
  have h' : (2 : ℝ) * (tri t : ℝ) = (t : ℝ) * ((t : ℝ) + 1) := by exact_mod_cast h
  linarith

/-- `g(x) = Σ_i x_i (x_i + 1) / 2`. -/
def triSum (x : Site d) : ℤ := ∑ i : Fin d, tri (x i)

theorem triSum_secondDiff (x : Site d) (i : Fin d) :
    -2 * triSum x + triSum (x + unit i) + triSum (x - unit i) = 1 := by
  have h : ∀ j : Fin d, -2 * tri (x j) + tri ((x + unit i) j) + tri ((x - unit i) j) =
      if j = i then 1 else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_eq_same, ite_true]
      exact tri_secondDiff _
    · simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_eq_of_ne hj, add_zero, sub_zero,
        ite_eq_right hj]
      ring
  calc -2 * triSum x + triSum (x + unit i) + triSum (x - unit i)
      = ∑ j : Fin d, (-2 * tri (x j) + tri ((x + unit i) j) + tri ((x - unit i) j)) := by
        simp only [triSum, Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ j : Fin d, (if j = i then (1 : ℤ) else 0) := Finset.sum_congr rfl fun j _ => h j
    _ = 1 := by simp

theorem lap_triSum (x : Site d) : lap triSum x = d := by
  rw [lap_eq_sum_second_diff, Finset.sum_congr rfl (fun i _ => triSum_secondDiff x i)]
  simp

/-- The vector `𝟙 = (1, …, 1)`. -/
def onesE (d : ℕ) : Rd d := WithLp.toLp 2 (fun _ => (1 : ℝ))

theorem triSum_cast (x : Site d) :
    ((triSum x : ℤ) : ℝ) = (‖toE x‖ ^ 2 + inner ℝ (onesE d) (toE x)) / 2 := by
  have h1 : ‖toE x‖ ^ 2 = ∑ i, ((x i : ℝ)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [toE_apply, sq_abs]
  have h2 : inner ℝ (onesE d) (toE x) = ∑ i, (x i : ℝ) := by
    simp [onesE, PiLp.inner_apply, toE_apply]
  rw [h1, h2]
  simp only [triSum, Int.cast_sum, tri_cast]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `v = g` on `B̄`, `0` elsewhere. -/
def triCut (B : Set (Site d)) (x : Site d) : ℤ := by
  classical exact if x ∈ dClosure B then triSum x else 0

theorem triCut_of_mem {B : Set (Site d)} {x : Site d} (hx : x ∈ dClosure B) :
    triCut B x = triSum x := by
  simp [triCut, hx]

theorem lap_triCut {B : Set (Site d)} {x : Site d} (hx : x ∈ B) : lap (triCut B) x = d := by
  rw [← lap_triSum x, lap_eq_sum_second_diff, lap_eq_sum_second_diff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [triCut_of_mem (subset_dClosure B hx), triCut_of_mem (add_unit_mem_dClosure hx i),
    triCut_of_mem (sub_unit_mem_dClosure hx i)]

theorem triCut_mem_stabilizing (hd : 1 ≤ d) {B : Set (Site d)} {η : Site d → ℤ}
    (hη : ∀ x ∈ B, η x ≤ (d : ℤ) - 1) : triCut B ∈ stabilizing η B := by
  refine ⟨⟨fun x => ?_, fun x hx => by simp [triCut, hx]⟩, fun x hx => ?_⟩
  · by_cases hx : x ∈ dClosure B
    · rw [triCut_of_mem hx]; exact Finset.sum_nonneg fun i _ => tri_nonneg _
    · simp [triCut, hx]
  · rw [lap_triCut hx]
    have := hη x hx
    have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
    linarith

theorem muStar_zero_lower (hd : 1 ≤ d) {l : ℝ} (hl : l < d) {η : Site d → ℤ} {n : ℕ}
    (hη : ∀ x ∈ ballZ0 (n : ℝ), η x ≤ (d : ℤ) - 1) :
    ENNReal.ofReal ((volume (closedBall (0 : Rd d) ((1 - l / d) / 2))).toReal *
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ muStar (ballZ0 (n : ℝ)) η l 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set s : ℝ := 1 - l / d with hs_def
  have hs : 0 < s := by
    rw [hs_def, sub_pos, div_lt_one hd0]; exact hl
  have hr : 0 ≤ s / 2 := by positivity
  set V := volume (closedBall (0 : Rd d) (s / 2))
  have hV : V ≠ ⊤ := measure_closedBall_lt_top.ne
  set B : Set (Site d) := ballZ0 (n : ℝ)
  set w : Site d → ℝ := fun x => ((triCut B x : ℤ) : ℝ) - (qlZ l x + qMZ 0 x) with hw
  have hwS : w ∈ perturbedSuper B η l 0 :=
    Set.mem_image_of_mem _ (triCut_mem_stabilizing hd hη)
  -- on `B̄`, `w(y) = (s/2)|y|² + ½ ⟨𝟙, y⟩`
  have hwval : ∀ y ∈ dClosure B,
      w y = s / 2 * ‖toE y‖ ^ 2 + inner ℝ ((1 / 2 : ℝ) • onesE d) (toE y) := by
    intro y hy
    simp only [w, triCut_of_mem hy, triSum_cast, qMZ_zero, add_zero, qlZ, ql, hs_def,
      real_inner_smul_left]
    field_simp
    ring
  have hball : ∀ x : B, closedBall (s • toE (x : Site d) + (1 / 2 : ℝ) • onesE d) (s / 2) ⊆
      subGrad w x B := by
    rintro ⟨x, hxB⟩ p hp y hy
    have hxc : x ∈ dClosure B := subset_dClosure B hxB
    set c : Rd d := s • toE x + (1 / 2 : ℝ) • onesE d
    have he : ‖p - c‖ ≤ s / 2 := by rw [mem_closedBall, dist_eq_norm] at hp; exact hp
    have hcs := abs_real_inner_le_norm (p - c) (toE y - toE x)
    have hz := norm_le_sq_toE_sub x y
    have h1 : ‖p - c‖ * ‖toE y - toE x‖ ≤ s / 2 * ‖toE y - toE x‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg _)
    have h2 : s / 2 * ‖toE y - toE x‖ ≤ s / 2 * ‖toE y - toE x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hz hr
    have hsplit : inner ℝ p (toE y - toE x) =
        inner ℝ (p - c) (toE y - toE x) + inner ℝ c (toE y - toE x) := by
      rw [inner_sub_left]; ring
    have hc : inner ℝ c (toE y - toE x) =
        s * inner ℝ (toE x) (toE y - toE x) +
          inner ℝ ((1 / 2 : ℝ) • onesE d) (toE y - toE x) := by
      simp only [c, inner_add_left, real_inner_smul_left]
    have hy2 : ‖toE y‖ ^ 2 = ‖toE x‖ ^ 2 + 2 * inner ℝ (toE x) (toE y - toE x) +
        ‖toE y - toE x‖ ^ 2 := by
      have : toE y = toE x + (toE y - toE x) := by abel
      conv_lhs => rw [this]
      rw [norm_add_sq_real]
    have hlin : inner ℝ ((1 / 2 : ℝ) • onesE d) (toE y) =
        inner ℝ ((1 / 2 : ℝ) • onesE d) (toE x) +
          inner ℝ ((1 / 2 : ℝ) • onesE d) (toE y - toE x) := by
      rw [inner_sub_right]; ring
    show w x + inner ℝ p (toE y - toE x) ≤ w y
    rw [hwval x hxc, hwval y hy, hsplit, hc, hy2, hlin]
    linarith [le_abs_self (inner ℝ (p - c) (toE y - toE x))]
  have hfin : B.Finite := ballZ0_finite _
  calc ENNReal.ofReal (V.toReal * (B.ncard : ℝ))
      = (B.ncard : ℝ≥0∞) * V := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hV,
          ENNReal.ofReal_natCast, mul_comm]
    _ = ∑' _ : B, V := by
        rw [ENNReal.tsum_set_const, ← hfin.cast_ncard_eq]
        simp
    _ ≤ ∑' x : B, volume (subGrad w x B) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        calc V = volume (closedBall (s • toE (x : Site d) + (1 / 2 : ℝ) • onesE d) (s / 2)) := by
              simp only [V, Measure.addHaar_closedBall _ _ hr]
          _ ≤ _ := measure_mono (hball x)
    _ = volume (subGradSet w B) := ((supGradSetVolume d w B).2).symm
    _ ≤ muStar B η l 0 := le_iSup₂_of_le w hwS le_rfl

/-! ### No flatness at `M = 0` -/

theorem volume_closedBall_toReal_pos {r : ℝ} (hr : 0 < r) :
    0 < (volume (closedBall (0 : Rd d) r)).toReal := by
  exact ENNReal.toReal_pos (measure_closedBall_pos volume _ hr).ne' measure_closedBall_lt_top.ne

/-- `μ(l, 0) > 0` for every environment and `l > 0`. -/
theorem muBar_zero_pos (hd : 1 ≤ d) (E : RandomEnvironment d) {l : ℝ} (hl : 0 < l) :
    0 < muBar E l 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine (volume_closedBall_toReal_pos (d := d) (by positivity : 0 < l / (2 * d))).trans_le ?_
  exact le_muBar_of hd E (Eventually.of_forall fun η n _ => mu_zero_lower hd hl η n)

/-- `μ*(l, 0) > 0` for `l < d` when `η ≤ d - 1` almost surely. -/
theorem muStarBar_zero_pos (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : ∀ᵐ η ∂E.P, ∀ x, η x ≤ (d : ℤ) - 1) {l : ℝ} (hl : l < d) :
    0 < muStarBar E l 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < (1 - l / d) / 2 := by
    have : l / d < 1 := (div_lt_one hd0).2 hl
    linarith
  refine (volume_closedBall_toReal_pos (d := d) hs).trans_le ?_
  refine le_muStarBar_of hd E ?_
  filter_upwards [hE] with η hη
  exact fun n _ => muStar_zero_lower hd hl fun x _ => hη x

/-- **`F̄_η` is not flat at `0`** for every environment with `η ≤ d - 1` almost surely (hence, by
`flatAt_add_smul_one_iff`, at no multiple of the identity). -/
theorem not_flatAt_zero (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hE : ∀ᵐ η ∂E.P, ∀ x, η x ≤ (d : ℤ) - 1) : ¬ FlatAt E 0 := by
  rintro ⟨h1, h2⟩
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  rcases lt_or_ge 0 (effOp E 0) with hl | hl
  · exact (muBar_zero_pos hd1 E hl).ne' h1
  · exact (muStarBar_zero_pos hd1 E hE (hl.trans_lt hd0)).ne' h2

theorem not_flatEff_of_le (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hE : ∀ᵐ η ∂E.P, ∀ x, η x ≤ (d : ℤ) - 1) : ¬ FlatEff E := fun h =>
  not_flatAt_zero hd E hE (h 0 (Matrix.isSymm_zero))

/-! ### The zero background -/

/-- The deterministic background `η ≡ 0` (law `δ_0`), with the bounds `η_min = 0`, `η_max = k`. -/
def zeroEnv (d : ℕ) (k : ℤ) (hk : 0 ≤ k) : RandomEnvironment d where
  P := Measure.dirac (0 : Config d)
  isProb := inferInstance
  ηmin := 0
  ηmax := k
  bounded := fun x => by
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 ⟨le_rfl, hk⟩
  stationary := fun y => by
    refine ⟨measurable_shift y, ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_shift y) hS, Measure.dirac_apply' _ hS,
      Measure.dirac_apply' _ (measurable_shift y hS)]
    have h0 : shift y (0 : Config d) = 0 := by funext z; simp [shift]
    have hpre : ((0 : Config d) ∈ shift y ⁻¹' S) ↔ (0 : Config d) ∈ S := by
      rw [Set.mem_preimage, h0]
    simp only [Set.indicator]
    by_cases h : (0 : Config d) ∈ S
    · rw [ite_eq_left (hpre.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hpre.1 h')), ite_eq_right h]
  ergodic := fun S hS _ => by
    rw [Measure.dirac_apply' _ hS]
    by_cases h : (0 : Config d) ∈ S
    · right; simp [h]
    · left; simp [h]

theorem zeroEnv_ae (d : ℕ) (k : ℤ) (hk : 0 ≤ k) : ∀ᵐ η ∂(zeroEnv d k hk).P, η = 0 := by
  show ∀ᵐ η ∂Measure.dirac (0 : Config d), η = 0
  rw [ae_dirac_eq]
  exact Filter.eventually_pure.2 rfl

theorem not_flatEff_zeroEnv (hd : 2 ≤ d) (k : ℤ) (hk : 0 ≤ k) : ¬ FlatEff (zeroEnv d k hk) := by
  refine not_flatEff_of_le hd _ ((zeroEnv_ae d k hk).mono fun η hη x => ?_)
  rw [hη]
  have : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  simp only [Pi.zero_apply]
  linarith

theorem two_mul_sub_two_nonneg (hd : 2 ≤ d) : (0 : ℤ) ≤ 2 * (d : ℤ) - 2 := by omega

/-- The flatness hypothesis of `SingleSourceTheoremFlatStmt` fails for the zero background with the
bound field `η_max = 2d - 2` required there. -/
theorem not_flatEff_zeroEnv_singleSource (hd : 2 ≤ d) :
    ¬ FlatEff (zeroEnv d (2 * (d : ℤ) - 2) (two_mul_sub_two_nonneg hd)) ∧
      (zeroEnv d (2 * (d : ℤ) - 2) (two_mul_sub_two_nonneg hd)).ηmax = 2 * (d : ℤ) - 2 :=
  ⟨not_flatEff_zeroEnv hd _ _, rfl⟩

/-! ### Positive definite matrices: the half of flatness that recurrence does not give

 §4. At a Peano point `x₁ ≠ 0` of the toppled region of a single-source
limit, with `N = D²u(x₁)`, recurrence (Prop 3.4) and Prop 3.3 give `μ*(l, N) = 0` for `l > 0`
(Claim R), hence `μ*(0, N) = 0`. Since `u = 0` is locally legal for every `η`, `μ(0, N) > 0` as soon
as `N ≥ λ I` with `λ > 0`; then `F̄_η(N) < 0` (`effOp_neg_of_quad`), so the printed constraint
`F̄_η(D²(v̄ + G)) ≥ 0` fails at `x₁`. -/

/-- If `q_M(z) ≥ (λ/2)|z|²` (`λ > 0`), the supergradient set of `-q_M` at `x` contains
`closedBall(-M x, λ/2)`, so `μ(B_n, η, 0, M) ≥ |B_{λ/2}| |B_n|` (`u = 0`). -/
theorem mu_lower_of_quad {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) {lam : ℝ}
    (hlam : 0 < lam) (hML : ∀ z : Rd d, lam / 2 * ‖z‖ ^ 2 ≤ qM M z) (η : Site d → ℤ) (n : ℕ) :
    ENNReal.ofReal ((volume (closedBall (0 : Rd d) (lam / 2))).toReal *
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ mu (ballZ0 (n : ℝ)) η 0 M := by
  have hr : 0 ≤ lam / 2 := by positivity
  set V := volume (closedBall (0 : Rd d) (lam / 2))
  have hV : V ≠ ⊤ := measure_closedBall_lt_top.ne
  set B : Set (Site d) := ballZ0 (n : ℝ)
  set w : Site d → ℝ := fun x => ((0 : Site d → ℤ) x : ℝ) - (qlZ 0 x + qMZ M x) with hw
  have hwS : w ∈ perturbedSub B η 0 M := Set.mem_image_of_mem _ (zero_mem_locLegal η B)
  have hball : ∀ x : Site d, closedBall (-(gradQ M x)) (lam / 2) ⊆ supGrad w x B := by
    intro x p hp y _
    have he : ‖p + gradQ M x‖ ≤ lam / 2 := by
      rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add] at hp; exact hp
    have hcs := abs_real_inner_le_norm (p + gradQ M x) (toE y - toE x)
    have hz := norm_le_sq_toE_sub x y
    have hq : qMZ M y - qMZ M x - inner ℝ (gradQ M x) (toE y - toE x) =
        qM M (toE y - toE x) := by
      rw [qMZ_expand hM]; rfl
    have hlow := hML (toE y - toE x)
    have h1 : ‖p + gradQ M x‖ * ‖toE y - toE x‖ ≤ lam / 2 * ‖toE y - toE x‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg _)
    have h2 : lam / 2 * ‖toE y - toE x‖ ≤ lam / 2 * ‖toE y - toE x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hz hr
    have hinner : inner ℝ (p + gradQ M x) (toE y - toE x) =
        inner ℝ p (toE y - toE x) + inner ℝ (gradQ M x) (toE y - toE x) :=
      inner_add_left _ _ _
    have hql0 : ∀ z : Site d, qlZ 0 z = 0 := fun z => by simp [qlZ, ql]
    simp only [w, Pi.zero_apply, Int.cast_zero, zero_sub, hql0, zero_add]
    linarith [neg_abs_le (inner ℝ (p + gradQ M x) (toE y - toE x))]
  have hfin : B.Finite := ballZ0_finite _
  calc ENNReal.ofReal (V.toReal * (B.ncard : ℝ))
      = (B.ncard : ℝ≥0∞) * V := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hV,
          ENNReal.ofReal_natCast, mul_comm]
    _ = ∑' _ : B, V := by
        rw [ENNReal.tsum_set_const, ← hfin.cast_ncard_eq]
        simp
    _ ≤ ∑' x : B, volume (supGrad w x B) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        calc V = volume (closedBall (-(gradQ M (x : Site d))) (lam / 2)) := by
              simp only [V, Measure.addHaar_closedBall _ _ hr]
          _ ≤ _ := measure_mono (hball x)
    _ = volume (supGradSet w B) := ((supGradSetVolume d w B).1).symm
    _ ≤ mu B η 0 M := le_iSup₂_of_le w hwS le_rfl

/-- `μ(0, M) > 0` for every environment when `q_M(z) ≥ (λ/2)|z|²`, `λ > 0`. -/
theorem muBar_pos_of_quad (hd : 1 ≤ d) (E : RandomEnvironment d) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.IsSymm) {lam : ℝ} (hlam : 0 < lam) (hML : ∀ z : Rd d, lam / 2 * ‖z‖ ^ 2 ≤ qM M z) :
    0 < muBar E 0 M :=
  (volume_closedBall_toReal_pos (d := d) (by positivity : 0 < lam / 2)).trans_le
    (le_muBar_of hd E (Eventually.of_forall fun η n _ => mu_lower_of_quad hM hlam hML η n))

/-- **The missing half of flatness.** If `q_M ≥ (λ/2)|·|²` with `λ > 0` and `μ*(0, M) = 0` (the
half that recurrence gives at a toppled Peano Hessian), then `F̄_η(M) < 0`. -/
theorem effOp_neg_of_quad (hd : 2 ≤ d) (E : RandomEnvironment d) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.IsSymm) {lam : ℝ} (hlam : 0 < lam) (hML : ∀ z : Rd d, lam / 2 * ‖z‖ ^ 2 ≤ qM M z)
    (h0 : muStarBar E 0 M = 0) : effOp E M < 0 := by
  by_contra hneg
  have hnn : 0 ≤ effOp E M := not_lt.1 hneg
  have hG := isGreatest_effOp muConvergence_unconditional hd E hM
  have h1 : muBar E 0 M ≤ muBar E (effOp E M) M := muBar_mono muMonotone (by omega) E M hnn
  have h2 : muStarBar E (effOp E M) M ≤ muStarBar E 0 M :=
    muStarBar_anti muMonotone (by omega) E M hnn
  have heq : muBar E (effOp E M) M = muStarBar E (effOp E M) M := hG.1
  have hpos := muBar_pos_of_quad (by omega) E hM hlam hML
  linarith

/-- **Non-flatness on lines with a positive definite critical matrix.** Let
`M_c = M + (F̄_η(M)/d) I` be the critical matrix of the line `M + ℝ I` (`F̄_η(M_c) = 0`). If
`q_{M_c} ≥ (λ/2)|·|²` with `λ > 0`, then `F̄_η` is not flat at `M`: `u = 0` is locally legal and
bends below `q_{M_c}`, so `μ(F̄_η(M), M) = μ(0, M_c) > 0`. -/
theorem not_flatAt_of_critical_quad (hd : 2 ≤ d) (E : RandomEnvironment d)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) {lam : ℝ} (hlam : 0 < lam)
    (hML : ∀ z : Rd d,
      lam / 2 * ‖z‖ ^ 2 ≤ qM (M + (effOp E M / d) • (1 : Matrix (Fin d) (Fin d) ℝ)) z) :
    ¬ FlatAt E M := by
  rintro ⟨h1, -⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hpos := muBar_pos_of_quad (by omega) E (isSymm_add_smul_one hM _) hlam hML
  have hsh := (muBar_shift muShift (by omega) E 0 (effOp E M / d) M).1
  rw [zero_add, mul_div_cancel₀ _ hd0.ne'] at hsh
  rw [hsh] at hpos
  exact hpos.ne' h1

theorem qM_smul_one_eq (c : ℝ) (x : Rd d) :
    qM (c • (1 : Matrix (Fin d) (Fin d) ℝ)) x = c * ‖x‖ ^ 2 / 2 := by
  simp only [qM, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  rw [← norm_sq_eq_dot]
  ring

/-- At `M = 0` the critical matrix is `(F̄_η(0)/d) I`: if `F̄_η(0) > 0`, `F̄_η` is not flat at `0`
(for every environment). The printed Theorem 9.2 forces `F̄_η(0) ≥ 0`; with flatness
at `0` this leaves only `F̄_η(0) = 0`. -/
theorem not_flatAt_zero_of_effOp_pos (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hpos : 0 < effOp E 0) : ¬ FlatAt E 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine not_flatAt_of_critical_quad hd E Matrix.isSymm_zero (lam := effOp E 0 / d)
    (by positivity) fun z => ?_
  rw [zero_add, qM_smul_one_eq]
  linarith

end RandomSandpile

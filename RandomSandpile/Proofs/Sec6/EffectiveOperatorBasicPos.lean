import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasic

/-! # Lemma 6.4, step 4: positivity of `μ(l, M)` for large `l`

`muPositive : MuPositiveStmt`. Let `l ≥ d(|M|₂ + 1)` and `w = -(q_l + q_M)` (the zero toppling).
The quadratic `q = q_l + q_M` satisfies `q(y) - q(x) - ∇q(x)·(y - x) ≥ |y - x|²/2`, and distinct
lattice points are at distance `≥ 1`. Hence `B̄(-∇q(x), 1/2) ⊆ ∂⁺(w, x, B_n)` for every `x`, and by
Lemma 5.3 (the volume of `∂⁺(w, B_n)` is the sum over `x`) `μ(B_n, η, l, M) ≥ |B̄_{1/2}| |B_n|`. -/

open MeasureTheory LatticeProb Filter Set Metric
open scoped ENNReal Topology Matrix

namespace RandomSandpile

namespace EffectiveOperatorBasic

open MuLipschitz

variable {d : ℕ}

theorem one_le_norm_toE_sub {x y : Site d} (hxy : y ≠ x) : 1 ≤ ‖toE y - toE x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
    by_contra h
    exact hxy (funext fun i => by_contra fun hne => h ⟨i, hne⟩)
  have h1 : (1 : ℤ) ≤ |y i - x i| := Int.one_le_abs (sub_ne_zero.2 hi)
  have h2 : (1 : ℝ) ≤ |((y i - x i : ℤ) : ℝ)| := by exact_mod_cast h1
  have h3 : ‖(toE y - toE x) i‖ ≤ ‖toE y - toE x‖ := PiLp.norm_apply_le _ i
  have h4 : (toE y - toE x) i = ((y i - x i : ℤ) : ℝ) := by
    simp [toE_apply]
  rw [h4, Real.norm_eq_abs] at h3
  linarith

theorem norm_sq_eq_dot (v : Rd d) : ‖v‖ ^ 2 = WithLp.ofLp v ⬝ᵥ WithLp.ofLp v := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- `x · B x ≥ -|B|₂ |x|²` for symmetric `B`. -/
theorem dot_mulVec_ge {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.IsSymm) (v : Rd d) :
    -‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B‖ * ‖v‖ ^ 2 ≤
      WithLp.ofLp v ⬝ᵥ (B *ᵥ WithLp.ofLp v) := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.1 (posSemidef_add_smul_one hB)).2
    (WithLp.ofLp v)
  rw [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, ← norm_sq_eq_dot] at h
  linarith

/-- The quadratic `q_l + q_M` is uniformly convex with modulus `1` when `l ≥ d(|M|₂ + 1)`. -/
theorem quad_lower {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (hd : 1 ≤ d) {l : ℝ}
    (hl : (d : ℝ) * (‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M‖ + 1) ≤ l) (x y : Site d) :
    (1 / 2 : ℝ) * ‖toE y - toE x‖ ^ 2 ≤
      (qlZ l y + qMZ M y) - (qlZ l x + qMZ M x) -
        inner ℝ ((l / d) • toE x + gradQ M x) (toE y - toE x) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set t := ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M‖
  have hM2 := qMZ_expand hM x y
  have hdiff : WithLp.ofLp (toE y) - WithLp.ofLp (toE x) = WithLp.ofLp (toE y - toE x) := rfl
  rw [hdiff] at hM2
  have hge := dot_mulVec_ge hM (toE y - toE x)
  -- the `q_l` part
  have hql : qlZ l y - qlZ l x - inner ℝ ((l / d) • toE x) (toE y - toE x) =
      l / (2 * d) * ‖toE y - toE x‖ ^ 2 := by
    simp only [qlZ, ql, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [norm_sub_sq_real, real_inner_comm]
    field_simp
    ring
  have hlt : l / (2 * d) ≥ (t + 1) / 2 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  rw [inner_add_left]
  have hn : 0 ≤ ‖toE y - toE x‖ ^ 2 := sq_nonneg _
  nlinarith

/-- **Step 4** (`MuPositiveStmt`). -/
theorem muPositive : MuPositiveStmt := by
  intro d hd M hM
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  set V := volume (closedBall (0 : Rd d) (1 / 2))
  have hV : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hV0 : 0 < V.toReal := ENNReal.toReal_pos (measure_closedBall_pos volume _ (by norm_num)).ne' hV
  refine ⟨(d : ℝ) * (‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M‖ + 1), V.toReal, hV0,
    fun l hl n hn η => ?_⟩
  set B : Set (Site d) := ballZ0 (n : ℝ)
  set w : Site d → ℝ := fun x => ((0 : Site d → ℤ) x : ℝ) - (qlZ l x + qMZ M x) with hw
  have hwS : w ∈ perturbedSub B η l M := Set.mem_image_of_mem _ (zero_mem_locLegal η B)
  have hball : ∀ x : Site d, closedBall (-((l / d) • toE x + gradQ M x)) (1 / 2) ⊆
      supGrad w x B := by
    intro x p hp y _
    have hq := quad_lower hM hd1 hl x y
    set g := (l / d) • toE x + gradQ M x
    have he : ‖p + g‖ ≤ 1 / 2 := by
      rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add] at hp; exact hp
    have hinner : inner ℝ p (toE y - toE x) =
        inner ℝ (p + g) (toE y - toE x) - inner ℝ g (toE y - toE x) := by
      rw [inner_add_left]; ring
    have hcs : -(‖p + g‖ * ‖toE y - toE x‖) ≤ inner ℝ (p + g) (toE y - toE x) := by
      have := abs_real_inner_le_norm (p + g) (toE y - toE x)
      linarith [neg_abs_le (inner ℝ (p + g) (toE y - toE x))]
    have hkey : (1 / 2 : ℝ) * ‖toE y - toE x‖ ≤ (1 / 2 : ℝ) * ‖toE y - toE x‖ ^ 2 := by
      by_cases hxy : y = x
      · subst hxy; simp
      · have h1 := one_le_norm_toE_sub hxy
        nlinarith
    have hpe : ‖p + g‖ * ‖toE y - toE x‖ ≤ (1 / 2 : ℝ) * ‖toE y - toE x‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg _)
    simp only [w, Pi.zero_apply, Int.cast_zero, zero_sub]
    rw [hinner]
    linarith
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
        calc V = volume (closedBall (-((l / d) • toE (x : Site d) + gradQ M x)) (1 / 2)) := by
              simp only [V, Measure.addHaar_closedBall _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          _ ≤ _ := measure_mono (hball x)
    _ = volume (supGradSet w B) := ((supGradSetVolume d w B).1).symm
    _ ≤ mu B η l M := le_iSup₂_of_le w hwS le_rfl

end EffectiveOperatorBasic

end RandomSandpile

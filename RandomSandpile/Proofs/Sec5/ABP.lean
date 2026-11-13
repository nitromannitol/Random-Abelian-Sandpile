import RandomSandpile.Steps.Sec5.ABP

/-! # Lemma 5.2 (the discrete Alexandroff-Bakelman-Pucci estimate): proofs of the steps

Proofs of the step statements of `RandomSandpile/Steps/Sec5/ABP.lean` and the assembly
`abp : ABPStmt`. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal Pointwise

namespace RandomSandpile

open ABP

/-- ABPeq:1: `|p · (z - x)| ≤ |p| D < w(x) - S` and `w(z) ≤ S` on `∂A`. -/
theorem tiltedPlaneAbove : TiltedPlaneAboveStmt := by
  intro d w A x _ S D p hS hD hp z hz
  have h1 := neg_abs_le (inner ℝ p (toE z - toE x))
  have h2 := abs_real_inner_le_norm p (toE z - toE x)
  have h3 : ‖p‖ * ‖toE z - toE x‖ ≤ ‖p‖ * D :=
    mul_le_mul_of_nonneg_left (hD z (bdry_subset_dClosure _ hz)) (norm_nonneg p)
  linarith [hS z hz]

/-- The sliding argument: a maximiser `y` over the finite set `Ā` of
`z ↦ w(z) - p · (z - x)` is a touching point of the lowered plane, and it is not on `∂A`, where
the plane through `(x, w(x))` is strictly above `w`. -/
theorem slidePlane : SlidePlaneStmt := by
  intro d w A hA x hx p hbd
  obtain ⟨y, hy, hmax⟩ := Set.exists_max_image (dClosure A)
    (fun z => w z - inner ℝ p (toE z - toE x)) (dClosure_finite hA) ⟨x, subset_dClosure A hx⟩
  have hyA : y ∈ A := by
    rcases (dClosure_eq A ▸ hy : y ∈ A ∪ bdry A) with hyA | hyb
    · exact hyA
    · have h1 := hmax x (subset_dClosure A hx)
      have h2 := hbd y hyb
      simp only [sub_self, inner_zero_right, sub_zero] at h1
      linarith
  refine Set.mem_iUnion₂.2 ⟨y, hyA, fun z hz => ?_⟩
  have h := hmax z hz
  have hsplit : inner ℝ p (toE z - toE y) =
      inner ℝ p (toE z - toE x) - inner ℝ p (toE y - toE x) := by
    rw [← inner_sub_right]; congr 1; abel
  linarith

/-- `diam(B̄_n) ≤ 3n`: points of `∂B_n` are neighbours of points of `B_n`, so `|z| < n + 1` on
`B̄_n`, while `n ≥ 1` as soon as `B_n ≠ ∅`. -/
theorem closureBallDiam : ClosureBallDiamStmt := by
  intro d n x hx z hz
  have hx' := mem_ballZ0.1 hx
  have hn : (0 : ℝ) < n := lt_of_le_of_lt (norm_nonneg _) hx'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast hn.ne')
  have hz' : ‖toE z‖ < n + 1 := by
    rcases (dClosure_eq _ ▸ hz : z ∈ ballZ0 (n : ℝ) ∪ bdry (ballZ0 (n : ℝ))) with hzB | hzb
    · linarith [mem_ballZ0.1 hzB]
    · obtain ⟨-, y, hyB, hadj⟩ := mem_bdry.1 hzb
      have hy' := mem_ballZ0.1 hyB
      obtain ⟨i, h | h⟩ := hadj
      · have : toE z = toE y - toE (unit i) := by rw [h, toE_add]; abel
        rw [this]
        linarith [norm_sub_le (toE y) (toE (unit i)), norm_toE_unit (d := d) i]
      · have : toE z = toE y + toE (unit i) := by rw [h, toE_add]
        rw [this]
        linarith [norm_add_le (toE y) (toE (unit i)), norm_toE_unit (d := d) i]
  linarith [norm_sub_le (toE z) (toE x)]

/-- The volume of a Euclidean ball: `|B_r(0)| = ω_d r^d` with `ω_d = |B_1(0)|`, so
`B_r(0) ⊆ E` gives `r ≤ ω_d^{-1/d} |E|^{1/d}`. -/
theorem ballVolumeRadius : BallVolumeRadiusStmt := by
  intro d hd
  set ω : ℝ := (volume (Metric.ball (0 : Rd d) 1)).toReal with hω
  have hωpos : 0 < ω :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Rd d) one_pos).ne'
      measure_ball_lt_top.ne
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  refine ⟨(ω ^ (1 / (d : ℝ)))⁻¹, by positivity, fun r hr E hE hEt => ?_⟩
  set V : ℝ := (volume E).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  rcases hr.eq_or_lt with hr0 | hrpos
  · rw [← hr0]; positivity
  have hvol : volume (Metric.ball (0 : Rd d) r) =
      ENNReal.ofReal (r ^ d) * volume (Metric.ball (0 : Rd d) 1) := by
    rw [Measure.addHaar_ball_of_pos volume (0 : Rd d) hrpos, finrank_euclideanSpace_fin]
  have hle : r ^ d * ω ≤ V := by
    have := ENNReal.toReal_mono hEt (measure_mono hE)
    rwa [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hle' : r ^ d ≤ V / ω := by rw [le_div_iff₀ hωpos]; exact hle
  have hroot : r = (r ^ d) ^ (1 / (d : ℝ)) := by
    rw [one_div, Real.pow_rpow_inv_natCast hr (by omega)]
  calc r = (r ^ d) ^ (1 / (d : ℝ)) := hroot
    _ ≤ (V / ω) ^ (1 / (d : ℝ)) := Real.rpow_le_rpow (by positivity) hle' (by positivity)
    _ = (ω ^ (1 / (d : ℝ)))⁻¹ * V ^ (1 / (d : ℝ)) := by
      rw [Real.div_rpow hV0 hωpos.le, div_eq_inv_mul]

/-- `∂⁻(w, A) = -∂⁺(-w, A)`, and Lebesgue measure is invariant under `p ↦ -p`. -/
theorem subGradNegVolume : SubGradNegVolumeStmt := by
  intro d w A
  have hset : subGradSet w A = -(supGradSet (fun z => -w z) A) := by
    ext p
    simp only [subGradSet, supGradSet, subGrad, supGrad, Set.mem_neg, Set.mem_iUnion,
      Set.mem_ofPred_eq, exists_prop, inner_neg_left]
    refine exists_congr fun y => and_congr_right fun _ => forall₂_congr fun z _ => ?_
    constructor <;> intro h <;> linarith
  rw [hset, Measure.measure_neg]

/-- Lemma 5.2 (ABP). -/
theorem abp : ABPStmt :=
  abp_of_steps tiltedPlaneAbove slidePlane closureBallDiam ballVolumeRadius subGradNegVolume

end RandomSandpile

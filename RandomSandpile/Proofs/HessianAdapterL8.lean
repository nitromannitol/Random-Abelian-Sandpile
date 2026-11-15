import RandomSandpile.Proofs.HessianAdapterDefs

/-!
# The identity-coefficient Calderón–Zygmund estimate
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal

namespace HessianAdapter

open PDE

private theorem field_mean_norm (d : ℕ) (p : ℝ) (U : Set (Vec d))
    (hUPos : 0 < volume U) (hUTop : volume U < ⊤) (F : Vec d → Vec d)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn U)) :
    euclideanFieldLpMeanNormOn U (ENNReal.ofReal p) F
      (memLp_normalizedVolumeOn_of_memLpOn hF hUPos) =
    ((volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
      eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn U)).toReal := by
  unfold euclideanFieldLpMeanNormOn
  rw [lpMeanNormOn_eq_toReal]
  congr 1
  exact eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUTop _ _

private theorem identity_perturbation (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    IsMatrixPerturbationLE δ (1 : Mat d) (1 : Mat d) := by
  intro xi
  have hzero : matVecMul ((1 : Mat d) - 1) xi = 0 := by
    funext i
    simp [matVecMul]
  rw [hzero]
  have hnorm : vecEuclideanNorm (0 : Vec d) = 0 := by
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  rw [hnorm]
  exact mul_nonneg hδ (Real.sqrt_nonneg _)

private theorem field_mean_norm_real (d : ℕ) (p : ℝ) (U : Set (Vec d))
    (hUPos : 0 < volume U) (hUTop : volume U < ⊤) (F : Vec d → Vec d)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn U)) :
    euclideanFieldLpMeanNormOn U (ENNReal.ofReal p) F
      (memLp_normalizedVolumeOn_of_memLpOn hF hUPos) =
    (volume U).toReal ^ (-(1 / ENNReal.ofReal p).toReal) *
      (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn U)).toReal := by
  rw [field_mean_norm d p U hUPos hUTop F hF]
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_inv,
    ← Real.rpow_neg_eq_inv_rpow]

/-- The identity-coefficient estimate in unnormalized `Lᵖ` norms. -/
theorem L8_erl_lp (d : ℕ) (hd : 0 < d) : ErlLpStmt d := by
  obtain ⟨C, hC, hCZ⟩ := exists_calderonZygmund_identity d hd
  intro p hp
  let S := euclideanBall (0 : Vec d) (1 / 2 : ℝ)
  let T := euclideanBall (0 : Vec d) 1
  have hSpos : 0 < volume S := volume_euclideanBall_pos _ (by norm_num)
  have hTpos : 0 < volume T := volume_euclideanBall_pos _ (by norm_num)
  have hStop : volume S < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  have hTtop : volume T < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  let a := (volume S).toReal ^ (-(1 / ENNReal.ofReal p).toReal)
  let b := (volume T).toReal ^ (-(1 / ENNReal.ofReal p).toReal)
  let c := (volume T).toReal ^ (-(1 / (2 : ℝ)))
  have ha : 0 < a := Real.rpow_pos_of_pos (ENNReal.toReal_pos hSpos.ne' hStop.ne) _
  have hb : 0 ≤ b := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hc : 0 ≤ c := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hK : 0 ≤ a⁻¹ * C * (c + p * b) := by positivity
  refine ⟨ENNReal.ofReal (a⁻¹ * C * (c + p * b)), ENNReal.ofReal_ne_top, ?_⟩
  intro u F hFm hF hEq
  have hpert : ∀ᵐ x ∂volumeOn T,
      IsMatrixPerturbationLE (1 / (C * p)) ((fun _ : Vec d => (1 : Mat d)) x) 1 := by
    filter_upwards with x
    exact identity_perturbation d _ (by positivity)
  obtain ⟨_, hgrad, hest⟩ := hCZ p hp (fun _ => (1 : Mat d))
    (by intro i j; exact aemeasurable_const) hpert u F hFm hF hEq
  have hL2 := u.gradMemL2.memLp_vecEuclideanNorm
  have henergy := sqrt_integralAverage_vecNormSq_euclideanBall_le_euclideanFieldLpNormOn
    (F := u.grad) (p := 2) (by norm_num) (0 : Vec d) (R := 1) (by norm_num)
    (V := T) (by rfl) (by simpa using hL2)
  rw [field_mean_norm_real d p S hSpos hStop u.grad hgrad,
      field_mean_norm_real d p T hTpos hTtop F hF] at hest
  have henergy' : Real.sqrt (integralAverage T (fun x => vecNormSq (u.grad x))) ≤
      c * (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volumeOn T)).toReal := by
    simpa [c, T, euclideanFieldLpNormOn, lpNormOn_eq_toReal, eLpNormOn, div_eq_mul_inv] using henergy
  have hreal : (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
        (volumeOn S)).toReal ≤
      (a⁻¹ * C * (c + p * b)) *
        ((eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volumeOn T)).toReal +
         (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn T)).toReal) := by
    have hx : 0 ≤ (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volumeOn T)).toReal := ENNReal.toReal_nonneg
    have hy : 0 ≤ (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn T)).toReal := ENNReal.toReal_nonneg
    change a * _ ≤ C * (_ + p * (b * _)) at hest
    rw [show a⁻¹ * C * (c + p * b) *
      ((eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volumeOn T)).toReal +
       (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn T)).toReal) =
      a⁻¹ * (C * (c + p * b) *
      ((eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volumeOn T)).toReal +
       (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) (volumeOn T)).toReal)) by ring]
    apply (le_inv_mul_iff₀ ha).2
    nlinarith [mul_nonneg hc hy, mul_nonneg (mul_nonneg (by linarith : 0 ≤ p) hb) hx,
      mul_nonneg (by linarith : 0 ≤ C) (sub_nonneg.mpr henergy')]
  apply (ENNReal.toReal_le_toReal hgrad.eLpNorm_ne_top (by finiteness)).1
  simpa [S, T, ENNReal.toReal_mul, ENNReal.toReal_add, hL2.eLpNorm_ne_top,
    hF.eLpNorm_ne_top, ENNReal.toReal_ofReal hK] using hreal

end HessianAdapter

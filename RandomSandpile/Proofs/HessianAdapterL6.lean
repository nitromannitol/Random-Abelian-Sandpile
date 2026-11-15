import LatticeProb.Analysis.HessianLpReduction
import RandomSandpile.Proofs.HessianAdapterDefs

/-!
# Coordinate transport for the Hessian estimate
-/

open MeasureTheory Metric
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace HessianAdapter

open PDE

private theorem norm_toLp (d : ℕ) (x : Vec d) :
    ‖(WithLp.toLp 2 x : Euc d)‖ = vecEuclideanNorm x := by
  rw [EuclideanSpace.norm_eq, vecEuclideanNorm, vecNormSq_eq_sum_sq]
  simp only [Real.norm_eq_abs, sq_abs]

private theorem toLp_preimage_ball (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (WithLp.toLp 2 : Vec d → Euc d) ⁻¹' ball 0 r = euclideanBall 0 r := by
  rw [EuclideanSpace.ball_zero_eq r hr]
  ext x
  simp [euclideanBall, euclideanSqDist, vecNormSq_eq_sum_sq]

/-- Coordinate derivative transport, as in `HessianAdapterL11`. -/
private theorem fderiv_toLp {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Euc d → F) (x u : Vec d) :
    fderiv ℝ (fun z : Vec d => f (WithLp.toLp 2 z)) x u =
      fderiv ℝ f (WithLp.toLp 2 x) (WithLp.toLp 2 u) := by
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.comp_right_fderiv
    (f := f) (x := x)
  exact congrArg (fun L => L u) h

private theorem toLp_basis {d : ℕ} (i : Fin d) :
    WithLp.toLp 2 (basisVec i) = EuclideanSpace.basisFun (Fin d) ℝ i := by
  simp [basisVec, EuclideanSpace.basisFun_apply]

private theorem hessian_entry {d : ℕ} (w : Euc d → ℝ) (x : Vec d) (i j : Fin d)
    (hx : DifferentiableAt ℝ (fderiv ℝ w) (WithLp.toLp 2 x)) :
    gradVec (dirDeriv (fun z => w (WithLp.toLp 2 z)) i) x j =
      fderiv ℝ (fderiv ℝ w) (WithLp.toLp 2 x) (WithLp.toLp 2 (basisVec j))
        (WithLp.toLp 2 (basisVec i)) := by
  have hfirst : dirDeriv (fun z => w (WithLp.toLp 2 z)) i =
      fun z => fderiv ℝ w (WithLp.toLp 2 z) (WithLp.toLp 2 (basisVec i)) := by
    funext z
    exact fderiv_toLp w z (basisVec i)
  have hsecond : HasFDerivAt (fun y => fderiv ℝ w y (WithLp.toLp 2 (basisVec i)))
      ((ContinuousLinearMap.apply ℝ ℝ (WithLp.toLp 2 (basisVec i))).comp
        (fderiv ℝ (fderiv ℝ w) (WithLp.toLp 2 x))) (WithLp.toLp 2 x) :=
    (ContinuousLinearMap.apply ℝ ℝ (WithLp.toLp 2 (basisVec i))).hasFDerivAt.comp _
      hx.hasFDerivAt
  unfold gradVec
  rw [hfirst]
  refine (fderiv_toLp (fun y => fderiv ℝ w y (WithLp.toLp 2 (basisVec i))) x
    (basisVec j)).trans ?_
  rw [hsecond.fderiv]
  rfl

private theorem lapVec_toLp {d : ℕ} (w : Euc d → ℝ) (x : Vec d)
    (hx : DifferentiableAt ℝ (fderiv ℝ w) (WithLp.toLp 2 x)) :
    lapVec (fun z => w (WithLp.toLp 2 z)) x = Δ w (WithLp.toLp 2 x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis w
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he := hessian_entry w x j j hx
  rw [toLp_basis] at he
  rw [iteratedFDeriv_two_apply]
  simpa [lapVec, gradVec] using he

private theorem eLpNorm_toLp {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    (g : Euc d → F) (p : ℝ≥0∞) {s : Set (Euc d)} (hs : MeasurableSet s) :
    eLpNorm (fun x : Vec d => g (WithLp.toLp 2 x)) p
        (volume.restrict (WithLp.toLp 2 ⁻¹' s)) = eLpNorm g p (volume.restrict s) := by
  have hm := (PiLp.volume_preserving_toLp (Fin d)).restrict_preimage hs
  rw [← hm.map_eq]
  exact ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding.eLpNorm_map_measure).symm

private theorem dual_norm_coordinates {d : ℕ} (φ : Euc d →L[ℝ] ℝ) :
    ‖φ‖ = ‖(WithLp.toLp 2 (fun i => φ (EuclideanSpace.basisFun (Fin d) ℝ i)) : Euc d)‖ := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let u : Euc d := (InnerProductSpace.toDual ℝ (Euc d)).symm φ
  have hu : ‖u‖ = ‖φ‖ := LinearIsometryEquiv.norm_map _ _
  have heq : (WithLp.toLp 2 (fun i => φ (b i)) : Euc d) = u := by
    ext i
    have hi : u i = ⟪b i, u⟫_ℝ := by
      rw [← EuclideanSpace.basisFun_repr, b.repr_apply_apply]
    have hj : ⟪b i, u⟫_ℝ = φ (b i) := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    simp [hi, hj]
  change ‖φ‖ = ‖(WithLp.toLp 2 (fun i => φ (b i)) : Euc d)‖
  rw [heq, hu]

private theorem opNorm_le_rows {d : ℕ} (H : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) :
    ‖H‖ ≤ ∑ i : Fin d,
      ‖(WithLp.toLp 2 (fun j => H (EuclideanSpace.basisFun (Fin d) ℝ j)
        (EuclideanSpace.basisFun (Fin d) ℝ i)) : Euc d)‖ := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let q : Fin d → Euc d →L[ℝ] ℝ := fun i => H.flip (b i)
  have hq : ∀ i, ‖q i‖ = ‖(WithLp.toLp 2 (fun j => H (b j) (b i)) : Euc d)‖ := by
    intro i
    exact dual_norm_coordinates (q i)
  change ‖H‖ ≤ ∑ i, ‖(WithLp.toLp 2 (fun j => H (b j) (b i)) : Euc d)‖
  simp_rw [← hq]
  have hs : 0 ≤ ∑ i, ‖q i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine H.opNorm_le_bound hs fun x => ?_
  refine (H x).opNorm_le_bound (mul_nonneg hs (norm_nonneg x)) fun y => ?_
  have hy : H x y = ∑ i, (b.repr y i) * q i x := by
    conv_lhs => rw [← b.sum_repr y]
    simp [q, map_sum, map_smul, smul_eq_mul]
  rw [hy]
  calc
    ‖∑ i, (b.repr y i) * q i x‖ ≤ ∑ i, ‖(b.repr y i) * q i x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, (‖q i‖ * ‖x‖) * ‖y‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hr : ‖b.repr y i‖ ≤ ‖y‖ := by
        simpa using (PiLp.norm_apply_le (b.repr y) i)
      have hv := (q i).le_opNorm x
      rw [norm_mul]
      nlinarith [norm_nonneg (b.repr y i), norm_nonneg (q i x)]
    _ = (∑ i, ‖q i‖) * ‖x‖ * ‖y‖ := by rw [Finset.sum_mul, Finset.sum_mul]

private theorem hessian_bound {d : ℕ} (w : Euc d → ℝ) (x : Vec d)
    (hx : DifferentiableAt ℝ (fderiv ℝ w) (WithLp.toLp 2 x)) :
    ‖fderiv ℝ (fderiv ℝ w) (WithLp.toLp 2 x)‖ ≤
      ∑ i : Fin d, vecEuclideanNorm (gradVec (dirDeriv (fun z => w (WithLp.toLp 2 z)) i) x) := by
  refine (opNorm_le_rows (fderiv ℝ (fderiv ℝ w) (WithLp.toLp 2 x))).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i hi
  rw [← norm_toLp]
  congr 1
  apply congrArg (WithLp.toLp 2)
  funext j
  rw [hessian_entry w x i j hx, toLp_basis, toLp_basis]

/-- A uniform bound for every coordinate row controls the full Hessian. -/
theorem L6_coordinates (d : ℕ) (h : LocalUnitVecStmt d) : LocalUnitStmt d := by
  intro p hp hp_top
  obtain ⟨K, hK, hrow⟩ := h p hp hp_top
  refine ⟨(d : ℝ≥0∞) * K, ENNReal.mul_ne_top (by simp) hK, ?_⟩
  intro w hw hdata
  let v : Vec d → ℝ := fun x => w (WithLp.toLp 2 x)
  have hT : Measurable (WithLp.toLp 2 : Vec d → Euc d) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable
  have hv : ContDiffOn ℝ ∞ v (euclideanBall 0 (4 / 3)) := by
    refine hw.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff.contDiffOn ?_
    intro x hx
    rw [← toLp_preimage_ball d (4 / 3) (by norm_num)] at hx
    exact hx
  have hdiff : ∀ y ∈ ball (0 : Euc d) (4 / 3), DifferentiableAt ℝ (fderiv ℝ w) y := by
    intro y hy
    have h2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) w y :=
      contDiffAt_infty.mp (hw.contDiffAt (isOpen_ball.mem_nhds hy)) 2
    exact (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hlap : eLpNorm (lapVec v) p (volumeOn (euclideanBall 0 (4 / 3))) =
      eLpNorm (Δ w) p (volume.restrict (ball 0 (4 / 3))) := by
    change eLpNorm (lapVec v) p (volume.restrict (euclideanBall 0 (4 / 3))) = _
    rw [← eLpNorm_toLp (Δ w) p (measurableSet_ball), toLp_preimage_ball d (4 / 3) (by norm_num)]
    apply eLpNorm_congr_ae
    rw [← toLp_preimage_ball d (4 / 3) (by norm_num)]
    apply ae_restrict_of_forall_mem (measurableSet_ball.preimage hT)
    intro x hx
    exact lapVec_toLp w x (hdiff _ hx)
  have hfun : eLpNorm v ⊤ (volumeOn (euclideanBall 0 (4 / 3))) =
      eLpNorm w ⊤ (volume.restrict (ball 0 (4 / 3))) := by
    change eLpNorm (fun x : Vec d => w (WithLp.toLp 2 x)) ⊤
      (volume.restrict (euclideanBall 0 (4 / 3))) = _
    rw [← toLp_preimage_ball d (4 / 3) (by norm_num)]
    exact eLpNorm_toLp w ⊤ measurableSet_ball
  have hvdata : eLpNorm (lapVec v) p (volumeOn (euclideanBall 0 (4 / 3))) +
      eLpNorm v ⊤ (volumeOn (euclideanBall 0 (4 / 3))) ≠ ⊤ := by
    rw [hlap, hfun]
    exact hdata
  have hleft : eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p
      (volume.restrict (ball 0 (1 / 2))) ≤
      ∑ i : Fin d, eLpNorm (fun x => vecEuclideanNorm (gradVec (dirDeriv v i) x)) p
        (volumeOn (euclideanBall 0 (1 / 2))) := by
    rw [← eLpNorm_toLp (fun y => ‖fderiv ℝ (fderiv ℝ w) y‖) p measurableSet_ball,
      toLp_preimage_ball d (1 / 2) (by norm_num)]
    calc
      eLpNorm (fun x : Vec d => ‖fderiv ℝ (fderiv ℝ w) (WithLp.toLp 2 x)‖) p
          (volume.restrict (euclideanBall 0 (1 / 2))) ≤
          eLpNorm (fun x : Vec d => ∑ i : Fin d, vecEuclideanNorm (gradVec (dirDeriv v i) x)) p
            (volume.restrict (euclideanBall 0 (1 / 2))) := by
        apply eLpNorm_mono_ae_real
          (((measurable_fderiv ℝ (fderiv ℝ w)).norm.comp hT).aestronglyMeasurable)
        rw [← toLp_preimage_ball d (1 / 2) (by norm_num)]
        apply ae_restrict_of_forall_mem (measurableSet_ball.preimage hT)
        intro x hx
        change ‖‖fderiv ℝ (fderiv ℝ w) (WithLp.toLp 2 x)‖‖ ≤ _
        rw [Real.norm_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ w) (WithLp.toLp 2 x)))]
        exact hessian_bound w x (hdiff _ (ball_subset_ball (by norm_num) hx))
      _ ≤ ∑ i : Fin d, eLpNorm (fun x => vecEuclideanNorm (gradVec (dirDeriv v i) x)) p
          (volumeOn (euclideanBall 0 (1 / 2))) := by
        have heq : (fun x : Vec d => ∑ i : Fin d, vecEuclideanNorm (gradVec (dirDeriv v i) x)) =
            ∑ i : Fin d, fun x => vecEuclideanNorm (gradVec (dirDeriv v i) x) := by
          funext x
          simp only [Finset.sum_apply]
        rw [heq]
        exact eLpNorm_sum_le (le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 2) hp)
  calc
    _ ≤ ∑ i : Fin d, eLpNorm (fun x => vecEuclideanNorm (gradVec (dirDeriv v i) x)) p
        (volumeOn (euclideanBall 0 (1 / 2))) := hleft
    _ ≤ ∑ _i : Fin d, K * (eLpNorm (lapVec v) p (volumeOn (euclideanBall 0 (4 / 3))) +
        eLpNorm v ⊤ (volumeOn (euclideanBall 0 (4 / 3)))) :=
      Finset.sum_le_sum fun i _ => hrow v hv hvdata i
    _ = (d : ℝ≥0∞) * (K * (eLpNorm (lapVec v) p (volumeOn (euclideanBall 0 (4 / 3))) +
        eLpNorm v ⊤ (volumeOn (euclideanBall 0 (4 / 3))))) := by simp
    _ = _ := by rw [hlap, hfun, mul_assoc]

end HessianAdapter

import RandomSandpile.Proofs.HessianAdapterDefs
import LatticeProb.Analysis.HessianLpReduction
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# The `L²` Hessian bound in ERL coordinates

`L2HessEucStmt d` is the `L²` bound for the full Hessian of a smooth function on the Euclidean
model space `EuclideanSpace ℝ (Fin d)`, on the unit ball in terms of the ball of radius `4 / 3`.
`L11_l2_coordinates` transports it along the identification `toLp` of native vectors with the
model space (a volume preserving continuous linear equivalence) to `L2HessVecStmt d`, the bound
for the rows `∇ ∂ᵢ w` of the Hessian in coordinates.
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace HessianAdapter

open PDE

section Transport

variable {d : ℕ}

/-- The Euclidean norm of a native vector is the norm of its image in the model space. -/
private theorem vecEuclideanNorm_eq_norm (x : Vec d) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq, vecEuclideanNorm, vecNormSq_eq_sum_sq]
  simp

/-- ERL's round ball is the preimage of the metric ball in the model space. -/
private theorem euclideanBall_zero_eq_preimage {R : ℝ} (hR : 0 < R) :
    euclideanBall (0 : Vec d) R = WithLp.toLp 2 ⁻¹' ball (0 : Euc d) R := by
  ext x
  simp only [euclideanBall, euclideanSqDist, sub_zero, Set.mem_ofPred_eq, Set.mem_preimage,
    mem_ball_zero_iff, ← vecEuclideanNorm_eq_norm, vecEuclideanNorm]
  exact (Real.sqrt_lt' hR).symm


/-- Differentiating after the identification `toLp` evaluates at the image direction. -/
private theorem fderiv_comp_toLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Euc d → F) (x u : Vec d) :
    fderiv ℝ (fun z : Vec d => f (WithLp.toLp 2 z)) x u =
      fderiv ℝ f (WithLp.toLp 2 x) (WithLp.toLp 2 u) := by
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.comp_right_fderiv
    (f := f) (x := x)
  exact congrArg (fun L => L u) h

/-- The image of a coordinate vector is the corresponding vector of the standard basis. -/
private theorem toLp_basisVec (i : Fin d) :
    WithLp.toLp 2 (basisVec i) = EuclideanSpace.basisFun (Fin d) ℝ i := by
  simp [basisVec, EuclideanSpace.basisFun_apply]

/-- The entries of the Hessian row `∇ ∂ᵢ w` are second derivatives in the model space. -/
private theorem gradVec_dirDeriv_apply {v : Euc d → ℝ} {w : Vec d → ℝ}
    (hwv : ∀ x, w x = v (WithLp.toLp 2 x)) (i j : Fin d) (x : Vec d)
    (hx : DifferentiableAt ℝ (fderiv ℝ v) (WithLp.toLp 2 x)) :
    gradVec (dirDeriv w i) x j =
      fderiv ℝ (fderiv ℝ v) (WithLp.toLp 2 x) (WithLp.toLp 2 (basisVec j))
        (WithLp.toLp 2 (basisVec i)) := by
  obtain rfl : w = fun z => v (WithLp.toLp 2 z) := funext hwv
  have h1 : dirDeriv (fun z => v (WithLp.toLp 2 z)) i =
      fun z => (fun y => fderiv ℝ v y (WithLp.toLp 2 (basisVec i))) (WithLp.toLp 2 z) := by
    funext z
    exact fderiv_comp_toLp v z (basisVec i)
  have h2 : HasFDerivAt (fun y => fderiv ℝ v y (WithLp.toLp 2 (basisVec i)))
      ((ContinuousLinearMap.apply ℝ ℝ (WithLp.toLp 2 (basisVec i))).comp
        (fderiv ℝ (fderiv ℝ v) (WithLp.toLp 2 x))) (WithLp.toLp 2 x) :=
    (ContinuousLinearMap.apply ℝ ℝ (WithLp.toLp 2 (basisVec i))).hasFDerivAt.comp _
      hx.hasFDerivAt
  unfold gradVec
  rw [h1]
  refine (fderiv_comp_toLp (fun y => fderiv ℝ v y (WithLp.toLp 2 (basisVec i))) x
    (basisVec j)).trans ?_
  rw [h2.fderiv]
  rfl

/-- The coordinate Laplacian is the Laplacian of the model space. -/
private theorem lapVec_eq_laplacian {v : Euc d → ℝ} {w : Vec d → ℝ}
    (hwv : ∀ x, w x = v (WithLp.toLp 2 x)) (x : Vec d)
    (hx : DifferentiableAt ℝ (fderiv ℝ v) (WithLp.toLp 2 x)) :
    lapVec w x = Δ v (WithLp.toLp 2 x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis v
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := gradVec_dirDeriv_apply hwv j j x hx
  rw [toLp_basisVec] at h
  rw [iteratedFDeriv_two_apply]
  simpa [gradVec] using h

/-- The Euclidean norm of a row of a bilinear form is at most the operator norm. -/
private theorem norm_row_le (H : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (i : Fin d) :
    ‖(WithLp.toLp 2 (fun j => H (EuclideanSpace.basisFun (Fin d) ℝ j)
      (EuclideanSpace.basisFun (Fin d) ℝ i)) : Euc d)‖ ≤ ‖H‖ := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  set φ : Euc d →L[ℝ] ℝ := H.flip (b i) with hφ
  have hφn : ‖φ‖ ≤ ‖H‖ := by
    refine φ.opNorm_le_bound (norm_nonneg H) fun y => ?_
    have := ContinuousLinearMap.le_opNorm₂ H y (b i)
    simpa [hφ, b.norm_eq_one i] using this
  set u : Euc d := (InnerProductSpace.toDual ℝ (Euc d)).symm φ with hu
  have hun : ‖u‖ = ‖φ‖ := LinearIsometryEquiv.norm_map _ _
  have hu_eq : (WithLp.toLp 2 (fun j => H (b j) (b i)) : Euc d) = u := by
    ext j
    have h1 : u j = ⟪b j, u⟫_ℝ := by
      rw [← EuclideanSpace.basisFun_repr, b.repr_apply_apply]
    have h2 : ⟪b j, u⟫_ℝ = φ (b j) := by
      rw [real_inner_comm, hu, InnerProductSpace.toDual_symm_apply]
    simp [h1, h2, hφ]
  rw [hu_eq, hun]
  exact hφn

/-- Rows of the coordinate Hessian are bounded by the operator norm of the Hessian of the
model space. -/
private theorem vecEuclideanNorm_gradVec_dirDeriv_le {v : Euc d → ℝ} {w : Vec d → ℝ}
    (hwv : ∀ x, w x = v (WithLp.toLp 2 x)) (i : Fin d) (x : Vec d)
    (hx : DifferentiableAt ℝ (fderiv ℝ v) (WithLp.toLp 2 x)) :
    vecEuclideanNorm (gradVec (dirDeriv w i) x) ≤ ‖fderiv ℝ (fderiv ℝ v) (WithLp.toLp 2 x)‖ := by
  rw [vecEuclideanNorm_eq_norm]
  have h : (WithLp.toLp 2 (gradVec (dirDeriv w i) x) : Euc d) =
      WithLp.toLp 2 (fun j => fderiv ℝ (fderiv ℝ v) (WithLp.toLp 2 x)
        (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
    congr 1
    funext j
    rw [gradVec_dirDeriv_apply hwv i j x hx, toLp_basisVec, toLp_basisVec]
  rw [h]
  exact norm_row_le _ i

/-- Composition with `toLp` does not change `L²` norms on matching restrictions of the volume. -/
private theorem eLpNorm_comp_toLp_restrict {F : Type*} [NormedAddCommGroup F] (g : Euc d → F)
    {S : Set (Euc d)} (hS : MeasurableSet S) :
    eLpNorm (fun x : Vec d => g (WithLp.toLp 2 x)) 2 (volume.restrict (WithLp.toLp 2 ⁻¹' S)) =
      eLpNorm g 2 (volume.restrict S) := by
  have hmp := (PiLp.volume_preserving_toLp (Fin d)).restrict_preimage hS
  rw [← hmp.map_eq]
  exact ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding.eLpNorm_map_measure).symm

/-- The Euclidean norm of the row `∇ ∂ᵢ w` is measurable. -/
private theorem measurable_vecEuclideanNorm_gradVec_dirDeriv (w : Vec d → ℝ) (i : Fin d) :
    Measurable fun x => vecEuclideanNorm (gradVec (dirDeriv w i) x) := by
  have h : ∀ j, Measurable fun x => gradVec (dirDeriv w i) x j := fun j =>
    (measurable_fderiv ℝ (dirDeriv w i)).apply_continuousLinearMap _
  simp only [vecEuclideanNorm, vecNormSq_eq_sum_sq]
  exact (Finset.measurable_sum _ fun j _ => (h j).pow_const 2).sqrt

end Transport

/-- The `L²` Hessian bound on the model space gives the `L²` bound for the rows of the Hessian in
coordinates, with the same constant. -/
theorem L11_l2_coordinates (d : ℕ) (h : L2HessEucStmt d) : L2HessVecStmt d := by
  obtain ⟨C₂, hC₂, hbound⟩ := h
  refine ⟨C₂, hC₂, fun w hw i => ?_⟩
  set v : Euc d → ℝ := fun y => w y.ofLp with hv_def
  have hwv : ∀ x, w x = v (WithLp.toLp 2 x) := fun x => by simp [hv_def]
  have hB1 : euclideanBall (0 : Vec d) 1 = WithLp.toLp 2 ⁻¹' ball (0 : Euc d) 1 :=
    euclideanBall_zero_eq_preimage one_pos
  have hB2 : euclideanBall (0 : Vec d) (4 / 3) = WithLp.toLp 2 ⁻¹' ball (0 : Euc d) (4 / 3) :=
    euclideanBall_zero_eq_preimage (by norm_num)
  have hv : ContDiffOn ℝ ∞ v (ball (0 : Euc d) (4 / 3)) := by
    refine hw.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).contDiff.contDiffOn ?_
    intro y hy
    rw [hB2]
    simpa using hy
  have hdiff : ∀ y ∈ ball (0 : Euc d) (4 / 3), DifferentiableAt ℝ (fderiv ℝ v) y := by
    intro y hy
    have h2 : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) v y :=
      contDiffAt_infty.mp (hv.contDiffAt (isOpen_ball.mem_nhds hy)) 2
    exact (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero
  have hS1 : MeasurableSet (ball (0 : Euc d) 1) := measurableSet_ball
  have hS2 : MeasurableSet (ball (0 : Euc d) (4 / 3)) := measurableSet_ball
  have hT : Measurable (WithLp.toLp 2 : Vec d → Euc d) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable
  have e1 := eLpNorm_comp_toLp_restrict (fun y => ‖fderiv ℝ (fderiv ℝ v) y‖) hS1
  have e2 := eLpNorm_comp_toLp_restrict (Δ v) hS2
  have e3 := eLpNorm_comp_toLp_restrict v hS2
  have hmem : ∀ {R : ℝ} {x : Vec d}, x ∈ WithLp.toLp 2 ⁻¹' ball (0 : Euc d) R →
      WithLp.toLp 2 x ∈ ball (0 : Euc d) R := fun hx => hx
  have hL : eLpNorm (fun x => vecEuclideanNorm (gradVec (dirDeriv w i) x)) 2
      (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
      eLpNorm (fun y => ‖fderiv ℝ (fderiv ℝ v) y‖) 2 (volume.restrict (ball (0 : Euc d) 1)) := by
    rw [← e1, hB1]
    refine eLpNorm_mono_ae
      (measurable_vecEuclideanNorm_gradVec_dirDeriv w i).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem (hS1.preimage hT) fun x hx => ?_
    have hx' : WithLp.toLp 2 x ∈ ball (0 : Euc d) (4 / 3) :=
      ball_subset_ball (by norm_num) (hmem hx)
    have h0 : 0 ≤ vecEuclideanNorm (gradVec (dirDeriv w i) x) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h0]
    refine (vecEuclideanNorm_gradVec_dirDeriv_le hwv i x (hdiff _ hx')).trans ?_
    exact le_of_eq
      (Real.norm_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ v) (WithLp.toLp 2 x)))).symm
  have hlap : eLpNorm (lapVec w) 2 (volumeOn (euclideanBall (0 : Vec d) (4 / 3))) =
      eLpNorm (Δ v) 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) := by
    rw [← e2, hB2]
    refine eLpNorm_congr_ae ?_
    refine ae_restrict_of_forall_mem (hS2.preimage hT) fun x hx => ?_
    exact lapVec_eq_laplacian hwv x (hdiff _ (hmem hx))
  have hfun : eLpNorm w 2 (volumeOn (euclideanBall (0 : Vec d) (4 / 3))) =
      eLpNorm v 2 (volume.restrict (ball (0 : Euc d) (4 / 3))) := by
    rw [← e3, hB2]
  rw [hlap, hfun]
  exact hL.trans (hbound v hv)

end HessianAdapter

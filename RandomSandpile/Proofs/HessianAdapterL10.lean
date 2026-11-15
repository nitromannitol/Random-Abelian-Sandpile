import RandomSandpile.Proofs.HessianAdapterDefs
import PDEFoundation.Analysis.LocalDivergenceIBP
import PDEFoundation.Analysis.IteratedCoordDeriv
import PDEFoundation.Measure.BallVolume

/-!
# Smooth equations for coordinate derivatives
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal

namespace HessianAdapter

open PDE

private theorem contDiffOn_dirDeriv {d : ℕ} {w : Vec d → ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) (i : Fin d) :
    ContDiffOn ℝ ∞ (dirDeriv w i) U := by
  exact (hw.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem contDiffOn_lapVec {d : ℕ} {w : Vec d → ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (lapVec w) U := by
  unfold lapVec
  apply ContDiffOn.sum
  intro j hj
  exact (contDiffOn_dirDeriv hU hw j |>.fderiv_of_isOpen hU (by simp)).clm_apply
    contDiffOn_const

private theorem memLp_of_continuousOn_larger_ball {d : ℕ} {f : Vec d → ℝ}
    (hf : ContinuousOn f (euclideanBall (0 : Vec d) (4 / 3))) (q : ℝ≥0∞) :
    MemLp f q (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  let U := euclideanBall (0 : Vec d) 1
  let K := euclideanClosedBall (0 : Vec d) 1
  have hKU : K ⊆ euclideanBall (0 : Vec d) (4 / 3) :=
    euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num)
  have hU : IsOpen U := isOpen_euclideanBall _ _
  have hcont : ContinuousOn f U := hf.mono (fun x hx => hKU (euclideanBall_subset_euclideanClosedBall _ _ hx))
  have hmeas : AEStronglyMeasurable f (volumeOn U) := hcont.aestronglyMeasurable hU.measurableSet
  obtain ⟨C, hC⟩ := (isCompact_euclideanClosedBall (0 : Vec d) (by norm_num)).exists_bound_of_continuousOn (hf.mono hKU)
  let : IsFiniteMeasure (volumeOn U) := isFiniteMeasure_volumeOn_euclideanBall _ (by norm_num)
  refine MemLp.of_bound hmeas C ?_
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact hC x (euclideanBall_subset_euclideanClosedBall _ _ hx)

private theorem continuousOn_forcing {d : ℕ} {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ ∞ w (euclideanBall (0 : Vec d) (4 / 3))) (i : Fin d) :
    ContinuousOn (fun x => (Pi.single i (-lapVec w x) : Vec d))
      (euclideanBall (0 : Vec d) (4 / 3)) := by
  have hF : ContDiffOn ℝ ∞ (fun x => (Pi.single i (-lapVec w x) : Vec d))
      (euclideanBall (0 : Vec d) (4 / 3)) := by
    refine contDiffOn_pi.2 fun j => ?_
    by_cases h : j = i
    · subst j
      simpa only [Pi.single_eq_same, Pi.neg_apply] using
        (contDiffOn_lapVec (isOpen_euclideanBall _ _) hw).neg
    · simpa [Pi.single_apply, h] using
        (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Vec d => (0 : ℝ)) _)
  exact hF.continuousOn

private theorem forcing_data {d : ℕ} {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ ∞ w (euclideanBall (0 : Vec d) (4 / 3))) (i : Fin d) :
    (∀ j : Fin d,
      AEStronglyMeasurable (fun x => (Pi.single i (-lapVec w x) : Vec d) j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
    (∀ q : ℝ≥0∞,
      MemLp (fun x => vecEuclideanNorm (Pi.single i (-lapVec w x) : Vec d)) q
        (volumeOn (euclideanBall (0 : Vec d) 1))) := by
  have hF := continuousOn_forcing hw i
  have hsub : euclideanBall (0 : Vec d) 1 ⊆ euclideanBall (0 : Vec d) (4 / 3) :=
    euclideanBall_mono (by norm_num) (by norm_num)
  constructor
  · intro j
    exact ((continuous_apply j).comp_continuousOn (hF.mono hsub)).aestronglyMeasurable
      (isOpen_euclideanBall _ _).measurableSet
  · intro q
    exact memLp_of_continuousOn_larger_ball
      (continuous_vecEuclideanNorm.comp_continuousOn hF) q

private theorem laplacian_dirDeriv_comm {d : ℕ} {w : Vec d → ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) (i : Fin d) {x : Vec d} (hx : x ∈ U) :
    (∑ j : Fin d, fderiv ℝ (dirDeriv (dirDeriv w i) j) x (basisVec j)) =
      fderiv ℝ (lapVec w) x (basisVec i) := by
  have hdiff (j : Fin d) : DifferentiableAt ℝ (dirDeriv (dirDeriv w j) j) x :=
    ((contDiffOn_dirDeriv hU (contDiffOn_dirDeriv hU hw j) j).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
  have hperm (j : Fin d) : List.Perm [j, j, i] [i, j, j] :=
    (List.Perm.cons j (List.Perm.swap i j [])).trans (List.Perm.swap i j [j])
  have hcomm (j : Fin d) :
      fderiv ℝ (dirDeriv (dirDeriv w i) j) x (basisVec j) =
      fderiv ℝ (dirDeriv (dirDeriv w j) j) x (basisVec i) := by
    have h := iteratedCoordDerivList_perm_eqOn hU hw (hperm j) hx
    simp only [iteratedCoordDerivList, euclideanCoordDeriv] at h ⊢
    exact h
  change (∑ j : Fin d, fderiv ℝ (dirDeriv (dirDeriv w i) j) x (basisVec j)) =
    fderiv ℝ (fun y => ∑ j : Fin d, dirDeriv (dirDeriv w j) j y) x (basisVec i)
  rw [fderiv_fun_sum (fun j _ => hdiff j)]
  simp only [_root_.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hcomm j)

private theorem integral_grad_dirDeriv {d : ℕ} {w : Vec d → ℝ}
    (hw : ContDiffOn ℝ ∞ w (euclideanBall (0 : Vec d) (4 / 3))) (i : Fin d)
    (φ : WeakTestFunction (euclideanBall (0 : Vec d) 1)) :
    (∫ x in euclideanBall (0 : Vec d) 1, vecDot (gradVec (dirDeriv w i) x) (φ.grad x)) =
      ∫ x in euclideanBall (0 : Vec d) 1, lapVec w x * φ.partialDeriv i x := by
  let U := euclideanBall (0 : Vec d) 1
  have hU : IsOpen U := isOpen_euclideanBall _ _
  have hsub : U ⊆ euclideanBall (0 : Vec d) (4 / 3) :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hwU : ContDiffOn ℝ ∞ w U := hw.mono hsub
  have hJ (j : Fin d) : ContDiffOn ℝ 1 (fun x => gradVec (dirDeriv w i) x j) U := by
    exact (contDiffOn_dirDeriv hU (contDiffOn_dirDeriv hU hwU i) j).of_le (by simp)
  have hLap : ContDiffOn ℝ 1 (lapVec w) U :=
    (contDiffOn_lapVec hU hwU).of_le (by simp)
  calc
    (∫ x in U, vecDot (gradVec (dirDeriv w i) x) (φ.grad x)) =
        -∫ x in U, (∑ j : Fin d, fderiv ℝ (dirDeriv (dirDeriv w i) j) x
          (basisVec j)) * φ x := by
      have hid := integral_vecDot_weakTestFunction_grad_eq_neg_integral_divergence_mul
        hU (gradVec (dirDeriv w i)) hJ φ
      simp only [classicalGradient_apply, gradVec] at hid ⊢
      exact hid
    _ = -∫ x in U, fderiv ℝ (lapVec w) x (basisVec i) * φ x := by
      congr 1
      apply setIntegral_congr_fun hU.measurableSet
      intro x hx
      dsimp only
      rw [laplacian_dirDeriv_comm hU hwU i hx]
    _ = ∫ x in U, lapVec w x * φ.partialDeriv i x :=
      (integral_mul_weakTestFunction_partialDeriv_eq_neg_integral_fderiv_mul
        hU hLap φ i).symm

private theorem matVecMul_one {d : ℕ} (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  exact Matrix.one_mulVec v

/-- Coordinate derivatives of a smooth function satisfy the identity-coefficient equation. -/
theorem L10_smooth_equation (d : ℕ) : SmoothEqStmt d := by
  intro w hw i u hu hgrad
  obtain ⟨hmeas, hnorm⟩ := forcing_data hw i
  refine ⟨hmeas, hnorm, ?_⟩
  let U := euclideanBall (0 : Vec d) 1
  let F : Vec d → Vec d := fun x => Pi.single i (-lapVec w x)
  have hF : MemVectorL2On U F := by
    intro j
    apply memLp_of_continuousOn_larger_ball _ 2
    exact (continuous_apply j).comp_continuousOn (continuousOn_forcing hw i)
  have hdata : DivergenceFormL2DataOn (fun _ => (1 : Mat d)) U u (0 : Vec d → ℝ) F := by
    refine ⟨?_, ?_, hF⟩
    · simpa only [matVecMul_one] using u.gradMemL2
    · exact MemLp.zero
  intro φ
  refine ⟨hdata.testable φ, ?_⟩
  have hdot (x : Vec d) : vecDot (F x) (φ.grad x) =
      -(lapVec w x * φ.partialDeriv i x) := by
    simp [F, vecDot, Pi.single_apply, WeakTestFunction.grad_apply]
  simp only [matVecMul_one, Pi.zero_apply, zero_mul, integral_zero, zero_sub]
  rw [hgrad]
  rw [integral_grad_dirDeriv hw i φ]
  change (∫ x in U, lapVec w x * φ.partialDeriv i x) =
    -∫ x in U, vecDot (F x) (φ.grad x)
  simp_rw [hdot, integral_neg, neg_neg]

end HessianAdapter

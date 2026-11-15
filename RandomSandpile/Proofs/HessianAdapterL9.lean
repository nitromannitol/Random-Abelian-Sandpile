import RandomSandpile.Proofs.HessianAdapterDefs
import PDEFoundation.Sobolev.ClassicalOnOpenWeakGradient

/-!
# Directional derivatives of smooth functions are `H¹` on the unit ball

For `w` smooth on the open ball `B_{4/3}`, the derivative `∂ᵢ w` is smooth on `B_{4/3}`, hence
bounded with bounded coordinate gradient on the compact closed unit ball. Its classical gradient
is a weak gradient on the open unit ball, so `∂ᵢ w` with `gradVec (∂ᵢ w)` is an `H1Function`
on `B_1`.
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal

namespace HessianAdapter

open PDE

/-- The closed unit ball lies inside the open ball of radius `4/3`. -/
private theorem closedUnitBall_subset (d : ℕ) :
    euclideanClosedBall (0 : Vec d) 1 ⊆ euclideanBall (0 : Vec d) (4 / 3) :=
  euclideanClosedBall_subset_euclideanBall (by norm_num) (by norm_num)

/-- A function continuous on the closed unit ball is in `L²` of the open unit ball. -/
private theorem memL2On_unitBall_of_continuousOn {d : ℕ} {g : Vec d → ℝ}
    (hg : ContinuousOn g (euclideanClosedBall (0 : Vec d) 1)) :
    MemL2On (euclideanBall (0 : Vec d) 1) g := by
  have hK : IsCompact (euclideanClosedBall (0 : Vec d) 1) :=
    isCompact_euclideanClosedBall 0 zero_le_one
  have hKm : MeasurableSet (euclideanClosedBall (0 : Vec d) 1) :=
    measurableSet_euclideanClosedBall 0 1
  have : IsFiniteMeasure (volume.restrict (euclideanClosedBall (0 : Vec d) 1)) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  have hK2 : MemLp g 2 (volume.restrict (euclideanClosedBall (0 : Vec d) 1)) :=
    MemLp.of_bound (hg.aestronglyMeasurable_of_isCompact hK hKm) C
      ((ae_restrict_iff' hKm).2 (Eventually.of_forall hC))
  exact hK2.mono_measure
    (Measure.restrict_mono (euclideanBall_subset_euclideanClosedBall 0 1) le_rfl)

/-- The coordinate derivative of a function smooth on an open set is smooth there. -/
private theorem contDiffOn_dirDeriv {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {w : Vec d → ℝ} (hw : ContDiffOn ℝ ∞ w U) (i : Fin d) :
    ContDiffOn ℝ ∞ (dirDeriv w i) U :=
  (hw.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const

/-- Coordinate derivatives of a smooth function are `H1Function`s on the unit ball. -/
theorem L9_smooth_h1 (d : ℕ) : SmoothH1Stmt d := by
  intro w hw i
  have hU' : IsOpen (euclideanBall (0 : Vec d) (4 / 3)) := isOpen_euclideanBall 0 (4 / 3)
  have hf : ContDiffOn ℝ ∞ (dirDeriv w i) (euclideanBall (0 : Vec d) (4 / 3)) :=
    contDiffOn_dirDeriv hU' hw i
  have hsub : euclideanBall (0 : Vec d) 1 ⊆ euclideanBall (0 : Vec d) (4 / 3) :=
    (euclideanBall_subset_euclideanClosedBall 0 1).trans (closedUnitBall_subset d)
  refine ⟨⟨dirDeriv w i, gradVec (dirDeriv w i), ?_, ?_, ?_⟩, rfl, rfl⟩
  · exact memL2On_unitBall_of_continuousOn
      (hf.continuousOn.mono (closedUnitBall_subset d))
  · intro j
    exact memL2On_unitBall_of_continuousOn
      ((contDiffOn_dirDeriv hU' hf j).continuousOn.mono (closedUnitBall_subset d))
  · exact HasWeakGradientOn.of_contDiffOn (isOpen_euclideanBall 0 1)
      ((hf.mono hsub).of_le (by exact_mod_cast le_top))

end HessianAdapter

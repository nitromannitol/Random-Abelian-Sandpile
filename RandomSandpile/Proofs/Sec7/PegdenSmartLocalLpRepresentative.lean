import Mathlib

/-!
# Ambient representatives of local L∞ classes

A local L∞ class on an open Euclidean domain has an ambient representative
whose restriction belongs to the class and is essentially bounded on the domain.
-/

noncomputable section

open MeasureTheory

namespace RandomSandpile.PegdenSmartAdapter

/-- A local `L∞` class has an ambient representative on the restricted measure. -/
theorem exists_memLp_restrict_representative {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (S : Lp ℝ ⊤ (Measure.comap (Subtype.val : U → EuclideanSpace ℝ (Fin d)) volume)) :
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ,
      MemLp g ⊤ (volume.restrict U) ∧
      (g ∘ Subtype.val) =ᵐ[Measure.comap Subtype.val volume] (S : U → ℝ) := by
  let i : U → EuclideanSpace ℝ (Fin d) := Subtype.val
  have hi : MeasurableEmbedding i := MeasurableEmbedding.subtype_coe hU.measurableSet
  obtain ⟨g, _, hg⟩ := hi.exists_stronglyMeasurable_extend (Lp.stronglyMeasurable S)
    (fun _ => ⟨0⟩)
  refine ⟨g, ?_, ?_⟩
  · rw [← map_comap_subtype_coe hU.measurableSet volume]
    apply hi.memLp_map_measure_iff.mpr
    rw [hg]
    exact Lp.memLp S
  · exact Filter.Eventually.of_forall (fun x => congrFun hg x)

end RandomSandpile.PegdenSmartAdapter

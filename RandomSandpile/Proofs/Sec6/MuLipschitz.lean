import RandomSandpile.Steps.Sec6.MuLipschitz
import RandomSandpile.Proofs.Sec6.MuMonotone

/-! # Lemma 6.3 (Lipschitz continuity of `μ` and `μ*` in `l`): proofs of the steps

Proofs of the deterministic steps of `RandomSandpile/Steps/Sec6/MuLipschitz.lean`.

* `boundaryGap : BoundaryGapStmt`, the ABP argument. The maximum (resp. minimum) of
  `f - p · (·)` over the finite set `Ā` is attained, and it cannot be attained on `∂A`, where the
  value is strictly smaller (resp. larger) than at `x₀ ∈ A`.
* `muLipschitz_of_bending`: Lemma 6.3 from the two non-deterministic steps, Lemma 6.2'
  (`NearMaxBendingStmt`) and the shell estimate (`ShellBoundStmt`, a consequence of Lemma 5.5). The
  level shift is `perturbedShift` (Lemma 6.1). -/

open MeasureTheory LatticeProb

namespace RandomSandpile

/-- **Step 3** (the ABP argument). -/
theorem boundaryGap : BoundaryGapStmt := by
  intro d A f x₀ p hfin hx₀
  have hx₀' : x₀ ∈ dClosure A := Or.inl hx₀
  refine ⟨fun hgap => ?_, fun hgap => ?_⟩
  · obtain ⟨z, hz, hmax⟩ :=
      Set.exists_max_image (dClosure A) (fun y => f y - inner ℝ p (toE y)) hfin ⟨x₀, hx₀'⟩
    have hzA : z ∈ A := by
      rcases hz with hz | hz
      · exact hz
      · exact absurd (hmax x₀ hx₀') (not_le.2 (hgap z hz))
    refine Set.mem_biUnion hzA fun y hy => ?_
    have h := hmax y hy
    rw [inner_sub_right]
    linarith
  · obtain ⟨z, hz, hmin⟩ :=
      Set.exists_min_image (dClosure A) (fun y => f y - inner ℝ p (toE y)) hfin ⟨x₀, hx₀'⟩
    have hzA : z ∈ A := by
      rcases hz with hz | hz
      · exact hz
      · exact absurd (hmin x₀ hx₀') (not_le.2 (hgap z hz))
    refine Set.mem_biUnion hzA fun y hy => ?_
    have h := hmin y hy
    rw [inner_sub_right]
    linarith

/-- **Lemma 6.3 from Lemma 6.2' and the shell estimate** (repaired proof). The two hypotheses
are the non-deterministic steps; every other step is proved. -/
theorem muLipschitz_of_bending (hbend : NearMaxBendingStmt) (hshell : ShellBoundStmt) :
    MuLipschitzStmt :=
  muLipschitz_of_steps perturbedShift boundaryGap hbend hshell

end RandomSandpile

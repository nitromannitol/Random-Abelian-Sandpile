import RandomSandpile.Proofs.Sec9.RecurrentMu
import RandomSandpile.Steps.Sec9.RecurrentIdentificationFinite

/-! Recurrent backgrounds identify the finite-volume upper gradient measures. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- Stabilizing a locally legal toppling on a background without forbidden
subconfigurations gives a recurrent function. -/
theorem isRecurrentFunction_of_locLegal_stabilizing {η u : Site d → ℤ}
    {A : Set (Site d)} (hη : NoForbiddenSubconfig η A)
    (hu : u ∈ locLegal η A) (hus : u ∈ stabilizing η A) :
    IsRecurrentFunction η A u := by
  refine ⟨hus.2, ?_⟩
  have hnf := noForbiddenLocLegal d A η u hη hu
  intro E hE hne hEA w hw x hx
  have hnfE := hnf.subset hEA
  have hs : ∀ z ∈ E, lap (fun y => w y - u y) z +
      (η z + lap u z) ≤ 2 * (d : ℤ) - 1 := by
    intro z hz
    rw [Burning.lap_sub_apply']
    linarith [hw z hz]
  obtain ⟨y, hy, hxy⟩ := supersolutionMinPrinciple d E hE
    (fun z => η z + lap u z) (fun z => w z - u z) hnfE hs x hx
  exact ⟨y, hy, by omega⟩

/-- On recurrent backgrounds, the recurrent and ordinary upper gradient measures agree. -/
theorem recurrentMuEqualityGlobal : RecurrentMuEqualityGlobalStmt := by
  intro d hd η hrec A hA l M
  apply le_antisymm (recurrentMuLe d hd A hA η l M)
  have hnf : NoForbiddenSubconfig η A := recurrentNoForbidden d (by omega) A η (hrec A hA)
  unfold mu muRecurrent
  refine iSup₂_le fun f hf => ?_
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.mp hf
  obtain ⟨v, ⟨hvL, hvS⟩, hvbd⟩ :=
    NearMaxSequence.exists_locLegal_stabilizing (by omega) hA η (NearMaxSequence.locLegal_isTopplingFn hu)
  have huv := locLegalLeStabilizing d A η u v hu hvS hvbd
  have hvr : IsRecurrentFunction η A v :=
    isRecurrentFunction_of_locLegal_stabilizing hnf hvL hvS
  let g : Site d → ℝ := fun x => (v x : ℝ) - (qlZ l x + qMZ M x)
  have hg : g ∈ recurrentPerturbed A η l M := ⟨v, hvr, rfl⟩
  have hsub : supGradSet (fun x => (u x : ℝ) - (qlZ l x + qMZ M x)) A ⊆
      supGradSet g A := by
    apply supGradSetMono d A hA
    · intro x hx
      dsimp [g]
      exact sub_le_sub_right (Int.cast_le.mpr (huv x)) _
    · intro x hx
      dsimp [g]
      rw [hvbd x hx]
  exact (measure_mono hsub).trans (le_iSup_of_le g (le_iSup_of_le hg le_rfl))

/-- The same finite-volume equality needs recurrence only on the given domain. -/
theorem recurrentMuEquality : RecurrentMuEqualityStmt := by
  intro d hd A hA η _ hrec l M
  apply le_antisymm (recurrentMuLe d hd A hA η l M)
  have hnf : NoForbiddenSubconfig η A := recurrentNoForbidden d (by omega) A η hrec
  unfold mu muRecurrent
  refine iSup₂_le fun f hf => ?_
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.mp hf
  obtain ⟨v, ⟨hvL, hvS⟩, hvbd⟩ :=
    NearMaxSequence.exists_locLegal_stabilizing (by omega) hA η (NearMaxSequence.locLegal_isTopplingFn hu)
  have huv := locLegalLeStabilizing d A η u v hu hvS hvbd
  have hvr := isRecurrentFunction_of_locLegal_stabilizing hnf hvL hvS
  let g : Site d → ℝ := fun x => (v x : ℝ) - (qlZ l x + qMZ M x)
  have hg : g ∈ recurrentPerturbed A η l M := ⟨v, hvr, rfl⟩
  have hsub : supGradSet (fun x => (u x : ℝ) - (qlZ l x + qMZ M x)) A ⊆
      supGradSet g A := by
    apply supGradSetMono d A hA
    · intro x hx
      dsimp [g]
      exact sub_le_sub_right (Int.cast_le.mpr (huv x)) _
    · intro x hx
      dsimp [g]
      rw [hvbd x hx]
  exact (measure_mono hsub).trans (le_iSup_of_le g (le_iSup_of_le hg le_rfl))

end RandomSandpile

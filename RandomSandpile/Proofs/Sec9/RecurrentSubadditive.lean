import RandomSandpile.Proofs.Sec9.RecurrentNoForbidden
import RandomSandpile.Steps.Sec5.MuConvergence
import RandomSandpile.Proofs.Sec5.MuBounded

/-! Subadditivity and locality of recurrent upper gradient measures. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- Recurrent upper measures are subadditive under finite covers. -/
theorem muRecurrent_subadditive (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (A : Set (Site d))
    (B : Fin k → Set (Site d)) (hAB : A = ⋃ j, B j) :
    muRecurrent A η l M ≤ ∑ j, muRecurrent (B j) η l M := by
  have hBA : ∀ j, B j ⊆ A := fun j => hAB ▸ Set.subset_iUnion B j
  have hx : ∀ x ∈ A, ∃ j, x ∈ B j := fun x hx => Set.mem_iUnion.1 (hAB ▸ hx)
  unfold muRecurrent
  refine iSup₂_le fun w hw => ?_
  obtain ⟨r, hr, rfl⟩ := hw
  let w : Site d → ℝ := fun x => (r x : ℝ) - (qlZ l x + qMZ M x)
  have hwj : ∀ j, w ∈ recurrentPerturbed (B j) η l M := fun j =>
    ⟨r, hr.mono (hBA j), rfl⟩
  have hsub : supGradSet w A ⊆ ⋃ j, supGradSet w (B j) := by
    intro p hp
    obtain ⟨x, hxA, hp⟩ := Set.mem_iUnion₂.1 hp
    obtain ⟨j, hxj⟩ := hx x hxA
    refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion₂.2 ⟨x, hxj, fun y hy => ?_⟩⟩
    exact hp y (dClosure_mono (hBA j) hy)
  calc volume (supGradSet w A) ≤ volume (⋃ j, supGradSet w (B j)) := measure_mono hsub
    _ ≤ ∑ j, volume (supGradSet w (B j)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ j, ⨆ f ∈ recurrentPerturbed (B j) η l M, volume (supGradSet f (B j)) :=
      Finset.sum_le_sum fun j _ => le_iSup₂ (f := fun f (_ : f ∈ recurrentPerturbed (B j) η l M) =>
        volume (supGradSet f (B j))) w (hwj j)

/-- Recurrent comparison depends on the background only inside the domain. -/
theorem isRecurrentFunction_congr_background {A : Set (Site d)} {η η' r : Site d → ℤ}
    (hη : ∀ x ∈ A, η x = η' x) :
    IsRecurrentFunction η A r ↔ IsRecurrentFunction η' A r := by
  have key : ∀ (η₁ η₂ : Site d → ℤ), (∀ x ∈ A, η₁ x = η₂ x) →
      IsRecurrentFunction η₁ A r → IsRecurrentFunction η₂ A r := by
    intro η₁ η₂ he h
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [← he x hx]
      exact h.1 x hx
    · intro E hE hne hEA w hw x hx
      apply h.2 E hE hne hEA w ?_ x hx
      intro y hy
      rw [he y (hEA hy)]
      exact hw y hy
  exact ⟨key η η' hη, key η' η (fun x hx => (hη x hx).symm)⟩

/-- The recurrent upper measure is local in the background. -/
theorem muRecurrent_congr_background {A : Set (Site d)} {η η' : Site d → ℤ}
    (hη : ∀ x ∈ A, η x = η' x) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muRecurrent A η l M = muRecurrent A η' l M := by
  have h : recurrentPerturbed A η l M = recurrentPerturbed A η' l M := by
    unfold recurrentPerturbed
    congr 1
    ext r
    exact isRecurrentFunction_congr_background hη
  simp only [muRecurrent, h]

/-- Locality makes the finite-volume recurrent upper measure measurable. -/
theorem measurable_muRecurrent {A : Set (Site d)} (hA : A.Finite) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : Measurable (fun η : Config d => muRecurrent A η l M) :=
  measurable_of_eqOn_finite hA (fun _ _ hη => muRecurrent_congr_background hη l M)

/-- Recurrent upper curvature obeys the contact-point volume bound. -/
theorem muRecurrent_le_ncard (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite)
    {η : Site d → ℤ} {ηmax : ℤ} (hη : ∀ x ∈ A, η x ≤ ηmax)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muRecurrent A η l M ≤ ENNReal.ofReal
      ((max ((ηmax : ℝ) + l + M.trace) 0 / d) ^ d * (A.ncard : ℝ)) := by
  unfold muRecurrent
  refine iSup₂_le fun w hw => ?_
  obtain ⟨r, hr, rfl⟩ := hw
  refine volume_biUnion_le_ncard hA _ (by positivity) fun x hx =>
    (supGradVolumeLe d A _ x hx).1.trans ?_
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ d)
  refine div_le_div_of_nonneg_right (max_le_max_right _ ?_) (Nat.cast_nonneg d)
  rw [lapR_sub', lapR_intCast, lapQuadratic d hd]
  have h1 := hr.height_nonneg hx
  have h2 := hη x hx
  have h3 : ((-ηmax : ℤ) : ℝ) ≤ (lap r x : ℝ) := by exact_mod_cast (show -ηmax ≤ lap r x by omega)
  push_cast at h3 ⊢
  linarith

end RandomSandpile

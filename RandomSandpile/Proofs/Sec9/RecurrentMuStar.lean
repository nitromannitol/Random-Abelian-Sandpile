import RandomSandpile.Proofs.Sec9.RecurrentBound
import RandomSandpile.Proofs.Sec9.StabLift

/-! Finite-volume lower gradient measures for recurrent perturbations. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- Every recurrent perturbation has the same lower gradient set as a nonnegative
stabilizing toppling function. -/
theorem muStarRecurrent_le_muStar {A : Set (Site d)} (hA : A.Finite)
    (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStarRecurrent A η l M ≤ muStar A η l M := by
  classical
  unfold muStarRecurrent muStar
  refine iSup₂_le fun f hf => ?_
  obtain ⟨r, hr, rfl⟩ := hf
  obtain ⟨c, _, hnonneg⟩ := hr.exists_nonnegative_shift (dClosure_finite hA)
  let v : Site d → ℤ := (dClosure A).indicator (fun x => r x + c)
  have hv : v ∈ stabilizing η A := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x
      by_cases hx : x ∈ dClosure A
      · simpa [v, hx] using hnonneg x hx
      · simp [v, hx]
    · intro x hx
      simp [v, hx]
    · intro x hx
      change lap ((dClosure A).indicator (fun x => r x + c)) x + η x ≤ _
      rw [SingleSourceH0.lap_indicator_dClosure _ hx, PegdenSmartRegularity.lap_add_const]
      exact hr.1 x hx
  let g : Site d → ℝ := fun x => (v x : ℝ) - (qlZ l x + qMZ M x)
  have hg : g ∈ perturbedSuper A η l M := ⟨v, hv, rfl⟩
  have heq : subGradSet g A = subGradSet (fun x => (r x : ℝ) -
      (qlZ l x + qMZ M x)) A := by
    apply SingleSourceH0.subGradSet_congr (c := (c : ℝ))
    intro y hy
    simp only [g, v, Set.indicator_of_mem hy, Int.cast_add]
    ring
  rw [← heq]
  exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)

/-- Lowering a function in the interior while keeping its boundary values can only
increase its lower gradient set. -/
theorem subGradSet_mono_fixed_boundary {A : Set (Site d)} (hA : A.Finite)
    {r v : Site d → ℝ} (hle : ∀ x ∈ A, r x ≤ v x)
    (hbd : ∀ y ∈ bdry A, r y = v y) : subGradSet v A ⊆ subGradSet r A := by
  classical
  intro p hp
  simp only [subGradSet, Set.mem_iUnion] at hp ⊢
  obtain ⟨x, hx, hp⟩ := hp
  let F : Site d → ℝ := fun z => r z - inner ℝ p (toE z)
  obtain ⟨y, hy, hymin⟩ := Set.exists_min_image (dClosure A) F (dClosure_finite hA)
    ⟨x, subset_dClosure A hx⟩
  have hmin : ∀ z ∈ dClosure A, F y ≤ F z := hymin
  have hmake : ∀ z ∈ A, F z = F y → ∀ t ∈ dClosure A,
      r z + inner ℝ p (toE t - toE z) ≤ r t := by
    intro z hz heq t ht
    have ht' := hmin t ht
    dsimp [F] at heq ht'
    rw [inner_sub_right]
    linarith
  by_cases hyA : y ∈ A
  · exact ⟨y, hyA, hmake y hyA rfl⟩
  · have hybd : y ∈ bdry A := (by simpa [dClosure_eq] using hy : y ∈ A ∨ y ∈ bdry A).resolve_left hyA
    have hxy : F y ≤ F x := hmin x (subset_dClosure A hx)
    have hpx := hp y hy
    have hr := hle x hx
    have heqbd := hbd y hybd
    have heq : F x = F y := by
      dsimp [F] at hxy ⊢
      rw [inner_sub_right] at hpx
      linarith
    exact ⟨x, hx, hmake x hx heq⟩

/-- Finite fixed-boundary recurrentization preserves the lower gradient measure. -/
theorem recurrentMuStarEquality : RecurrentMuStarEqualityStmt := by
  intro d hd A hA η l M
  apply le_antisymm (muStarRecurrent_le_muStar hA η l M)
  unfold muStar muStarRecurrent
  refine iSup₂_le fun f hf => ?_
  obtain ⟨v, hv, rfl⟩ := mem_perturbedSuper.mp hf
  obtain ⟨r, hr, hrbd, hrle⟩ := recurrentizeFixedBoundary d hd A hA η v hv.2
  let g : Site d → ℝ := fun x => (r x : ℝ) - (qlZ l x + qMZ M x)
  have hg : g ∈ recurrentPerturbed A η l M := ⟨r, hr, rfl⟩
  have hsub : subGradSet (fun x => (v x : ℝ) - (qlZ l x + qMZ M x)) A ⊆
      subGradSet g A := by
    apply subGradSet_mono_fixed_boundary hA
    · intro x hx
      have h := hrle v (fun _ _ => rfl) hv.2 x hx
      dsimp [g]
      exact sub_le_sub_right (Int.cast_le.mpr h) _
    · intro y hy
      dsimp [g]
      rw [hrbd y hy]
  exact (measure_mono hsub).trans (le_iSup_of_le g (le_iSup_of_le hg le_rfl))

end RandomSandpile

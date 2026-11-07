import RandomSandpile.Proofs.Sec9.RecurrentMonotone
import RandomSandpile.Proofs.Sec6.StrictConcavityNearMax

/-! Selection and Laplacian bounds for recurrent near-maximizers. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal Matrix
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- Every finite domain admits a recurrent stabilizing function. -/
theorem exists_recurrentFunction (hd : 2 ≤ d) {A : Set (Site d)} (hA : A.Finite)
    (η : Site d → ℤ) : ∃ r : Site d → ℤ, IsRecurrentFunction η A r := by
  obtain ⟨v, hv, _⟩ := NearMaxSequence.exists_locLegal_stabilizing (by omega) hA η
    (u := 0) ⟨fun _ => le_rfl, fun _ _ => rfl⟩
  obtain ⟨r, hr, _, _⟩ := recurrentizeFixedBoundary d hd A hA η v hv.2.2
  exact ⟨r, hr⟩

/-- Finite-volume recurrent upper measures admit recurrent near-maximizers. -/
theorem exists_nearMax_recurrent (hd : 2 ≤ d) {A : Set (Site d)} (hA : A.Finite)
    (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {ηmax : ℤ}
    (hη : ∀ x, η x ≤ ηmax) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : Site d → ℤ, IsRecurrentFunction η A r ∧
      ENNReal.ofReal ((muRecurrent A η l M).toReal - δ) ≤
        volume (supGradSet (fun x => (r x : ℝ) - (qlZ l x + qMZ M x)) A) := by
  have hfin : muRecurrent A η l M ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (muRecurrent_le_ncard (by omega) hA (fun x _ => hη x) l M)
  by_cases h0 : (muRecurrent A η l M).toReal - δ ≤ 0
  · obtain ⟨r, hr⟩ := exists_recurrentFunction hd hA η
    exact ⟨r, hr, by rw [ENNReal.ofReal_eq_zero.2 h0]; exact bot_le⟩
  · rw [not_le] at h0
    have hlt : ENNReal.ofReal ((muRecurrent A η l M).toReal - δ) < muRecurrent A η l M := by
      conv_rhs => rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    rw [muRecurrent] at hlt
    obtain ⟨w, hw, hlt'⟩ := lt_biSup_iff.1 hlt
    obtain ⟨r, hr, rfl⟩ := hw
    exact ⟨r, hr, hlt'.le⟩

/-- Recurrence and bounded background give the Laplacian bound required by compactness. -/
theorem recurrent_abs_lapR_le (hd : 1 ≤ d) {η r : Site d → ℤ} {ηmin ηmax : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) {A : Set (Site d)}
    (hr : IsRecurrentFunction η A r) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    {x : Site d} (hx : x ∈ A) :
    |lapR (fun y => (r y : ℝ) - (qlZ l y + qMZ M y)) x| ≤
      NearMaxSequence.lapBound d ηmin ηmax l M := by
  rw [lapR_sub', lapR_intCast, lapQuadratic d hd]
  have h1 := hr.height_nonneg hx
  have h2 := hr.1 x hx
  obtain ⟨hη1, hη2⟩ := hη x
  set B : ℤ := |max ηmax 0| + |2 * (d : ℤ) - 1 - ηmin|
  have hlo : -B ≤ lap r x := by
    have := le_max_left ηmax 0
    have := le_abs_self (max ηmax 0)
    have := abs_nonneg (2 * (d : ℤ) - 1 - ηmin)
    linarith
  have hhi : lap r x ≤ B := by
    have := le_abs_self (2 * (d : ℤ) - 1 - ηmin)
    have := abs_nonneg (max ηmax 0)
    linarith
  have hlo' : -(B : ℝ) ≤ (lap r x : ℝ) := by exact_mod_cast hlo
  have hhi' : (lap r x : ℝ) ≤ B := by exact_mod_cast hhi
  unfold NearMaxSequence.lapBound
  rw [abs_le]
  constructor <;> linarith [le_abs_self (l + M.trace), neg_abs_le (l + M.trace)]

/-- Finite-volume recurrent lower measures admit recurrent near-maximizers. -/
theorem exists_nearMax_recurrent_lower (hd : 2 ≤ d) {A : Set (Site d)} (hA : A.Finite)
    (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {ηmin : ℤ}
    (hη : ∀ x, ηmin ≤ η x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : Site d → ℤ, IsRecurrentFunction η A r ∧
      ENNReal.ofReal ((muStarRecurrent A η l M).toReal - δ) ≤
        volume (subGradSet (fun x => (r x : ℝ) - (qlZ l x + qMZ M x)) A) := by
  have hfin : muStarRecurrent A η l M ≠ ⊤ := by
    rw [recurrentMuStarEquality d hd A hA η l M]
    exact NearMaxSequence.muStar_ne_top (by omega) hA hη l M
  by_cases h0 : (muStarRecurrent A η l M).toReal - δ ≤ 0
  · obtain ⟨r, hr⟩ := exists_recurrentFunction hd hA η
    exact ⟨r, hr, by rw [ENNReal.ofReal_eq_zero.2 h0]; exact bot_le⟩
  · rw [not_le] at h0
    have hlt : ENNReal.ofReal ((muStarRecurrent A η l M).toReal - δ) < muStarRecurrent A η l M := by
      conv_rhs => rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    rw [muStarRecurrent] at hlt
    obtain ⟨w, hw, hlt'⟩ := lt_biSup_iff.1 hlt
    obtain ⟨r, hr, rfl⟩ := hw
    exact ⟨r, hr, hlt'.le⟩

end RandomSandpile

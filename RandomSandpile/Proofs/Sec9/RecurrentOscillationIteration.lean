import RandomSandpile.Proofs.Sec9.RecurrentPoissonOscillation

/-! # Iteration of lattice oscillation estimates -/

noncomputable section
open LatticeProb

namespace RandomSandpile

/-- Pairwise bounds on a finite lattice box are attained by a minimum and maximum. -/
theorem lattice_box_extrema {d R : ℕ} (c : Site d) (f : Site d → ℝ) :
    ∃ a b : ℝ, (∀ z ∈ box d R, a ≤ f (c + z) ∧ f (c + z) ≤ b) ∧
      ∃ x ∈ box d R, ∃ y ∈ box d R, b - a = |f (c + x) - f (c + y)| := by
  let A := originBox d R
  have hbox : ∀ z : Site d, z ∈ A ↔ z ∈ box d R := by
    intro z
    simp only [A, originBox, Fintype.mem_piFinset, Finset.mem_Icc, box, Set.mem_setOf_eq]
    exact forall_congr' fun i => (abs_le).symm
  have hA : A.Nonempty := ⟨0, (hbox 0).2 (by simp [box])⟩
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image A (fun z => f (c + z)) hA
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image A (fun z => f (c + z)) hA
  refine ⟨f (c + x), f (c + y), ?_, y, (hbox y).1 hy, x, (hbox x).1 hx, ?_⟩
  · intro z hz
    exact ⟨hmin z ((hbox z).2 hz), hmax z ((hbox z).2 hz)⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmin y hy))]

/-- A bound on all pairwise differences contracts on the half-sized box. -/
theorem poisson_pairwise_contraction (d : ℕ) (hd : 1 ≤ d) :
    ∃ q C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 < C ∧
      ∀ (R : ℕ) (c : Site d) (f : Site d → ℝ) (B M : ℝ), 1 ≤ R → 0 ≤ M →
        (∀ x ∈ box d (2 * R), ∀ y ∈ box d (2 * R),
          |f (c + x) - f (c + y)| ≤ B) →
        (∀ z ∈ box d (2 * R),
          |nbrSum f (c + z) - 2 * (d : ℝ) * f (c + z)| ≤ M) →
        ∀ x ∈ box d R, ∀ y ∈ box d R,
          |f (c + x) - f (c + y)| ≤ q * B + C * M * ((R : ℝ) + 1) ^ 2 := by
  obtain ⟨q, C, hq, hq1, hC, h⟩ := poisson_oscillation_contraction_translate d hd
  refine ⟨q, C, hq, hq1, hC, ?_⟩
  intro R c f B M hR hM hb hl x hx y hy
  obtain ⟨a, b, hab, u, hu, v, hv, heq⟩ := lattice_box_extrema (R := 2 * R) c f
  have hdiam : b - a ≤ B := by rw [heq]; exact hb u hu v hv
  exact (h R c f a b M hR hM hab hl x hx y hy).trans (by
    gcongr)

/-- Iterating the contraction gives a geometric decay plus a forcing error. -/
theorem poisson_pairwise_dyadic (d : ℕ) (hd : 1 ≤ d) :
    ∃ q C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 < C ∧
      ∀ (k R S : ℕ) (c : Site d) (f : Site d → ℝ) (B M : ℝ),
        1 ≤ R → 2 ^ k * R ≤ S → 0 ≤ M →
        (∀ x ∈ box d S, ∀ y ∈ box d S, |f (c + x) - f (c + y)| ≤ B) →
        (∀ z ∈ box d S, |nbrSum f (c + z) - 2 * (d : ℝ) * f (c + z)| ≤ M) →
        ∀ x ∈ box d R, ∀ y ∈ box d R,
          |f (c + x) - f (c + y)| ≤
            q ^ k * B + C * M * ((S : ℝ) + 1) ^ 2 * ∑ i ∈ Finset.range k, q ^ i := by
  obtain ⟨q, C, hq, hq1, hC, hc⟩ := poisson_pairwise_contraction d hd
  refine ⟨q, C, hq, hq1, hC, ?_⟩
  intro k
  induction k with
  | zero =>
    intro R S c f B M hR hRS hM hb hl x hx y hy
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] at *
    exact hb x (mem_box_of_le hRS hx) y (mem_box_of_le hRS hy)
  | succ k ih =>
    intro R S c f B M hR hRS hM hb hl x hx y hy
    have hRS' : 2 ^ k * (2 * R) ≤ S := by
      have : 2 ^ (k + 1) * R = 2 ^ k * (2 * R) := by rw [pow_succ]; ring
      omega
    have hR2 : 1 ≤ 2 * R := by omega
    have hb' := ih (2 * R) S c f B M hR2 hRS' hM hb hl
    have hsmall : 2 * R ≤ S := by
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      nlinarith
    have hl' : ∀ z ∈ box d (2 * R),
        |nbrSum f (c + z) - 2 * (d : ℝ) * f (c + z)| ≤ M :=
      fun z hz => hl z (mem_box_of_le hsmall hz)
    have hh := hc R c f
      (q ^ k * B + C * M * ((S : ℝ) + 1) ^ 2 * ∑ i ∈ Finset.range k, q ^ i)
      M hR hM hb' hl' x hx y hy
    have hE : C * M * ((R : ℝ) + 1) ^ 2 ≤ C * M * ((S : ℝ) + 1) ^ 2 := by
      gcongr
      exact_mod_cast (by omega : R ≤ S)
    have hsum : (∑ i ∈ Finset.range (k + 1), q ^ i) =
        1 + q * ∑ i ∈ Finset.range k, q ^ i := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, pow_succ', ← Finset.mul_sum]
      ring
    rw [hsum, pow_succ]
    nlinarith

end RandomSandpile

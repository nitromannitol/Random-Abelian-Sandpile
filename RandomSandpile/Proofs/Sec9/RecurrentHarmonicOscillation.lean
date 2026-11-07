import LatticeProb.Walk.Harnack
import Mathlib.Tactic

/-! # Oscillation contraction for lattice harmonic functions -/

noncomputable section
open LatticeProb
namespace RandomSandpile

/-- Harnack's inequality contracts the oscillation of harmonic functions on concentric boxes. -/
theorem harmonic_oscillation_contraction (d : ℕ) (hd : 1 ≤ d) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ (R : ℕ) (u : Site d → ℝ) (a b : ℝ), 1 ≤ R →
        (∀ x ∈ box d (2 * R), a ≤ u x ∧ u x ≤ b) →
        (∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) →
        ∀ x ∈ box d R, ∀ y ∈ box d R, |u x - u y| ≤ q * (b - a) := by
  obtain ⟨C₀, hC₀, hH⟩ := harnack d hd
  let C := max C₀ 1
  have hC : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨(C - 1) / (C + 1), by positivity, ?_, ?_⟩
  · apply (div_lt_one (by positivity : 0 < C + 1)).2
    linarith
  intro R u a b hR hbounds hharm x hx y hy
  have hsumconst : ∀ c : ℝ, ∀ z : Site d, nbrSum (fun _ => c) z = 2 * (d : ℝ) * c := by
    intro c z
    simp [nbrSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hlow : ∀ z ∈ box d (2 * R - 1),
      nbrSum (fun w => u w - a) z = 2 * (d : ℝ) * (u z - a) := by
    intro z hz
    have h := nbrSum_add_const_mul 1 (-1) u (fun _ => a) z
    simp only [one_mul, neg_one_mul] at h
    rw [hsumconst, hharm z hz] at h
    have heq : 2 * (d : ℝ) * u z + -(2 * (d : ℝ) * a) =
        2 * (d : ℝ) * (u z - a) := by ring
    rw [heq] at h
    simpa only [sub_eq_add_neg] using h
  have hhigh : ∀ z ∈ box d (2 * R - 1),
      nbrSum (fun w => b - u w) z = 2 * (d : ℝ) * (b - u z) := by
    intro z hz
    have h := nbrSum_add_const_mul 1 (-1) (fun _ => b) u z
    simp only [one_mul, neg_one_mul] at h
    rw [hsumconst, hharm z hz] at h
    have heq : 2 * (d : ℝ) * b + -(2 * (d : ℝ) * u z) =
        2 * (d : ℝ) * (b - u z) := by ring
    rw [heq] at h
    simpa only [sub_eq_add_neg] using h
  have hlpos : ∀ z ∈ box d (2 * R), 0 ≤ u z - a := fun z hz => sub_nonneg.2 (hbounds z hz).1
  have hhpos : ∀ z ∈ box d (2 * R), 0 ≤ b - u z := fun z hz => sub_nonneg.2 (hbounds z hz).2
  have hxy0 := hH R (fun z => u z - a) hR hlpos hlow x hx y hy
  have hyx0 := hH R (fun z => u z - a) hR hlpos hlow y hy x hx
  have hxy1 := hH R (fun z => b - u z) hR hhpos hhigh x hx y hy
  have hyx1 := hH R (fun z => b - u z) hR hhpos hhigh y hy x hx
  have hxpos := hlpos x (mem_box_of_le (by omega) hx)
  have hypos := hlpos y (mem_box_of_le (by omega) hy)
  have hxpos' := hhpos x (mem_box_of_le (by omega) hx)
  have hypos' := hhpos y (mem_box_of_le (by omega) hy)
  have hxy : u x - a ≤ C * (u y - a) := hxy0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hypos)
  have hyx : u y - a ≤ C * (u x - a) := hyx0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxpos)
  have hxy' : b - u x ≤ C * (b - u y) := hxy1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hypos')
  have hyx' : b - u y ≤ C * (b - u x) := hyx1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxpos')
  have hden : 0 < C + 1 := by positivity
  rw [abs_le]
  constructor
  · have hb : (C + 1) * (u y - u x) ≤ (C - 1) * (b - a) := by nlinarith
    have hb' : u y - u x ≤ ((C - 1) * (b - a)) / (C + 1) :=
      (le_div_iff₀ hden).2 (by nlinarith [hb])
    rw [div_mul_eq_mul_div]
    linarith
  · have hb : (C + 1) * (u x - u y) ≤ (C - 1) * (b - a) := by nlinarith
    have hb' : u x - u y ≤ ((C - 1) * (b - a)) / (C + 1) :=
      (le_div_iff₀ hden).2 (by nlinarith [hb])
    rw [div_mul_eq_mul_div]
    linarith

end RandomSandpile

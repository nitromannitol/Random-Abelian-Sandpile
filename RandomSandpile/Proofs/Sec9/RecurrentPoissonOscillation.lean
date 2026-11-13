import RandomSandpile.Proofs.Sec9.RecurrentPoissonDecomposition
import RandomSandpile.Proofs.Sec9.RecurrentHarmonicOscillation
import LatticeProb.Walk.ExitBox

/-! # Oscillation estimate for bounded discrete Laplacians -/

noncomputable section
open LatticeProb

namespace RandomSandpile

/-- Harnack contraction with a quadratic error for a bounded Laplacian. -/
theorem poisson_oscillation_contraction (d : ℕ) (hd : 1 ≤ d) :
    ∃ q C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 < C ∧
      ∀ (R : ℕ) (f : Site d → ℝ) (a b M : ℝ), 1 ≤ R → 0 ≤ M →
        (∀ x ∈ box d (2 * R), a ≤ f x ∧ f x ≤ b) →
        (∀ x ∈ box d (2 * R), |nbrSum f x - 2 * (d : ℝ) * f x| ≤ M) →
        ∀ x ∈ box d R, ∀ y ∈ box d R,
          |f x - f y| ≤ q * (b - a) + C * M * ((R : ℝ) + 1) ^ 2 := by
  obtain ⟨q, hq0, hq1, hcontract⟩ := harmonic_oscillation_contraction d hd
  obtain ⟨C, hC, hexit⟩ := u_originBox_le (by omega : 0 < d)
  refine ⟨q, 72 * C, hq0, hq1, by positivity, ?_⟩
  intro R f a b M hR hM hbounds hlap x hx y hy
  let A := originBox d (2 * R)
  have hbox : ∀ z : Site d, z ∈ A ↔ z ∈ box d (2 * R) := by
    intro z
    simp only [A, originBox, Fintype.mem_piFinset, Finset.mem_Icc, box, Set.mem_ofPred_eq]
    exact forall_congr' fun i => (abs_le).symm
  obtain ⟨p, hp0, hplap⟩ := finite_poisson_decomposition (by omega : 0 < d) A f
  have hpM : ∀ z ∈ A, |(∑ a : Dir d, p (z + dirVec a)) - 2 * d * p z| ≤ M := by
    intro z hz
    rw [hplap z hz, ← nbrSum_eq_sum_dir]
    exact hlap z ((hbox z).1 hz)
  have hpb := finite_poisson_abs_le_exit (by omega : 0 < d) A p M hp0 hpM
  let K : ℝ := M * (C * ((2 * (2 * R) + 1 : ℕ) : ℝ) ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hp : ∀ z, |p z| ≤ K := by
    intro z
    by_cases hz : z ∈ A
    · exact (hpb z hz).trans (mul_le_mul_of_nonneg_left (hexit (2 * R) z) hM)
    · rw [hp0 z hz, abs_zero]; exact hK
  let h : Site d → ℝ := fun z => f z - p z
  have hhb : ∀ z ∈ box d (2 * R), a - K ≤ h z ∧ h z ≤ b + K := by
    intro z hz
    have hf := hbounds z hz
    have hpz := abs_le.mp (hp z)
    dsimp [h]
    constructor <;> linarith
  have hhh : ∀ z ∈ box d (2 * R - 1), nbrSum h z = 2 * (d : ℝ) * h z := by
    intro z hz
    have hz' : z ∈ A := (hbox z).2 (mem_box_of_le (by omega) hz)
    have hh := hplap z hz'
    rw [← nbrSum_eq_sum_dir, ← nbrSum_eq_sum_dir] at hh
    have hn := nbrSum_add_const_mul 1 (-1) f p z
    simp only [one_mul, neg_one_mul] at hn
    have hn' : nbrSum h z = nbrSum f z - nbrSum p z := by
      simpa [h, sub_eq_add_neg] using hn
    rw [hn']
    dsimp [h]
    linarith
  have hc := hcontract R h (a - K) (b + K) hR hhb hhh x hx y hy
  have htriangle : |f x - f y| ≤ |h x - h y| + |p x| + |p y| := by
    have h1 := abs_add_le (h x - h y) (p x - p y)
    have h2 : |p x - p y| ≤ |p x| + |p y| := by
      simpa [sub_eq_add_neg] using abs_add_le (p x) (-p y)
    have heq : h x - h y + (p x - p y) = f x - f y := by dsimp [h]; ring
    rw [heq] at h1
    linarith
  have hscale : ((2 * (2 * R) + 1 : ℕ) : ℝ) ^ 2 ≤ 16 * ((R : ℝ) + 1) ^ 2 := by
    push_cast
    have hr : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    nlinarith [sq_nonneg (R : ℝ)]
  have hKbound : K ≤ 16 * M * C * ((R : ℝ) + 1) ^ 2 := by
    dsimp [K]
    nlinarith [mul_nonneg hM (le_of_lt hC), mul_nonneg (mul_nonneg hM (le_of_lt hC))
      (sub_nonneg.mpr hscale)]
  have hqK := mul_nonneg (sub_nonneg.mpr hq1.le) hK
  nlinarith [hp x, hp y]

/-- The bounded-Laplacian oscillation estimate on boxes with arbitrary center. -/
theorem poisson_oscillation_contraction_translate (d : ℕ) (hd : 1 ≤ d) :
    ∃ q C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 < C ∧
      ∀ (R : ℕ) (c : Site d) (f : Site d → ℝ) (a b M : ℝ), 1 ≤ R → 0 ≤ M →
        (∀ z ∈ box d (2 * R), a ≤ f (c + z) ∧ f (c + z) ≤ b) →
        (∀ z ∈ box d (2 * R),
          |nbrSum f (c + z) - 2 * (d : ℝ) * f (c + z)| ≤ M) →
        ∀ x ∈ box d R, ∀ y ∈ box d R,
          |f (c + x) - f (c + y)| ≤ q * (b - a) + C * M * ((R : ℝ) + 1) ^ 2 := by
  obtain ⟨q, C, hq0, hq1, hC, h⟩ := poisson_oscillation_contraction d hd
  refine ⟨q, C, hq0, hq1, hC, ?_⟩
  intro R c f a b M hR hM hb hl x hx y hy
  apply h R (fun z => f (c + z)) a b M hR hM hb _ x hx y hy
  intro z hz
  have hn : nbrSum (fun w => f (c + w)) z = nbrSum f (c + z) := by
    simp only [nbrSum_eq_sum_dir, add_assoc]
  rw [hn]
  exact hl z hz

end RandomSandpile

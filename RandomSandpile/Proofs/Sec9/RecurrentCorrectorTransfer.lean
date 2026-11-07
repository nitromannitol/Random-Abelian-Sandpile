import RandomSandpile.Proofs.Sec9.RecurrentCorrectorOscillation

/-! # Transfer of recurrent corrector oscillation estimates -/

noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

/-- Choose nested dyadic radii whose outer radius is controlled by the
macroscopic scale, once that scale dominates the rounding errors. -/
theorem recurrent_corrector_choose_dyadic_radii (s ρ : ℝ) (k : ℕ)
    (hs : 0 < s) (hρ : 0 < ρ)
    (hlarge : 3 * (2 : ℝ) ^ k ≤ ρ * s) :
    ∃ R S : ℕ, 1 ≤ R ∧ 2 ^ k * R ≤ S ∧
      s * (ρ / (2 : ℝ) ^ k) + 1 ≤ R ∧
      (S : ℝ) + 1 ≤ 2 * ρ * s := by
  let t : ℝ := (2 : ℝ) ^ k
  have ht : 1 ≤ t := one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by linarith
  let R : ℕ := ⌈s * (ρ / t) + 1⌉₊
  refine ⟨R, 2 ^ k * R, ?_, le_rfl, Nat.le_ceil _, ?_⟩
  · have h := Nat.le_ceil (s * (ρ / t) + 1)
    have hp : 0 ≤ s * (ρ / t) := by positivity
    exact_mod_cast (show (1 : ℝ) ≤ R by dsimp [R] at *; linarith)
  · have hceil : (R : ℝ) < s * (ρ / t) + 2 := by
      dsimp [R]
      have hpos : 0 ≤ s * (ρ / t) + 1 := by positivity
      have h := Nat.ceil_lt_add_one hpos
      linarith
    have hmul := mul_lt_mul_of_pos_left hceil ht0
    have heq : t * (s * (ρ / t)) = ρ * s := by field_simp
    push_cast
    change (t * (R : ℝ)) + 1 ≤ 2 * ρ * s
    rw [mul_add, heq] at hmul
    change 3 * t ≤ ρ * s at hlarge
    nlinarith

/-- A rounded center and a lattice box lie in a macroscopic ball when
their continuum radius and rounding error fit inside that ball. -/
theorem recurrent_corrector_rounded_box_containment {d S : ℕ} (s m : ℝ)
    (x : Rd d) (hs : 0 ≤ s)
    (hsize : s * ‖x‖ + Real.sqrt d + Real.sqrt d * S ≤ m * s) :
    ∀ z ∈ box d S, ‖toE (latticeRound (s • x) + z)‖ ≤ m * s := by
  intro z hz
  have hround := norm_toE_latticeRound_sub_le_sqrt (s • x)
  have hcenter := norm_le_insert' (toE (latticeRound (s • x))) (s • x)
  rw [norm_smul, Real.norm_of_nonneg hs] at hcenter
  have hbox := translated_box_norm_le (latticeRound (s • x)) z hz
  linarith

/-- A lattice dyadic estimate transfers to rounded continuum points whenever the
smaller lattice box contains both rounded points. -/
theorem recurrent_corrector_dyadic_transfer {d : ℕ} {η : Site d → ℤ}
    (κ : ℝ) (n k R S : ℕ) (q B C m : ℝ) (x y : Rd d)
    (hs : 0 ≤ ssScale d n)
    (hR : ssScale d n * dist x y + 1 ≤ R)
    (hdyadic : ∀ (c : Site d),
      (∀ z ∈ box d S, ‖toE (c + z)‖ ≤ m * ssScale d n) →
      ∀ a ∈ box d R, ∀ b ∈ box d R,
        |((n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n (c + a)) -
          ((n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n (c + b))| ≤
          q ^ k * B + C * (((S : ℝ) + 1) / ssScale d n) ^ 2)
    (hball : ∀ z ∈ box d S,
      ‖toE (latticeRound (ssScale d n • x) + z)‖ ≤ m * ssScale d n) :
    |ssCorrector d η κ n x - ssCorrector d η κ n y| ≤
      q ^ k * B + C * (((S : ℝ) + 1) / ssScale d n) ^ 2 := by
  let a := latticeRound (ssScale d n • x)
  let b := latticeRound (ssScale d n • y)
  have hab : b - a ∈ box d R := by
    intro i
    have h := abs_latticeRound_sub_le (ssScale d n • y) (ssScale d n • x) i
    have heq : ‖ssScale d n • y - ssScale d n • x‖ = ssScale d n * dist x y := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hs, dist_eq_norm, norm_sub_rev]
    rw [heq] at h
    have hi : |((b - a) i : ℝ)| ≤ (R : ℝ) := by
      simpa [a, b] using h.trans hR
    exact_mod_cast hi
  have hzero : (0 : Site d) ∈ box d R := by simp [box]
  have h := hdyadic a hball 0 hzero (b - a) hab
  simp only [add_zero, add_sub_cancel] at h
  simpa [ssCorrector, a, b, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

end RandomSandpile

import RandomSandpile.Proofs.Sec9.RecurrentCompactnessLap
import RandomSandpile.Proofs.Sec9.RecurrentCorrectorBoxBoundary
import RandomSandpile.Proofs.Sec9.OpenBoundaryCompactness

/-! # The discrete Poisson equation for recurrent correctors -/

noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

/-- Removing the lattice Green kernel cancels the point source. -/
theorem lapR_ssW {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ) (n : ℕ) (z : Site d) :
    lapR (ssW d η n) z = (lap (singleSourceOdometer η n) z : ℝ) +
      (n : ℝ) * (if z = 0 then 1 else 0) := by
  have hg : lapR (fun p => (n : ℝ) * ssGreen d p) z =
      (n : ℝ) * lapR (ssGreen d) z := by
    simpa using lapR_mul_sub_const (n : ℝ) 0 (ssGreen d) z
  have h := lapR_const_mul_sub 1 (fun p => (singleSourceOdometer η n p : ℝ))
    (fun p => (n : ℝ) * ssGreen d p) z
  change lapR (fun p => (singleSourceOdometer η n p : ℝ) - (n : ℝ) * ssGreen d p) z = _
  simpa [lapR_intCast, hg, lapR_ssGreen hd] using h

/-- Adding constants and multiplying by the macroscopic normalization leaves
the discrete Poisson equation in its scaled form. -/
theorem lapR_recurrent_corrector {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (κ : ℝ) (n : ℕ) (z : Site d) :
    lapR (fun p => (n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n p +
      (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n) z =
      (n : ℝ) ^ (-(2 / (d : ℝ))) *
        ((lap (singleSourceOdometer η n) z : ℝ) +
          (n : ℝ) * (if z = 0 then 1 else 0)) := by
  rw [← lapR_ssW hd η n z]
  simp only [lapR, nbrSum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- A bounded background yields an inverse-square scaled bound on the
corrector's discrete Laplacian. -/
theorem recurrent_corrector_abs_lapR_le {d : ℕ} (hd : 2 ≤ d)
    {ηmin ηmax : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) (hfinite : SingleSourceFinite η)
    (κ : ℝ) (n : ℕ) (z : Site d) :
    |lapR (fun p => (n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n p +
      (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n) z| ≤
      (ssScale d n ^ 2)⁻¹ * (|(ηmin : ℝ)| + |(ηmax : ℝ)| + |(2 * (d : ℝ) - 1)|) := by
  rw [lapR_recurrent_corrector hd, rpow_neg_two_div, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left (recurrent_abs_lap_add_le hη hfinite n z)
    (inv_nonneg.mpr (sq_nonneg _))

/-- The boundary estimate and discrete Poisson equation give a uniform
interior bound on a growing macroscopic box. -/
theorem recurrent_corrector_box_interior_bound_above {d : ℕ} (hd : 2 ≤ d)
    {ηmin ηmax : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) (hfinite : SingleSourceFinite η)
    (htail : SingleSourceVanishingTail η) (κ Cg Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ Cg * ‖toE z‖ ^ (-(d : ℝ)))
    (m : ℝ) :
    ∃ r : ℝ, 0 < r ∧ m ≤ r ∧ ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ originBox d ⌈r * ssScale d n⌉₊,
        |(n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n z +
          (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n| ≤ B := by
  obtain ⟨r, hr, hm, B, hB⟩ :=
    recurrent_corrector_box_boundary_bound_above hd η htail κ Cg Rg hRg hasymp m
  obtain ⟨C, hC, hpoisson⟩ := originBox_poisson_abs_le_boundary (by omega : 0 < d)
  let K : ℝ := |(ηmin : ℝ)| + |(ηmax : ℝ)| + |(2 * (d : ℝ) - 1)|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨r, hr, hm, B + C * K * (2 * r + 3) ^ 2, ?_⟩
  filter_upwards [hB, eventually_ge_atTop 1] with n hn hn1
  intro z hz
  let s := ssScale d n
  let L := ⌈r * s⌉₊
  let f : Site d → ℝ := fun p => (n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n p +
    (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n
  have hs : 1 ≤ s := one_le_ssScale hn1
  have hs0 : 0 < s := by linarith
  have hceil : (L : ℝ) < r * s + 1 := Nat.ceil_lt_add_one (mul_nonneg hr.le hs0.le)
  have hrad : ((2 * L + 1 : ℕ) : ℝ) ≤ (2 * r + 3) * s := by push_cast; nlinarith
  have hratio : ((2 * L + 1 : ℕ) : ℝ) / s ≤ 2 * r + 3 := (div_le_iff₀ hs0).2 hrad
  have hsq : (((2 * L + 1 : ℕ) : ℝ) / s) ^ 2 ≤ (2 * r + 3) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hratio
  have hforce : C * ((s ^ 2)⁻¹ * K) * ((2 * L + 1 : ℕ) : ℝ) ^ 2 ≤
      C * K * (2 * r + 3) ^ 2 := by
    have heq : C * ((s ^ 2)⁻¹ * K) * ((2 * L + 1 : ℕ) : ℝ) ^ 2 =
        C * K * ((((2 * L + 1 : ℕ) : ℝ) / s) ^ 2) := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hsq (mul_nonneg hC.le hK)
  have hbound := hpoisson L f B ((s ^ 2)⁻¹ * K) (by positivity)
    (by simpa [f, L, s] using hn)
    (by
      intro x hx
      rw [← nbrSum_eq_sum_dir]
      exact recurrent_corrector_abs_lapR_le hd hη hfinite κ n x) z hz
  exact le_trans hbound (by linarith)

/-- A sufficiently large macroscopic box has a uniformly bounded corrector. -/
theorem recurrent_corrector_box_interior_bound {d : ℕ} (hd : 2 ≤ d)
    {ηmin ηmax : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) (hfinite : SingleSourceFinite η)
    (htail : SingleSourceVanishingTail η) (κ Cg Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ Cg * ‖toE z‖ ^ (-(d : ℝ))) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ originBox d ⌈r * ssScale d n⌉₊,
        |(n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n z +
          (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n| ≤ B := by
  obtain ⟨r, hr, _, B, hB⟩ :=
    recurrent_corrector_box_interior_bound_above hd hη hfinite htail κ Cg Rg hRg hasymp 0
  exact ⟨r, hr, B, hB⟩

/-- Every macroscopic lattice ball has an eventual uniform corrector bound. -/
theorem recurrent_corrector_lattice_ball_bound {d : ℕ} (hd : 2 ≤ d)
    {ηmin ηmax : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) (hfinite : SingleSourceFinite η)
    (htail : SingleSourceVanishingTail η) (κ Cg Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ Cg * ‖toE z‖ ^ (-(d : ℝ)))
    (m : ℝ) : ∃ B : ℝ, ∀ᶠ n : ℕ in atTop, ∀ z : Site d,
      ‖toE z‖ ≤ m * ssScale d n →
      |(n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n z +
        (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n| ≤ B := by
  obtain ⟨r, hr, hm, B, hB⟩ :=
    recurrent_corrector_box_interior_bound_above hd hη hfinite htail κ Cg Rg hRg hasymp m
  refine ⟨B, ?_⟩
  filter_upwards [hB, eventually_ge_atTop 1] with n hn hn1
  intro z hz
  apply hn z
  rw [mem_originBox_iff_abs_le]
  intro i
  have hs : 0 ≤ ssScale d n := (ssScale_pos hn1).le
  have hi : |(z i : ℝ)| ≤ ‖toE z‖ := by
    simpa [toE_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (toE z) i
  have hcoord : |(z i : ℝ)| ≤ (⌈r * ssScale d n⌉₊ : ℝ) :=
    le_trans hi (le_trans hz (le_trans (mul_le_mul_of_nonneg_right hm hs) (Nat.le_ceil _)))
  exact_mod_cast hcoord

/-- The rescaled recurrent correctors are eventually bounded on every ball. -/
theorem recurrent_corrector_local_bound {d : ℕ} (hd : 2 ≤ d)
    {ηmin ηmax : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) (hfinite : SingleSourceFinite η)
    (htail : SingleSourceVanishingTail η) (κ Cg Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ Cg * ‖toE z‖ ^ (-(d : ℝ)))
    (m : ℕ) : ∃ B : ℝ, ∀ᶠ n : ℕ in atTop, ∀ x : Rd d,
      ‖x‖ ≤ m → |ssCorrector d η κ n x| ≤ B := by
  obtain ⟨B, hB⟩ := recurrent_corrector_lattice_ball_bound hd hη hfinite htail κ Cg Rg hRg
    hasymp ((m : ℝ) + Real.sqrt d)
  refine ⟨B, ?_⟩
  filter_upwards [hB, eventually_ge_atTop 1] with n hn hn1
  intro x hx
  have hs : 1 ≤ ssScale d n := one_le_ssScale hn1
  have hround := norm_toE_latticeRound_sub_le_sqrt (ssScale d n • x)
  have htri := norm_le_insert' (toE (latticeRound (ssScale d n • x))) (ssScale d n • x)
  have hnorm : ‖toE (latticeRound (ssScale d n • x))‖ ≤
      ((m : ℝ) + Real.sqrt d) * ssScale d n := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)] at htri
    have := Real.sqrt_nonneg (d : ℝ)
    nlinarith
  simpa [ssCorrector] using hn (latticeRound (ssScale d n • x)) hnorm

end RandomSandpile

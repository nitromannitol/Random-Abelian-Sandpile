import RandomSandpile.Steps.Sec7.OdometerLowerBound
import RandomSandpile.Proofs.Sec5.MuBounded

/-!
# Proofs of the steps of Lemma 7.4 (a lower bound on the odometer)

Proofs of `SuperharmonicMinPrincipleStmt`, `StabilizingGreenComparisonStmt` and
`MeanGreenPotentialLowerStmt` (`RandomSandpile/Steps/Sec7/OdometerLowerBound.lean`), and the
assembly `odometerLowerBound_of_divisibleHomogenize : DivisibleHomogenizeStmt →
OdometerLowerBoundStmt` (Lemma 7.4 from Lemma 7.3).

* The minimum principle is the classical extremal argument: among the minimizers of `f` over the
  finite set `A`, take one, `z`, with the largest first coordinate. If every value of `f` on `∂A`
  exceeded `f(x)`, all neighbours of `z` would satisfy `f ≥ f(z)`; superharmonicity forces
  `f(z + e_1) = f(z)`, so `z + e_1` is either a minimizer in `A` with a larger first coordinate or
  a point of `∂A` with `f ≤ f(x)`.
* The Laplacian of the quadratic `q_l = l |x|² / (2d)` is `l` (`lapQuadratic`, Lemma 5.4 support,
  `RandomSandpile/Proofs/Sec5/MuBounded.lean`); the Green potentials solve the Poisson equation in
  `B_n` (`lapR_greenPotential`) and vanish on `∂B_n` (`greenPotential_eq_zero_of_not_mem`).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- **Discrete minimum principle** (1243-1247). -/
theorem superharmonicMinPrinciple : SuperharmonicMinPrincipleStmt := by
  intro d hd A hA f hf x hx
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  obtain ⟨B, rfl⟩ := hA.exists_finset_coe
  have hxB : x ∈ B := by exact_mod_cast hx
  obtain ⟨z0, hz0B, hz0⟩ := B.exists_min_image f ⟨x, hxB⟩
  set M := B.filter (fun z => f z = f z0) with hM_def
  have hz0M : z0 ∈ M := Finset.mem_filter.2 ⟨hz0B, rfl⟩
  let i₀ : Fin d := ⟨0, hd⟩
  obtain ⟨z, hzM, hzmax⟩ := M.exists_max_image (fun z => z i₀) ⟨z0, hz0M⟩
  obtain ⟨hzB, hfz⟩ := Finset.mem_filter.1 hzM
  have hfx : f z ≤ f x := hfz ▸ hz0 x hxB
  have hnb : ∀ y, Adj y z → f z ≤ f y := by
    intro y hy
    by_cases hyB : y ∈ B
    · rw [hfz]; exact hz0 y hyB
    · have hyb : y ∈ bdry (B : Set (Site d)) :=
        mem_bdry.2 ⟨by exact_mod_cast hyB, z, by exact_mod_cast hzB, hy⟩
      linarith [hcon y hyb]
  have hplus : ∀ i, f z ≤ f (z + unit i) := fun i => hnb _ ⟨i, Or.inr rfl⟩
  have hminus : ∀ i, f z ≤ f (z - unit i) := fun i =>
    hnb _ ⟨i, Or.inl (sub_add_cancel z (unit i)).symm⟩
  have hlap := hf z (by exact_mod_cast hzB)
  rw [lapR_eq_sum_secondDiff] at hlap
  have hterm : ∀ i, 0 ≤ secondDiff i f z := fun i => by
    simp only [secondDiff]; linarith [hplus i, hminus i]
  have h0 : secondDiff i₀ f z ≤ 0 :=
    (Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ i₀)).trans hlap
  have heq : f (z + unit i₀) = f z := by
    simp only [secondDiff] at h0; linarith [hplus i₀, hminus i₀]
  by_cases hB : z + unit i₀ ∈ B
  · have hM : z + unit i₀ ∈ M := Finset.mem_filter.2 ⟨hB, heq.trans hfz⟩
    have h := hzmax _ hM
    simp [unit] at h
  · have hyb : z + unit i₀ ∈ bdry (B : Set (Site d)) :=
      mem_bdry.2 ⟨by exact_mod_cast hB, z, by exact_mod_cast hzB, ⟨i₀, Or.inr rfl⟩⟩
    linarith [hcon _ hyb]

namespace OdometerLowerBound

/-- `Δ_{ℤ^d} q_l = l` on the lattice (`lapQuadratic` with `M = 0`). -/
theorem lapR_qlZ (hd : 1 ≤ d) (l : ℝ) (x : Site d) : lapR (qlZ l) x = l := by
  have h := lapQuadratic d hd l 0 x
  have hq : (fun y => qlZ l y + qMZ (0 : Matrix (Fin d) (Fin d) ℝ) y) = qlZ l :=
    funext fun y => by simp [qMZ, qM]
  rw [hq] at h
  simpa using h

theorem qlZ_eq (l : ℝ) (x : Site d) : qlZ l x = l * ‖toE x‖ ^ 2 / (2 * d) := rfl

end OdometerLowerBound

open OdometerLowerBound

/-- **Comparison of the odometer with `r_n`**. -/
theorem stabilizingGreenComparison : StabilizingGreenComparisonStmt := by
  intro d hd n η w hw hw0 x hx
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set B := ballZ0 (d := d) (n : ℝ)
  set f : Site d → ℝ := fun y =>
    ((w y : ℝ) - greenPotentialBall n η y) - qlZ (2 * d - 1) y with hf_def
  have hsuper : ∀ z ∈ B, lapR f z ≤ 0 := by
    intro z hz
    rw [hf_def, lapR_sub', lapR_sub', lapR_intCast, greenPotentialBall,
      lapR_greenPotential hd (ballZ0_finite _) _ hz, lapR_qlZ hd]
    have := hw.2 z hz
    have h' : (lap w z : ℝ) + (η z : ℝ) ≤ 2 * d - 1 := by exact_mod_cast this
    linarith
  obtain ⟨y, hy, hfy⟩ := superharmonicMinPrinciple d hd B (ballZ0_finite _) f hsuper x hx
  have hyB : y ∉ B := (mem_bdry.1 hy).1
  have hr : greenPotentialBall n η y = 0 := greenPotential_eq_zero_of_not_mem _ _ hyB
  have hfy' : f y = -((2 * d - 1) * ‖toE y‖ ^ 2 / (2 * d)) := by
    simp only [hf_def, hw0 y hy, hr, qlZ_eq, Int.cast_zero, sub_zero, zero_sub]
  have hyn : ‖toE y‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_lt_of_mem_bdry_ballZ0 hy).le 2
  have h2d : (0 : ℝ) ≤ 2 * d - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hq : (2 * d - 1) * ‖toE y‖ ^ 2 / (2 * d) ≤ (2 * d - 1) * ((n : ℝ) + 1) ^ 2 / (2 * d) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hyn h2d) (by positivity)
  have hfx : f x = ((w x : ℝ) - greenPotentialBall n η x) - (2 * d - 1) * ‖toE x‖ ^ 2 / (2 * d) :=
    rfl
  have e : (2 * d - 1) * (((n : ℝ) + 1) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) =
      (2 * d - 1) * ((n : ℝ) + 1) ^ 2 / (2 * d) - (2 * d - 1) * ‖toE x‖ ^ 2 / (2 * d) := by
    ring
  rw [e]
  linarith

/-- **Lower bound on `d_n`**. -/
theorem meanGreenPotentialLower : MeanGreenPotentialLowerStmt := by
  intro d hd n m hm x hx
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set B := ballZ0 (d := d) (n : ℝ)
  set f : Site d → ℝ := fun y => greenPotentialBallMean n m y - qlZ (-m) y with hf_def
  have hsuper : ∀ z ∈ B, lapR f z ≤ 0 := by
    intro z hz
    rw [hf_def, lapR_sub', greenPotentialBallMean,
      lapR_greenPotential hd (ballZ0_finite _) _ hz, lapR_qlZ hd]
    linarith
  obtain ⟨y, hy, hfy⟩ := superharmonicMinPrinciple d hd B (ballZ0_finite _) f hsuper x hx
  have hyB : y ∉ B := (mem_bdry.1 hy).1
  have hr : greenPotentialBallMean n m y = 0 := greenPotential_eq_zero_of_not_mem _ _ hyB
  have hfy' : f y = m * ‖toE y‖ ^ 2 / (2 * d) := by
    simp only [hf_def, hr, qlZ_eq]
    ring
  have hyn : (n : ℝ) ^ 2 ≤ ‖toE y‖ ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) (le_norm_of_mem_bdry_ballZ0 hy) 2
  have hq : m * (n : ℝ) ^ 2 / (2 * d) ≤ m * ‖toE y‖ ^ 2 / (2 * d) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hyn hm) (by positivity)
  have hfx : f x = greenPotentialBallMean n m x + m * ‖toE x‖ ^ 2 / (2 * d) := by
    simp only [hf_def, qlZ_eq]; ring
  have e : m * ((n : ℝ) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) =
      m * (n : ℝ) ^ 2 / (2 * d) - m * ‖toE x‖ ^ 2 / (2 * d) := by ring
  rw [e]
  linarith

/-- **Lemma 7.4** (`lowerbound`) from Lemma 7.3 (`divisible_homogenize`). -/
theorem odometerLowerBound_of_divisibleHomogenize (h73 : DivisibleHomogenizeStmt) :
    OdometerLowerBoundStmt :=
  odometerLowerBound_of_steps h73 existsLegalStabilizing stabilizingGreenComparison
    meanGreenPotentialLower

end RandomSandpile

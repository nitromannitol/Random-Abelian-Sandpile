import RandomSandpile.Steps.Sec7.DivisibleHomogenize
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodicAll

/-!
# Lemma 7.3: `CubeErgodicStmt` from the rectangle ergodic theorem

`paper/random_piles-corrected.tex`). The step `CubeErgodicStmt` of
`Steps/Sec7/DivisibleHomogenize.lean` is the specialisation of Lattice-Probability's rectangle
a.e. ergodic theorem `LatticeProb.RectangleErgodicAll` to the shift action of a
`RandomEnvironment` on `Config d` and the bounded observable
`h(η) = clamp_{[η_min, η_max]}(η(0)) - E η(0)`, applied to the dyadic rectangle with corners
`2^{-j} k` and `2^{-j} (k + 1)`. Since `η_min ≤ η(x) ≤ η_max` for all `x` almost surely, the
clamp is invisible along the orbit, and `∫ h = 0`; a countable intersection over `(j, k)` gives a
single almost sure event.

* `cubeErgodic_of_rectangleErgodicAll`: `CubeErgodicStmt` from `RectangleErgodicAll d` for all `d`.
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- The bounded observable `η ↦ clamp_{[η_min, η_max]}(η(0)) - E η(0)`. -/
private def clampObs (E : RandomEnvironment d) (η : Config d) : ℝ :=
  max (E.ηmin : ℝ) (min ((η 0 : ℤ) : ℝ) E.ηmax) - meanEta E.P

private theorem measurable_clampObs (E : RandomEnvironment d) : Measurable (clampObs E) := by
  have h0 : Measurable (fun η : Config d => ((η 0 : ℤ) : ℝ)) :=
    Measurable.of_discrete.comp (measurable_pi_apply 0)
  unfold clampObs
  exact (measurable_const.max (h0.min measurable_const)).sub measurable_const

private theorem clampObs_bound (E : RandomEnvironment d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η, |clampObs E η| ≤ M := by
  refine ⟨|(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| + |meanEta E.P|, by positivity, fun η => ?_⟩
  unfold clampObs
  have h1 : (E.ηmin : ℝ) ≤ max (E.ηmin : ℝ) (min ((η 0 : ℤ) : ℝ) E.ηmax) := le_max_left _ _
  have h2 : max (E.ηmin : ℝ) (min ((η 0 : ℤ) : ℝ) E.ηmax) ≤ |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| :=
    max_le (le_add_of_le_of_nonneg (le_abs_self _) (abs_nonneg _))
      (le_add_of_nonneg_of_le (abs_nonneg _) ((min_le_right _ _).trans (le_abs_self _)))
  have h3 := neg_abs_le (E.ηmin : ℝ)
  have h4 := abs_nonneg (E.ηmax : ℝ)
  have h5 := neg_abs_le (meanEta E.P)
  have h6 := le_abs_self (meanEta E.P)
  rw [abs_le]
  constructor <;> linarith

/-- On the event `η_min ≤ η(x) ≤ η_max` the clamp does nothing. -/
private theorem clampObs_shift (E : RandomEnvironment d) (η : Config d) (x : Site d)
    (hx : E.ηmin ≤ η x ∧ E.ηmax ≥ η x) : clampObs E (shift x η) = (η x : ℝ) - meanEta E.P := by
  unfold clampObs
  have h1 : (E.ηmin : ℝ) ≤ (η x : ℝ) := by exact_mod_cast hx.1
  have h2 : (η x : ℝ) ≤ (E.ηmax : ℝ) := by exact_mod_cast hx.2
  rw [shift_apply, add_zero, min_eq_left h2, max_eq_right h1]

private theorem integral_clampObs (E : RandomEnvironment d) : ∫ η, clampObs E η ∂E.P = 0 := by
  have hae : clampObs E =ᵐ[E.P] fun η => ((η 0 : ℤ) : ℝ) - meanEta E.P := by
    filter_upwards [E.bounded 0] with η hη
    have := clampObs_shift E η 0 hη
    simpa [shift_zero] using this
  have h0 : Measurable (fun η : Config d => ((η 0 : ℤ) : ℝ)) :=
    Measurable.of_discrete.comp (measurable_pi_apply 0)
  have hint : Integrable (fun η : Config d => ((η 0 : ℤ) : ℝ)) E.P := by
    refine Integrable.of_bound h0.aestronglyMeasurable (|(E.ηmin : ℝ)| + |(E.ηmax : ℝ)|) ?_
    filter_upwards [E.bounded 0] with η hη
    have h1 : (E.ηmin : ℝ) ≤ (η 0 : ℝ) := by exact_mod_cast hη.1
    have h2 : (η 0 : ℝ) ≤ (E.ηmax : ℝ) := by exact_mod_cast hη.2
    rw [Real.norm_eq_abs, abs_le]
    have h3 := neg_abs_le (E.ηmin : ℝ)
    have h4 := le_abs_self (E.ηmax : ℝ)
    have h5 := abs_nonneg (E.ηmin : ℝ)
    have h6 := abs_nonneg (E.ηmax : ℝ)
    constructor <;> linarith
  rw [integral_congr_ae hae, integral_sub hint (integrable_const _), integral_const]
  simp [meanEta]

/-- **(ergodic)**): `CubeErgodicStmt` follows from the rectangle
a.e. ergodic theorem `LatticeProb.RectangleErgodicAll`, applied to the shift action on `Config d`,
the bounded observable `clamp(η(0)) - E η(0)`, and the dyadic rectangles
`∏_i [2^{-j} k_i, 2^{-j} (k_i + 1))`. -/
theorem cubeErgodic_of_rectangleErgodicAll (h : ∀ d : ℕ, RectangleErgodicAll d) :
    CubeErgodicStmt := by
  intro d _ E
  have hrect : ∀ (j : ℕ) (k : Site d), ∀ᵐ η ∂E.P,
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
        ∑ x ∈ dyadicCube j k N, clampObs E (shift x η)) atTop (𝓝 0) := by
    intro j k
    have hab : ∀ i : Fin d, (k i : ℝ) / 2 ^ j ≤ ((k i : ℝ) + 1) / 2 ^ j := fun i =>
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have := h d E.P shift E.stationary (fun z w ω => shift_add z w ω) E.ergodic (clampObs E)
      (measurable_clampObs E) (clampObs_bound E)
      (fun i => (k i : ℝ) / 2 ^ j) (fun i => ((k i : ℝ) + 1) / 2 ^ j) hab
    filter_upwards [this] with η hη
    rw [integral_clampObs, mul_zero] at hη
    exact hη
  have hall : ∀ᵐ η ∂E.P, ∀ (j : ℕ) (k : Site d),
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
        ∑ x ∈ dyadicCube j k N, clampObs E (shift x η)) atTop (𝓝 0) :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun k => hrect j k
  filter_upwards [hall, ae_all_iff.2 E.bounded] with η hη hbd j k
  refine (hη j k).congr fun N => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_mul_eq_div]
  congr 1
  exact Finset.sum_congr rfl fun x _ => clampObs_shift E η x (hbd x)

end RandomSandpile

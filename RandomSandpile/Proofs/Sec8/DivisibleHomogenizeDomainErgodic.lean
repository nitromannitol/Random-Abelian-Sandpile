import RandomSandpile.Steps.Sec8.DivisibleHomogenizeDomain
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeReflect
import RandomSandpile.Infra.SubadditiveCubes

/-!
# Lemma 8.1: `CubeErgodicRealStmt` for real random environments

`paper/random_piles-corrected.tex`, 1131-1140. The proof is that of
`RandomSandpile.cubeErgodic_of_rectangleErgodic` (`Proofs/Sec7/DivisibleHomogenizeReflect.lean`),
transcribed from the integer environment `RandomEnvironment d` to the real environment
`RealRandomEnvironment d`: the bounded observable is `η ↦ clamp_{[η_min, η_max]}(η(0)) - E η(0)`
on `RealConfig d = ℤ^d → ℝ`, the action is the real shift `shiftReal`, reflected in the coordinates
`{i | k_i < 0}` by `LatticeProb.reflectActionS_props`, and the reflected dyadic rectangle is handled
by the generic box lemmas of `RandomSandpile.DivisibleHomogenize` (`floorBox`, `sum_rectBox_refl`,
`dyadic_vs_floor`, `tendsto_div_of_close`, `reflLo`, `reflHi`).

* `realClampObs`: the bounded real observable, with measurability, bound, shift and mean-zero lemmas.
* `cubeErgodicReal`: `CubeErgodicRealStmt`, from `RandomSandpile.rectangleErgodic`.
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology

namespace RandomSandpile

namespace DivisibleHomogenize

variable {d : ℕ}

/-! ### The bounded real observable -/

/-- The bounded observable `η ↦ clamp_{[η_min, η_max]}(η(0)) - E η(0)` on real configurations. -/
def realClampObs (E : RealRandomEnvironment d) (η : RealConfig d) : ℝ :=
  max E.ηmin (min (η 0) E.ηmax) - meanEtaReal E.P

theorem measurable_realClampObs (E : RealRandomEnvironment d) : Measurable (realClampObs E) := by
  have h0 : Measurable (fun η : RealConfig d => η 0) := measurable_pi_apply 0
  unfold realClampObs
  exact (measurable_const.max (h0.min measurable_const)).sub measurable_const

theorem realClampObs_bound (E : RealRandomEnvironment d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η, |realClampObs E η| ≤ M := by
  refine ⟨|E.ηmin| + |E.ηmax| + |meanEtaReal E.P|, by positivity, fun η => ?_⟩
  unfold realClampObs
  have h1 : E.ηmin ≤ max E.ηmin (min (η 0) E.ηmax) := le_max_left _ _
  have h2 : max E.ηmin (min (η 0) E.ηmax) ≤ |E.ηmin| + |E.ηmax| :=
    max_le (le_add_of_le_of_nonneg (le_abs_self _) (abs_nonneg _))
      (le_add_of_nonneg_of_le (abs_nonneg _) ((min_le_right _ _).trans (le_abs_self _)))
  have h3 := neg_abs_le E.ηmin
  have h4 := abs_nonneg E.ηmax
  have h5 := neg_abs_le (meanEtaReal E.P)
  have h6 := le_abs_self (meanEtaReal E.P)
  rw [abs_le]
  constructor <;> linarith

/-- On the event `η_min ≤ η(x) ≤ η_max` the clamp does nothing. -/
theorem realClampObs_shift (E : RealRandomEnvironment d) (η : RealConfig d) (x : Site d)
    (hx : E.ηmin ≤ η x ∧ η x ≤ E.ηmax) :
    realClampObs E (shiftReal x η) = η x - meanEtaReal E.P := by
  unfold realClampObs
  rw [shiftReal_apply, add_zero, min_eq_left hx.2, max_eq_right hx.1]

theorem integral_realClampObs (E : RealRandomEnvironment d) :
    ∫ η, realClampObs E η ∂E.P = 0 := by
  have hae : realClampObs E =ᵐ[E.P] fun η => η 0 - meanEtaReal E.P := by
    filter_upwards [E.bounded 0] with η hη
    have := realClampObs_shift E η 0 hη
    simpa [shiftReal_zero] using this
  have h0 : Measurable (fun η : RealConfig d => η 0) := measurable_pi_apply 0
  have hint : Integrable (fun η : RealConfig d => η 0) E.P := by
    refine Integrable.of_bound h0.aestronglyMeasurable (|E.ηmin| + |E.ηmax|) ?_
    filter_upwards [E.bounded 0] with η hη
    rw [Real.norm_eq_abs, abs_le]
    have h3 := neg_abs_le E.ηmin
    have h4 := le_abs_self E.ηmax
    have h5 := abs_nonneg E.ηmin
    have h6 := abs_nonneg E.ηmax
    constructor <;> linarith [hη.1, hη.2]
  rw [integral_congr_ae hae, integral_sub hint (integrable_const _), integral_const]
  simp [meanEtaReal]

end DivisibleHomogenize

open DivisibleHomogenize

/-- **(ergodic)** for real environments (1131-1140): `CubeErgodicRealStmt`, proved
from the rectangle a.e. ergodic theorem `RandomSandpile.rectangleErgodic` for `0 ≤ a ≤ b`, applied to
the real shift action reflected in the coordinates `{i | k_i < 0}`, the bounded observable
`clamp(η(0)) - E η(0)`, and the reflected dyadic rectangle; the reflected box differs from the
dyadic cube only in two hyperplane layers per coordinate. -/
theorem cubeErgodicReal : CubeErgodicRealStmt := by
  intro d hd E
  have hrect : ∀ (j : ℕ) (k : Site d), ∀ᵐ η ∂E.P,
      Tendsto (fun N : ℕ => (∑ x ∈ floorBox j k (Finset.univ.filter fun i => k i < 0) N,
        realClampObs E (shiftReal x η)) / (N : ℝ) ^ d) atTop (𝓝 0) := by
    intro j k
    obtain ⟨h1, h2, h3⟩ := reflectActionS_props (τ := shiftReal) E.stationary
      (fun z w ω => shiftReal_add z w ω) E.ergodic (Finset.univ.filter fun i => k i < 0)
    have := rectangleErgodic (by omega : 1 ≤ d) E.P
      (reflectActionS shiftReal (Finset.univ.filter fun i => k i < 0)) h1 h2 h3
      (realClampObs E) (measurable_realClampObs E) (realClampObs_bound E)
      (reflLo j k (Finset.univ.filter fun i => k i < 0))
      (reflHi j k (Finset.univ.filter fun i => k i < 0)) (reflLo_nonneg j k)
      (reflLo_le_reflHi j k _)
    filter_upwards [this] with η hη
    rw [integral_realClampObs, mul_zero] at hη
    refine hη.congr fun N => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_mul_eq_div]
    congr 1
    exact sum_rectBox_refl j k _ N (fun y => realClampObs E (shiftReal y η))
  have hall : ∀ᵐ η ∂E.P, ∀ (j : ℕ) (k : Site d),
      Tendsto (fun N : ℕ => (∑ x ∈ floorBox j k (Finset.univ.filter fun i => k i < 0) N,
        realClampObs E (shiftReal x η)) / (N : ℝ) ^ d) atTop (𝓝 0) :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun k => hrect j k
  obtain ⟨M, hM0, hM⟩ := realClampObs_bound E
  filter_upwards [hall, ae_all_iff.2 E.bounded] with η hη hbd j k
  have hsum : ∀ N : ℕ, ∑ y ∈ dyadicCube j k N, (η y - meanEtaReal E.P) =
      ∑ y ∈ dyadicCube j k N, realClampObs E (shiftReal y η) := fun N =>
    Finset.sum_congr rfl fun x _ => (realClampObs_shift E η x (hbd x)).symm
  have hclose := tendsto_div_of_close (by omega : 1 ≤ d)
    (fun N => ∑ y ∈ dyadicCube j k N, realClampObs E (shiftReal y η))
    (fun N => ∑ x ∈ floorBox j k (Finset.univ.filter fun i => k i < 0) N,
      realClampObs E (shiftReal x η))
    (M * (4 * d)) (by positivity) (hη j k) (fun N => by
      have := dyadic_vs_floor j k (Finset.univ.filter fun i => k i < 0) N
        (fun y => realClampObs E (shiftReal y η)) M (fun y => hM _)
      calc _ ≤ _ := this
        _ = _ := by ring)
  refine hclose.congr fun N => ?_
  rw [hsum]

end RandomSandpile

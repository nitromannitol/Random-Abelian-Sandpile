import RandomSandpile.Proofs.Sec9.SingleSourceThresholdZero
import RandomSandpile.Proofs.Sec5.MuBounded

/-!
# `H(0) = 0` for the high stable backgrounds `d ≤ η ≤ 2d - 2`

if `η ≥ d`, a stabilizing integer toppling function has
`Δ v ≤ 2d - 1 - η ≤ d - 1` at every site of `A`, so its coordinate second differences cannot all be
`≥ 1`; but the subgradient cell of `v - q_l` (`l ≥ 0`) at that site lies in a box with sides
`Δ_i v - l/d`, which has positive volume only if every integer `Δ_i v` is `≥ 1`. Hence every
subgradient cell is Lebesgue-null.

* `muStar_eq_zero_of_ge`: `μ*(A, η, l, 0) = 0` for finite `A`, `η ≥ d` on `A`, `l ≥ 0`.
* `stabThresholdZero_of_ge`: `d ≤ η_min` implies `StabThresholdZero E` (`H_η(0) = 0`).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal

namespace RandomSandpile

open EffectiveOperatorBasic

variable {d : ℕ}

/-- A set inside a box with a non-positive side is Lebesgue-null. -/
theorem volume_eq_zero_of_subset_box (S : Set (Rd d)) (a b : Fin d → ℝ)
    (hS : ∀ p ∈ S, ∀ i, a i ≤ p i ∧ p i ≤ b i) (i₀ : Fin d) (h0 : b i₀ - a i₀ ≤ 0) :
    volume S = 0 := by
  have hsub : S ⊆ WithLp.ofLp ⁻¹' Set.Icc a b := fun q hq =>
    ⟨fun i => (hS q hq i).1, fun i => (hS q hq i).2⟩
  refine measure_mono_null hsub ?_
  rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i₀) (ENNReal.ofReal_eq_zero.2 h0)

theorem subGrad_null (hd : 1 ≤ d) {A : Set (Site d)} {x : Site d} (hx : x ∈ A)
    {v : Site d → ℤ} {η : Site d → ℤ} (hv : lap v x + η x ≤ 2 * (d : ℤ) - 1)
    (hη : (d : ℤ) ≤ η x) {l : ℝ} (hl : 0 ≤ l) :
    volume (subGrad (fun y => (v y : ℝ) - (qlZ l y + qMZ 0 y)) x A) = 0 := by
  set w : Site d → ℝ := fun y => (v y : ℝ) - (qlZ l y + qMZ 0 y) with hw
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd : ∀ i, secondDiff i w x = (v (x + unit i) + v (x - unit i) - 2 * v x : ℤ) - l / d := by
    intro i
    have h1 : secondDiff i w x = secondDiff i (fun y => (v y : ℝ)) x -
        secondDiff i (fun y => qlZ l y + qMZ 0 y) x := by
      simp only [secondDiff, hw]; ring
    have h2 : secondDiff i (fun y => qlZ l y + qMZ 0 y) x = l / d := by
      have e : secondDiff i (fun y => qlZ l y + qMZ 0 y) x =
          secondDiff i (qlZ l) x + secondDiff i (qMZ 0) x := by simp only [secondDiff]; ring
      rw [e, secondDiff_qlZ hd, secondDiff_qMZ]; simp
    rw [h1, h2]; simp only [secondDiff]; push_cast; ring
  by_cases hall : ∀ i, 0 < secondDiff i w x
  · exfalso
    have hk : ∀ i, (1 : ℤ) ≤ v (x + unit i) + v (x - unit i) - 2 * v x := by
      intro i
      have := hall i
      rw [hsd i] at this
      have h3 : (0 : ℝ) < ((v (x + unit i) + v (x - unit i) - 2 * v x : ℤ) : ℝ) := by
        have : 0 ≤ l / d := by positivity
        linarith
      have h4 : (0 : ℤ) < v (x + unit i) + v (x - unit i) - 2 * v x := by exact_mod_cast h3
      omega
    have hlap : lap v x = ∑ i, (v (x + unit i) + v (x - unit i) - 2 * v x) := by
      have h := lapR_eq_sum_secondDiff (fun y => (v y : ℝ)) x
      rw [lapR_intCast] at h
      have : ((lap v x : ℤ) : ℝ) = ((∑ i, (v (x + unit i) + v (x - unit i) - 2 * v x) : ℤ) : ℝ) := by
        rw [h]; push_cast; simp only [secondDiff]
      exact_mod_cast this
    have hsum : (d : ℤ) ≤ ∑ i, (v (x + unit i) + v (x - unit i) - 2 * v x) := by
      calc (d : ℤ) = ∑ _i : Fin d, (1 : ℤ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => hk i
    omega
  · obtain ⟨i₀, hi₀⟩ : ∃ i, ¬ 0 < secondDiff i w x := by
      by_contra hc
      exact hall fun i => by_contra fun h => hc ⟨i, h⟩
    rw [not_lt] at hi₀
    refine volume_eq_zero_of_subset_box _ (fun i => w x - w (x - unit i))
      (fun i => w (x + unit i) - w x) (fun p hp i => ?_) i₀ ?_
    · have h1 := hp _ (add_unit_mem_dClosure hx i)
      have h2 := hp _ (sub_unit_mem_dClosure hx i)
      rw [inner_toE_add_unit] at h1
      rw [inner_toE_sub_unit] at h2
      constructor <;> linarith
    · simp only [secondDiff] at hi₀
      linarith

theorem muStar_eq_zero_of_ge (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) {η : Site d → ℤ}
    (hη : ∀ x ∈ A, (d : ℤ) ≤ η x) {l : ℝ} (hl : 0 ≤ l) : muStar A η l 0 = 0 := by
  unfold muStar
  simp only [ENNReal.iSup_eq_zero]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := mem_perturbedSuper.1 hw
  unfold subGradSet
  rw [measure_biUnion_null_iff hA.countable]
  intro x hx
  exact subGrad_null hd hx (hv.2 x hx) (hη x hx) hl

/-- `d ≤ η_min` implies `H_η(0) = 0`: `μ*(l, 0) = 0` for all `l ≥ 0`. -/
theorem stabThresholdZero_of_ge (hd : 1 ≤ d) (E : RandomEnvironment d) (hE : (d : ℤ) ≤ E.ηmin) :
    StabThresholdZero E := by
  intro l hl
  unfold muStarBar
  have h0 : (∫⁻ η, limsup (fun n : ℕ => muStar (ballZ0 (n : ℝ)) η l 0 /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P) = 0 := by
    refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
    filter_upwards [ae_all_iff.2 E.bounded] with η hη
    have : ∀ n : ℕ, muStar (ballZ0 (n : ℝ)) η l 0 = 0 := fun n =>
      muStar_eq_zero_of_ge hd (MuLipschitz.ballZ0_finite _) (fun x _ => hE.trans (hη x).1) hl.le
    simp [this]
  rw [h0]; simp

end RandomSandpile

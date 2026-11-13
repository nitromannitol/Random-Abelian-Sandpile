import RandomSandpile.Proofs.Sec9.LiftEnv

/-!
# Operator fact (11): the shift identity for `μ*`

`muStar_lift`: for finite `B`, `k : ℕ` and `K = 2dk`,
`μ*(B, η + K, l, M - 2kI) = μ*(B, η, l, M)` ((1)). A stabilizing `v`
for `η` gives the stabilizing `v - k|z|² + C` for `η + K` (only the values on `B̄` matter), whose
perturbation `v' - q_l - q_{M-2kI}` is that of `v` plus a constant on `B̄`, so the subgradient sets
coincide; the converse is `v' ↦ v' + k|z|²`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal

namespace RandomSandpile

open EffectiveOperatorBasic MuLipschitz

namespace SingleSourceH0

variable {d : ℕ}

/-- `|z|²` as an integer. -/
def sqSum (z : Site d) : ℤ := ∑ i, z i ^ 2

theorem sqSum_nonneg (z : Site d) : 0 ≤ sqSum z := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqSum_add_unit (x : Site d) (i : Fin d) : sqSum (x + unit i) = sqSum x + 2 * x i + 1 := by
  unfold sqSum
  have : ∀ j, (x + unit i) j ^ 2 = x j ^ 2 + (2 * x j + 1) * (if j = i then 1 else 0) := by
    intro j
    by_cases h : j = i
    · subst h; simp [unit]; ring
    · simp [unit, h]
  simp only [this, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (f := fun j => (2 * x j + 1) * (if j = i then (1 : ℤ) else 0)) i
    (fun j _ hj => by rw [ite_eq_right hj, mul_zero]) (by simp)]
  simp [mul_one]
  ring

theorem sqSum_sub_unit (x : Site d) (i : Fin d) : sqSum (x - unit i) = sqSum x - 2 * x i + 1 := by
  unfold sqSum
  have : ∀ j, (x - unit i) j ^ 2 = x j ^ 2 + (-2 * x j + 1) * (if j = i then 1 else 0) := by
    intro j
    by_cases h : j = i
    · subst h; simp [unit]; ring
    · simp [unit, h]
  simp only [this, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (f := fun j => (-2 * x j + 1) * (if j = i then (1 : ℤ) else 0)) i
    (fun j _ hj => by rw [ite_eq_right hj, mul_zero]) (by simp)]
  simp [mul_one]
  ring

theorem lap_add_sqSum (f : Site d → ℤ) (a c : ℤ) (x : Site d) :
    lap (fun z => f z + a * sqSum z + c) x = lap f x + 2 * d * a := by
  rw [lap_eq_sum_second_diff, lap_eq_sum_second_diff]
  have : ∀ i : Fin d, (-2 * (f x + a * sqSum x + c) + (f (x + unit i) + a * sqSum (x + unit i) + c) +
      (f (x - unit i) + a * sqSum (x - unit i) + c)) =
      (-2 * f x + f (x + unit i) + f (x - unit i)) + 2 * a := fun i => by
    rw [sqSum_add_unit, sqSum_sub_unit]; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem subGradSet_congr {B : Set (Site d)} {w₁ w₂ : Site d → ℝ} {c : ℝ}
    (h : ∀ y ∈ dClosure B, w₁ y = w₂ y + c) : subGradSet w₁ B = subGradSet w₂ B := by
  unfold subGradSet
  refine Set.iUnion₂_congr fun x hx => ?_
  ext p
  simp only [subGrad, Set.mem_ofPred_eq]
  have hx' := h x (mem_dClosure_of_mem hx)
  constructor
  · intro hp y hy
    have := hp y hy; rw [h y hy, hx'] at this; linarith
  · intro hp y hy
    have := hp y hy; rw [h y hy, hx']; linarith

theorem qMZ_sub_two_smul (M : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (z : Site d) :
    qMZ (M - ((2 * k : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ)) z = qMZ M z - k * (sqSum z : ℝ) := by
  have h1 : M - ((2 * k : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ) =
      M + (-(2 * k : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by rw [neg_smul, sub_eq_add_neg]
  have h2 : ‖toE z‖ ^ 2 = (sqSum z : ℝ) := by
    rw [norm_toE_sq_eq_sum]; unfold sqSum; push_cast; rfl
  simp only [qMZ, h1, qM_add_smul_one, h2]
  ring

theorem muStar_lift (B : Set (Site d)) (hB : B.Finite) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) :
    muStar B (fun x => η x + 2 * (d : ℤ) * (k : ℤ)) l (M - ((2 * k : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      muStar B η l M := by
  classical
  have hfinD : (dClosure B).Finite := dClosure_finite hB
  apply le_antisymm
  · unfold muStar
    refine iSup₂_le fun w' hw' => ?_
    obtain ⟨v', hv', rfl⟩ := mem_perturbedSuper.1 hw'
    set v : Site d → ℤ := (dClosure B).indicator (fun z => v' z + (k : ℤ) * sqSum z) with hvdef
    have hv : v ∈ stabilizing η B := by
      refine ⟨⟨fun z => ?_, fun z hz => Set.indicator_of_notMem hz _⟩, fun x hx => ?_⟩
      · by_cases hz : z ∈ dClosure B
        · rw [hvdef, Set.indicator_of_mem hz]
          have := hv'.1.1 z
          have := sqSum_nonneg z
          positivity
        · rw [hvdef, Set.indicator_of_notMem hz]
      · rw [hvdef, lap_indicator_dClosure _ hx]
        have h1 := lap_add_sqSum v' (k : ℤ) 0 x
        have h2 := hv'.2 x hx
        simp only [add_zero] at h1
        rw [h1]
        linarith
    refine le_iSup₂_of_le _ (mem_perturbedSuper.2 ⟨v, hv, rfl⟩) ?_
    have hc := subGradSet_congr (B := B) (c := 0)
      (w₁ := fun x => (v' x : ℝ) - (qlZ l x + qMZ (M - ((2 * k : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ)) x))
      (w₂ := fun x => (v x : ℝ) - (qlZ l x + qMZ M x)) (fun y hy => by
        rw [hvdef, Set.indicator_of_mem hy, qMZ_sub_two_smul]
        push_cast
        ring)
    rw [hc]
  · unfold muStar
    refine iSup₂_le fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := mem_perturbedSuper.1 hw
    obtain ⟨Kc, hKc⟩ : ∃ Kc : ℤ, ∀ z ∈ dClosure B, (k : ℤ) * sqSum z ≤ Kc := by
      obtain ⟨Kc, hKc⟩ := (hfinD.image fun z => (k : ℤ) * sqSum z).bddAbove
      exact ⟨Kc, fun z hz => hKc ⟨z, hz, rfl⟩⟩
    set v' : Site d → ℤ := (dClosure B).indicator (fun z => v z + (-(k : ℤ)) * sqSum z + Kc) with hvdef
    have hv' : v' ∈ stabilizing (fun x => η x + 2 * (d : ℤ) * (k : ℤ)) B := by
      refine ⟨⟨fun z => ?_, fun z hz => Set.indicator_of_notMem hz _⟩, fun x hx => ?_⟩
      · by_cases hz : z ∈ dClosure B
        · rw [hvdef, Set.indicator_of_mem hz]
          have := hv.1.1 z
          have := hKc z hz
          linarith
        · rw [hvdef, Set.indicator_of_notMem hz]
      · rw [hvdef, lap_indicator_dClosure _ hx]
        have h1 := lap_add_sqSum v (-(k : ℤ)) Kc x
        have h2 := hv.2 x hx
        rw [h1]
        simp only
        linarith
    refine le_iSup₂_of_le _ (mem_perturbedSuper.2 ⟨v', hv', rfl⟩) ?_
    have hc := subGradSet_congr (B := B) (c := (Kc : ℝ))
      (w₁ := fun x => (v' x : ℝ) - (qlZ l x + qMZ (M - ((2 * k : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ)) x))
      (w₂ := fun x => (v x : ℝ) - (qlZ l x + qMZ M x)) (fun y hy => by
        rw [hvdef, Set.indicator_of_mem hy, qMZ_sub_two_smul]
        push_cast
        ring)
    rw [hc]

end SingleSourceH0

end RandomSandpile

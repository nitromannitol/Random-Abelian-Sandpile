import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatFinal

/-!
# Operator fact (11): correctors from `μ̄(0, M) = μ̄*(0, M) = 0`

`flatCorrector_of_zero`: if `μ̄(0, M) = μ̄*(0, M) = 0` for a stationary ergodic bounded law, then
almost surely for every `ε > 0` and all large `R` there are an integer function `h`, stabilizing in
`B_R`, and a constant `c` with `|h - q_M - c| ≤ ε R²` on `B̄_R`. Proof: a legal and stabilizing
`h` with boundary values `⌈q_M⌉ + C₀` (least action); the two ABP bounds (Lemma 5.2) and the
ergodic limits (Lemma 5.5), as in `center_bound_gen`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal

namespace RandomSandpile

open EffectiveOperatorBasic MuLipschitz

namespace SingleSourceH0

variable {d : ℕ}

theorem flatCorrector_of_zero (hd : 2 ≤ d) (E : RandomEnvironment d) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.IsSymm) (h1 : muBar E 0 M = 0) (h2 : muStarBar E 0 M = 0) :
    ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ (h : Site d → ℤ) (c : ℝ),
      (∀ x ∈ ballZ0 (R : ℝ), lap h x + η x ≤ 2 * (d : ℤ) - 1) ∧
      ∀ z ∈ dClosure (ballZ0 (R : ℝ)), |(h z : ℝ) - qMZ M z - c| ≤ ε * (R : ℝ) ^ 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨C, hC, hABP⟩ := abp d hd
  have hconv := (muConvergence_unconditional d hd).1
  have hW := StrictConcavityBall.isLipschitzDomain_ball (0 : Rd d) one_pos
  filter_upwards [hconv E M hM 0] with η hη ε hε
  obtain ⟨hfin, hT1, hT2⟩ := hη _ hW
  rw [h1] at hT1
  rw [h2] at hT2
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (6 * C) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨N, hN⟩ := ((hT1.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ d))).and
    ((hT2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ d))).and
      (eventually_ge_atTop (⌈2 / ε⌉₊ + 1)))).exists_forall_of_atTop
  refine ⟨N, fun R hR => ?_⟩
  obtain ⟨hr1, hr2, hRN⟩ := hN R hR
  have hR1 : 1 ≤ R := by omega
  have hRε : 2 / ε < R := by
    have h1' : 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2' : ((⌈2 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hRN
    push_cast at h2'
    linarith
  simp only [discretize_unitBall_eq' hR1] at hr1 hr2
  have hf1 := (hfin R).2
  have hf2 := (hfin R).1
  rw [discretize_unitBall_eq' hR1] at hf1 hf2
  have hcard : (0 : ℝ) < ((ballZ0 (d := d) (R : ℝ)).ncard : ℝ) := by
    exact_mod_cast ncard_ballZ0_pos hR1
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hcard9 : ((ballZ0 (d := d) (R : ℝ)).ncard : ℝ) ≤ (3 * (R : ℝ)) ^ d :=
    (ncard_ballZ0_le R).trans (pow_le_pow_left₀ (by positivity) (by linarith) d)
  have hs : ∀ t : ℝ, 0 ≤ t → t / ((ballZ0 (d := d) (R : ℝ)).ncard : ℝ) < δ ^ d →
      t ^ (1 / (d : ℝ)) ≤ 3 * δ * R := by
    intro t ht htb
    rw [div_lt_iff₀ hcard] at htb
    have h3 : t ≤ (3 * δ * R) ^ d := by
      calc t ≤ δ ^ d * ((ballZ0 (d := d) (R : ℝ)).ncard : ℝ) := htb.le
        _ ≤ δ ^ d * (3 * (R : ℝ)) ^ d := by gcongr
        _ = (3 * δ * R) ^ d := by rw [← mul_pow]; ring_nf
    calc t ^ (1 / (d : ℝ)) ≤ ((3 * δ * R) ^ d) ^ (1 / (d : ℝ)) :=
          Real.rpow_le_rpow ht h3 (by positivity)
      _ = 3 * δ * R := by
          rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  have hs1 := hs _ ENNReal.toReal_nonneg hr1
  have hs2 := hs _ ENNReal.toReal_nonneg hr2
  -- the legal stabilizing function with ceiling boundary data
  set B := ballZ0 (d := d) (R : ℝ) with hB
  have hfinB : B.Finite := ballZ0_finite _
  have hfinD : (dClosure B).Finite := dClosure_finite hfinB
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℤ, ∀ y ∈ dClosure B, -⌈qMZ M y⌉ ≤ C₀ := by
    obtain ⟨C₀, hC₀⟩ := (hfinD.image fun y => -⌈qMZ M y⌉).bddAbove
    exact ⟨C₀, fun y hy => hC₀ ⟨y, hy, rfl⟩⟩
  obtain ⟨u, hudef⟩ : ∃ u : Site d → ℤ,
      u = (dClosure B).indicator fun y => ⌈qMZ M y⌉ + C₀ := ⟨_, rfl⟩
  have hu : IsTopplingFn B u := by
    rw [hudef]
    refine ⟨fun y => ?_, fun y hy => Set.indicator_of_notMem hy _⟩
    by_cases hy : y ∈ dClosure B
    · rw [Set.indicator_of_mem hy]; linarith [hC₀ y hy]
    · rw [Set.indicator_of_notMem hy]
  obtain ⟨h, ⟨hL, hS⟩, hbd⟩ :=
    NearMaxSequence.exists_locLegal_stabilizing (by omega) hfinB η hu
  have hbd' : ∀ y ∈ bdry B, (h y : ℝ) = ⌈qMZ M y⌉ + C₀ := by
    intro y hy
    rw [hbd y hy, hudef, Set.indicator_of_mem (bdry_subset_dClosure B hy)]
    push_cast; ring
  have hql : ∀ z : Site d, qlZ 0 z = 0 := fun z => by simp [qlZ, ql]
  have hne : (bdry B).Nonempty := Burning.bdry_nonempty (by omega) hfinB
    ⟨0, mem_ballZ0.2 (by rw [toE_zero, norm_zero]; exact_mod_cast hR1)⟩
  have hw₁ : (fun y => (h y : ℝ) - (qlZ 0 y + qMZ M y)) ∈ perturbedSuper B (η) 0 M :=
    Set.mem_image_of_mem _ hS
  have hw₂ : (fun y => (h y : ℝ) - (qlZ 0 y + qMZ M y)) ∈ perturbedSub B η 0 M :=
    mem_perturbedSub.2 ⟨h, hL, rfl⟩
  -- boundary values of w = h - q_M lie in [C₀, C₀ + 1)
  have hwb : ∀ y ∈ bdry B, (C₀ : ℝ) ≤ (h y : ℝ) - (qlZ 0 y + qMZ M y) ∧
      (h y : ℝ) - (qlZ 0 y + qMZ M y) ≤ C₀ + 1 := by
    intro y hy
    rw [hbd' y hy, hql]
    have a := Int.le_ceil (qMZ M y)
    have b := Int.ceil_lt_add_one (qMZ M y)
    constructor <;> linarith
  have hinf : (C₀ : ℝ) ≤ sInf ((fun y => (h y : ℝ) - (qlZ 0 y + qMZ M y)) '' bdry B) :=
    le_csInf (hne.image _) (by rintro _ ⟨y, hy, rfl⟩; exact (hwb y hy).1)
  have hsup : sSup ((fun y => (h y : ℝ) - (qlZ 0 y + qMZ M y)) '' bdry B) ≤ C₀ + 1 :=
    csSup_le (hne.image _) (by rintro _ ⟨y, hy, rfl⟩; exact (hwb y hy).2)
  have hCR : 0 ≤ C * R := by positivity
  have hbig : C * R * (3 * δ * R) = ε / 2 * (R : ℝ) ^ 2 := by
    rw [hδ]; field_simp; ring
  have hone : 1 ≤ ε / 2 * (R : ℝ) ^ 2 := by
    have : 2 < ε * R := by rwa [div_lt_iff₀ hε, mul_comm] at hRε
    nlinarith
  refine ⟨h, C₀, hS.2, fun z hz => ?_⟩
  rw [dClosure_eq] at hz
  rcases hz with hzB | hzb
  · have hA1 := (hABP R η 0 M hM).2 hf1 _ hw₁ z hzB
    have hA2 := (hABP R η 0 M hM).1 hf2 _ hw₂ z hzB
    have m1 := mul_le_mul_of_nonneg_left hs1 hCR
    have m2 := mul_le_mul_of_nonneg_left hs2 hCR
    simp only [hql, zero_add] at hA1 hA2 hinf hsup
    rw [abs_le]
    constructor <;> nlinarith
  · have := hwb z hzb
    simp only [hql, zero_add] at this
    rw [abs_le]
    constructor <;> nlinarith [mul_pos hε (by positivity : (0 : ℝ) < (R : ℝ) ^ 2)]

end SingleSourceH0

end RandomSandpile

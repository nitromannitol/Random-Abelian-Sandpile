import RandomSandpile.Proofs.Sec9.RecurrentOdometerExhaustion
import RandomSandpile.Steps.Sec9.RecurrentComparison

/-! # Recurrent odometers on compact subsets of the positivity set -/

open Filter LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- A compact set where a subsequential limit is uniformly positive has, away
from the source, eventually recurrent rounded lattice approximations. -/
theorem recurrent_on_rounded_compact_of_positive_limit {d : ℕ} (hd : 0 < d)
    {η : Site d → ℤ} (hfinite : SingleSourceFinite η) {u : Rd d → ℝ}
    {nk : ℕ → ℕ} (hconv : TendstoLocallyUniformlyOn
      (fun k => rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k)) u atTop
      {x : Rd d | x ≠ 0})
    {K : Set (Rd d)} (hK : IsCompact K) (hK0 : K ⊆ {x : Rd d | x ≠ 0})
    {ε : ℝ} (hε : 0 < ε) (hu : ∀ x ∈ K, ε ≤ u x) :
    ∀ᶠ k in atTop, IsRecurrentFunction η
      {z : Site d | z ≠ 0 ∧ ∃ x ∈ K,
        latticeRound ((nk k : ℝ) ^ (1 / (d : ℝ)) • x) = z}
      (singleSourceOdometer η (nk k)) := by
  have hunif := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
    (hconv.mono hK0)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif ε hε] with k hk
  apply singleSourceOdometer_recurrent_of_toppled hd (nk k) (hfinite (nk k))
  · exact fun z hz => hz.1
  · intro z hz
    obtain ⟨_, x, hx, hz⟩ := hz
    have hdist := hk x hx
    rw [Real.dist_eq] at hdist
    have hres : 0 < rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k) x := by
      have := (abs_lt.1 hdist).2
      linarith [hu x hx]
    have hmul : 0 < (nk k : ℝ) ^ (-(2 / (d : ℝ))) *
        (singleSourceOdometer η (nk k) z : ℝ) := by
      change 0 < (nk k : ℝ) ^ (-(2 / (d : ℝ))) *
        (singleSourceOdometer η (nk k)
          (latticeRound ((nk k : ℝ) ^ (1 / (d : ℝ)) • x)) : ℝ) at hres
      rw [hz] at hres
      exact hres
    have hnonneg : 0 ≤ (nk k : ℝ) ^ (-(2 / (d : ℝ))) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hpos : 0 < (singleSourceOdometer η (nk k) z : ℝ) := pos_of_mul_pos_right hmul hnonneg
    exact Int.add_one_le_iff.mpr (by exact_mod_cast hpos)

/-- On a compact subset of the positivity set, the single-source odometers are
eventually recurrent on the corresponding rescaled lattice sites. -/
theorem recurrent_on_scaled_compact_of_positive_limit {d : ℕ} (hd : 0 < d)
    {η : Site d → ℤ} (hfinite : SingleSourceFinite η) {u : Rd d → ℝ}
    {nk : ℕ → ℕ} (hnk : StrictMono nk) (hconv : TendstoLocallyUniformlyOn
      (fun k => rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k)) u atTop
      {x : Rd d | x ≠ 0})
    {K : Set (Rd d)} (hK : IsCompact K) (hK0 : K ⊆ {x : Rd d | x ≠ 0})
    (hcont : ContinuousOn u K) (hpos : ∀ x ∈ K, 0 < u x) :
    ∀ᶠ k in atTop, IsRecurrentFunction η
      {z : Site d | ((nk k : ℝ) ^ (1 / (d : ℝ)))⁻¹ • toE z ∈ K}
      (singleSourceOdometer η (nk k)) := by
  have hbound : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ u x := by
    by_cases hne : K.Nonempty
    · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hcont
      exact ⟨u x, hpos x hx, fun y hy => hmin hy⟩
    · exact ⟨1, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨ε, hε, hu⟩ := hbound
  filter_upwards [recurrent_on_rounded_compact_of_positive_limit hd hfinite hconv hK hK0 hε hu,
    hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk hn
  apply hk.mono
  intro z hz
  let s : ℝ := (nk k : ℝ) ^ (1 / (d : ℝ))
  have hs : 0 < s := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  refine ⟨?_, s⁻¹ • toE z, hz, ?_⟩
  · intro hz0
    subst z
    have hzE : toE (0 : Site d) = 0 := by ext i; simp [toE]
    change s⁻¹ • toE (0 : Site d) ∈ K at hz
    rw [hzE, smul_zero] at hz
    exact hK0 hz rfl
  · change latticeRound (s • (s⁻¹ • toE z)) = z
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, latticeRound_toE]

end RandomSandpile

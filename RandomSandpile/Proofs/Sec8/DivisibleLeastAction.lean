import RandomSandpile.Steps.Sec8.DivisibleLeastAction

/-!
# Proof of Proposition 8.1 (least action principle for the divisible sandpile)

Proofs of the three steps of `RandomSandpile/Steps/Sec8/DivisibleLeastAction.lean` and of
`RandomSandpile.DivisibleLeastActionStmt` (Proposition 8.1, `paper/random_piles-corrected.tex`; Proposition 2.5 in Levine-Peres [levine2016divisible]).

* `divOdometerUpToLeSupersolution` (Step 1): induction on the number of rounds `k`. At a site
  `x ∈ V` that is unstable at round `k`, `v_{k+1}(x) = (η(x) - 1 + ∑_{y ∼ x} v_k(y)) / (2d)`
  (conservation of mass, `divConfig_eq`), which is at most `f(x)` when `v_k ≤ f` and
  `Δ_{ℤ^d} f(x) + η(x) ≤ 1`.
* `existsDivSupersolution` (Step 2): the Green potential in `V` of `(η - 1)⁺` is nonnegative
  (`greenKilled_nonneg`) and solves `Δ_{ℤ^d} f = -(η - 1)⁺ ≤ 1 - η` in `V`
  (`lapR_greenPotential`).
* `divOdometerMemLeastActionSet` (Step 3): on `V`, `σ_k(x) - 1 ≤ 2d (v_{k+1}(x) - v_k(x))`, and
  passing to the limit gives `η(x) + Δ_{ℤ^d} v(x) - 1 ≤ 0`.
-/

noncomputable section

open LatticeProb Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- At a site `x ∈ V`, one round of parallel toppling increases the odometer by
`(σ_k(x) - 1)⁺ / (2d)`. -/
theorem divOdometerUpTo_succ_of_mem {V : Set (Site d)} (η : Site d → ℝ) (k : ℕ) {x : Site d}
    (hx : x ∈ V) :
    divOdometerUpTo V η (k + 1) x
      = divOdometerUpTo V η k x + max (divConfig V η k x - 1) 0 / (2 * d) := by
  rw [divOdometerUpTo_succ, divEmission, Set.indicator_of_mem hx]

/-- **Step 1 of Proposition 8.1**: the odometers of parallel toppling lie below every nonnegative
supersolution of `Δ_{ℤ^d} f + η ≤ 1` in `V`. -/
theorem divOdometerUpToLeSupersolution : DivOdometerUpToLeSupersolutionStmt := by
  intro d hd V η f hf k
  induction k with
  | zero =>
      intro x
      simpa [divOdometerUpTo] using hf.1 x
  | succ k ih =>
      intro x
      by_cases hxV : x ∈ V
      · rw [divOdometerUpTo_succ_of_mem η k hxV]
        rcases le_total (divConfig V η k x - 1) 0 with h | h
        · rw [max_eq_right h, zero_div, add_zero]
          exact ih x
        · rw [max_eq_left h, divConfig_eq]
          have hd' : (0 : ℝ) < 2 * d := by positivity
          have hf2 := hf.2 x hxV
          have hnb : nbrSum (divOdometerUpTo V η k) x ≤ nbrSum f x :=
            Finset.sum_le_sum fun i _ => add_le_add (ih _) (ih _)
          have hkey : (η x + lapR (divOdometerUpTo V η k) x - 1) / (2 * d)
              ≤ f x - divOdometerUpTo V η k x := by
            rw [div_le_iff₀ hd']
            have hexp : (f x - divOdometerUpTo V η k x) * (2 * d)
                = 2 * d * f x - 2 * d * divOdometerUpTo V η k x := by ring
            rw [hexp]
            simp only [lapR] at hf2 ⊢
            linarith
          linarith
      · rw [divOdometerUpTo_eq_zero_of_not_mem V η _ hxV]
        exact hf.1 x

/-- **Step 2 of Proposition 8.1**: for finite `V` the Green potential of `(η - 1)⁺` in `V` is a
nonnegative supersolution of `Δ_{ℤ^d} f + η ≤ 1` in `V`. -/
theorem existsDivSupersolution : ExistsDivSupersolutionStmt := by
  intro d hd V hV η
  refine ⟨greenPotential V fun x => max (η x - 1) 0, fun x => ?_, fun x hx => ?_⟩
  · obtain ⟨B, rfl⟩ := hV.exists_finset_coe
    rw [greenPotential_coe_finset]
    exact Finset.sum_nonneg fun y _ => mul_nonneg (greenKilled_nonneg _ _ _) (le_max_right _ _)
  · rw [lapR_greenPotential hd hV _ hx]
    linarith [le_max_left (η x - 1) 0]

/-- **Step 3 of Proposition 8.1**: if the divisible sandpile stabilizes in `V`, its odometer is a
nonnegative supersolution of `Δ_{ℤ^d} v + η ≤ 1` in `V`. -/
theorem divOdometerMemLeastActionSet : DivOdometerMemLeastActionSetStmt := by
  intro d hd V η h
  refine ⟨divOdometer_nonneg V η, fun x hx => ?_⟩
  have hd' : (0 : ℝ) < 2 * d := by positivity
  have hT : ∀ y, Tendsto (fun k => divOdometerUpTo V η k y) atTop (𝓝 (divOdometer V η y)) :=
    tendsto_divOdometerUpTo h
  have hlap : Tendsto (fun k => lapR (divOdometerUpTo V η k) x) atTop
      (𝓝 (lapR (divOdometer V η) x)) := by
    simp only [lapR, nbrSum]
    exact (tendsto_finsetSum _ fun i _ => (hT _).add (hT _)).sub ((hT x).const_mul _)
  have hinc : Tendsto (fun k => divOdometerUpTo V η (k + 1) x - divOdometerUpTo V η k x) atTop
      (𝓝 0) := by
    simpa using ((hT x).comp (tendsto_add_atTop_nat 1)).sub (hT x)
  have hle : ∀ k, η x + lapR (divOdometerUpTo V η k) x - 1
      ≤ 2 * d * (divOdometerUpTo V η (k + 1) x - divOdometerUpTo V η k x) := by
    intro k
    rw [divOdometerUpTo_succ_of_mem η k hx, add_sub_cancel_left, ← divConfig_eq,
      mul_div_cancel₀ _ hd'.ne']
    exact le_max_left _ _
  have hlim := le_of_tendsto_of_tendsto' (((hlap.const_add (η x)).sub_const 1))
    (hinc.const_mul (2 * (d : ℝ))) hle
  rw [mul_zero] at hlim
  linarith

/-- **Proposition 8.1** (prop:div_lap): for `d ≥ 2` and finite `V`,
the divisible sandpile `η` stabilizes in `V` and its odometer is the least nonnegative
supersolution of `Δ_{ℤ^d} f + η ≤ 1` in `V`. -/
theorem divisibleLeastAction : DivisibleLeastActionStmt :=
  divisibleLeastAction_of_steps divOdometerUpToLeSupersolution existsDivSupersolution
    divOdometerMemLeastActionSet

end RandomSandpile

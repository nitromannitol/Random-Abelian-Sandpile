import RandomSandpile.Draft.Section8

/-!
# Steps of Proposition 8.1 (least action principle for the divisible sandpile)

Carving of `RandomSandpile.DivisibleLeastActionStmt` (Proposition 8.1,
`paper/random_piles-corrected.tex`; Proposition 2.5 in Levine-Peres
[levine2016divisible]) into three steps, and the reduction `divisibleLeastAction_of_steps`.
The class `divLeastActionSet V η = {f ≥ 0 : Δ_{ℤ^d} f + η ≤ 1 in V}` is the class of nonnegative
supersolutions of the divisible-sandpile obstacle problem in `V`.

* `DivOdometerUpToLeSupersolutionStmt` (the least action principle along the dynamics): the
  odometers `v_k = divOdometerUpTo V η k` of parallel toppling lie below every `f` of the class.
  If `v_k ≤ f` and `x ∈ V` topples at round `k`, then
  `v_{k+1}(x) = (η(x) - 1 + ∑_{y ∼ x} v_k(y)) / (2d) ≤ (η(x) - 1 + ∑_{y ∼ x} f(y)) / (2d) ≤ f(x)`,
  the last inequality being `Δ_{ℤ^d} f(x) + η(x) ≤ 1`. No finiteness of `V` is needed.
* `ExistsDivSupersolutionStmt`: for finite `V` the class is nonempty; a member is the Green
  potential in `V` of `(η - 1)⁺`, which solves `Δ_{ℤ^d} f = -(η - 1)⁺` in `V`.
* `DivOdometerMemLeastActionSetStmt`: if the dynamics stabilizes, its limit `v = divOdometer V η`
  is in the class. The limit configuration `η + Δ_{ℤ^d} v` is the limit of `σ_k = η + Δ_{ℤ^d} v_k`
  (`divConfig_eq`), and on `V`, `σ_k - 1 ≤ (σ_k - 1)⁺ = 2d (v_{k+1} - v_k) → 0`, so the limit
  configuration is stable in `V`.

Assembly (`divisibleLeastAction_of_steps`): the first step applied to the supersolution of the
second step bounds the nondecreasing `k ↦ v_k(x)`, so the dynamics stabilizes; the third step puts
`v` in the class, and the first step, passing to the supremum over `k`, puts `v` below every member
of the class.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

/-- Step 1 of Proposition 8.1, the least action principle along parallel toppling (Levine-Peres):
for `d ≥ 1`, every odometer `v_k = divOdometerUpTo V η k` of the dynamics in `V` lies below every
nonnegative supersolution `f` of `Δ_{ℤ^d} f + η ≤ 1` in `V`. -/
def DivOdometerUpToLeSupersolutionStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (V : Set (Site d)) (η f : Site d → ℝ), f ∈ divLeastActionSet V η →
    ∀ (k : ℕ) (x : Site d), divOdometerUpTo V η k x ≤ f x

/-- Step 2 of Proposition 8.1: for `d ≥ 1` and finite `V`, the class of nonnegative supersolutions
of `Δ_{ℤ^d} f + η ≤ 1` in `V` is nonempty. -/
def ExistsDivSupersolutionStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (V : Set (Site d)), V.Finite → ∀ η : Site d → ℝ,
    (divLeastActionSet V η).Nonempty

/-- Step 3 of Proposition 8.1: for `d ≥ 1`, if the divisible sandpile `η` stabilizes in `V`, its
odometer `v = lim_k v_k` is a nonnegative supersolution of `Δ_{ℤ^d} v + η ≤ 1` in `V` (the final
configuration is stable in `V`). -/
def DivOdometerMemLeastActionSetStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (V : Set (Site d)) (η : Site d → ℝ), DivStabilizes V η →
    divOdometer V η ∈ divLeastActionSet V η

/-- **Reduction of Proposition 8.1** to its three steps. -/
theorem divisibleLeastAction_of_steps (h1 : DivOdometerUpToLeSupersolutionStmt)
    (h2 : ExistsDivSupersolutionStmt) (h3 : DivOdometerMemLeastActionSetStmt) :
    DivisibleLeastActionStmt := by
  intro d hd V hV η
  have hd0 : 0 < d := by omega
  obtain ⟨f, hf⟩ := h2 d hd0 V hV η
  have hstab : DivStabilizes V η := fun x =>
    ⟨f x, by rintro _ ⟨k, rfl⟩; exact h1 d hd0 V η f hf k x⟩
  refine ⟨hstab, h3 d hd0 V η hstab, fun g hg x => ?_⟩
  show (⨆ k : ℕ, divOdometerUpTo V η k x) ≤ g x
  exact ciSup_le fun k => h1 d hd0 V η g hg k x

end RandomSandpile

import RandomSandpile.Draft.Section8

/-!
# Steps of Theorem 8.2 (convergence of the random divisible sandpile)

Carving of `RandomSandpile.DivisibleTheoremStmt` (Theorem 8.2, `paper/random_piles-corrected.tex`) into three steps, and the reduction `divisibleTheorem_of_steps`, which takes the least
action principle `DivisibleLeastActionStmt` (Proposition 8.1) and the homogenization of the Green
potentials `DivisibleHomogenizeDomainStmt` (Lemma 8.1) as explicit hypotheses.

Notation. For a finite `V ⊆ ℤ^d` and `η, η' : ℤ^d → ℝ`, `r = greenPotential V η` and
`r' = greenPotential V η'` solve `Δ_{ℤ^d} r = -η`, `Δ_{ℤ^d} r' = -η'` in `V` and vanish off `V`
(`lapR_greenPotential`, `greenPotential_eq_zero_of_not_mem`); in the printed proof
`V = W_n`, `η' ≡ η_avg`, `r = r_n`, `r' = d_n`. The class
`divLeastActionSet V η = {f ≥ 0 : Δ_{ℤ^d} f + η ≤ 1 in V}` is the class of nonnegative
supersolutions of the divisible-sandpile obstacle problem.

* `DivCompetitorStmt`: since `Δ_{ℤ^d} (r - r') = η' - η` in `V`, a supersolution
  `f` for `η` gives the supersolution `f - (r - r') + δ` for `η'`, whenever `|r - r'| ≤ δ` in `V`:
  `Δ_{ℤ^d} (f - (r - r') + δ) + η' = Δ_{ℤ^d} f + η ≤ 1` in `V`, and `f - (r - r') + δ ≥ 0` (in `V`
  because `f ≥ 0` and `r - r' ≤ δ`; off `V` because `r = r' = 0` there and `δ ≥ 0`). This is the
  printed competitor `v_n - (r_n - d_n) + εCn²`.
* `DivOdometerComparisonStmt` ("the other direction is identical"): if the
  odometers `v`, `v'` of `η`, `η'` in `V` are the least elements of their classes and
  `|r - r'| ≤ δ` in `V`, then `|v - v'| ≤ 2δ` on `ℤ^d`. By `DivCompetitorStmt` and minimality,
  `v' ≤ v - (r - r') + δ` and `v ≤ v' + (r - r') + δ`, and `|r - r'| ≤ δ` everywhere
  (`r - r' = 0` off `V`). It is derived from `DivCompetitorStmt` in
  `divOdometerComparison_of_competitor`.
* `DivDomainFiniteStmt`: `W_n = ℤ^d ∩ nW` is finite for a (bounded) Lipschitz domain `W`, so
  that Proposition 8.1 and the Poisson equation for the Green potentials apply in `W_n`.

Assembly (`divisibleTheorem_of_steps`). Lemma 8.1 gives `C = C_d` and, on an event of full
probability, `n₀(ε')` with `|r_n - d_n| ≤ ε' C n² ≤ ε' |C| n²` on `W̄_n ⊇ W_n` for `n ≥ n₀`. With
`ε' = ε / (2(|C| + 1))`, the comparison step gives `|v_n - v_{avg_n}| ≤ 2ε'|C| n² ≤ ε n²`; at
`x = n⁻¹ z`, `z ∈ W̄_n`, `[nx] = z` (`latticeRound_smul_inv_smul_toE`), so
`|v̄_n(x) - v̄_{avg_n}(x)| ≤ ε`. The stabilization conjunct is the first half of Proposition 8.1 in
the finite set `W_n`. Printed proof: the constant `C` of Lemma 8.1 is used as if positive (the
statement does not say `C > 0`), which is why `|C|` appears; this changes nothing.
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology

namespace RandomSandpile

/-- Step 1 of Theorem 8.2, the competitor in the least action principle: for
`d ≥ 1` and finite `V`, if `f ≥ 0` is a supersolution of `Δ_{ℤ^d} f + η ≤ 1` in `V` and the Green
potentials `r`, `r'` of `η`, `η'` in `V` satisfy `|r - r'| ≤ δ` in `V` with `δ ≥ 0`, then
`f - (r - r') + δ` is a nonnegative supersolution of `Δ_{ℤ^d} g + η' ≤ 1` in `V`. -/
def DivCompetitorStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (V : Set (Site d)), V.Finite → ∀ (η η' f : Site d → ℝ) (δ : ℝ), 0 ≤ δ →
    (∀ x ∈ V, |greenPotential V η x - greenPotential V η' x| ≤ δ) →
    f ∈ divLeastActionSet V η →
    (fun x => f x - (greenPotential V η x - greenPotential V η' x) + δ) ∈ divLeastActionSet V η'

/-- Step 2 of Theorem 8.2, the comparison of odometers: for `d ≥ 1` and finite
`V`, if the odometers of `η` and `η'` in `V` are the least elements of their classes of
nonnegative supersolutions, and the Green potentials of `η`, `η'` in `V` differ by at most `δ ≥ 0`
in `V`, then the odometers differ by at most `2δ` on `ℤ^d`. -/
def DivOdometerComparisonStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (V : Set (Site d)), V.Finite → ∀ (η η' : Site d → ℝ) (δ : ℝ), 0 ≤ δ →
    IsLeast (divLeastActionSet V η) (divOdometer V η) →
    IsLeast (divLeastActionSet V η') (divOdometer V η') →
    (∀ x ∈ V, |greenPotential V η x - greenPotential V η' x| ≤ δ) →
    ∀ x, |divOdometer V η x - divOdometer V η' x| ≤ 2 * δ

/-- Step 3 of Theorem 8.2: for a Lipschitz domain `W ⊆ ℝ^d` (bounded by definition),
`W_n = ℤ^d ∩ nW` is finite. -/
def DivDomainFiniteStmt : Prop :=
  ∀ (d : ℕ) (W : Set (Rd d)), IsLipschitzDomain W → ∀ n : ℕ, (discretize W n).Finite

/-- Step 2 of Theorem 8.2 follows from Step 1 applied in both directions. -/
theorem divOdometerComparison_of_competitor (h1 : DivCompetitorStmt) :
    DivOdometerComparisonStmt := by
  intro d hd V hV η η' δ hδ hv hv' hg x
  set g : Site d → ℝ := fun z => greenPotential V η z - greenPotential V η' z
  have hgx : |g x| ≤ δ := by
    by_cases hx : x ∈ V
    · exact hg x hx
    · simpa [g, greenPotential_eq_zero_of_not_mem _ _ hx] using hδ
  have hg' : ∀ z ∈ V, |greenPotential V η' z - greenPotential V η z| ≤ δ := fun z hz => by
    rw [abs_sub_comm]
    exact hg z hz
  have ha := hv'.2 (h1 d hd V hV η η' (divOdometer V η) δ hδ hg hv.1) x
  have hb := hv.2 (h1 d hd V hV η' η (divOdometer V η') δ hδ hg' hv'.1) x
  simp only at ha hb
  have hgx' := abs_le.mp hgx
  rw [abs_le]
  constructor <;> linarith

/-- **Reduction of Theorem 8.2** to Proposition 8.1, Lemma 8.1 and Steps 2 and 3. -/
theorem divisibleTheorem_of_steps (hLA : DivisibleLeastActionStmt)
    (hH : DivisibleHomogenizeDomainStmt) (h2 : DivOdometerComparisonStmt)
    (h3 : DivDomainFiniteStmt) : DivisibleTheoremStmt := by
  intro d hd E W hW
  obtain ⟨C, hC⟩ := hH d hd
  filter_upwards [hC E W hW] with η hη
  have hfin := h3 d W hW
  refine ⟨fun n => ⟨(hLA d hd _ (hfin n) η).1, (hLA d hd _ (hfin n) _).1⟩, ?_⟩
  intro ε hε
  have hK : 0 < 2 * (|C| + 1) := by positivity
  obtain ⟨n₀, hn₀⟩ := hη (ε / (2 * (|C| + 1))) (div_pos hε hK)
  filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn
  rintro _ ⟨z, -, rfl⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hε' : 0 ≤ ε / (2 * (|C| + 1)) := (div_pos hε hK).le
  have hg : ∀ x ∈ discretize W n,
      |greenPotential (discretize W n) η x -
        greenPotential (discretize W n) (fun _ => meanEtaReal E.P) x| ≤
        ε / (2 * (|C| + 1)) * |C| * (n : ℝ) ^ 2 := fun x hx =>
    (hn₀ n (le_of_max_le_left hn) x (subset_dClosure _ hx)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self C) hε') (sq_nonneg _))
  have hcmp := h2 d (by omega) _ (hfin n) η _ _ (by positivity) (hLA d hd _ (hfin n) η).2
    (hLA d hd _ (hfin n) _).2 hg z
  have hbound : 2 * (ε / (2 * (|C| + 1)) * |C| * (n : ℝ) ^ 2) ≤ ε * (n : ℝ) ^ 2 := by
    have hfrac : |C| / (|C| + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have heq : 2 * (ε / (2 * (|C| + 1)) * |C| * (n : ℝ) ^ 2) =
        ε * (n : ℝ) ^ 2 * (|C| / (|C| + 1)) := by
      field_simp
    rw [heq]
    exact mul_le_of_le_one_right (by positivity) hfrac
  simp only [rescaleDivOdo, divOdometerDomain, divOdometerAvg,
    latticeRound_smul_inv_smul_toE (by omega : n ≠ 0) z]
  rw [← sub_div, abs_div, abs_of_pos (pow_pos hnpos 2), div_le_iff₀ (pow_pos hnpos 2)]
  exact hcmp.trans hbound

end RandomSandpile

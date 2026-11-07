import RandomSandpile.Steps.Sec8.DivisibleTheorem
import RandomSandpile.Proofs.Sec8.DivisibleLeastAction

/-!
# Proofs of the steps of Theorem 8.2

Proofs of the steps of `RandomSandpile.DivisibleTheoremStmt` decomposed in
`RandomSandpile/Steps/Sec8/DivisibleTheorem.lean` (`paper/random_piles-corrected.tex`):

* `divCompetitor : DivCompetitorStmt`, from the Poisson equation for the Green potentials
  (`lapR_greenPotential`) and their vanishing off `V` (`greenPotential_eq_zero_of_not_mem`);
* `divOdometerComparison : DivOdometerComparisonStmt`, by `divOdometerComparison_of_competitor`;
* `divDomainFinite : DivDomainFiniteStmt`, `W_n` lies in a box of side `2⌈R⌉` when `nW` lies in
  the ball of radius `R`.

Assembly: `divisibleTheorem_of_homogenizeDomain`, Theorem 8.2 from Lemma 8.1
(`DivisibleHomogenizeDomainStmt`), with Proposition 8.1 supplied by `divisibleLeastAction`
(`RandomSandpile/Proofs/Sec8/DivisibleLeastAction.lean`).
-/

noncomputable section

open LatticeProb Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- The discrete Laplacian of the competitor `f - (r - r') + δ` is `Δ f - Δ r + Δ r'`. -/
theorem lapR_sub_sub_add_const (f r r' : Site d → ℝ) (δ : ℝ) (x : Site d) :
    lapR (fun z => f z - (r z - r' z) + δ) x = lapR f x - lapR r x + lapR r' x := by
  simp only [lapR, nbrSum, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Step 1 of Theorem 8.2: the competitor `f - (r - r') + δ`. -/
theorem divCompetitor : DivCompetitorStmt := by
  intro d hd V hV η η' f δ hδ hg hf
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · by_cases hx : x ∈ V
    · have := (abs_le.mp (hg x hx)).2
      linarith [hf.1 x]
    · simp only [greenPotential_eq_zero_of_not_mem _ _ hx, sub_zero]
      linarith [hf.1 x]
  · rw [lapR_sub_sub_add_const, lapR_greenPotential hd hV η hx, lapR_greenPotential hd hV η' hx]
    linarith [hf.2 x hx]

/-- Step 2 of Theorem 8.2: the comparison of odometers. -/
theorem divOdometerComparison : DivOdometerComparisonStmt :=
  divOdometerComparison_of_competitor divCompetitor

/-- Step 3 of Theorem 8.2: `W_n = ℤ^d ∩ nW` is finite for a (bounded) Lipschitz domain `W`. -/
theorem divDomainFinite : DivDomainFiniteStmt := by
  intro d W hW n
  obtain ⟨R, hR⟩ := (hW.1.smul₀ (n : ℝ)).exists_norm_le
  refine (Set.finite_Icc (fun _ : Fin d => -⌈R⌉) (fun _ => ⌈R⌉)).subset fun x hx => ?_
  have hi : ∀ i, |(x i : ℝ)| ≤ R := fun i => by
    simpa [toE] using (PiLp.norm_apply_le (toE x) i).trans (hR _ hx)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h2 : (-(⌈R⌉ : ℤ) : ℝ) ≤ x i := by linarith [(abs_le.mp (hi i)).1, Int.le_ceil R]
    exact_mod_cast h2
  · have h2 : (x i : ℝ) ≤ (⌈R⌉ : ℤ) := by linarith [(abs_le.mp (hi i)).2, Int.le_ceil R]
    exact_mod_cast h2

/-- **Theorem 8.2 from Lemma 8.1.** The random divisible sandpile homogenizes on `W_n`, given the
homogenization of the Green potentials `DivisibleHomogenizeDomainStmt` (Lemma 8.1); Proposition
8.1 is `divisibleLeastAction`. -/
theorem divisibleTheorem_of_homogenizeDomain (hH : DivisibleHomogenizeDomainStmt) :
    DivisibleTheoremStmt :=
  divisibleTheorem_of_steps divisibleLeastAction hH divOdometerComparison divDomainFinite

end RandomSandpile

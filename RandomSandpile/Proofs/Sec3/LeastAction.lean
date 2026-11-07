import RandomSandpile.Steps.Sec3.LeastAction
import RandomSandpile.Defs.Odometer

/-!
# Proof of Proposition 3.1 (least action principle)

Proofs of the two steps of `RandomSandpile/Steps/Sec3/LeastAction.lean` and of
`RandomSandpile.LeastActionStmt` (Proposition 3.1, `paper/random_piles-corrected.tex`).

* `IsLegal.induction`: induction on legal toppling functions, one toppling at a time
  (`IsLegal.snoc` is the converse step).
* `legalLeStabilizing` (Step 1, the least action principle): along a legal toppling sequence the
  toppling function stays below a stabilizing `v`; at the first site `x` where it would exceed `v`
  it agrees with `v` at `x` before toppling, so its Laplacian at `x` is at most `Δ_{ℤ^d} v (x)`
  (`LatticeProb.Sandpile.lap_le_lap_of_le`), and `x` would be stable.
* `existsLegalStabilizing` (Step 2): the number of topplings of a legal toppling function equals its
  mass `∑_{y ∈ A} u(y)`, which is bounded by the mass of a stabilizing toppling function (Step 1 and
  `stabilizingOpen_nonempty`); a legal toppling function that is not stabilizing can be extended by
  one more legal toppling, so a legal toppling function of maximal mass is stabilizing.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

private theorem sum_Iio_eq_sum_ite' {n : ℕ} (i : Fin n) (f : Fin n → ℤ) :
    ∑ j ∈ Finset.Iio i, f j = ∑ j, if j < i then f j else 0 := by
  rw [← Finset.sum_filter]; congr 1; ext j; simp

/-- Induction on legal toppling functions for `η` in `A`: a property of toppling functions that
holds for `0` and is preserved by appending a legal toppling at an unstable site of `A` holds for
every legal toppling function. -/
theorem IsLegal.induction {η : Site d → ℤ} {A : Set (Site d)} (P : (Site d → ℤ) → Prop)
    (h0 : P 0)
    (hstep : ∀ (u : Site d → ℤ) (x : Site d), IsLegal η A u → P u → x ∈ A →
      2 * (d : ℤ) ≤ lap u x + η x → P (u + dirac x))
    {u : Site d → ℤ} (hu : IsLegal η A u) : P u := by
  obtain ⟨n, xs, hA, hleg, rfl⟩ := hu
  induction n with
  | zero =>
    convert h0 using 1
    funext y; simp
  | succ n ih =>
    have hsplit : (fun y => ∑ i : Fin (n + 1), dirac (xs i) y) =
        (fun y => ∑ i : Fin n, dirac (xs (Fin.castSucc i)) y) + dirac (xs (Fin.last n)) := by
      funext y; simp [Fin.sum_univ_castSucc]
    have hpre : ∀ i : Fin n, (fun y => ∑ j ∈ Finset.Iio (Fin.castSucc i), dirac (xs j) y) =
        fun y => ∑ j ∈ Finset.Iio i, dirac (xs (Fin.castSucc j)) y := by
      intro i; funext y
      rw [sum_Iio_eq_sum_ite', sum_Iio_eq_sum_ite', Fin.sum_univ_castSucc]
      simp [not_lt.2 (Fin.castSucc_lt_last i).le]
    have hlast : (fun y => ∑ j ∈ Finset.Iio (Fin.last n), dirac (xs j) y) =
        fun y => ∑ i : Fin n, dirac (xs (Fin.castSucc i)) y := by
      funext y
      rw [sum_Iio_eq_sum_ite', Fin.sum_univ_castSucc]
      simp [Fin.castSucc_lt_last]
    have hleg' : ∀ i : Fin n, 2 * (d : ℤ) ≤
        lap (fun y => ∑ j ∈ Finset.Iio i, dirac (xs (Fin.castSucc j)) y) (xs (Fin.castSucc i)) +
          η (xs (Fin.castSucc i)) := by
      intro i; rw [← hpre i]; exact hleg (Fin.castSucc i)
    have hP := ih (fun i => xs (Fin.castSucc i)) (fun i => hA _) hleg'
    rw [hsplit]
    refine hstep _ _ ⟨n, fun i => xs (Fin.castSucc i), fun i => hA _, hleg', rfl⟩ hP (hA _) ?_
    rw [← hlast]; exact hleg (Fin.last n)

/-- **Step 1 of Proposition 3.1, the least action principle**: a legal toppling function for `η`
in `A` lies below every stabilizing toppling function for `η` in `A`. -/
theorem legalLeStabilizing : LegalLeStabilizingStmt := by
  intro d A η u v hu hv
  refine IsLegal.induction (fun u => u ≤ v) (fun y => hv.1.1 y) ?_ hu
  intro u x _ huv hxA hx y
  by_cases hy : y = x
  · subst hy
    simp only [Pi.add_apply, dirac]
    by_contra hlt
    push Not at hlt
    have heq : u y = v y := le_antisymm (huv y) (by omega)
    have h1 := lap_le_lap_of_le (fun z => huv z) heq
    have h2 := hv.2 y hxA
    omega
  · simp only [Pi.add_apply, dirac_of_ne hy, add_zero]
    exact huv y

/-- **Step 2 of Proposition 3.1**: for `d ≥ 1` and finite `A`, some toppling function is legal
and stabilizing for `η` in `A`. -/
theorem existsLegalStabilizing : ExistsLegalStabilizingStmt := by
  intro d hd A hA η
  classical
  obtain ⟨u₀, hu₀, -⟩ := stabilizingOpen_nonempty hd η hA
  by_contra H
  push Not at H
  have key : ∀ k : ℕ, ∃ u, IsLegal η A u ∧ ∑ y ∈ hA.toFinset, u y = k := by
    intro k
    induction k with
    | zero => exact ⟨0, IsLegal.zero η A, by simp⟩
    | succ k ih =>
      obtain ⟨u, hu, hmu⟩ := ih
      have hex : ∃ x ∈ A, 2 * (d : ℤ) ≤ lap u x + η x := by
        by_contra hx
        push Not at hx
        exact H u hu ⟨hu.isTopplingFn, fun x hxA => by have := hx x hxA; omega⟩
      obtain ⟨x, hxA, hx⟩ := hex
      refine ⟨u + dirac x, hu.snoc hxA hx, ?_⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib, hmu]
      simp [dirac, Finset.sum_ite_eq', hxA]
  obtain ⟨u, hu, hmu⟩ := key ((∑ y ∈ hA.toFinset, u₀ y).toNat + 1)
  have hle : u ≤ u₀ := legalLeStabilizing d A η u u₀ hu hu₀
  have hsum : ∑ y ∈ hA.toFinset, u y ≤ ∑ y ∈ hA.toFinset, u₀ y :=
    Finset.sum_le_sum fun y _ => hle y
  have htn := Int.self_le_toNat (∑ y ∈ hA.toFinset, u₀ y)
  push_cast at hmu
  omega

/-- **Proposition 3.1** (least action principle). -/
theorem leastAction : LeastActionStmt :=
  leastAction_of_steps legalLeStabilizing existsLegalStabilizing

end RandomSandpile

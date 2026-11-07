import RandomSandpile.Steps.Sec3.Burning

/-!
# Steps of Proposition 3.4 (a sandpile in which every site has toppled is recurrent)

Carving of `RandomSandpile.RecurrentOfToppledStmt` (Proposition 3.4,
`paper/random_piles-corrected.tex`) into four steps, and the reductions
`noForbiddenRecurrent_of_steps` and `recurrentOfToppled_of_steps`.

No proof is printed. The hidden proof shows that `Δ_{ℤ^d} w + η` has no forbidden
subconfiguration in `A` (Dhar): in a nonempty `B ⊆ A`, the site whose last toppling comes first
afterwards receives a chip from each of its neighbours in `B`. It then appeals to the
forbidden-subconfiguration criterion for recurrence. That criterion is classical for stable
sandpiles, while `Δ_{ℤ^d} w + η` need not be stable in `A`, and the paper's recurrence
is reachability from `2d - 1 + s`, `s ≥ 0`, by legal topplings .
We prove the criterion for every sandpile on a finite set (`NoForbiddenRecurrentStmt`). This
resolves N1, and the statement holds as drafted, also when `A ⊊ W`.

* `ToppledFiniteStmt`: `A` is finite, since `w = w_∂ + ŵ` with `w_∂ = 0` in `W` and `ŵ` a finite
  sum of unit topplings; so `A` is contained in the finite set of toppled sites.
* `ToppledNoForbiddenStmt`: `Δ_{ℤ^d} w + η` has no forbidden subconfiguration in `A`.
* `LegalOfNoForbiddenStmt` (a generalized burning algorithm): if `η` has no forbidden
  subconfiguration in the finite set `A`, every toppling function `φ` supported in `A` is legal for
  `η - Δ_{ℤ^d} φ` in `A`. Greedily topple a site where `φ - ψ` is maximal, `ψ` the topplings done so
  far. (For `φ = 1_A` this is Dhar's burning test.)
* `SuperharmonicBarrierStmt`: on a finite set `A` there is a toppling function `φ ≥ 0` supported in
  `A` with `Δ_{ℤ^d} φ ≤ -2C` in `A`, namely `C (R - x₀²)` on `A`.
* `NoForbiddenRecurrentStmt`, from the last two: `η = (η - Δ_{ℤ^d} φ) + Δ_{ℤ^d} φ` with
  `η - Δ_{ℤ^d} φ ≥ 2d - 1` in `A` for `C` large, and `φ` legal for `η - Δ_{ℤ^d} φ`.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Step 1 of Proposition 3.4: if `w ∈ 𝓛(η, W)` and `w ≥ 1` on `A ⊆ W`, then `A` is finite. -/
def ToppledFiniteStmt : Prop :=
  ∀ (d : ℕ) (A W : Set (Site d)) (η w : Site d → ℤ), A ⊆ W → w ∈ locLegal η W →
    (∀ x ∈ A, 1 ≤ w x) → A.Finite

/-- Step 2 of Proposition 3.4 (hidden proof): if `w ∈ 𝓛(η, W)` and `w ≥ 1` on
`A ⊆ W`, then `Δ_{ℤ^d} w + η` has no forbidden subconfiguration in `A`. -/
def ToppledNoForbiddenStmt : Prop :=
  ∀ (d : ℕ) (A W : Set (Site d)) (η w : Site d → ℤ), A ⊆ W → w ∈ locLegal η W →
    (∀ x ∈ A, 1 ≤ w x) → NoForbiddenSubconfig (fun x => lap w x + η x) A

/-- Step 3 of Proposition 3.4, a generalized burning algorithm: if `η` has no forbidden
subconfiguration in the finite set `A`, then every toppling function `φ ≥ 0` vanishing off `A` is
legal for `η - Δ_{ℤ^d} φ` in `A`. -/
def LegalOfNoForbiddenStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)), A.Finite → ∀ (η φ : Site d → ℤ), NoForbiddenSubconfig η A →
    (∀ x, 0 ≤ φ x) → (∀ x ∉ A, φ x = 0) → IsLegal (fun x => η x - lap φ x) A φ

/-- Step 4 of Proposition 3.4, a strict supersolution barrier: for `d ≥ 1`, a finite set `A` and
`C ≥ 0`, some `φ ≥ 0` vanishing off `A` has `Δ_{ℤ^d} φ ≤ -2C` in `A`. -/
def SuperharmonicBarrierStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (A : Set (Site d)), A.Finite → ∀ C : ℤ, 0 ≤ C →
    ∃ φ : Site d → ℤ, (∀ x, 0 ≤ φ x) ∧ (∀ x ∉ A, φ x = 0) ∧ ∀ x ∈ A, lap φ x ≤ -2 * C

/-- The forbidden-subconfiguration criterion for recurrence, for sandpiles that need not be
stable: for `d ≥ 1`, a sandpile with no forbidden subconfiguration in the finite set `A` is
recurrent in `A` in the sense (`IsRecurrentOn`). With `RecurrentNoForbiddenStmt`
(`RandomSandpile/Steps/Sec3/Burning.lean`) this is an equivalence. -/
def NoForbiddenRecurrentStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (A : Set (Site d)), A.Finite → ∀ η : Site d → ℤ,
    NoForbiddenSubconfig η A → IsRecurrentOn η A

/-- Reduction of the forbidden-subconfiguration criterion to Steps 3-4. -/
theorem noForbiddenRecurrent_of_steps (hleg : LegalOfNoForbiddenStmt)
    (hbar : SuperharmonicBarrierStmt) : NoForbiddenRecurrentStmt := by
  intro d hd A hA η hη
  obtain ⟨m, hm⟩ := (hA.image η).bddBelow
  have hm' : ∀ x ∈ A, m ≤ η x := fun x hx => hm ⟨x, hx, rfl⟩
  have hC0 : (0 : ℤ) ≤ max (2 * (d : ℤ) - 1 - m) 0 := le_max_right _ _
  have hC1 : 2 * (d : ℤ) - 1 - m ≤ max (2 * (d : ℤ) - 1 - m) 0 := le_max_left _ _
  obtain ⟨φ, hφ0, hφA, hφlap⟩ := hbar d hd A hA _ hC0
  have hφ := hleg d A hA η φ hη hφ0 hφA
  refine ⟨fun x => η x - lap φ x - (2 * (d : ℤ) - 1), φ, fun x hx => ?_, ?_,
    fun x hx => hφA x (Set.disjoint_right.1 (bdry_disjoint A) hx), fun x _ => ?_⟩
  · show 0 ≤ η x - lap φ x - (2 * (d : ℤ) - 1)
    linarith [hφlap x hx, hm' x hx]
  · refine mem_locLegal_of_isLegal ?_
    convert hφ using 1
    funext x
    ring
  · show η x = 2 * (d : ℤ) - 1 + (η x - lap φ x - (2 * (d : ℤ) - 1)) + lap φ x
    ring

/-- Reduction of Proposition 3.4 to Steps 1-2 and the forbidden-subconfiguration criterion. -/
theorem recurrentOfToppled_of_steps (hfin : ToppledFiniteStmt) (hnf : ToppledNoForbiddenStmt)
    (hrec : NoForbiddenRecurrentStmt) : RecurrentOfToppledStmt := by
  intro d hd A W hAW _ _ η w hw h1
  exact hrec d (by omega) A (hfin d A W η w hAW hw h1) _ (hnf d A W η w hAW hw h1)

end RandomSandpile

import RandomSandpile.Defs.Lattice

/-!
# Toppling functions: legal, locally legal and stabilizing topplings (Section 2)

`paper/random_piles-corrected.tex`. A sandpile is a function `η : ℤ^d → ℤ`; only its
values on the domain `A` matter below. A *toppling function* on `Ā` is a function `Ā → ℕ`; here it
is a function `u : ℤ^d → ℤ` with `u ≥ 0` that vanishes off `Ā` (`IsTopplingFn`), so the sets
`locLegal η A` and `stabilizing η A` are in bijection with the paper's sets of functions `Ā → ℕ`.

The Laplacian is the integer Laplacian `LatticeProb.Sandpile.lap` and a unit toppling at `x` is
`LatticeProb.Sandpile.dirac x`. Lattice-Probability's `LatticeProb.Sandpile.IsLegalToppling`
(`LatticeProb/Sandpile/LeastAction.lean`) is a *parallel*, whole-space notion of legal toppling;
`IsLegal` keeps the paper's sequential definition on a domain.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- `u` is a *toppling function* on `Ā`: a nonnegative integer function vanishing off
the discrete closure `Ā = A ∪ ∂A`. (The paper says "positive integer-valued functions on `Ā`" and
means `ℕ`-valued ones.) -/
def IsTopplingFn (A : Set (Site d)) (u : Site d → ℤ) : Prop :=
  (∀ x, 0 ≤ u x) ∧ ∀ x ∉ dClosure A, u x = 0

/-- `u` is *legal* for `η` in `A`: for some `n ≥ 0` and sites
`x̂_1, …, x̂_n ∈ A` (indexed here by `Fin n`, from `0`),
`u = u_0 + u_1 + ⋯ + u_n` with `u_0 = 0` and `u_i = 1_{x̂_i}` the unit toppling at `x̂_i`, and
`(Δ_{ℤ^d}(u_1 + ⋯ + u_{i-1}) + η)(x̂_i) ≥ 2d` for every `i`: each toppling happens at a site of `A`
that is unstable in the configuration reached so far.

The paper requires `u_i(x) = 0` for `x ∈ A ∖ {x̂_i}` and `u_i(x̂_i) = 1`; we read `u_i` as the unit
toppling `1_{x̂_i}` (zero on `∂A` as well), the reading under which "when `η ≤ 2d - 1` the only legal
toppling function is `u = 0`" holds and under which the decomposition `u = w + û` of
`locLegal` is meaningful. -/
def IsLegal (η : Site d → ℤ) (A : Set (Site d)) (u : Site d → ℤ) : Prop :=
  ∃ (n : ℕ) (x : Fin n → Site d), (∀ i, x i ∈ A) ∧
    (∀ i : Fin n,
      2 * (d : ℤ) ≤ lap (fun y => ∑ j ∈ Finset.Iio i, dirac (x j) y) (x i) + η (x i)) ∧
    u = fun y => ∑ i : Fin n, dirac (x i) y

/-- The zero toppling function is legal (`n = 0`). -/
theorem IsLegal.zero (η : Site d → ℤ) (A : Set (Site d)) : IsLegal η A 0 :=
  ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by funext y; simp⟩

/-- A legal toppling function is a toppling function on `Ā`; it even vanishes off `A`. -/
theorem IsLegal.isTopplingFn {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (hu : IsLegal η A u) : IsTopplingFn A u := by
  obtain ⟨n, xs, hA, -, rfl⟩ := hu
  refine ⟨fun y => Finset.sum_nonneg fun i _ => ?_, fun y hy => Finset.sum_eq_zero fun i _ => ?_⟩
  · unfold dirac; split_ifs <;> norm_num
  · refine dirac_of_ne fun h => hy ?_
    subst h
    exact subset_dClosure A (hA i)

private theorem sum_Iio_eq_sum_ite {n : ℕ} (i : Fin n) (f : Fin n → ℤ) :
    ∑ j ∈ Finset.Iio i, f j = ∑ j, if j < i then f j else 0 := by
  rw [← Finset.sum_filter]; congr 1; ext j; simp

/-- Appending one legal toppling: if `u` is legal for `η` in `A`, `x ∈ A` and `x` is unstable in
`Δ_{ℤ^d} u + η`, then `u + 1_x` is legal for `η` in `A`. -/
theorem IsLegal.snoc {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ} {x : Site d}
    (hu : IsLegal η A u) (hx : x ∈ A) (h : 2 * (d : ℤ) ≤ lap u x + η x) :
    IsLegal η A (u + dirac x) := by
  obtain ⟨n, xs, hA, hleg, rfl⟩ := hu
  refine ⟨n + 1, Fin.snoc xs x, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hx
    · simpa using hA j
  · intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · have hs : (fun y => ∑ j ∈ Finset.Iio (Fin.last n),
          dirac ((Fin.snoc xs x : Fin (n + 1) → Site d) j) y) =
          fun y => ∑ j : Fin n, dirac (xs j) y := by
        funext y
        rw [sum_Iio_eq_sum_ite, Fin.sum_univ_castSucc]
        simp [Fin.castSucc_lt_last]
      rw [hs]; simpa using h
    · have hs : (fun y => ∑ j ∈ Finset.Iio (Fin.castSucc k),
          dirac ((Fin.snoc xs x : Fin (n + 1) → Site d) j) y) =
          fun y => ∑ j ∈ Finset.Iio k, dirac (xs j) y := by
        funext y
        rw [sum_Iio_eq_sum_ite, sum_Iio_eq_sum_ite, Fin.sum_univ_castSucc]
        simp [not_lt.2 (Fin.castSucc_lt_last k).le]
      rw [hs]; simpa using hleg k
  · funext y
    simp [Fin.sum_univ_castSucc]

/-- The set `𝓛(η, A)` of *locally legal* topplings for `η` in `A`: toppling
functions `u = w + û` on `Ā` where `w = 0` in `A`, `û = 0` on `∂A`, and `û` is legal for
`Δ_{ℤ^d} w + η` in `A`. The constraint is only enforced in `A`: `w` is an arbitrary toppling of the
boundary `∂A`. -/
def locLegal (η : Site d → ℤ) (A : Set (Site d)) : Set (Site d → ℤ) :=
  {u | ∃ w uh : Site d → ℤ, IsTopplingFn A w ∧ IsTopplingFn A uh ∧ u = w + uh ∧
    (∀ x ∈ A, w x = 0) ∧ (∀ x ∈ bdry A, uh x = 0) ∧ IsLegal (fun y => lap w y + η y) A uh}

/-- The set `𝓢(η, A)` of *stabilizing* topplings for `η` in `A`: toppling functions
`v` on `Ā` with `Δ_{ℤ^d} v + η ≤ 2d - 1` in `A`; they may topple `∂A` arbitrarily. -/
def stabilizing (η : Site d → ℤ) (A : Set (Site d)) : Set (Site d → ℤ) :=
  {v | IsTopplingFn A v ∧ ∀ x ∈ A, lap v x + η x ≤ 2 * (d : ℤ) - 1}

/-- `η` is *stable* in `A`: `η ≤ 2d - 1` in `A`. -/
def IsStableOn (η : Site d → ℤ) (A : Set (Site d)) : Prop :=
  ∀ x ∈ A, η x ≤ 2 * (d : ℤ) - 1

/-- `η` is *recurrent* in `A`: there are `s : A → ℕ` and `u ∈ 𝓛(s + 2d - 1, A)` with
`u = 0` on `∂A` such that `η = 2d - 1 + s + Δ_{ℤ^d} u` in `A`; that is, `η` is reached from the
constant sandpile `2d - 1` on `A` by adding chips in `A` and then toppling legally. -/
def IsRecurrentOn (η : Site d → ℤ) (A : Set (Site d)) : Prop :=
  ∃ s u : Site d → ℤ, (∀ x ∈ A, 0 ≤ s x) ∧
    u ∈ locLegal (fun y => s y + (2 * (d : ℤ) - 1)) A ∧ (∀ x ∈ bdry A, u x = 0) ∧
    ∀ x ∈ A, η x = 2 * (d : ℤ) - 1 + s x + lap u x

end RandomSandpile

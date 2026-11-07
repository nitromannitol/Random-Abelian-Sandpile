import RandomSandpile.Steps.Sec3.LeastAction

/-!
# Steps of Proposition 3.3 (burning: maximum and comparison principles)

Carving of `RandomSandpile.BurningStmt` (Proposition 3.3, `paper/random_piles-corrected.tex`) into four steps, and the reduction `burning_of_steps`.

The paper derives (eq:stable) and (eq:rec) from the proof of Dhar's burning algorithm (Klivans,
Theorem 2.6.3; Corry-Perkinson, Theorem 7.5), and from (eq:rec) applied to the
configuration `η_v = Δ_{ℤ^d} v + s`. Here the burning algorithm enters through the classical
notion of a *forbidden subconfiguration* (Dhar): a nonempty `B ⊆ A` with `η(z) < deg_B(z)` for
every `z ∈ B`, where `deg_B(z)` is the number of neighbours of `z` in `B`. Since
`Δ_{ℤ^d} 1_B (z) = deg_B(z) - 2d` for `z ∈ B`, "`η(z) ≥ deg_B(z)` for some `z ∈ B`" reads
`2d ≤ η(z) - Δ_{ℤ^d} 1_B (z)`: after toppling every site outside `B` once, some site of `B` is
unstable (the burning step). `NoForbiddenSubconfig η A` says that `A` contains no forbidden
subconfiguration of `η`.

* `StableMaxPrincipleStmt` (eq:stable): the maximum principle for stable `s`.
* `RecurrentNoForbiddenStmt` (burning algorithm): a recurrent sandpile has no forbidden
  subconfiguration.
* `NoForbiddenLocLegalStmt`: adding chips from boundary topplings and toppling legally preserves
  the absence of forbidden subconfigurations; in particular `η_v = s + Δ_{ℤ^d} v` has none when
  `s` has none and `v ∈ 𝓛(s, A)` (the paper's "`η_v` is recurrent").
* `SupersolutionMinPrincipleStmt`: the minimum principle for supersolutions of the discrete
  sandpile PDE: if `η` has no forbidden subconfiguration in the finite set `A` and
  `Δ_{ℤ^d} z + η ≤ 2d - 1` in `A`, then `inf_A z ≥ inf_{∂A} z`.

Assembly (`burning_of_steps`): (eq:stable) is the first step. (eq:rec) is the minimum principle
applied to `z = v`, which is a supersolution because it is stabilizing. is the minimum
principle applied to `z = (u + g) - (v + h)` and `η_v = s + Δ_{ℤ^d} v`: in `A`,
`Δ_{ℤ^d} z + η_v = Δ_{ℤ^d} u + s ≤ 2d - 1` since `g` and `h` are harmonic in `A`. This is the
paper's proof with the auxiliary solution `ŵ` and Propositions 3.1 and 3.2
bypassed: the paper shows `inf_A w ≥ inf_A ŵ` (least action) and applies (eq:rec) to `ŵ`; the
minimum principle applies to the supersolution `w` itself. Stability of `s` is used only in
(eq:stable), and connectedness of `A` is not used.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- `η` has *no forbidden subconfiguration* in `A` (Dhar): every finite nonempty `B ⊆ A` contains
a site `z` with `η(z) ≥ deg_B(z)`, written `2d ≤ η(z) - Δ_{ℤ^d} 1_B (z)`; equivalently, toppling
every site outside `B` once makes some site of `B` unstable. -/
def NoForbiddenSubconfig {d : ℕ} (η : Site d → ℤ) (A : Set (Site d)) : Prop :=
  ∀ B : Set (Site d), B ⊆ A → B.Finite → B.Nonempty →
    ∃ z ∈ B, 2 * (d : ℤ) ≤ η z - lap (B.indicator fun _ => (1 : ℤ)) z

/-- Step 1 of Proposition 3.3, (eq:stable): the maximum principle for the discrete
sandpile PDE with stable source. If `s` is stable in `A`, `v ∈ 𝓛(s, A) ∩ 𝒮(s, A)` and `v = f ≥ 0`
on `∂A`, then `sup_A v ≤ sup_{∂A} f`, in pointwise form. -/
def StableMaxPrincipleStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (A : Set (Site d)), A.Finite →
    ∀ (f s v : Site d → ℤ), (∀ y ∈ bdry A, 0 ≤ f y) →
      v ∈ locLegal s A ∩ stabilizing s A → (∀ y ∈ bdry A, v y = f y) →
      IsStableOn s A → ∀ x ∈ A, ∃ y ∈ bdry A, v x ≤ f y

/-- Step 2 of Proposition 3.3, the burning algorithm (Dhar;): a sandpile that is
recurrent in `A` has no forbidden subconfiguration in `A`. -/
def RecurrentNoForbiddenStmt : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (A : Set (Site d)) (η : Site d → ℤ),
    IsRecurrentOn η A → NoForbiddenSubconfig η A

/-- Step 3 of Proposition 3.3: if `η` has no forbidden subconfiguration in `A` and
`v ∈ 𝓛(η, A)`, then `η + Δ_{ℤ^d} v` has none: boundary topplings only add chips in `A`, and a
legal toppling preserves the absence of forbidden subconfigurations. -/
def NoForbiddenLocLegalStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)) (η v : Site d → ℤ), NoForbiddenSubconfig η A →
    v ∈ locLegal η A → NoForbiddenSubconfig (fun x => η x + lap v x) A

/-- Step 4 of Proposition 3.3: the minimum principle for supersolutions of the discrete sandpile
PDE `Δ_{ℤ^d} z + η ≤ 2d - 1` in `A`, when `η` has no forbidden subconfiguration in the
finite set `A`: `inf_A z ≥ inf_{∂A} z`, in pointwise form. The supersolution `z` is an arbitrary
integer function; it need not be a toppling function. -/
def SupersolutionMinPrincipleStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)), A.Finite → ∀ (η z : Site d → ℤ), NoForbiddenSubconfig η A →
    (∀ x ∈ A, lap z x + η x ≤ 2 * (d : ℤ) - 1) → ∀ x ∈ A, ∃ y ∈ bdry A, z y ≤ z x

namespace Burning

variable {d : ℕ}

/-- Additivity of the integer Laplacian. -/
theorem lap_add_apply' (f g : Site d → ℤ) (x : Site d) :
    lap (fun y => f y + g y) x = lap f x + lap g x := by
  simp only [lap, nbrSumZ, Finset.sum_add_distrib]
  ring

/-- Additivity of the integer Laplacian, for the pointwise sum `f + g`. -/
theorem lap_pi_add_apply (f g : Site d → ℤ) (x : Site d) :
    lap (f + g) x = lap f x + lap g x :=
  lap_add_apply' f g x

/-- The integer Laplacian commutes with differences. -/
theorem lap_sub_apply' (f g : Site d → ℤ) (x : Site d) :
    lap (fun y => f y - g y) x = lap f x - lap g x := by
  simp only [lap, nbrSumZ, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

end Burning

/-- Reduction of Proposition 3.3 to its four steps. -/
theorem burning_of_steps (h1 : StableMaxPrincipleStmt) (h2 : RecurrentNoForbiddenStmt)
    (h3 : NoForbiddenLocLegalStmt) (h4 : SupersolutionMinPrincipleStmt) : BurningStmt := by
  intro d hd A hA _ f s v hf hv hvf
  have hd0 : 0 < d := by omega
  refine ⟨fun hst => h1 d hd0 A hA f s v hf hv hvf hst, fun hrec x hx => ?_,
    fun _ hrec f' u _ hu huf g h hg hh x hx => ?_⟩
  · obtain ⟨y, hy, hle⟩ := h4 d A hA s v (h2 d hd0 A s hrec) hv.2.2 x hx
    exact ⟨y, hy, by rw [← hvf y hy]; exact hle⟩
  · have hnf := h3 d A s v (h2 d hd0 A s hrec) hv.1
    have hsup : ∀ x ∈ A, lap (fun y => (u y + g y) - (v y + h y)) x + (s x + lap v x) ≤
        2 * (d : ℤ) - 1 := by
      intro x hx
      rw [Burning.lap_sub_apply', Burning.lap_add_apply', Burning.lap_add_apply', hg x hx,
        hh x hx]
      linarith [hu.2.2 x hx]
    obtain ⟨y, hy, hle⟩ := h4 d A hA _ _ hnf hsup x hx
    rw [huf y hy, hvf y hy] at hle
    exact ⟨y, hy, hle⟩

end RandomSandpile

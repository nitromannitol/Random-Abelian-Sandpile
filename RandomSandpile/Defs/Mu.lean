import RandomSandpile.Defs.Toppling

/-! # Perturbed sub/supersolutions, the monotone quantities `μ`, `μ*`, and concave envelopes

Section 5 of the paper (545-606).

* `perturbedSub A η l M` and `perturbedSuper A η l M`: the sets `S(A, η, l, M)` and
  `S*(A, η, l, M)` of locally legal (resp. stabilizing) toppling functions perturbed by the parabola
  `-(q_l + q_M)`;
* `mu A η l M` and `muStar A η l M`: the monotone quantities `μ(A, η, l, M)` and `μ*(A, η, l, M)`,
  suprema of the Lebesgue measures of supergradient (resp. subgradient) sets;
* `cubeHull n`, `cubeHullClosure n`: the convex hulls `𝒬_n = conv Q_n` and `𝒬̄_n = conv Q̄_n`
;
* `concaveEnvelopeOn A w`, `concaveEnvelope w n`: the concave envelope `Γ_w` of `w` over `Ā`,
  resp. over `Q̄_n`;
* `supGradR g x K` and `supGradSetR g U K`: supergradients of a function on `ℝ^d` tested on a set
  `K ⊆ ℝ^d`, as used for `∂⁺(Γ_w, x, Q_n)` and `∂⁺(Γ_w, 𝒬_n)` in Lemma 5.3. -/

open MeasureTheory LatticeProb
open scoped ENNReal

namespace RandomSandpile

variable {d : ℕ}

/-! ### Perturbed subsolutions and supersolutions -/

/-- The set of *perturbed subsolutions* `S(A, η, l, M) = {u : Ā → ℕ : u ∈ 𝓛(η, A)} - (q_l + q_M)`: locally legal toppling functions minus the parabola `q_l + q_M` restricted to the
lattice. Toppling functions vanish off `Ā`; only the values on `Ā` enter `supGradSet`. -/
def perturbedSub (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Set (Site d → ℝ) :=
  (fun u x => (u x : ℝ) - (qlZ l x + qMZ M x)) '' locLegal η A

/-- The set of *perturbed supersolutions*
`S*(A, η, l, M) = {v : Ā → ℕ : v ∈ 𝓢(η, A)} - (q_l + q_M)`: stabilizing toppling
functions minus the parabola `q_l + q_M` restricted to the lattice. -/
def perturbedSuper (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Set (Site d → ℝ) :=
  (fun v x => (v x : ℝ) - (qlZ l x + qMZ M x)) '' stabilizing η A

theorem mem_perturbedSub {A : Set (Site d)} {η : Site d → ℤ} {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {w : Site d → ℝ} :
    w ∈ perturbedSub A η l M ↔
      ∃ u ∈ locLegal η A, w = fun x => (u x : ℝ) - (qlZ l x + qMZ M x) := by
  simp only [perturbedSub, Set.mem_image, eq_comm]

theorem mem_perturbedSuper {A : Set (Site d)} {η : Site d → ℤ} {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {w : Site d → ℝ} :
    w ∈ perturbedSuper A η l M ↔
      ∃ v ∈ stabilizing η A, w = fun x => (v x : ℝ) - (qlZ l x + qMZ M x) := by
  simp only [perturbedSuper, Set.mem_image, eq_comm]

/-- The zero toppling is locally legal: take `w = 0` and `û = 0` in the definition of `𝓛(η, A)`. -/
theorem zero_mem_locLegal (η : Site d → ℤ) (A : Set (Site d)) : (0 : Site d → ℤ) ∈ locLegal η A :=
  ⟨0, 0, ⟨fun _ => le_rfl, fun _ _ => rfl⟩, ⟨fun _ => le_rfl, fun _ _ => rfl⟩, (add_zero 0).symm,
    fun _ _ => rfl, fun _ _ => rfl, IsLegal.zero _ _⟩

/-- `S(A, η, l, M)` is nonempty: it contains `-(q_l + q_M)`. -/
theorem perturbedSub_nonempty (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : (perturbedSub A η l M).Nonempty :=
  ⟨_, Set.mem_image_of_mem _ (zero_mem_locLegal η A)⟩

/-! ### The monotone quantities `μ` and `μ*` -/

/-- The monotone quantity controlling subsolutions,
`μ(A, η, l, M) = sup {|∂⁺(w, A)| : w ∈ S(A, η, l, M)}`, where `|·|` is Lebesgue
measure on `ℝ^d`. It is valued in `[0, ∞]`: Lemma 5.4 (`MuBoundedStmt`) bounds it by `C |Q_n|`
on cubes. Since `0 ∈ 𝓛(η, A)`, the supremum is over a nonempty set. -/
noncomputable def mu (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ℝ≥0∞ :=
  ⨆ w ∈ perturbedSub A η l M, volume (supGradSet w A)

/-- The monotone quantity controlling supersolutions,
`μ*(A, η, l, M) = sup {|∂⁻(w, A)| : w ∈ S*(A, η, l, M)}`, valued in `[0, ∞]`. -/
noncomputable def muStar (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : ℝ≥0∞ :=
  ⨆ w ∈ perturbedSuper A η l M, volume (subGradSet w A)

/-! ### Concave envelopes -/

/-- The convex hull `𝒬_n = conv Q_n ⊆ ℝ^d` of the discrete cube `Q_n = {|y|_∞ < n}`. -/
def cubeHull (d : ℕ) (n : ℕ) : Set (Rd d) := convexHull ℝ (toE '' cubeZ0 (n : ℝ))

/-- The convex hull `𝒬̄_n = conv Q̄_n ⊆ ℝ^d` of the discrete closure `Q̄_n = Q_n ∪ ∂Q_n`
. -/
def cubeHullClosure (d : ℕ) (n : ℕ) : Set (Rd d) :=
  convexHull ℝ (toE '' dClosure (cubeZ0 (n : ℝ)))

/-- The *concave envelope* of `w` over the discrete closure `Ā`,
`Γ_w(x) = inf_{p ∈ ℝ^d} max_{y ∈ Ā} (w(y) + p · (x - y))` (where `A = Q_n`).

The maximum is taken over the subtype `Ā`, so it is a genuine maximum when `Ā` is finite and
nonempty. For `x ∈ conv Ā` the infimum is over a family bounded below by `min_{Ā} w` (write `x` as a
convex combination of points of `Ā`); outside `conv Ā` the paper does not define `Γ_w`, and the
value here is the junk value of `⨅` in `ℝ`. -/
noncomputable def concaveEnvelopeOn (A : Set (Site d)) (w : Site d → ℝ) (x : Rd d) : ℝ :=
  ⨅ p : Rd d, ⨆ y : dClosure A, (w y + inner ℝ p (x - toE (y : Site d)))

/-- The *convex envelope* of `w` over the discrete closure `Ā`, i.e. the greatest convex function
below `w` on `Ā`:
`Γ*_w(x) = sup_{p ∈ ℝ^d} min_{y ∈ Ā} (w(y) + p · (x - y))`.
This mirrors `concaveEnvelopeOn` with the inequalities reversed. The paper uses it
without printing it, in the `μ*` half of Lemma 6.2 ("with a sign change"). As for
`concaveEnvelopeOn`, its values outside `conv Ā` are junk. -/
noncomputable def convexEnvelopeOn (A : Set (Site d)) (w : Site d → ℝ) (x : Rd d) : ℝ :=
  ⨆ p : Rd d, ⨅ y : dClosure A, (w y + inner ℝ p (x - toE (y : Site d)))

/-- The concave envelope `Γ_w : 𝒬̄_n → ℝ` of `w` over `Q̄_n`:
`Γ_w(x) = inf_{p ∈ ℝ^d} max_{y ∈ Q̄_n} (w(y) + p · (x - y))`. The paper notes that it is the
pointwise least concave function on `𝒬̄_n` with `Γ_w ≥ w` on `Q̄_n`. Values outside `𝒬̄_n`
(`cubeHullClosure d n`) are junk. -/
noncomputable def concaveEnvelope (w : Site d → ℝ) (n : ℕ) : Rd d → ℝ :=
  concaveEnvelopeOn (cubeZ0 (n : ℝ)) w

/-! ### Supergradients of functions on `ℝ^d` -/

/-- The supergradient set of `g : ℝ^d → ℝ` at `x`, tested on `K ⊆ ℝ^d`:
`{p ∈ ℝ^d : g(x) + p · (y - x) ≥ g(y) for all y ∈ K}`.

With `K = 𝒬̄_n` (`cubeHullClosure d n`) and `g = Γ_w` this is `∂⁺(Γ_w, x, Q_n)` of Lemma 5.3
. The paper does not spell out the test set there; at a contact point `x ∈ Q_n`
with `Γ_w(x) = w(x)`, testing on `𝒬̄_n` or on `Q̄_n` gives the same set, namely `∂⁺(w, x, Q_n)`,
because `Γ_w` is the least concave majorant of `w` on `Q̄_n`. -/
def supGradR (g : Rd d → ℝ) (x : Rd d) (K : Set (Rd d)) : Set (Rd d) :=
  {p | ∀ y ∈ K, g y ≤ g x + inner ℝ p (y - x)}

/-- The supergradient set of `g` over `U`, tested on `K`: `⋃_{x ∈ U} supGradR g x K`.
With `U = 𝒬_n` and `K = 𝒬̄_n` this is
`∂⁺(g, 𝒬_n) = {p ∈ ℝ^d : ∃ x ∈ 𝒬_n, g(x) + p · (y - x) ≥ g(y) for all y ∈ 𝒬̄_n}`. -/
def supGradSetR (g : Rd d → ℝ) (U K : Set (Rd d)) : Set (Rd d) := ⋃ x ∈ U, supGradR g x K

end RandomSandpile

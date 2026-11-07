import Mathlib

/-!
# Statement audit: the main theorem as a comparator challenge

Bou-Rabee, *Convergence of the random Abelian sandpile*, Ann. Probab. 49 (2021), Theorem 1.1.

This file imports only Mathlib. It restates, in the namespace `RandomSandpile.StatementAudit.MainTheorem`,
every definition that `RandomSandpile.MainTheoremStmt` unfolds to, and the five literature inputs as
propositions. The restated bodies are those of the library (`RandomSandpile/Defs`, `RandomSandpile/Inputs`,
`RandomSandpile/Draft/Section1.lean`) and of the Lattice-Probability modules they use, placed in the same
namespaces relative to `RandomSandpile.StatementAudit.MainTheorem`. `Bridge.lean` proves that each restated
definition equals the library definition, and `Solution.lean` proves `mainTheorem` from the library.

`mainTheorem` is the one intentional proof placeholder of this file.
-/

namespace RandomSandpile.StatementAudit.MainTheorem

noncomputable section

-- VOCABULARY-BEGIN
/-! ## Lattice vocabulary from Lattice-Probability (`LatticeProb/Site.lean`, `LatticeProb/Graph/Boundary.lean`, `LatticeProb/Sandpile/Toppling.lean`) -/

namespace LatticeProb

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

theorem unit_ne_zero {d : ℕ} (i : Fin d) : unit i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unit, Pi.single_eq_same] at this

/-- The nearest-neighbour lattice on `ℤ^d`. -/
def lattice (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := ∃ i : Fin d, y = x + unit i ∨ x = y + unit i
  symm := ⟨fun _ _ h => h.imp fun _ hi => hi.symm⟩
  loopless := ⟨fun x h => by
    obtain ⟨i, hi | hi⟩ := h
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)⟩

/-- The sum of `u` over the neighbours of `x`, direction by direction. -/
def nbrSum {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

namespace Graph

variable {V : Type*}

/-- The outer boundary `∂A`: the vertices outside `A` adjacent to a vertex of `A`. -/
def outerBoundary (G : SimpleGraph V) (A : Set V) : Set V :=
  {x | x ∉ A ∧ ∃ y ∈ A, G.Adj x y}

/-- The closure `Ā = A ∪ ∂A`. -/
def closureN (G : SimpleGraph V) (A : Set V) : Set V := A ∪ outerBoundary G A

end Graph

namespace Sandpile

open LatticeProb

variable {d : ℕ}

/-- The unit mass at `z`. -/
def dirac (z : Site d) : Site d → ℤ := fun x => if x = z then 1 else 0

/-- The sum of `u` over the `2d` neighbours of `x`, direction by direction. -/
def nbrSumZ (u : Site d → ℤ) (x : Site d) : ℤ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

/-- The lattice Laplacian `Δu(x) = ∑_{y∼x}(u(y)-u(x))`. -/
def lap (u : Site d → ℤ) (x : Site d) : ℤ := nbrSumZ u x - 2 * d * u x

end Sandpile

end LatticeProb

/-! ## The lattice `ℤ^d` and the continuum `ℝ^d` (paper Section 1.1; tex 151-203) -/

open LatticeProb
open scoped Pointwise Matrix

variable {d : ℕ}

/-- The continuum `ℝ^d`, with the Euclidean norm and Lebesgue measure (tex 151-160). -/
abbrev Rd (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The embedding `ℤ^d ⊂ ℝ^d`. -/
def toE (x : Site d) : Rd d := WithLp.toLp 2 (fun i => (x i : ℝ))

/-- The discrete boundary `∂A = {y ∈ ℤ^d ∖ A : ∃ x ∈ A, y ∼ x}` (tex 161-164). -/
def bdry (A : Set (Site d)) : Set (Site d) := Graph.outerBoundary (lattice d) A

/-- The discrete closure `Ā = A ∪ ∂A` (tex 165-168). -/
def dClosure (A : Set (Site d)) : Set (Site d) := Graph.closureN (lattice d) A

/-- The discrete Laplacian of a real function, `Δ_{ℤ^d} f(x) = ∑_{y ∼ x} (f(y) - f(x))`
(tex 195-197), written direction by direction as `∑_i (f(x + e_i) + f(x - e_i)) - 2d f(x)`. -/
def lapR (f : Site d → ℝ) (x : Site d) : ℝ := nbrSum f x - 2 * d * f x

/-- The lattice ball `B_r(x) = {y ∈ ℤ^d : |x - y|_2 < r}` (tex 181-184). -/
def ballZ (x : Site d) (r : ℝ) : Set (Site d) := {y | ‖toE y - toE x‖ < r}

/-- `B_r = B_r(0)` (tex 185). -/
def ballZ0 (r : ℝ) : Set (Site d) := ballZ 0 r

/-- The finite difference approximation `W_n = ℤ^d ∩ nW` of `W ⊆ ℝ^d` (tex 94). -/
def discretize (W : Set (Rd d)) (n : ℕ) : Set (Site d) := {x | toE x ∈ (n : ℝ) • W}

/-- The lattice point `[x]` attached to `x ∈ ℝ^d`, used in `v̄_n(x) = n⁻² v_n([nx])` (tex 98).
The paper never defines `[·]`; we take the coordinatewise floor `[x]_i = ⌊x_i⌋`. -/
def latticeRound (x : Rd d) : Site d := fun i => ⌊x i⌋

/-- `q_M(x) = ½ xᵀ M x` on `ℝ^d` (tex 159). -/
def qM (M : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) : ℝ :=
  (1 / 2 : ℝ) * (WithLp.ofLp x ⬝ᵥ M *ᵥ WithLp.ofLp x)

/-- `q_l(x) = l |x|² / (2d)` on `ℝ^d` (tex 159). -/
def ql (l : ℝ) (x : Rd d) : ℝ := l * ‖x‖ ^ 2 / (2 * d)

/-- `q_M` restricted to the lattice. -/
def qMZ (M : Matrix (Fin d) (Fin d) ℝ) (x : Site d) : ℝ := qM M (toE x)

/-- `q_l` restricted to the lattice. -/
def qlZ (l : ℝ) (x : Site d) : ℝ := ql l (toE x)

/-- The supergradient set `∂⁺(v, x, A) = {p ∈ ℝ^d : v(x) + p·(y - x) ≥ v(y) for all y ∈ Ā}`
(tex 427-430). -/
def supGrad (v : Site d → ℝ) (x : Site d) (A : Set (Site d)) : Set (Rd d) :=
  {p | ∀ y ∈ dClosure A, v y ≤ v x + inner ℝ p (toE y - toE x)}

/-- The subgradient set `∂⁻(v, x, A) = {p ∈ ℝ^d : v(x) + p·(y - x) ≤ v(y) for all y ∈ Ā}`
(tex 431-434). -/
def subGrad (v : Site d → ℝ) (x : Site d) (A : Set (Site d)) : Set (Rd d) :=
  {p | ∀ y ∈ dClosure A, v x + inner ℝ p (toE y - toE x) ≤ v y}

/-- `∂⁺(v, A) = ⋃_{x ∈ A} ∂⁺(v, x, A)` (tex 435-438). -/
def supGradSet (v : Site d → ℝ) (A : Set (Site d)) : Set (Rd d) := ⋃ x ∈ A, supGrad v x A

/-- `∂⁻(v, A) = ⋃_{x ∈ A} ∂⁻(v, x, A)`, the subgradient analogue of `supGradSet`. -/
def subGradSet (v : Site d → ℝ) (A : Set (Site d)) : Set (Rd d) := ⋃ x ∈ A, subGrad v x A

/-! ## Bounded Lipschitz domains (paper Section 1; tex 97-99) -/

/-- `W ⊆ ℝ^d` is a *bounded Lipschitz domain*: `W` is bounded, open and connected, and for every
boundary point `x₀ ∈ ∂W` there are a radius `r > 0`, a unit vector `e` (the vertical direction
after a rigid motion) and a Lipschitz function `γ`, such that inside the ball `B_r(x₀)` the set `W`
is exactly the region strictly above the graph of `γ`:
`W ∩ B_r(x₀) = {y ∈ B_r(x₀) : γ(z') < z·e}`, where `z = y - x₀` and `z' = z - (z·e) e`. -/
def IsLipschitzDomain (W : Set (Rd d)) : Prop :=
  Bornology.IsBounded W ∧ IsOpen W ∧ IsConnected W ∧
    ∀ x₀ ∈ frontier W, ∃ r : ℝ, 0 < r ∧ ∃ e : Rd d, ‖e‖ = 1 ∧
      ∃ (L : NNReal) (γ : Rd d → ℝ), LipschitzWith L γ ∧
        ∀ y ∈ Metric.ball x₀ r,
          (y ∈ W ↔ γ ((y - x₀) - inner ℝ (y - x₀) e • e) < inner ℝ (y - x₀) e)

/-! ## The random environment (paper Section 1.2; tex 205-228) -/

open MeasureTheory LatticeProb

/-- A configuration (initial sandpile) `η : ℤ^d → ℤ`, with the product σ-algebra generated by the
coordinate maps (tex 207-208). -/
abbrev Config (d : ℕ) : Type := Site d → ℤ

/-- The translation `T_y η(z) = η(y + z)` (tex 213-216). -/
def shift (y : Site d) (η : Config d) : Config d := fun z => η (y + z)

/-- A *random environment* (tex 205-224): a probability measure `P` on configurations which is
uniformly bounded, stationary and ergodic (tex 209-223). -/
structure RandomEnvironment (d : ℕ) where
  /-- The law `P` of the initial sandpile. -/
  P : Measure (Config d)
  /-- `P` is a probability measure. -/
  [isProb : IsProbabilityMeasure P]
  /-- The lower bound `η_min`. -/
  ηmin : ℤ
  /-- The upper bound `η_max`. -/
  ηmax : ℤ
  /-- Uniform boundedness (tex 209-211). -/
  bounded : ∀ x : Site d, ∀ᵐ η ∂P, ηmin ≤ η x ∧ η x ≤ ηmax
  /-- Stationarity (tex 218-220). -/
  stationary : ∀ y : Site d, MeasurePreserving (shift y) P P
  /-- Ergodicity (tex 221-223). -/
  ergodic : ∀ S : Set (Config d), MeasurableSet S → (∀ y : Site d, shift y ⁻¹' S = S) →
    P S = 0 ∨ P S = 1

attribute [instance] RandomEnvironment.isProb

/-- The mean density `E(η(0))` (tex 225-227). -/
def meanEta (P : Measure (Config d)) : ℝ := ∫ η, (η 0 : ℝ) ∂P

/-- *High density* `E(η(0)) > 2d - 1` (tex 225-227). -/
def HighDensity (P : Measure (Config d)) : Prop := 2 * (d : ℝ) - 1 < meanEta P

/-! ## Toppling functions, legal and stabilizing topplings (paper Section 2; tex 231-252) -/

open LatticeProb.Sandpile

/-- `u` is a *toppling function* on `Ā` (tex 231): a nonnegative integer function vanishing off
the discrete closure `Ā = A ∪ ∂A`. -/
def IsTopplingFn (A : Set (Site d)) (u : Site d → ℤ) : Prop :=
  (∀ x, 0 ≤ u x) ∧ ∀ x ∉ dClosure A, u x = 0

/-- `u` is *legal* for `η` in `A` (tex 232-240): for some `n ≥ 0` and sites
`x̂_1, …, x̂_n ∈ A`, `u = 1_{x̂_1} + ⋯ + 1_{x̂_n}` and each toppling happens at a site of `A`
that is unstable in the configuration reached so far. -/
def IsLegal (η : Site d → ℤ) (A : Set (Site d)) (u : Site d → ℤ) : Prop :=
  ∃ (n : ℕ) (x : Fin n → Site d), (∀ i, x i ∈ A) ∧
    (∀ i : Fin n,
      2 * (d : ℤ) ≤ lap (fun y => ∑ j ∈ Finset.Iio i, dirac (x j) y) (x i) + η (x i)) ∧
    u = fun y => ∑ i : Fin n, dirac (x i) y

/-- The set `𝓛(η, A)` of *locally legal* topplings for `η` in `A` (tex 243-248): toppling
functions `u = w + û` on `Ā` where `w = 0` in `A`, `û = 0` on `∂A`, and `û` is legal for
`Δ_{ℤ^d} w + η` in `A`. -/
def locLegal (η : Site d → ℤ) (A : Set (Site d)) : Set (Site d → ℤ) :=
  {u | ∃ w uh : Site d → ℤ, IsTopplingFn A w ∧ IsTopplingFn A uh ∧ u = w + uh ∧
    (∀ x ∈ A, w x = 0) ∧ (∀ x ∈ bdry A, uh x = 0) ∧ IsLegal (fun y => lap w y + η y) A uh}

/-- The set `𝓢(η, A)` of *stabilizing* topplings for `η` in `A` (tex 250-252): toppling
functions `v` on `Ā` with `Δ_{ℤ^d} v + η ≤ 2d - 1` in `A`. -/
def stabilizing (η : Site d → ℤ) (A : Set (Site d)) : Set (Site d → ℤ) :=
  {v | IsTopplingFn A v ∧ ∀ x ∈ A, lap v x + η x ≤ 2 * (d : ℤ) - 1}

/-! ## Perturbed sub- and supersolutions and the monotone quantities `μ`, `μ*` (paper Section 5; tex 447-462) -/

open MeasureTheory LatticeProb
open scoped ENNReal

/-- The set of *perturbed subsolutions* `S(A, η, l, M) = {u : Ā → ℕ : u ∈ 𝓛(η, A)} - (q_l + q_M)`
(tex 447-449). -/
def perturbedSub (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Set (Site d → ℝ) :=
  (fun u x => (u x : ℝ) - (qlZ l x + qMZ M x)) '' locLegal η A

/-- The set of *perturbed supersolutions* `S*(A, η, l, M) = {v : Ā → ℕ : v ∈ 𝓢(η, A)} - (q_l + q_M)`
(tex 450-452). -/
def perturbedSuper (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Set (Site d → ℝ) :=
  (fun v x => (v x : ℝ) - (qlZ l x + qMZ M x)) '' stabilizing η A

/-- The monotone quantity controlling subsolutions,
`μ(A, η, l, M) = sup {|∂⁺(w, A)| : w ∈ S(A, η, l, M)}` (tex 455-457), where `|·|` is Lebesgue
measure on `ℝ^d`. It is valued in `[0, ∞]`. -/
noncomputable def mu (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ℝ≥0∞ :=
  ⨆ w ∈ perturbedSub A η l M, volume (supGradSet w A)

/-- The monotone quantity controlling supersolutions,
`μ*(A, η, l, M) = sup {|∂⁻(w, A)| : w ∈ S*(A, η, l, M)}` (tex 458-461), valued in `[0, ∞]`. -/
noncomputable def muStar (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : ℝ≥0∞ :=
  ⨆ w ∈ perturbedSuper A η l M, volume (subGradSet w A)

/-! ## The effective operator `F̄_η` (paper Section 6; tex 781-790, 955-966) -/

open Filter

/-- The deterministic limit `μ(l, M)` of Lemma 5.5 (tex 781-785): the `P`-average of
`limsup_n μ(B_n, η, l, M) / |B_n|`, with `B_n = {|y|₂ < n}` the discrete ball (tex 174),
computed in `[0, ∞]`. -/
noncomputable def muBar (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (∫⁻ η, limsup (fun n : ℕ => mu (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P).toReal

/-- The deterministic limit `μ*(l, M)` of Lemma 5.5 (tex 786-789): the `P`-average of
`limsup_n μ*(B_n, η, l, M) / |B_n|`, computed in `[0, ∞]`. -/
noncomputable def muStarBar (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ℝ :=
  (∫⁻ η, limsup (fun n : ℕ => muStar (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P).toReal

/-- The set of levels `l ∈ ℝ` with `μ(l, M) = μ*(l, M)` (tex 958-960). -/
def muEqSet (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) : Set ℝ :=
  {l | muBar E l M = muStarBar E l M}

/-- The *effective operator* `F̄_η(M) = l_M`, the largest `l ∈ ℝ` with `μ(l, M) = μ*(l, M)`
(tex 958-966), written as `sSup (muEqSet E M)`. -/
noncomputable def effOp (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup (muEqSet E M)

/-- The single-source operator of Pegden and Smart (tex 106-111):
`F̄_0(M) = inf {s ∈ ℝ : ∃ u : ℤ^d → ℤ, ∀ y ∈ ℤ^d, Δ_{ℤ^d} u(y) ≤ 2d - 1 and
u(y) ≥ ½ yᵀ (M - s I) y}`. -/
noncomputable def effOp0 (d : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sInf {s : ℝ | ∃ u : Site d → ℤ, ∀ y : Site d,
    lap u y ≤ 2 * (d : ℤ) - 1 ∧ qMZ (M - s • (1 : Matrix (Fin d) (Fin d) ℝ)) y ≤ (u y : ℝ)}

/-! ## Viscosity-solution vocabulary (paper Sections 1, 7 and 9)

Test-function definitions of viscosity sub- and supersolutions in the style of Crandall, Ishii and
Lions (*User's guide to viscosity solutions*, Bull. AMS 27 (1992), Def. 2.2), and the notions of
convergence used in the main theorems. -/

open MeasureTheory Filter Topology Asymptotics
open scoped Matrix

/-- The Hessian matrix `D²φ(x)`: the `(i, j)` entry is the second Fréchet derivative
`D²φ(x)(eᵢ, eⱼ)`, with `eᵢ` the standard basis of `ℝ^d`. -/
def hessian (φ : Rd d → ℝ) (x : Rd d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- Second-order Taylor expansion with Peano remainder at `a`, with gradient `p` and matrix `X`:
`u(x) = u(a) + p·(x-a) + ½(x-a)ᵀX(x-a) + o(|x-a|²)` as `x → a`. -/
def HasSecondOrderTaylorAt (u : Rd d → ℝ) (a p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (fun x => u x - u a - inner ℝ p (x - a) - qM X (x - a)) =o[𝓝 a] fun x => ‖x - a‖ ^ 2

/-- "`u` is twice differentiable at `a`" in the sense of Pegden and Smart (Lemma 7.6): `u` admits
a second-order Taylor expansion with Peano remainder at `a` with some symmetric matrix `X`. -/
def PeanoTwiceDifferentiableAt (u : Rd d → ℝ) (a : Rd d) : Prop :=
  ∃ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ), X.IsSymm ∧ HasSecondOrderTaylorAt u a p X

/-- Degenerate ellipticity in the Crandall-Ishii-Lions convention: `F(Y) ≤ F(X)` whenever
`X ≤ Y` in the Loewner order (`Y - X` positive semidefinite), for symmetric `X`, `Y`. -/
def DegenerateElliptic (F : Matrix (Fin d) (Fin d) ℝ → ℝ) : Prop :=
  ∀ X Y : Matrix (Fin d) (Fin d) ℝ, X.IsSymm → Y.IsSymm → (Y - X).PosSemidef → F Y ≤ F X

/-- `F(D²u) ≥ 0` in `U` tested from above: whenever `φ` is `C²` near `x ∈ U` and `u - φ` has a
local maximum at `x`, then `0 ≤ F(D²φ(x))`. -/
def ViscFromAboveGE (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMax (fun y => u y - φ y) x →
    0 ≤ F (hessian φ x)

/-- `F(D²u) ≤ 0` in `U` tested from below: whenever `φ` is `C²` near `x ∈ U` and `u - φ` has a
local minimum at `x`, then `F(D²φ(x)) ≤ 0`. -/
def ViscFromBelowLE (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMin (fun y => u y - φ y) x →
    F (hessian φ x) ≤ 0

/-- `F(D²u) ≥ 0` in `U` tested from below: whenever `φ` is `C²` near `x ∈ U` and `u - φ` has a
local minimum at `x`, then `0 ≤ F(D²φ(x))`. For a degenerate elliptic `F` this is the
Crandall-Ishii-Lions viscosity supersolution property. -/
def ViscFromBelowGE (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMin (fun y => u y - φ y) x →
    0 ≤ F (hessian φ x)

/-- Weak-* convergence of `f n` to `s` in `L^∞(ℝ^d) = (L¹(ℝ^d))*` (Theorem 1.1, tex 113):
`∫ f n · g → ∫ s · g` for every Lebesgue-integrable `g : ℝ^d → ℝ`. -/
def WeakStarTendsto (f : ℕ → Rd d → ℝ) (s : Rd d → ℝ) : Prop :=
  ∀ g : Rd d → ℝ, Integrable g →
    Tendsto (fun n => ∫ x, f n x * g x) atTop (𝓝 (∫ x, s x * g x))

/-! ## The obstacle problem of Theorem 1.1 (paper tex 98-102; provisional correction [C3]) -/

/-- The constraint set of the obstacle problem of Theorem 1.1 (tex 100-102):
`{v ∈ C(ℝ^d) : v ≥ 0, F̄_η(D²v) ≥ 0 in W, F̄_0(D²v) ≤ 0 in ℝ^d}`, both differential inequalities
in the viscosity-supersolution sense (test functions touching from below). -/
def obstacleSet (E : RandomEnvironment d) (W : Set (Rd d)) : Set (Rd d → ℝ) :=
  {v | Continuous v ∧ 0 ≤ v ∧ ViscFromBelowGE (effOp E) W v ∧
    ViscFromBelowLE (effOp0 d) Set.univ v}

/-- The solution `v̄ = min obstacleSet` of the obstacle problem of Theorem 1.1 (tex 100), defined
as the pointwise infimum `v̄(x) = inf {v(x) : v ∈ obstacleSet E W}` (junk value `0` if the set is
empty). That the infimum is attained is part of Theorem 1.1. -/
def obstacleSolution (E : RandomEnvironment d) (W : Set (Rd d)) : Rd d → ℝ :=
  fun x => sInf ((fun v : Rd d → ℝ => v x) '' obstacleSet E W)

/-! ## Odometers and stabilized sandpiles (paper Theorem 1.1, tex 96-113, 1026-1031) -/

open LatticeProb.Sandpile

/-- The pointwise infimum `x ↦ inf {u(x) : u ∈ S}` of a set `S` of nonnegative integer functions,
computed in `ℕ` (so it is `0` at every site when `S = ∅`). -/
def pointwiseInf (S : Set (Site d → ℤ)) : Site d → ℤ :=
  fun x => ((sInf {n : ℕ | ∃ u ∈ S, u x = n} : ℕ) : ℤ)

/-- The odometer `v_n` of `η` on `W_n` with the *free* boundary condition (tex 96, 1026-1031):
`v_n = min {v : ℤ^d → ℕ : Δ_{ℤ^d} v + η 1_{W_n} ≤ 2d - 1}`. Junk value `0` if the class is
empty. -/
def freeOdometer (η : Site d → ℤ) (Wn : Set (Site d)) : Site d → ℤ :=
  pointwiseInf (stabilizing (Wn.indicator η) Set.univ)

/-- The stable sandpile `s_n = η 1_{W_n} + Δ_{ℤ^d} v_n` (tex 96, 113) reached from `η · 1_{W_n}`
with the free boundary condition. -/
def freeSandpile (η : Site d → ℤ) (Wn : Set (Site d)) : Site d → ℤ :=
  fun x => Wn.indicator η x + lap (freeOdometer η Wn) x

/-- The rescaled odometer `v̄_n(x) = n⁻² v_n([nx])` (tex 99, 1031, 1576). -/
def rescaleOdo (v : Site d → ℤ) (n : ℕ) : Rd d → ℝ :=
  fun x => (v (latticeRound ((n : ℝ) • x)) : ℝ) / (n : ℝ) ^ 2

/-- The rescaled sandpile `s̄_n(x) = s_n([nx])` (tex 113), real-valued so that its weak-* limit in
`L^∞(ℝ^d)` and the integral `∫ s̄_n` make sense. -/
def rescaleSandpile (s : Site d → ℤ) (n : ℕ) : Rd d → ℝ :=
  fun x => (s (latticeRound ((n : ℝ) • x)) : ℝ)

/-! ## Literature inputs (the five hypotheses of the theorem; none is assumed inside the vocabulary) -/

/-- **Alexandrov's theorem** (input IR9): for a convex `f : ℝⁿ → ℝ`, almost every point admits a
second-order Peano expansion with gradient `Df(x)` and a symmetric matrix `D²f(x)`. -/
def AlexandrovStmt : Prop :=
  ∀ (d : ℕ) (f : Rd d → ℝ), ConvexOn ℝ Set.univ f →
    ∀ᵐ x ∂(volume : Measure (Rd d)), ∃ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ),
      X.IsSymm ∧ HasSecondOrderTaylorAt f x p X

/-- `u` is a weak solution of `Δu = s` in the open set `U` (Pegden-Smart (2.1)):
`∫ u Δφ = ∫ s φ` for every smooth compactly supported `φ` with support in `U`, `Δφ = tr D²φ`. -/
def IsWeakSolutionLaplace (U : Set (Rd d)) (u s : Rd d → ℝ) : Prop :=
  ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x, u x * Matrix.trace (hessian φ x) = ∫ x, s x * φ x

/-- **Pegden-Smart, Proposition 2.5** (input IR2; PS13, cited to Caffarelli-Cabré, Theorem 3.2):
if `s ∈ L^∞(B_1)` and `u ∈ C(B̄_1)` is a weak solution of `Δu = s` in `B_1`, and
`sup_{B_1} u > sup_{∂B_1} u`, then the set of `x ∈ B_1` with `u(x) > sup_{∂B_1} u`, `u`
twice differentiable at `x` and `D²u(x) < 0` has positive measure. -/
def PegdenSmartProp25Stmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ s u : Rd d → ℝ,
    MemLp s ⊤ (volume.restrict (Metric.ball (0 : Rd d) 1)) →
    ContinuousOn u (Metric.closedBall 0 1) →
    IsWeakSolutionLaplace (Metric.ball 0 1) u s →
    sSup (u '' Metric.sphere 0 1) < sSup (u '' Metric.ball 0 1) →
      0 < volume {x : Rd d | x ∈ Metric.ball 0 1 ∧ sSup (u '' Metric.sphere 0 1) < u x ∧
        ∃ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ),
          X.IsSymm ∧ HasSecondOrderTaylorAt u x p X ∧ (-X).PosDef}

/-- **Pegden-Smart, Proposition 2.4** (input IR2; PS13, cited to Christ, Theorem III.4): if
`s ∈ L^∞(B_1)` and `u ∈ C(B_1)` is a weak solution of `Δu = s` in `B_1`, then `u` is twice
differentiable (in the Peano sense) at almost every point of `B_1`. -/
def PegdenSmartProp24Stmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ s u : Rd d → ℝ,
    MemLp s ⊤ (volume.restrict (Metric.ball (0 : Rd d) 1)) →
    ContinuousOn u (Metric.ball 0 1) →
    IsWeakSolutionLaplace (Metric.ball 0 1) u s →
      ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Rd d) 1)), PeanoTwiceDifferentiableAt u x

/-- Viscosity solutions of `|Δu| ≤ K` are weak solutions of `Δu = s` with `|s| ≤ K` (input,
Ishii 1995): a continuous `u` that is a viscosity subsolution of `Δu ≥ -K` and a viscosity
supersolution of `Δu ≤ K` in `U` is a weak solution of `Δu = s` for a measurable `s` with
`|s| ≤ K`. -/
def ViscosityWeakLaplaceStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ U : Set (Rd d), IsOpen U → U.Nonempty → ∀ (K : ℝ) (u : Rd d → ℝ),
    ContinuousOn u U →
    ViscFromAboveGE (fun X => X.trace + K) U u → ViscFromBelowLE (fun X => X.trace - K) U u →
      ∃ s : Rd d → ℝ, Measurable s ∧ (∀ x, |s x| ≤ K) ∧ IsWeakSolutionLaplace U u s

/-- **Lawler-Limic, difference estimate for discrete harmonic functions** (input): for `d ≥ 1`
there is `C` such that for `n ≥ 1`, `f : ℤ^d → ℝ` with `Δ_{ℤ^d} f = 0` on `B_n` and `|f| ≤ M`
on `B̄_n`, and every direction `i`, `|f(e_i) - f(0)| ≤ C M / n`. -/
def LawlerLimicHarmonicDifferenceStmt : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (f : Site d → ℝ) (M : ℝ),
    (∀ z ∈ ballZ0 (n : ℝ), lapR f z = 0) → (∀ z ∈ dClosure (ballZ0 (n : ℝ)), |f z| ≤ M) →
      ∀ i : Fin d, |f (unit i) - f 0| ≤ C * M / n

/-! ## Theorem 1.1: the main theorem on the free-boundary odometers -/

/-- **Theorem 1.1** (paper tex 96-121), with the provisional correction [C3] (the obstacle
inequality for `F̄_η` is tested from below) and the correction [C12] (the support
radius `R` depends on `d`, `W` and `η_max`, chosen before the environment).

Let `η` be stationary, ergodic and bounded with `E η(0) > 2d - 1`, `W ⊂ ℝ^d` a bounded Lipschitz
domain, `v_n` the free-boundary odometer of `η 1_{W_n}` and `s_n` the stable sandpile. Then:

1. `F̄_η` is a nonrandom, degenerate elliptic operator.
2. The obstacle problem has a unique least solution `v̄`: `IsLeast (obstacleSet E W) (obstacleSolution E W)`.
3. Almost surely the odometers are finite and the rescaled odometers `n⁻² v_n([nx])` converge
   uniformly on `ℝ^d` to `v̄`.
4. There is a deterministic `s ∈ L^∞(ℝ^d)` with the rescaled sandpiles converging weakly-* to `s`,
   `∫ s = |W| E η(0)`, `s ≤ 2d - 1`, `s = 0` outside the `R`-neighbourhood of `W`, and
   `∫ s φ = ∫ v̄ Δφ + E η(0) ∫_W φ` for every smooth compactly supported `φ`. -/
def MainTheoremStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ ηmax : ℤ, ∃ R : ℝ, 0 < R ∧
    ∀ E : RandomEnvironment d, E.ηmax = ηmax → HighDensity E.P →
      DegenerateElliptic (effOp E) ∧
      IsLeast (obstacleSet E W) (obstacleSolution E W) ∧
      (∀ᵐ η ∂E.P,
        (∀ n : ℕ, (stabilizing ((discretize W n).indicator η) Set.univ).Nonempty) ∧
          TendstoUniformly (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n)
            (obstacleSolution E W) atTop) ∧
      ∃ s : Rd d → ℝ, MemLp s ⊤ volume ∧
        (∀ᵐ η ∂E.P,
          WeakStarTendsto (fun n : ℕ => rescaleSandpile (freeSandpile η (discretize W n)) n) s) ∧
        ∫ x, s x = (volume W).toReal * meanEta E.P ∧
        (∀ᵐ x ∂volume, s x ≤ 2 * (d : ℝ) - 1) ∧
        (∀ᵐ x ∂volume, x ∉ Metric.thickening R W → s x = 0) ∧
        ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, s x * φ x =
            (∫ x, obstacleSolution E W x * Matrix.trace (hessian φ x)) +
              meanEta E.P * ∫ x in W, φ x
-- VOCABULARY-END

/-- **Theorem 1.1.** From the five literature inputs, the restated main statement holds. -/
theorem mainTheorem
    (hAlexandrov : AlexandrovStmt)
    (hLawlerLimicHarmonicDifference : LawlerLimicHarmonicDifferenceStmt)
    (hPS25 : PegdenSmartProp25Stmt)
    (hPS24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) :
    MainTheoremStmt := sorry

end

end RandomSandpile.StatementAudit.MainTheorem

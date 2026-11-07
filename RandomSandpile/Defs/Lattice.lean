import Mathlib
import LatticeProb.Sandpile.Toppling
import LatticeProb.Graph.Boundary

/-!
# The lattice `ℤ^d` and the continuum `ℝ^d`: notation of Section 1.1

Notation and conventions of `paper/random_piles-corrected.tex`, together with the
finite difference approximation `W_n = ℤ^d ∩ nW`, the lattice rounding `[nx]`
and the supergradient and subgradient sets of Section 3.

Reused from Lattice-Probability:

* `LatticeProb.Site d = Fin d → ℤ`, the unit vectors `LatticeProb.unit i = e_i`, the
  nearest-neighbour graph `LatticeProb.lattice d` and the real neighbour sum
  `LatticeProb.nbrSum` (`LatticeProb/Site.lean`);
* the integer discrete Laplacian `LatticeProb.Sandpile.lap` and the unit toppling
  `LatticeProb.Sandpile.dirac` (`LatticeProb/Sandpile/Toppling.lean`);
* the outer boundary and closure `LatticeProb.Graph.outerBoundary`, `LatticeProb.Graph.closureN`
  (`LatticeProb/Graph/Boundary.lean`).

The continuum `ℝ^d` is `EuclideanSpace ℝ (Fin d)`: its norm is the Euclidean norm `|x|_2` and its
`volume` is Lebesgue measure. A site is sent into `ℝ^d` by `toE`.
-/

noncomputable section

open LatticeProb
open scoped Pointwise Matrix

namespace RandomSandpile

variable {d : ℕ}

/-- The continuum `ℝ^d`, with the Euclidean norm and Lebesgue measure. -/
abbrev Rd (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The embedding `ℤ^d ⊂ ℝ^d`. -/
def toE (x : Site d) : Rd d := WithLp.toLp 2 (fun i => (x i : ℝ))

@[simp] theorem toE_apply (x : Site d) (i : Fin d) : toE x i = (x i : ℝ) := rfl

/-! ### Neighbours, boundary and closure -/

/-- `y ∼ x`: `y - x` is an integer vector with `|y - x| = 1`, that is, `y = x ± e_i`
for some coordinate direction `i`. This is the adjacency of `LatticeProb.lattice d`; its
`ℓ¹` characterization is `adj_iff_sum_abs`. -/
def Adj (x y : Site d) : Prop := (lattice d).Adj x y

/-- The discrete boundary `∂A = {y ∈ ℤ^d ∖ A : ∃ x ∈ A, y ∼ x}`. -/
def bdry (A : Set (Site d)) : Set (Site d) := Graph.outerBoundary (lattice d) A

/-- The discrete closure `Ā = A ∪ ∂A`. -/
def dClosure (A : Set (Site d)) : Set (Site d) := Graph.closureN (lattice d) A

theorem mem_bdry {A : Set (Site d)} {y : Site d} : y ∈ bdry A ↔ y ∉ A ∧ ∃ x ∈ A, Adj y x :=
  Iff.rfl

theorem dClosure_eq (A : Set (Site d)) : dClosure A = A ∪ bdry A := rfl

theorem bdry_disjoint (A : Set (Site d)) : Disjoint A (bdry A) :=
  Set.disjoint_left.2 fun _ hx hy => hy.1 hx

theorem subset_dClosure (A : Set (Site d)) : A ⊆ dClosure A := Set.subset_union_left

theorem bdry_subset_dClosure (A : Set (Site d)) : bdry A ⊆ dClosure A := Set.subset_union_right

/-- `y ∼ x` exactly when `y - x` has `ℓ¹` norm `1` (for integer vectors this is the paper's
Euclidean condition `|y - x|_2 = 1`). -/
theorem adj_iff_sum_abs {x y : Site d} : Adj x y ↔ ∑ i, |y i - x i| = 1 := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · subst hi
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [unit, hj]) (by simp)]
      simp [unit]
    · subst hi
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [unit, hj]) (by simp)]
      simp [unit]
  · intro h
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, |y i - x i| ≠ 0 := by
      by_contra! h0
      rw [Finset.sum_eq_zero h0] at h
      exact zero_ne_one h
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => |y j - x j|) (Finset.mem_univ i)
    have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, |y j - x j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg _
    have hpos : 0 < |y i - x i| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hi)
    have hone : |y i - x i| = 1 := by omega
    have hzero : ∑ j ∈ Finset.univ.erase i, |y j - x j| = 0 := by omega
    have hoff : ∀ j, j ≠ i → y j = x j := fun j hj => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => abs_nonneg (y k - x k))).1 hzero j
        (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
      rw [abs_eq_zero, sub_eq_zero] at this
      exact this
    refine ⟨i, ?_⟩
    rcases abs_eq (zero_le_one' ℤ) |>.1 hone with h1 | h1
    · left
      funext j
      by_cases hj : j = i
      · subst hj; simp [unit]; omega
      · simp [unit, hj, hoff j hj]
    · right
      funext j
      by_cases hj : j = i
      · subst hj; simp [unit]; omega
      · simp [unit, hj, hoff j hj]

/-! ### Discrete Laplacian and second differences -/

/-- The discrete Laplacian of a real function, `Δ_{ℤ^d} f(x) = ∑_{y ∼ x} (f(y) - f(x))`, written direction by direction as `∑_i (f(x + e_i) + f(x - e_i)) - 2d f(x)`,
exactly as the integer Laplacian `LatticeProb.Sandpile.lap` (`lapR_intCast`). For `d ≥ 1` it is
`LatticeProb.Graph.laplacian (lattice d)` (`LatticeProb.laplacian_eq_nbrSum_sub`,
`LatticeProb/Walk/Harnack/Basics.lean`). -/
def lapR (f : Site d → ℝ) (x : Site d) : ℝ := nbrSum f x - 2 * d * f x

/-- The discrete second difference `Δ_i f(x) = f(x + e_i) + f(x - e_i) - 2 f(x)`. -/
def secondDiff (i : Fin d) (f : Site d → ℝ) (x : Site d) : ℝ :=
  f (x + unit i) + f (x - unit i) - 2 * f x

theorem lapR_eq_sum_secondDiff (f : Site d → ℝ) (x : Site d) :
    lapR f x = ∑ i, secondDiff i f x := by
  simp only [lapR, nbrSum, secondDiff, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The real Laplacian of an integer function is the integer Laplacian. -/
theorem lapR_intCast (u : Site d → ℤ) (x : Site d) :
    lapR (fun y => (u y : ℝ)) x = (Sandpile.lap u x : ℝ) := by
  simp [lapR, Sandpile.lap, Sandpile.nbrSumZ, nbrSum]

/-! ### Balls and cubes -/

/-- The lattice ball `B_r(x) = {y ∈ ℤ^d : |x - y|_2 < r}`. -/
def ballZ (x : Site d) (r : ℝ) : Set (Site d) := {y | ‖toE y - toE x‖ < r}

/-- The lattice cube `Q_r(x) = {y ∈ ℤ^d : |x - y|_∞ < r}`; the paper mostly uses an
integer radius `r = n`, which is a special case. -/
def cubeZ (x : Site d) (r : ℝ) : Set (Site d) := {y | ∀ i, |((y i - x i : ℤ) : ℝ)| < r}

/-- `B_r = B_r(0)`. -/
def ballZ0 (r : ℝ) : Set (Site d) := ballZ 0 r

/-- `Q_r = Q_r(0)`. -/
def cubeZ0 (r : ℝ) : Set (Site d) := cubeZ 0 r

/-- The continuum cube `Q_r(x) = {y ∈ ℝ^d : |x - y|_∞ < r}`; continuum balls are
`Metric.ball x r`. -/
def cubeR (x : Rd d) (r : ℝ) : Set (Rd d) := {y | ∀ i, |y i - x i| < r}

/-! ### Discretization and rescaling (98) -/

/-- The finite difference approximation `W_n = ℤ^d ∩ nW` of `W ⊆ ℝ^d`. -/
def discretize (W : Set (Rd d)) (n : ℕ) : Set (Site d) := {x | toE x ∈ (n : ℝ) • W}

/-- The lattice point `[x]` attached to `x ∈ ℝ^d`, used in `v̄_n(x) = n⁻² v_n([nx])`.

The paper never defines `[·]`. At it is applied to `nx ∈ ℝ^d` and the result is fed to
`v_n : ℤ^d → ℕ`, so it is a map `ℝ^d → ℤ^d`; we take the coordinatewise floor
`[x]_i = ⌊x_i⌋`. Tex 1031 calls `v̄_n` the "rescaled linear interpolation" of `v_n`, a second
reading (piecewise-linear interpolation of `v_n` between lattice points). The two readings, and the
nearest-point rounding, differ by `n⁻² · O(n)` on compact sets wherever `v_n` has gradient `O(n)`,
so the uniform limits stated in the paper are the same for all of them. -/
def latticeRound (x : Rd d) : Site d := fun i => ⌊x i⌋

/-! ### Quadratics -/

/-- `q_M(x) = ½ xᵀ M x` on `ℝ^d`. Symmetry of `M` is a hypothesis of statements. -/
def qM (M : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) : ℝ :=
  (1 / 2 : ℝ) * (WithLp.ofLp x ⬝ᵥ M *ᵥ WithLp.ofLp x)

/-- `q_l(x) = l |x|² / (2d)` on `ℝ^d`. -/
def ql (l : ℝ) (x : Rd d) : ℝ := l * ‖x‖ ^ 2 / (2 * d)

/-- `q_M` restricted to the lattice. -/
def qMZ (M : Matrix (Fin d) (Fin d) ℝ) (x : Site d) : ℝ := qM M (toE x)

/-- `q_l` restricted to the lattice. -/
def qlZ (l : ℝ) (x : Site d) : ℝ := ql l (toE x)

/-! ### Supergradient and subgradient sets -/

/-- The supergradient set `∂⁺(v, x, A) = {p ∈ ℝ^d : v(x) + p·(y - x) ≥ v(y) for all y ∈ Ā}`
. The paper takes `v : ℤ^d → ℤ`; integer functions enter through the cast. -/
def supGrad (v : Site d → ℝ) (x : Site d) (A : Set (Site d)) : Set (Rd d) :=
  {p | ∀ y ∈ dClosure A, v y ≤ v x + inner ℝ p (toE y - toE x)}

/-- The subgradient set `∂⁻(v, x, A) = {p ∈ ℝ^d : v(x) + p·(y - x) ≤ v(y) for all y ∈ Ā}`
. -/
def subGrad (v : Site d → ℝ) (x : Site d) (A : Set (Site d)) : Set (Rd d) :=
  {p | ∀ y ∈ dClosure A, v x + inner ℝ p (toE y - toE x) ≤ v y}

/-- `∂⁺(v, A) = ⋃_{x ∈ A} ∂⁺(v, x, A)`. -/
def supGradSet (v : Site d → ℝ) (A : Set (Site d)) : Set (Rd d) := ⋃ x ∈ A, supGrad v x A

/-- `∂⁻(v, A) = ⋃_{x ∈ A} ∂⁻(v, x, A)`, the subgradient analogue of `supGradSet`. -/
def subGradSet (v : Site d → ℝ) (A : Set (Site d)) : Set (Rd d) := ⋃ x ∈ A, subGrad v x A

end RandomSandpile

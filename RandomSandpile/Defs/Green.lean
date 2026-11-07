import RandomSandpile.Defs.Environment
import LatticeProb.Walk.Harnack.Basics

/-!
# The Green's function of simple random walk killed on exiting a set (Sections 7.2 and 8.2)

`paper/random_piles-corrected.tex` (Lemma 7.3, on the balls `B_n`) and 1497-1511
(Lemma 8.1, on the discretized domains `W_n`).

For `A ⊆ ℤ^d`, let `S_t^{(x)}` be simple random walk on `ℤ^d` started at `x` and
`τ_A = min{t ≥ 0 : S_t^{(x)} ∉ A}` its exit time from `A`. The Green's function of the walk killed
on exiting `A` is
`g_A(x,y) = (2d)⁻¹ E ∑_{t < τ_A} 1{S_t^{(x)} = y}` (`greenKilled`).

The factor `(2d)⁻¹` makes `g_A(·,y)` the Green's function of the discrete Laplacian
`Δ_{ℤ^d} f(x) = ∑_{y ∼ x} (f(y) - f(x))` (`lapR`), not of the generator `(2d)⁻¹ Δ_{ℤ^d}` of the walk:
for finite `A` and `d ≥ 1`, `Δ_{ℤ^d} g_A(·,y) = -1{· = y}` in `A` (`lapR_greenKilled`) and
`g_A(x,·) = 0` for `x ∉ A`. Hence the Green potential `∑_{y ∈ A} g_A(·,y) f(y)` (`greenPotential`)
solves `Δ_{ℤ^d} u = -f` in `A` with `u = 0` off `A` (`lapR_greenPotential`,
`greenPotential_eq_zero_of_not_mem`). For `A = B_n`, `f = η` and `f ≡ E η(0)` these are the
functions `r_n`, `d_n`, with `Δ r_n = -η`, `Δ d_n = -E η(0)` in `B_n` and
`r_n = d_n = 0` on `∂B_n`, as.

Reused from Lattice-Probability: `LatticeProb.Graph.killedGreenReal G C x y`, the real value of
`(∑_k p^C_k(x,y)) / deg(y)`, where `p^C_k(x,y) = P_x(S_0, …, S_k ∈ C, S_k = y)` is the `k`-step
kernel of the walk killed on leaving `C` (`LatticeProb.Graph.killedHeat`,
`LatticeProb/Graph/Basic.lean`). On `ℤ^d` every degree is `2d` and
`∑_k p^C_k(x,y) = E ∑_{t < τ_C} 1{S_t^{(x)} = y}`, so this is `g_C(x,y)` with the paper's
normalisation. The value is the `toReal` of an element of `[0, ∞]`; it is finite (and the
`toReal` is faithful) for finite `C` in `d ≥ 1`, which covers `B_n` and `W_n` for bounded `W`. The
Poisson equation is `LatticeProb.Network.laplacian_killedGreenReal`, used through
`LatticeProb.nbrSum_harnackGreen_eq` (`LatticeProb/Walk/Harnack/Basics.lean`).
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

variable {d : ℕ}

/-! ### The killed Green's function -/

/-- The Green's function of simple random walk killed on exiting `A` (1504),
`g_A(x,y) = (2d)⁻¹ E ∑_{t < τ_A} 1{S_t^{(x)} = y}`, `τ_A = min{t ≥ 0 : S_t^{(x)} ∉ A}`. With the
normalisation `(2d)⁻¹` it inverts `-Δ_{ℤ^d}` in `A` (`lapR_greenKilled`). The paper writes `g_n`
for `g_{B_n}` (Section 7) and for `g_{W_n}` (Section 8). -/
def greenKilled (A : Set (Site d)) (x y : Site d) : ℝ :=
  Graph.killedGreenReal (lattice d) A x y

/-- `g_A(x,y) = 0` when the walk starts outside `A` (`τ_A = 0`). -/
theorem greenKilled_eq_zero_of_not_mem_left (A : Set (Site d)) {x : Site d} (hx : x ∉ A)
    (y : Site d) : greenKilled A x y = 0 := by
  have h : ∀ k, Graph.killedHeat (lattice d) A k x y = 0 := by
    intro k
    cases k <;> simp [Graph.killedHeat, hx]
  simp [greenKilled, Graph.killedGreenReal, Graph.killedGreen, h]

/-- On a finite set, `g_A(x,y)` is Lattice-Probability's `harnackGreen` (pole in the second slot),
by the symmetry `g_A(x,y) = g_A(y,x)` of the killed Green's function. -/
theorem greenKilled_eq_harnackGreen (hd : 1 ≤ d) (B : Finset (Site d)) (x y : Site d) :
    greenKilled (B : Set (Site d)) x y = harnackGreen B x y := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := exists_not_mem_finset hd B
  exact Network.killedGreenReal_symm (Graph.Zd.latticeConnected d) B hq x y

/-- `g_A(x,y) = 0` when `y ∉ A`, for finite `A`. -/
theorem greenKilled_eq_zero_of_not_mem_right (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite)
    (x : Site d) {y : Site d} (hy : y ∉ A) : greenKilled A x y = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨B, rfl⟩ := hA.exists_finset_coe
  obtain ⟨q, hq⟩ := exists_not_mem_finset hd B
  exact Network.killedGreenReal_eq_zero_of_not_mem (Graph.Zd.latticeConnected d) B hq
    (by exact_mod_cast hy) x

/-- The killed Green's function is nonnegative. -/
theorem greenKilled_nonneg (A : Set (Site d)) (x y : Site d) : 0 ≤ greenKilled A x y :=
  ENNReal.toReal_nonneg

/-- **The Poisson equation for the killed Green's function.** For finite `A`, `d ≥ 1` and
`x ∈ A`, `Δ_{ℤ^d} g_A(·,y)(x) = -1{x = y}`. -/
theorem lapR_greenKilled (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) {x : Site d}
    (hx : x ∈ A) (y : Site d) :
    lapR (fun z => greenKilled A z y) x = -(if x = y then 1 else 0) := by
  obtain ⟨B, rfl⟩ := hA.exists_finset_coe
  have hxB : x ∈ B := by exact_mod_cast hx
  by_cases hy : y ∈ B
  · have hfun : (fun z => greenKilled (B : Set (Site d)) z y) = fun z => harnackGreen B z y :=
      funext fun z => greenKilled_eq_harnackGreen hd B z y
    rw [hfun, lapR, nbrSum_harnackGreen_eq hd B hxB hy]
    ring
  · have hfun : (fun z => greenKilled (B : Set (Site d)) z y) = fun _ => 0 :=
      funext fun z => greenKilled_eq_zero_of_not_mem_right hd hA z (by exact_mod_cast hy)
    have hxy : x ≠ y := fun h => hy (h ▸ hxB)
    rw [hfun]
    simp [lapR, nbrSum, hxy]

/-! ### Green potentials (1504-1511) -/

/-- The Green potential `u(x) = ∑_{y ∈ A} g_A(x,y) f(y)` of `f` in `A`. For finite `A` it solves
`Δ_{ℤ^d} u = -f` in `A` (`lapR_greenPotential`) and `u = 0` off `A`
(`greenPotential_eq_zero_of_not_mem`). The sum is a `finsum`, the honest finite sum for finite
`A`. -/
def greenPotential (A : Set (Site d)) (f : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ᶠ y ∈ A, greenKilled A x y * f y

theorem greenPotential_coe_finset (B : Finset (Site d)) (f : Site d → ℝ) (x : Site d) :
    greenPotential (B : Set (Site d)) f x = ∑ y ∈ B, greenKilled (B : Set (Site d)) x y * f y :=
  finsum_mem_coe_finset _ _

/-- The Green potential vanishes off `A`; in particular on `∂A`. -/
theorem greenPotential_eq_zero_of_not_mem (A : Set (Site d)) (f : Site d → ℝ) {x : Site d}
    (hx : x ∉ A) : greenPotential A f x = 0 := by
  simp [greenPotential, greenKilled_eq_zero_of_not_mem_left A hx]

/-- **The Poisson equation for the Green potential**: for finite `A`, `d ≥ 1` and
`x ∈ A`, `Δ_{ℤ^d} (∑_{y ∈ A} g_A(·,y) f(y))(x) = -f(x)`. -/
theorem lapR_greenPotential (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) (f : Site d → ℝ)
    {x : Site d} (hx : x ∈ A) : lapR (greenPotential A f) x = -f x := by
  obtain ⟨B, rfl⟩ := hA.exists_finset_coe
  have hxB : x ∈ B := by exact_mod_cast hx
  have hfun : greenPotential (B : Set (Site d)) f = fun z => ∑ y ∈ B, harnackGreen B z y * f y :=
    funext fun z => by
      rw [greenPotential_coe_finset]
      exact Finset.sum_congr rfl fun y _ => by rw [greenKilled_eq_harnackGreen hd B z y]
  rw [hfun, lapR, nbrSum_sum_mul,
    Finset.sum_congr rfl fun y hy => by rw [nbrSum_harnackGreen_eq hd B hxB hy]]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    if_pos hxB, Finset.mul_sum, mul_assoc]
  ring

/-- `r_n(x) = ∑_{y ∈ B_n} g_n(x,y) η(y)`, for an integer configuration `η`, the
Green potential of `η` in the ball `B_n = ballZ0 n`. It is the random function of Lemma 7.3. -/
def greenPotentialBall (n : ℕ) (η : Config d) : Site d → ℝ :=
  greenPotential (ballZ0 n) fun y => (η y : ℝ)

/-- `d_n(x) = ∑_{y ∈ B_n} g_n(x,y) E(η(0))`, the Green potential in `B_n` of the
constant `m`; the paper takes `m = E(η(0))` (`meanEta`). -/
def greenPotentialBallMean (n : ℕ) (m : ℝ) : Site d → ℝ :=
  greenPotential (ballZ0 n) fun _ => m

/-- `r_n(x) = ∑_{y ∈ W_n} g_n(x,y) η(y)`, for a real configuration `η`, the Green
potential of `η` in `W_n = ℤ^d ∩ nW` (`discretize W n`), with `g_n = g_{W_n}`. It is the random
function of Lemma 8.1. -/
def greenPotentialDomain (W : Set (Rd d)) (n : ℕ) (η : Site d → ℝ) : Site d → ℝ :=
  greenPotential (discretize W n) η

/-- `d_n(x) = ∑_{y ∈ W_n} g_n(x,y) η_avg`, the Green potential in `W_n` of the
constant `m`; the paper takes `m = η_avg = E η(0)` (`meanEtaReal`, `Defs/Divisible.lean`). -/
def greenPotentialDomainMean (W : Set (Rd d)) (n : ℕ) (m : ℝ) : Site d → ℝ :=
  greenPotential (discretize W n) fun _ => m

end RandomSandpile

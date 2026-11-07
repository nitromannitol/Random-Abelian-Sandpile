import RandomSandpile.Defs.Divisible
import RandomSandpile.Defs.Domain

/-! # Section 8: convergence of the random divisible sandpile — statements

Statements (`...Stmt : Prop`) of the numbered results of Section 8 of the paper
:

* `DivisibleLeastActionStmt` (Proposition 8.1, cited from Levine-Peres): the odometer of the
  divisible sandpile in a finite `V ⊂ ℤ^d` is the least nonnegative supersolution of
  `Δ_{ℤ^d} f + η ≤ 1` in `V`;
* `DivisibleHomogenizeDomainStmt` (Lemma 8.1): almost surely, the Green potentials `r_n`, `d_n` of
  `η` and of `η_avg = E η(0)` in `W_n = ℤ^d ∩ nW` satisfy `sup_{W̄_n} |r_n - d_n| ≤ ε C_d n²` for
  `n` large;
* `DivisibleTheoremStmt` (Theorem 8.2): almost surely the rescaled odometers `v̄_n`, `v̄_{avg_n}`
  converge uniformly together on `n⁻¹ W̄_n`.

Every statement carries the standing assumption `d ≥ 2`. The random statements quantify
over a `RealRandomEnvironment d` (: real, uniformly bounded, stationary, ergodic; no
high density). `W` is a bounded Lipschitz domain (`IsLipschitzDomain`, which includes
boundedness), fixed before the event of full probability, and `W̄_n = W_n ∪ ∂W_n` is
`dClosure (discretize W n)`.

Normalisation (see the module docstring of `Defs/Divisible.lean`): the odometer `divOdometer`
is the mass emitted by a site to each of its `2d` neighbours (the printed text, says
"total mass emitted", which is `2d` times this); this is the normalisation in which the printed
least action principle `Δ_{ℤ^d} f + η ≤ 1`, with the unnormalised Laplacian, holds.
Theorem 8.2 is invariant under this rescaling. The stability threshold `1` of Proposition 8.1 is
the divisible-sandpile threshold (a site is unstable iff its mass exceeds `1`). -/

open MeasureTheory LatticeProb Filter Topology

namespace RandomSandpile

/-- Proposition 8.1 (prop:div_lap; Proposition 2.5 in Levine-Peres
[levine2016divisible]), the least action principle for the divisible sandpile. Begin with a
distribution of mass `η : V → ℝ` on `V ⊂ ℤ^d`; its odometer `v` satisfies
`v = min {f : V̄ → ℝ⁺ : Δ_{ℤ^d} f + η ≤ 1 in V}`.

Reading. `v = divOdometer V η` is the odometer of parallel toppling in `V` with sinks off `V`
. `V` is finite: the result is applied to `V = W_n`, and it fails for
`V = ℤ^d` (e.g. `η ≡ 2` never stabilizes). The class is `divLeastActionSet V η`: `f ≥ 0` on all
of `ℤ^d` instead of on `V̄`, which has the same least element (only `f` on `V̄` enters
`Δ_{ℤ^d} f` in `V`, and the least element vanishes off `V`). Only the values of `η` on `V` enter
either side. The conjunct `DivStabilizes V η` says that the odometer is the genuine limit of the
nondecreasing `k ↦ v_k(x)` (`tendsto_divOdometerUpTo`) and not the junk value `sSup` of an
unbounded set; `min` is `IsLeast`. -/
def DivisibleLeastActionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ V : Set (Site d), V.Finite → ∀ η : Site d → ℝ,
    DivStabilizes V η ∧ IsLeast (divLeastActionSet V η) (divOdometer V η)

/-- Lemma 8.1 (divisible_homogenize2), the restatement of Lemma 7.3 on `W_n`.
Let `W ⊂ ℝ^d` be a bounded Lipschitz domain, `W_n = ℤ^d ∩ nW`, `g_n` the Green's function of simple
random walk killed on exiting `W_n`, `r_n(x) = ∑_{y ∈ W_n} g_n(x,y) η(y)` and
`d_n(x) = ∑_{y ∈ W_n} g_n(x,y) η_avg`, `η_avg = E η(0)`. There exists a constant `C := C_d` so that
on an event of full probability, for each `ε > 0` there exists `n₀ ∈ ℕ` so that for all `n ≥ n₀`,
`sup_{x ∈ W̄_n} |r_n(x) - d_n(x)| ≤ ε C_d n²`.

Reading. `r_n = greenPotentialDomain W n η`, `d_n = greenPotentialDomainMean W n (meanEtaReal E.P)`
(`Defs/Green.lean`, `g_n = greenKilled (discretize W n)`); the supremum over the finite set `W̄_n`
is written pointwise. `C_d` depends only on `d`, so it is chosen before the environment and `W`
(the paper does not write `C > 0`). Since `ε` is arbitrary, the conclusion for one `C` amounts to
`sup_{W̄_n} |r_n - d_n| = o(n²)` a.s.; the placement of `C` and the normalisation of `g_n`
(`(2d)⁻¹` times the expected number of visits) do not change its content. The event
of full probability may depend on `W`, which is fixed before the lemma. No junk value
enters: `W_n` is finite (`W` bounded), so the `finsum`s defining `r_n`, `d_n` are finite sums, and
`η(0)` is a.s. bounded, hence integrable. -/
def DivisibleHomogenizeDomainStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ C : ℝ, ∀ (E : RealRandomEnvironment d) (W : Set (Rd d)),
    IsLipschitzDomain W →
      ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∀ x ∈ dClosure (discretize W n),
          |greenPotentialDomain W n η x - greenPotentialDomainMean W n (meanEtaReal E.P) x| ≤
            ε * C * (n : ℝ) ^ 2

/-- Theorem 8.2 (divisible_theorem). Let `W ⊂ ℝ^d` be a bounded Lipschitz domain,
`v_n` the odometer of the divisible sandpile initialized according to `η` in `W_n = ℤ^d ∩ nW`, and
`v_{avg_n}` that of the averaged sandpile `η_avg = E η(0)` in `W_n`. On an event of
full probability, as `n → ∞`, the rescaled functions `v̄_n := n⁻² v_n([nx])` and
`v̄_{avg_n} := n⁻² v_{avg_n}([nx])` converge uniformly together,
`sup_{x ∈ n⁻¹ W̄_n} |v̄_n(x) - v̄_{avg_n}(x)| → 0`.

Reading. `v_n = divOdometerDomain W n η`, `v_{avg_n} = divOdometerAvg W n (meanEtaReal E.P)`, the
odometers of the dynamics with sinks off `W_n`; the paper defines them "via Proposition 8.1", i.e. as the least elements of `divLeastActionSet`, which is the same function by
`DivisibleLeastActionStmt`. The rescaling is `rescaleDivOdo` and `n⁻¹ W̄_n` is
`rescaledDClosure W n`. The convergence `sup → 0` is written as `∀ ε > 0`, eventually in `n`,
`|v̄_n - v̄_{avg_n}| ≤ ε` on `n⁻¹ W̄_n`, which avoids the junk value `sSup = 0` of an `ℝ`-valued
supremum. The conjunct `∀ n, DivStabilizes (W_n) η ∧ DivStabilizes (W_n) η_avg` rules out the
junk reading in which both odometers are the junk value `0` of an unbounded supremum (which would
make the limit trivial); it holds for every real `η` because `W_n` is finite (sinks off `W_n`), so
no condition such as `E η(0) < 1` is needed for the odometers to be finite (: no density
assumption). The event of full probability may depend on `W`. -/
def DivisibleTheoremStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (E : RealRandomEnvironment d) (W : Set (Rd d)), IsLipschitzDomain W →
    ∀ᵐ η ∂E.P,
      (∀ n : ℕ, DivStabilizes (discretize W n) η ∧
        DivStabilizes (discretize W n) (fun _ => meanEtaReal E.P)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x ∈ rescaledDClosure W n,
        |rescaleDivOdo (divOdometerDomain W n η) n x -
          rescaleDivOdo (divOdometerAvg W n (meanEtaReal E.P)) n x| ≤ ε

end RandomSandpile

import RandomSandpile.Defs.Effective
import RandomSandpile.Defs.Odometer
import RandomSandpile.Defs.Green
import RandomSandpile.Defs.Viscosity
import RandomSandpile.Defs.Domain

/-! # Statements of Section 7: the proof of Theorem 1.1

* `OneDimTopplingStmt` — Lemma 7.1 (`lemma:one_dim`, cited from Fey-Levine-Peres,
  Lemma 3.3), with the proposed correction [C5];
* `CompactnessStmt` — Lemma 7.2 (`compactness`);
* `DivisibleHomogenizeStmt` — Lemma 7.3 (`divisible_homogenize`);
* `OdometerLowerBoundStmt` — Lemma 7.4 (`lowerbound`);
* `FlatStmt` — Lemma 7.5 (`flat`);
* `PegdenSmartRegularityStmt` — Lemma 7.6 (`regularity`, cited from Pegden-Smart,
  Proposition 2.5 and Lemma 4.1; part 3 sketched in the paper).

Standing assumptions: `d ≥ 2`, and the law of `η` is a `RandomEnvironment d`.
High density `E η(0) > 2d - 1` (`HighDensity`) is assumed exactly where the paper uses it:
Lemma 7.4 (`δ := E(η(0)) - (2d - 1) > 0`; notes it is the only use),
Lemma 7.5 (whose proof invokes Lemma 7.4) and Lemma 7.6 (stated inside the proof of
Theorem 1.1; part 3 uses the ergodic averages of `η` above `2d - 1`). Lemma 7.1
is one-dimensional and holds in every dimension `d`, which only enters through `R_k`., every constant `C` is positive.

`B_n` is `ballZ0 n`, `W_n = ℤ^d ∩ nW` is `discretize W n`, `v_n` is the free odometer
`freeOdometer η W_n` and `v̄_n = rescaleOdo v_n n`. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal

namespace RandomSandpile

/-- **Lemma 7.1** (`lemma:one_dim`; Fey-Levine-Peres, *Growth rates and explosions in
sandpiles*, Lemma 3.3). Let `ℓ ∈ ℕ` be given. Pick `k ∈ ℕ` so that `R_k := η_max - (2d - k) = 2r`
for some `r ∈ ℕ`. Then there exists `g : ℤ → ℕ` with `Δ g = f`, where `Δ` is the one-dimensional
second difference `g(x+1) + g(x-1) - 2g(x)` and
`f(x) = -R_k` for `|x| ≤ ℓ`, `2` for `ℓ < |x| ≤ ℓ(r+1)`, `1` for `ℓ(r+1) < |x| ≤ ℓ(r+1) + r`,
`0` for `ℓ(r+1) + r < |x|`. Moreover `g` is supported in `I = {x ∈ ℤ : |x| < ℓ(r+1) + r}` and
there exists `C := C_r` for which `g(x) ≤ C x²`.

[C5 proposed: the printed bound `g(x) ≤ C x²` is false at `x = 0` as soon as `r ≥ 1`: the unique
compactly supported solution is `g(x) = ½ ∑_y |x - y| f(y)` (since `∑ f = 0` and `∑ y f(y) = 0`),
so `g(0) = ½ ∑_y |y| f(y) ≈ r(r+1)ℓ² > 0` (e.g. `r = 1, ℓ = 1`: `g(0) = 5`; and `r = 1, ℓ = 0`:
`g(0) = 1`), while `C · 0² = 0`. The use ("`v_n ≤ C_d |x|²`, hence `v̄_n ≤ C_d`")
needs `g ≤ C ℓ²`. Corrected bound: `g(x) ≤ C (ℓ + 1)²` for all `x` (the `+ 1` covers `ℓ = 0`,
allowed since `0 ∈ ℕ` in the paper, cf. `v_n : ℤ^d → ℕ`); for `ℓ ≥ 1` it is the bound `g ≤ 4C ℓ²`.
Numerically `g(0)/(ℓ+1)² < r(r+1)` for `r ≤ 4`, `ℓ ≤ 20`.]

Quantifier order: `C := C_r` is chosen after `r` and before `ℓ, d, η_max, k`. -/
def OneDimTopplingStmt : Prop :=
  ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (ηmax : ℤ) (ℓ k : ℕ), ηmax - (2 * (d : ℤ) - k) = 2 * r →
      ∃ g : ℤ → ℕ,
        (∀ x : ℤ, (g (x + 1) : ℤ) + g (x - 1) - 2 * g x =
          if |x| ≤ ℓ then -(ηmax - (2 * (d : ℤ) - k))
          else if |x| ≤ ℓ * (r + 1) then 2
          else if |x| ≤ ℓ * (r + 1) + r then 1
          else 0) ∧
        (∀ x : ℤ, ℓ * (r + 1) + r ≤ |x| → g x = 0) ∧
        ∀ x : ℤ, (g x : ℝ) ≤ C * ((ℓ : ℝ) + 1) ^ 2

/-- **Lemma 7.2** (`compactness`). For every subsequence `n_k → ∞` there is a
subsequence `n_{k_j}` and a function `v̄ ∈ C(ℝ^d)` so that `v̄_{n_{k_j}} → v̄` uniformly as
`j → ∞`; here `v̄_n(x) = n⁻² v_n([nx])` with `v_n` the free odometer of `η 1_{W_n}`
.

The printed lemma has no "almost surely": its proof uses only `d ≥ 2`, the bounds
`η_min ≤ η ≤ η_max` (the upper bound for the comparison function built from Lemma 7.1, both bounds
for `|Δ v_n| ≤ C`), and that `W` is bounded. It is stated for every bounded `η : ℤ^d → ℤ` and every
bounded Lipschitz domain `W` (the setting of Theorem 1.1).

Junk exclusion: `freeOdometer` is the junk value `0` if no stabilizing toppling exists; the first
conjunct asserts that the class is nonempty for every `n` (the proof exhibits
`min(u_1, …, u_d)`), so `v_n` is the least stabilizing toppling
(`isLeast_freeOdometer`) and not a junk value. -/
def CompactnessStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ (ηmin ηmax : ℤ) (η : Site d → ℤ), (∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) →
      (∀ n : ℕ, (stabilizing ((discretize W n).indicator η) Set.univ).Nonempty) ∧
      ∀ nk : ℕ → ℕ, StrictMono nk →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ vbar : Rd d → ℝ, Continuous vbar ∧
          TendstoUniformly
            (fun j => rescaleOdo (freeOdometer η (discretize W (nk (φ j)))) (nk (φ j)))
            vbar atTop

/-- **Lemma 7.3** (`divisible_homogenize`). For each `η ∈ Ω̃_0`, an event of
probability 1, there is a constant `C := C_{d,η}` so that: for each `ε > 0` there exists `n_0 ∈ ℕ`
so that for all `n ≥ n_0`, `sup_{x ∈ B_n} |r_n(x) - d_n(x)| ≤ ε C n²`, where
`r_n(x) = ∑_{y ∈ B_n} g_n(x,y) η(y)` and `d_n(x) = ∑_{y ∈ B_n} g_n(x,y) E(η(0))`, `g_n` the Green's function of simple random walk killed on exiting `B_n`.

The supremum is written pointwise (`sup_{B_n} ≤ t` iff every point is `≤ t`). No high density. -/
def DivisibleHomogenizeStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ᵐ η ∂E.P, ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ x ∈ ballZ0 (d := d) (n : ℝ),
        |greenPotentialBall n η x - greenPotentialBallMean n (meanEta E.P) x| ≤
          ε * C * (n : ℝ) ^ 2

/-- **Lemma 7.4** (`lowerbound`). For each `η ∈ Ω̃_0`, an event of probability 1,
and each `ε > 0`, there exists `n_0` so that for all `n ≥ n_0`, `w_n ≥ 1` for all
`x ∈ B_{(1-ε)n}`, where `w_n ∈ 𝓛(η, B_n) ∩ 𝓢(η, B_n)` and `w_n = 0` on `∂B_n`.

High density is assumed: the proof compares with the divisible sandpile of density
`η_avg = E(η(0)) > 2d - 1` (printed `E(η(0)) - 2d - 1`, a parenthesization slip).
The printed `w_n` is characterised by the displayed membership (it is the open-boundary odometer
`openOdometer η B_n`, Proposition 3.1). The statement asserts the bound for every such `w` and,
to exclude vacuity, that one exists. -/
def OdometerLowerBoundStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∃ w ∈ locLegal η (ballZ0 (n : ℝ)) ∩ stabilizing η (ballZ0 (n : ℝ)),
        ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)), w y = 0) ∧
      ∀ w ∈ locLegal η (ballZ0 (n : ℝ)) ∩ stabilizing η (ballZ0 (n : ℝ)),
        (∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)), w y = 0) →
          ∀ x ∈ ballZ0 (d := d) ((1 - ε) * n), 1 ≤ w x

/-- **Lemma 7.5** (`flat`). `μ(l_M, M) = μ*(l_M, M) = 0`, where `μ, μ*` are the
deterministic limits of Lemma 5.5 (`muBar`, `muStarBar`) and `l_M = F̄_η(M)` (`effOp`), for every `M ∈ 𝕊^d`.

High density is assumed: the proof invokes Lemma 7.4 to make `Δ w + η` recurrent.
Junk values: `muBar`, `muStarBar` are `ENNReal.toReal` of a lower integral, which would be `0` at
`∞`; the integrand is bounded by Lemma 5.4 (`μ(A, η, l, M) ≤ C |A|`), so `= 0` is not met by the
junk value. If `muEqSet E M` were empty or unbounded, `effOp E M` would be `0`; this is excluded by
Lemma 6.4(3) (`EffectiveOperatorBasicStmt`) and does not make the statement trivial. -/
def FlatStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm →
      muBar E (effOp E M) M = 0 ∧ muStarBar E (effOp E M) M = 0

/-- **Lemma 7.6** (`regularity`; Pegden-Smart, *Convergence of the Abelian
sandpile*, Proposition 2.5 and Lemma 4.1). In the setting of the proof of Theorem 1.1: `η, η' ∈ Ω_0`, an event of probability 1; `v, v'` are uniform limits of
subsequences of the rescaled free odometers `v̄_n, v̄'_n` of `η, η'` on `W`; `v ≠ v'`, normalised
(exchanging `η` and `η'`) so that `sup_{B_R}(v - v') > 0 = sup_{∂B_R}(v - v')`.
1. There exists `a ∈ ℝ^d` either in `W` or outside the closure of `W` so that `v(a) > v'(a)`, both
   `v` and `v'` are twice differentiable at `a` and `D²(v - v')(a) < -δI` for some `δ > 0`.
2. For each `ε > 0`, if `a` is outside the closure of `W`, we may select `u : ℤ^d → ℤ` such that
   `Δu(x) ≤ 2d - 1` and `u(x) ≥ ½ xᵀ(D²v(a) - εI)x` for all `x ∈ ℤ^d`.
3. For each `ε > 0`, if `a` is in `W`, we may select `u : ℤ^d → ℤ` such that `Δu(x) ≤ 2d - 1` and
   `u(x) ≥ ½ xᵀ(D²v(a) - εI)x + o(|x|²)` for all `x ∈ ℤ^d`.

Reading. `W` is fixed first (as in Theorem 1.1); `Ω_0` is then a set with null complement,
and `η, η'` range over it independently ("Pick `η, η' ∈ Ω_0`"). The two subsequences
`n_k, n'_k` may differ. Since `v = v' = 0` outside some `B_R` (proof of Lemma 7.2), the
normalisation is exactly `∃ x, v'(x) < v(x)`. "Twice differentiable at `a`" is a second-order
Peano expansion with a symmetric matrix (`PeanoTwiceDifferentiableAt`): `X = D²v(a)`,
`X' = D²v'(a)`; `D²(v - v')(a) < -δI` is `-δI - (X - X') ≻ 0`. In part 3, `u ≥ q + o(|x|²)` means:
for every `κ > 0` there is `R` with `u(x) ≥ q(x) - κ|x|²` whenever `|x| ≥ R`. -/
def PegdenSmartRegularityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ W : Set (Rd d), IsLipschitzDomain W →
      ∃ Ω₀ : Set (Config d), E.P Ω₀ᶜ = 0 ∧ ∀ η ∈ Ω₀, ∀ η' ∈ Ω₀,
        ∀ (nk nk' : ℕ → ℕ), StrictMono nk → StrictMono nk' → ∀ v v' : Rd d → ℝ,
          TendstoUniformly
            (fun k => rescaleOdo (freeOdometer η (discretize W (nk k))) (nk k)) v atTop →
          TendstoUniformly
            (fun k => rescaleOdo (freeOdometer η' (discretize W (nk' k))) (nk' k)) v' atTop →
          (∃ x, v' x < v x) →
            ∃ (a p p' : Rd d) (X X' : Matrix (Fin d) (Fin d) ℝ),
              (a ∈ W ∨ a ∉ closure W) ∧ v' a < v a ∧
              X.IsSymm ∧ X'.IsSymm ∧ HasSecondOrderTaylorAt v a p X ∧
              HasSecondOrderTaylorAt v' a p' X' ∧
              (∃ δ : ℝ, 0 < δ ∧ (-(δ • (1 : Matrix (Fin d) (Fin d) ℝ)) - (X - X')).PosDef) ∧
              (a ∉ closure W → ∀ ε : ℝ, 0 < ε → ∃ u : Site d → ℤ, ∀ x : Site d,
                lap u x ≤ 2 * (d : ℤ) - 1 ∧
                  qMZ (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ (u x : ℝ)) ∧
              (a ∈ W → ∀ ε : ℝ, 0 < ε → ∃ u : Site d → ℤ,
                (∀ x : Site d, lap u x ≤ 2 * (d : ℤ) - 1) ∧
                ∀ κ : ℝ, 0 < κ → ∃ R : ℝ, ∀ x : Site d, R ≤ ‖toE x‖ →
                  qMZ (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x - κ * ‖toE x‖ ^ 2 ≤ (u x : ℝ))

end RandomSandpile

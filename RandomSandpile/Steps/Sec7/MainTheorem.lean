import RandomSandpile.Draft.Section1
import RandomSandpile.Draft.Section5
import RandomSandpile.Draft.Section6
import RandomSandpile.Draft.Section7

/-!
# Steps of Theorem 1.1 (convergence of the random Abelian sandpile)

Decomposition of `RandomSandpile.MainTheoremStmt` (Theorem 1.1, `paper/random_piles-corrected.tex`, with the correction [C3]) into three groups of steps and the reduction `mainTheorem_of_steps`.

* uniqueness of subsequential limits, the printed proof: `LimitComparisonStmt`,
  decomposed into `ExteriorSupersolutionStmt`, `ExteriorSubsolutionStmt` (Pegden-Smart, the argument
  of their Theorem 4.2 outside `W̄`), `InteriorMaxPrincipleStmt`, `InteriorMinPrincipleStmt`
  (Lemma 5.2 on `B_{rn}(na)` with Lemma 5.5), with Lemmas 7.5 and 7.6(1) as
  hypotheses.
* (I) identification of the common limit with the least element of the obstacle set, not printed: `LimitViscEffStmt` (`F̄_η(D²v) ≥ 0` in `W`, the [C3] sign),
  `LimitViscZeroStmt` (`F̄_0(D²v) ≤ 0` in `ℝ^d`), `LimitMinimalStmt` (comparison with every member
  of the constraint set). Continuity and nonnegativity of the limit are proved in the reduction.
* the sandpile claims of the second paragraph, not printed:
  `SandpileLimitStmt`, decomposed into `EnvWeakStarStmt` (ergodic theorem), `RescaledLapWeakStmt`
  (summation by parts), `WeakStarRepresentationStmt` (`L^∞` as the dual of `L¹`) and
  `SandpileSupportStmt` (the radius `R = R(W, E η(0))`).

Repairs of the printed proof (and two further slips found while decomposition).
1. Sides of the comparison. The minimum principle of Lemma 5.2 for perturbed
   supersolutions (`μ*`) never contradicts a strict local maximum, and the strict concavity
   `D²(v - v')(a) < -δI` is a strict local maximum of `v - v'` modulo an affine function. The
   argument that closes uses the maximum principle (perturbed subsolutions, `μ`) on the side of `η`
   and the minimum principle (`μ*`) on the side of `η'`: with `φ` the Taylor polynomial of `v'` at
   `a`, `M = D²v'(a)` and `l = F̄_η(M)`, the Hessian of `v - φ - q_l` at `a` is
   `D²(v - v')(a) - (l/d) I < -(δ + l/d) I`, which contradicts the maximum principle if
   `l > -dδ`; the Hessian of `v' - φ - q_l` is `-(l/d) I > 0` if `l < 0`, which contradicts the
   minimum principle. (`q_l(x) = l |x|² / (2d)`, `ql`.) Both principles hold at `l = l_M` by
   Lemma 7.5 (`μ(l_M, M) = μ*(l_M, M) = 0`), so the repair changes no input.
2. Rational approximation (N10 (b)). Only `M` needs approximating by a rational matrix; then
   `μ(l', M) = 0` for rational `l' ≤ l_M` and `μ*(l'', M) = 0` for rational `l'' ≥ l_M`
   (Lemma 6.1 and Lemma 7.5), and the slack `δ` absorbs `M - D²v'(a)`; affine terms (N10 (d)) are
   part of the test quadratics of `InteriorMaxPrincipleStmt` and `InteriorMinPrincipleStmt`.
3. Exterior case. The competitor argument of Pegden-Smart needs a function `u` with
   `Δu ≤ 2d - 1` above the quadratic of the *larger* Hessian `D²v'(a)` (it builds a stabilizing
   toppling below `v_n` near `na`, whose Hessian must exceed `D²v(a)`); Lemma 7.6(2) as printed
   gives `u` for `D²v(a)`. Pegden-Smart's Lemma 4.1 applies to every limit at every point outside
   `W̄` touched from below by a quadratic, so the decomposition uses it in that form
   (`ExteriorSupersolutionStmt`), at `v'`; Lemma 7.6 enters only through its part 1.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- `v` is a subsequential uniform limit of the rescaled free odometers
`v̄_n = n⁻² v_n([n ·])` of `η 𝟙_{W_n}`: there is `n_k → ∞` strictly increasing with
`v̄_{n_k} → v` uniformly on `ℝ^d`. -/
def IsOdoSubseqLimit (η : Site d → ℤ) (W : Set (Rd d)) (v : Rd d → ℝ) : Prop :=
  ∃ nk : ℕ → ℕ, StrictMono nk ∧
    TendstoUniformly (fun k => rescaleOdo (freeOdometer η (discretize W (nk k))) (nk k)) v atTop

/-! ### Uniqueness of subsequential limits -/

/-- **Step: comparison of subsequential limits**. There is an event `Ω₀` of
full probability such that, for `η, η' ∈ Ω₀`, every subsequential limit `v` of the rescaled
odometers of `η` lies below every subsequential limit `v'` of those of `η'`. The paper argues by
contradiction from `sup (v - v') > 0`; applied twice, the statement gives `v = v'`. -/
def LimitComparisonStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ W : Set (Rd d), IsLipschitzDomain W →
      ∃ Ω₀ : Set (Config d), E.P Ω₀ᶜ = 0 ∧ ∀ η ∈ Ω₀, ∀ η' ∈ Ω₀, ∀ v v' : Rd d → ℝ,
        IsOdoSubseqLimit η W v → IsOdoSubseqLimit η' W v' → ∀ x, v x ≤ v' x

/-- **Step: supersolution property outside `W̄`** (Pegden-Smart, Lemma 4.1; the input of
Lemma 7.6(2)). Outside `W̄` the pile `η 𝟙_{W_n}` vanishes and the
odometers satisfy `Δ_{ℤ^d} v_n ≤ 2d - 1`. If a quadratic with Hessian `N` touches a subsequential
limit `v` from below at `a ∉ W̄`, then for every `ε > 0` some `u : ℤ^d → ℤ` has
`Δ_{ℤ^d} u ≤ 2d - 1` and `u ≥ ½ xᵀ(N - εI)x` on `ℤ^d`. -/
def ExteriorSupersolutionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ (ηmin ηmax : ℤ) (η : Site d → ℤ), (∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) →
      ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (N : Matrix (Fin d) (Fin d) ℝ), a ∉ closure W → N.IsSymm →
          (∀ᶠ y in 𝓝 a, v a + inner ℝ p (y - a) + qM N (y - a) ≤ v y) →
          ∀ ε : ℝ, 0 < ε → ∃ u : Site d → ℤ, ∀ x : Site d,
            lap u x ≤ 2 * (d : ℤ) - 1 ∧
              qMZ (N - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ (u x : ℝ)

/-- **Step: subsolution property outside `W̄` where `v > 0`** (the argument in the proof of
Pegden-Smart, Theorem 4.2: leastness of the odometer). If a quadratic with Hessian `N`
touches a subsequential limit `v` from above at `a ∉ W̄` with `v(a) > 0`, then no `u : ℤ^d → ℤ`
with `Δ_{ℤ^d} u ≤ 2d - 1` lies above `½ xᵀ(N + εI)x` for an `ε > 0`: otherwise
`min(v_n, n² (v(a) - c) + affine + u(· - [na]))` would be a stabilizing toppling smaller than the
least one `v_n` near `na`. -/
def ExteriorSubsolutionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ (ηmin ηmax : ℤ) (η : Site d → ℤ), (∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) →
      ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (N : Matrix (Fin d) (Fin d) ℝ), a ∉ closure W → N.IsSymm → 0 < v a →
          (∀ᶠ y in 𝓝 a, v y ≤ v a + inner ℝ p (y - a) + qM N (y - a)) →
          ∀ ε : ℝ, 0 < ε → ¬ ∃ u : Site d → ℤ, ∀ x : Site d,
            lap u x ≤ 2 * (d : ℤ) - 1 ∧
              qMZ (N + ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ (u x : ℝ)

/-- **Step: maximum principle in `W` from `μ(l, M) = 0`** (the side of `η`,
with the repair 1 of the module docstring). Fix `l`, a symmetric `M` with `μ(l, M) = 0`. Almost
surely, every subsequential limit `v` satisfies the maximum principle relative to the quadratic
`Q(x) = p·(x - a) + ½(x - a)ᵀM(x - a) + q_l(x - a)` on every closed ball `B̄_r(a) ⊆ W`: the value of
`v - Q` at a point of the ball is at most its value at some point of the sphere `∂B_r(a)`.

Proof route: Lemma 5.2 (`ABPStmt`, perturbed subsolutions) on `B_{rn}(na) ∩ ℤ^d` for the
restriction of the legal toppling `v_n` (Proposition 3.1), affine invariance of `μ`, rescaling
(the error is `C r (μ(B_{rn}(na), η, l, M) / n^d)^{1/d}`), and Lemma 5.5 for the ball `B_r(a)`
(`μ(n B_r(a) ∩ ℤ^d) / |n B_r(a) ∩ ℤ^d| → μ(l, M) = 0`). -/
def InteriorMaxPrincipleStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → muBar E l M = 0 →
      ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v x - (inner ℝ p (x - a) + qM M (x - a) + ql l (x - a)) ≤
              v y - (inner ℝ p (y - a) + qM M (y - a) + ql l (y - a))

/-- **Step: minimum principle in `W` from `μ*(l, M) = 0`** (and 1426-1429, the
side of `η'`, with the repairs 1 and N10 (a), (c)). Fix `l`, a symmetric `M` with `μ*(l, M) = 0`.
Almost surely, every subsequential limit `v` satisfies the minimum principle relative to the
quadratic `Q(x) = p·(x - a) + ½(x - a)ᵀM(x - a) + q_l(x - a)` on every closed ball `B̄_r(a) ⊆ W`.

Proof route: Lemma 5.2 (`ABPStmt`, perturbed supersolutions) on `B_{rn}(na) ∩ ℤ^d` for the
stabilizing toppling `v_n`, affine invariance of `μ*`, rescaling, and Lemma 5.5. -/
def InteriorMinPrincipleStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → muStarBar E l M = 0 →
      ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v y - (inner ℝ p (y - a) + qM M (y - a) + ql l (y - a)) ≤
              v x - (inner ℝ p (x - a) + qM M (x - a) + ql l (x - a))

/-- **Step: vanishing ranges of `μ` and `μ*`**. For symmetric
`M`, `μ(l, M) = 0` for `l ≤ l_M = F̄_η(M)` and `μ*(l, M) = 0` for `l ≥ l_M`. Route: Lemma 7.5
(`FlatStmt`: both vanish at `l_M`), Lemma 6.1 (`MuMonotoneStmt`: `μ` nondecreasing and `μ*`
nonincreasing in `l` on the balls `B_n`), and finiteness of the averages defining `muBar`,
`muStarBar` (the bound of Lemma 5.4 on balls), without which `ENNReal.toReal`
would not be monotone. -/
def MuVanishStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ l : ℝ,
      (l ≤ effOp E M → muBar E l M = 0) ∧ (effOp E M ≤ l → muStarBar E l M = 0)

/-! ### (I) Identification of the limit -/

/-- **Step: the limit is a viscosity supersolution of `F̄_η(D²v) ≥ 0` in `W`** ([C3] sign,
test functions touching from below). Route: if `φ` touches `v` from below at `x ∈ W` and
`F̄_η(D²φ(x)) < 0`, then for a rational `M` near `D²φ(x)` and a rational `l` with
`F̄_η(M) ≤ l < 0` (Lemma 6.4(2)), `μ*(l, M) = 0` (Lemmas 6.1, 7.5), and `v - φ - q_l` has a strict
local minimum at `x`, against `InteriorMinPrincipleStmt`. -/
def LimitViscEffStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ W : Set (Rd d), IsLipschitzDomain W →
      ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v → ViscFromBelowGE (effOp E) W v

/-- **Step: the limit is a viscosity supersolution of `F̄_0(D²v) ≤ 0` in `ℝ^d`**
(Pegden-Smart's `D²v ∈ Γ̄`). Outside `W̄` this is `ExteriorSupersolutionStmt`; in `W` it is the
route of Lemma 7.6(3) (`u ≥ q_{D²φ - εI} + o(|x|²)`) with Pegden-Smart's passage from `o(|x|²)`
to `Γ̄` (and the remark); on `∂W` it needs its own argument. -/
def LimitViscZeroStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ W : Set (Rd d), IsLipschitzDomain W →
      ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ViscFromBelowLE (effOp0 d) Set.univ v

/-- **Step: minimality of the limit** ("`min`"). Almost surely, every subsequential
limit lies below every member of the constraint set `obstacleSet E W`. Route: Pegden-Smart's
Proposition 2.5 (Jensen-Alexandrov touching) for `v - w`, then the contradictions
of `InteriorMaxPrincipleStmt` (in `W`, with `F̄_η(D²w) ≥ 0`) and `ExteriorSubsolutionStmt` (outside
`W̄`, with `F̄_0(D²w) ≤ 0`). -/
def LimitMinimalStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ W : Set (Rd d), IsLipschitzDomain W →
      ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ∀ w ∈ obstacleSet E W, ∀ x, v x ≤ w x

/-! ### The sandpile claims -/

/-- **Step: the sandpile claims, given the convergence of the odometers**. The
radius `R` depends only on `W` and `m = E η(0)`. For every continuous `v̄` such that
almost surely `v̄_n → v̄` uniformly, there is `s ∈ L^∞(ℝ^d)` with `s̄_n → s` weakly-* almost surely,
`∫ s = |W| E η(0)`, `s ≤ 2d - 1`, `s = 0` off `B_R(W)` and `s = Δv̄ + E η(0) 𝟙_W` weakly. -/
def SandpileLimitStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ m : ℝ, ∃ R : ℝ, 0 < R ∧
    ∀ E : RandomEnvironment d, HighDensity E.P → meanEta E.P = m →
      ∀ vbar : Rd d → ℝ, Continuous vbar →
        (∀ᵐ η ∂E.P, TendstoUniformly
          (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n) vbar atTop) →
        ∃ s : Rd d → ℝ, MemLp s ⊤ volume ∧
          (∀ᵐ η ∂E.P,
            WeakStarTendsto (fun n : ℕ => rescaleSandpile (freeSandpile η (discretize W n)) n) s) ∧
          ∫ x, s x = (volume W).toReal * meanEta E.P ∧
          (∀ᵐ x ∂volume, s x ≤ 2 * (d : ℝ) - 1) ∧
          (∀ᵐ x ∂volume, x ∉ Metric.thickening R W → s x = 0) ∧
          ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            ∫ x, s x * φ x =
              (∫ x, vbar x * Matrix.trace (hessian φ x)) + meanEta E.P * ∫ x in W, φ x

/-- **Step: ergodic theorem for the rescaled environment.** Almost surely the rescaled
restricted environment `x ↦ η([nx]) 𝟙_{W_n}([nx])` converges weakly-* to `E η(0) 𝟙_W`. Route: the
multiparameter pointwise ergodic theorem for boxes (Akcoglu-Krengel for additive processes, in
Lattice-Probability), boxes approximating the Lipschitz domain `W` (`|∂W| = 0`), and density of
step functions in `L¹`. -/
def EnvWeakStarStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ᵐ η ∂E.P, WeakStarTendsto (fun n : ℕ => rescaleSandpile ((discretize W n).indicator η) n)
      (W.indicator fun _ => meanEta E.P)

/-- **Step: summation by parts for the rescaled Laplacian.** If integer functions `v_n`
vanish off the cubes `{|x|_∞ < R₀ (n + 1)}` and `v̄_n = n⁻² v_n([n ·]) → v̄` uniformly with `v̄`
continuous, then `∫ Δ_{ℤ^d} v_n([nx]) φ(x) dx → ∫ v̄ Δφ` for every test function `φ ∈ C_c^∞`.
Route: `∫ Δv_n([nx]) φ = Σ_y v_n(y) Δ_y ∫_{(y + [0,1)^d)/n} φ`, Taylor's theorem for `φ`
(`Δ_y ∫_{cell} φ = n^{-d-2} Δφ(y/n) + O(n^{-d-3})`) and Riemann sums. -/
def RescaledLapWeakStmt : Prop :=
  ∀ (d : ℕ) (R₀ : ℕ) (v : ℕ → Site d → ℤ) (vbar : Rd d → ℝ),
    (∀ (n : ℕ) (x : Site d), (∃ i, (R₀ : ℤ) * ((n : ℤ) + 1) ≤ |x i|) → v n x = 0) →
    Continuous vbar →
    TendstoUniformly (fun n => rescaleOdo (v n) n) vbar atTop →
    ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      Tendsto (fun n : ℕ => ∫ x, rescaleSandpile (lap (v n)) n x * φ x) atTop
        (𝓝 (∫ x, vbar x * Matrix.trace (hessian φ x)))

/-- **Step: weak-* limits in `L^∞`** (`L^∞(ℝ^d) = L¹(ℝ^d)*`, Banach-Alaoglu). A sequence of
measurable functions bounded by `C`, eventually vanishing off a fixed bounded set, whose integrals
against every `φ ∈ C_c^∞` converge, converges weakly-* to some `s ∈ L^∞`. Route: density of
`C_c^∞` in `L¹` gives the limit functional on `L¹`; it is a finite signed measure absolutely
continuous with respect to Lebesgue measure (Radon-Nikodym). -/
def WeakStarRepresentationStmt : Prop :=
  ∀ (d : ℕ) (f : ℕ → Rd d → ℝ) (C : ℝ) (B : Set (Rd d)), Bornology.IsBounded B →
    (∀ n, Measurable (f n)) → (∀ n x, |f n x| ≤ C) →
    (∀ᶠ n in atTop, ∀ x, x ∉ B → f n x = 0) →
    (∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∃ L : ℝ, Tendsto (fun n => ∫ x, f n x * φ x) atTop (𝓝 L)) →
    ∃ s : Rd d → ℝ, MemLp s ⊤ volume ∧ WeakStarTendsto f s

/-- **Step: the support radius** ("`R > 0` depending on `W` and `E(η(0))`"). There is
`R > 0`, depending only on `W` and `m`, such that for every environment of mean `m` almost surely
the rescaled sandpiles eventually vanish off `B_R(W)`. The bound of Lemma 7.2's proof (via
Lemma 7.1) depends on `η_max`; a bound depending only on the mass `|W| m` needs an outer estimate
of Levine-Peres type for the toppled region. The variant
with `R` chosen after the law is `SandpileSupportLawStmt` (proved). -/
def SandpileSupportStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ m : ℝ, ∃ R : ℝ, 0 < R ∧
    ∀ E : RandomEnvironment d, HighDensity E.P → meanEta E.P = m →
      ∀ᵐ η ∂E.P, ∀ᶠ n : ℕ in atTop, ∀ x : Rd d, x ∉ Metric.thickening R W →
        rescaleSandpile (freeSandpile η (discretize W n)) n x = 0

/-- **The support radius chosen after the law.** For every environment there is `R > 0` such that almost surely the rescaled sandpiles
eventually vanish off `B_R(W)`; `R` depends on `W` and `η_max` (Lemma 7.2's box), not only on
`E η(0)`. Proved from `FreeOdometerUpperBoundStmt` (`sandpileSupportLaw`,
`Proofs/Sec7/SandpileSupport.lean`). -/
def SandpileSupportLawStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ E : RandomEnvironment d,
    ∃ R : ℝ, 0 < R ∧ ∀ᵐ η ∂E.P, ∀ᶠ n : ℕ in atTop, ∀ x : Rd d, x ∉ Metric.thickening R W →
      rescaleSandpile (freeSandpile η (discretize W n)) n x = 0

/-- **Step with the radius chosen after the law**: `SandpileLimitStmt` with `∃ R` after `E`. -/
def SandpileLimitLawStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ E : RandomEnvironment d,
    HighDensity E.P → ∃ R : ℝ, 0 < R ∧
      ∀ vbar : Rd d → ℝ, Continuous vbar →
        (∀ᵐ η ∂E.P, TendstoUniformly
          (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n) vbar atTop) →
        ∃ s : Rd d → ℝ, MemLp s ⊤ volume ∧
          (∀ᵐ η ∂E.P,
            WeakStarTendsto (fun n : ℕ => rescaleSandpile (freeSandpile η (discretize W n)) n) s) ∧
          ∫ x, s x = (volume W).toReal * meanEta E.P ∧
          (∀ᵐ x ∂volume, s x ≤ 2 * (d : ℝ) - 1) ∧
          (∀ᵐ x ∂volume, x ∉ Metric.thickening R W → s x = 0) ∧
          ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            ∫ x, s x * φ x =
              (∫ x, vbar x * Matrix.trace (hessian φ x)) + meanEta E.P * ∫ x in W, φ x

/-! ### The reduction -/

/-- Uniform limits of rescaled free odometers are nonnegative. -/
theorem IsOdoSubseqLimit.nonneg {η : Site d → ℤ} {W : Set (Rd d)} {v : Rd d → ℝ}
    (hv : IsOdoSubseqLimit η W v) (x : Rd d) : 0 ≤ v x := by
  obtain ⟨nk, -, hconv⟩ := hv
  refine ge_of_tendsto' (hconv.tendsto_at x) fun k => ?_
  exact div_nonneg (Int.cast_nonneg (freeOdometer_nonneg _ _ _)) (sq_nonneg _)

/-- The conclusion of Theorem 1.1 for one environment `E` and one support radius `R`, given the
sandpile step for `E` and `R` (the core of `mainTheorem_of_steps`, shared with the law-radius
variant `mainTheorem_lawRadius_of_steps`, `Proofs/Sec7/SandpileSupport.lean`). -/
theorem mainTheorem_core (hComp : CompactnessStmt) (h64 : EffectiveOperatorBasicStmt)
    (hU : LimitComparisonStmt) (hEff : LimitViscEffStmt) (hZero : LimitViscZeroStmt)
    (hMin : LimitMinimalStmt) (hd : 2 ≤ d) {W : Set (Rd d)} (hW : IsLipschitzDomain W)
    (E : RandomEnvironment d) (hHD : HighDensity E.P) {R : ℝ}
    (hSR : ∀ vbar : Rd d → ℝ, Continuous vbar →
      (∀ᵐ η ∂E.P, TendstoUniformly
        (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n) vbar atTop) →
      ∃ s : Rd d → ℝ, MemLp s ⊤ volume ∧
        (∀ᵐ η ∂E.P,
          WeakStarTendsto (fun n : ℕ => rescaleSandpile (freeSandpile η (discretize W n)) n) s) ∧
        ∫ x, s x = (volume W).toReal * meanEta E.P ∧
        (∀ᵐ x ∂volume, s x ≤ 2 * (d : ℝ) - 1) ∧
        (∀ᵐ x ∂volume, x ∉ Metric.thickening R W → s x = 0) ∧
        ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, s x * φ x =
            (∫ x, vbar x * Matrix.trace (hessian φ x)) + meanEta E.P * ∫ x in W, φ x) :
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
              meanEta E.P * ∫ x in W, φ x := by
  have hDE : DegenerateElliptic (effOp E) := by
    obtain ⟨C, -, hC⟩ := h64 d hd E.ηmin E.ηmax
    intro X Y hX hY hXY
    exact (hC E rfl rfl X Y hX hY).1 hXY
  obtain ⟨Ω₀, hΩ₀, hcmp⟩ := hU d hd E hHD W hW
  have hΩ : ∀ᵐ η ∂E.P, η ∈ Ω₀ := ae_iff.2 hΩ₀
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  have hG : ∀ᵐ η ∂E.P, (η ∈ Ω₀ ∧ ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax) ∧
      (∀ v, IsOdoSubseqLimit η W v → ViscFromBelowGE (effOp E) W v) ∧
      (∀ v, IsOdoSubseqLimit η W v → ViscFromBelowLE (effOp0 d) Set.univ v) ∧
      (∀ v, IsOdoSubseqLimit η W v → ∀ w ∈ obstacleSet E W, ∀ x, v x ≤ w x) := by
    filter_upwards [hΩ, hbdd, hEff d hd E hHD W hW, hZero d hd E hHD W hW,
      hMin d hd E hHD W hW] with η h1 h2 h3 h4 h5
    exact ⟨⟨h1, h2⟩, h3, h4, h5⟩
  obtain ⟨η₀, ⟨hη₀Ω, hη₀b⟩, hη₀Eff, hη₀Zero, hη₀Min⟩ := hG.exists
  obtain ⟨-, hsub₀⟩ := hComp d hd W hW E.ηmin E.ηmax η₀ hη₀b
  obtain ⟨φ, hφ, vbar, hvc, hvconv⟩ := hsub₀ id strictMono_id
  have hvbar : IsOdoSubseqLimit η₀ W vbar := ⟨φ, hφ, hvconv⟩
  -- every subsequential limit of a good `η` is `vbar`
  have huniq : ∀ η ∈ Ω₀, ∀ v, IsOdoSubseqLimit η W v → v = vbar := fun η hη v hv =>
    funext fun x => le_antisymm (hcmp η hη η₀ hη₀Ω v vbar hv hvbar x)
      (hcmp η₀ hη₀Ω η hη vbar v hvbar hv x)
  -- hence the whole sequence converges
  have hconv : ∀ η, (η ∈ Ω₀ ∧ ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax) →
      TendstoUniformly (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n) vbar
        atTop := by
    rintro η ⟨hηΩ, hηb⟩
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    obtain ⟨nk, hnk, hbad⟩ := extraction_of_frequently_atTop hcon
    obtain ⟨-, hsub⟩ := hComp d hd W hW E.ηmin E.ηmax η hηb
    obtain ⟨ψ, hψ, v', -, hv'⟩ := hsub nk hnk
    have hv'eq : v' = vbar := huniq η hηΩ v' ⟨nk ∘ ψ, hnk.comp hψ, hv'⟩
    rw [hv'eq, Metric.tendstoUniformly_iff] at hv'
    obtain ⟨j, hj⟩ := (hv' ε hε).exists
    exact hbad (ψ j) hj
  have hmem : vbar ∈ obstacleSet E W :=
    ⟨hvc, fun x => hvbar.nonneg x, hη₀Eff vbar hvbar, hη₀Zero vbar hvbar⟩
  have hLeast : IsLeast (obstacleSet E W) vbar :=
    ⟨hmem, fun w hw x => hη₀Min vbar hvbar w hw x⟩
  have hsol : obstacleSolution E W = vbar := obstacleSolution_eq_of_isLeast hLeast
  have hae : ∀ᵐ η ∂E.P, TendstoUniformly
      (fun n : ℕ => rescaleOdo (freeOdometer η (discretize W n)) n) vbar atTop := by
    filter_upwards [hG] with η hη
    exact hconv η hη.1
  rw [hsol]
  refine ⟨hDE, hLeast, ?_, hSR vbar hvc hae⟩
  filter_upwards [hG] with η hη
  exact ⟨(hComp d hd W hW _ _ η hη.1.2).1, hconv η hη.1⟩

/-- **Theorem 1.1 with the printed radius** (`MainTheoremPrintedStmt`; the corrected statement
is `MainTheoremStmt`, [C12]) from its steps: compactness (Lemma 7.2), Lemma 6.4(1), the comparison
of subsequential limits, the identification steps- and the sandpile step. -/
theorem mainTheorem_of_steps (hComp : CompactnessStmt) (h64 : EffectiveOperatorBasicStmt)
    (hU : LimitComparisonStmt) (hEff : LimitViscEffStmt) (hZero : LimitViscZeroStmt)
    (hMin : LimitMinimalStmt) (hS : SandpileLimitStmt) : MainTheoremPrintedStmt := by
  intro d hd W hW m
  obtain ⟨R, hR, hSR⟩ := hS d hd W hW m
  exact ⟨R, hR, fun E hHD hm =>
    mainTheorem_core hComp h64 hU hEff hZero hMin hd hW E hHD (hSR E hHD hm)⟩

end RandomSandpile

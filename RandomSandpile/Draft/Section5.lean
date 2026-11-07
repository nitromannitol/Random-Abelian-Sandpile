import RandomSandpile.Defs.Effective
import RandomSandpile.Defs.Domain
import RandomSandpile.Defs.Subadditive

/-! # Section 5: the monotone quantities `μ` and `μ*` — statements

Statements (`...Stmt : Prop`) of the numbered results of Section 5 of the paper
:

* `StabilizingLegalStmt` (Lemma 5.1): solutions maximize curvature among legal (resp.
  stabilizing) topplings with the same boundary values;
* `ABPStmt` (Lemma 5.2): the discrete Alexandroff-Bakelman-Pucci estimate in terms of `μ`, `μ*`;
* `ConcaveEnvelopeRepStmt` (Proposition 5.1, cited): the Carathéodory representation of the
  concave envelope `Γ_w`;
* `MongeAmpereRepStmt` (Lemma 5.3): the measure of the supergradient set is preserved by taking the
  concave envelope;
* `MuBoundedStmt` (Lemma 5.4): `μ ≤ C |Q_n|`, `μ* ≤ C* |Q_n|`, and the ranges where they vanish;
* `HarnackQuadraticStmt` (Proposition 5.2, cited): quadratic growth from the discrete Harnack
  inequality;
* `SubadditiveErgodicStmt` (Proposition 5.3, cited): the multiparameter subadditive ergodic
  theorem;
* `MuConvergenceStmt` (Lemma 5.5): almost sure convergence of `μ(nW ∩ ℤ^d) / |nW ∩ ℤ^d|` and
  `μ*(nW ∩ ℤ^d) / |nW ∩ ℤ^d|` to the deterministic limits `μ(l, M)`, `μ*(l, M)`.

Every statement carries the standing assumption `d ≥ 2`. Matrices `M ∈ 𝕊^d` carry
`M.IsSymm`. Sections 5.1-5.2 are deterministic: there the configuration is an arbitrary
`η : ℤ^d → ℤ`. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal

namespace RandomSandpile

/-- Lemma 5.1 (stabilizing-legal). Let `A ⊂ ℤ^d` be finite. If `u ∈ 𝓛(η, A)`, the
solution `h` of `h ∈ 𝓛(η, A) ∩ 𝒮(η, A)`, `h = u` on `∂A`, satisfies `∂⁺(u, A) ⊆ ∂⁺(h, A)`.
Similarly, if `v ∈ 𝒮(η, A)`, the solution `h*` of `h* ∈ 𝓛(η, A) ∩ 𝒮(η, A)`, `h* = v` on `∂A`,
satisfies `∂⁻(v, A) ⊆ ∂⁻(h*, A)`.

"The solution" is unique by the least action principle (Proposition 3.1, Proposition 3.2); the
statement quantifies over every such `h`, which is the printed claim whenever the solution exists.
Finiteness of `A` is used in the printed proof ("as `A` is finite, `t < ∞`").
Supergradient and subgradient sets are those of the real casts of the integer toppling functions. -/
def StabilizingLegalStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (η : Site d → ℤ) (A : Set (Site d)), A.Finite →
    (∀ u h : Site d → ℤ, u ∈ locLegal η A → h ∈ locLegal η A ∩ stabilizing η A →
        (∀ x ∈ bdry A, h x = u x) →
        supGradSet (fun x => (u x : ℝ)) A ⊆ supGradSet (fun x => (h x : ℝ)) A) ∧
    (∀ v h : Site d → ℤ, v ∈ stabilizing η A → h ∈ locLegal η A ∩ stabilizing η A →
        (∀ x ∈ bdry A, h x = v x) →
        subGradSet (fun x => (v x : ℝ)) A ⊆ subGradSet (fun x => (h x : ℝ)) A)

/-- Lemma 5.2 (ABP), the discrete Alexandroff-Bakelman-Pucci estimate. There is
`C_d > 0` such that for all `w ∈ S(B_n, η, l, M)`,
`max_{B_n} w ≤ max_{∂B_n} w + C_d n μ(B_n, η, l, M)^{1/d}`, and for all `w ∈ S*(B_n, η, l, M)`,
`inf_{∂B_n} w ≤ inf_{B_n} w + C_d n μ*(B_n, η, l, M)^{1/d}`.

Reading. `max_{B_n} w ≤ R` is written `w x ≤ R` for every `x ∈ B_n` (vacuous for `n = 0`, where
`B_0 = ∅`), and similarly for the infimum over `B_n`. The extremum over `∂B_n` is `sSup`/`sInf` of
the image of the finite set `∂B_n`, nonempty for `n ≥ 1`, hence a genuine maximum/minimum.
`μ`, `μ*` are `[0, ∞]`-valued and enter through `ENNReal.toReal`; the hypothesis `μ ≠ ∞`
(resp. `μ* ≠ ∞`) only discards the case where the printed right-hand side is `+∞` and the printed
claim is vacuous, while it keeps the junk value `toReal ∞ = 0` from turning the claim into
`max_{B_n} w ≤ max_{∂B_n} w`. -/
def ABPStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm →
      (mu (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
        ∀ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
          w x ≤ sSup (w '' bdry (ballZ0 (n : ℝ))) +
            C * n * (mu (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / (d : ℝ))) ∧
      (muStar (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
        ∀ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
          sInf (w '' bdry (ballZ0 (n : ℝ))) ≤
            w x + C * n * (muStar (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / (d : ℝ)))

/-- Proposition 5.1 (concave_rep, Lemma 4.5). For `x ∈ 𝒬̄_n`,
`Γ_w(x) = sup {∑_{i=1}^{d+1} λ_i w(x_i) : x_i ∈ Q̄_n, ∑ λ_i x_i = x, λ_i ∈ [0, 1], ∑ λ_i = 1}`,
and if `Γ_w(x) = ∑_{i=1}^{d+1} λ_i w(x_i)` (with such `λ_i`, `x_i`) then for each `x_i`,
`Γ_w(x_i) = w(x_i)`, and `Γ_w` is linear in `conv(x_1, …, x_{d+1})`.

[C proposed: the second claim is restricted to the indices with `λ_i > 0`.] As printed it is false
for indices with `λ_i = 0`: such an `x_i` is an arbitrary point of `Q̄_n`, where `Γ_w(x_i) > w(x_i)`
can hold, and on whose hull with the other points `Γ_w` need not be affine (take `x = x_1` a
contact point, `λ_1 = 1`). The paper's hidden proof assumes `λ_i > 0`, and Lemma 5.3
uses the representation with `λ_i > 0`. "Linear" means affine:
`Γ_w(y) = c + p · y` on the hull. The supremum is stated as a least upper bound (`IsLUB`), which
also asserts that the set is nonempty and bounded above, so no junk value of `sSup` enters.
`w : ℤ^d → ℝ` is arbitrary; only its values on `Q̄_n` matter. -/
def ConcaveEnvelopeRepStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (n : ℕ) (w : Site d → ℝ), ∀ x ∈ cubeHullClosure d n,
    IsLUB {s : ℝ | ∃ (lam : Fin (d + 1) → ℝ) (xs : Fin (d + 1) → Site d),
        (∀ i, xs i ∈ dClosure (cubeZ0 (n : ℝ))) ∧ (∀ i, 0 ≤ lam i ∧ lam i ≤ 1) ∧
        ∑ i, lam i = 1 ∧ ∑ i, lam i • toE (xs i) = x ∧ s = ∑ i, lam i * w (xs i)}
      (concaveEnvelope w n x) ∧
    ∀ (lam : Fin (d + 1) → ℝ) (xs : Fin (d + 1) → Site d),
      (∀ i, xs i ∈ dClosure (cubeZ0 (n : ℝ))) → (∀ i, 0 ≤ lam i ∧ lam i ≤ 1) →
      ∑ i, lam i = 1 → ∑ i, lam i • toE (xs i) = x →
      concaveEnvelope w n x = ∑ i, lam i * w (xs i) →
      (∀ i, 0 < lam i → concaveEnvelope w n (toE (xs i)) = w (xs i)) ∧
      ∃ (p : Rd d) (c : ℝ), ∀ y ∈ convexHull ℝ {z : Rd d | ∃ i, 0 < lam i ∧ z = toE (xs i)},
        concaveEnvelope w n y = c + inner ℝ p y

/-- Lemma 5.3 (MA-rep). For `w : ℤ^d → ℝ`,
`∑_{x ∈ Q_n} |∂⁺(w, x, Q_n)| = |∂⁺(w, Q_n)|
  = ∑_{x : Γ_w(x) = w(x)} |∂⁺(Γ_w, x, Q_n)| = |∂⁺(Γ_w, 𝒬_n)|`,
where `|·|` is Lebesgue measure on `ℝ^d` and `Γ_w` is the concave envelope over `Q̄_n`.

Reading. Sums are `[0, ∞]`-valued sums over the finite index sets. `∂⁺(Γ_w, x, Q_n)` is
`supGradR Γ_w x 𝒬̄_n` (supergradients tested on `𝒬̄_n`) and `∂⁺(Γ_w, 𝒬_n)` is
`supGradSetR Γ_w 𝒬_n 𝒬̄_n`. The contact set `{x : Γ_w(x) = w(x)}` of the third term is read inside
`Q_n`, as the first term and the proof indicate: contact points on `∂Q_n` include
the vertices of `𝒬̄_n`, whose supergradient sets tested on `𝒬̄_n` are unbounded cones of infinite
measure, while the other three terms are finite. -/
def MongeAmpereRepStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (n : ℕ) (w : Site d → ℝ),
    (∑' x : (cubeZ0 (d := d) (n : ℝ)), volume (supGrad w x (cubeZ0 (n : ℝ)))) =
        volume (supGradSet w (cubeZ0 (n : ℝ))) ∧
      volume (supGradSet w (cubeZ0 (n : ℝ))) =
        (∑' x : {x : Site d | x ∈ cubeZ0 (n : ℝ) ∧ concaveEnvelope w n (toE x) = w x},
          volume (supGradR (concaveEnvelope w n) (toE (x : Site d)) (cubeHullClosure d n))) ∧
      (∑' x : {x : Site d | x ∈ cubeZ0 (n : ℝ) ∧ concaveEnvelope w n (toE x) = w x},
          volume (supGradR (concaveEnvelope w n) (toE (x : Site d)) (cubeHullClosure d n))) =
        volume (supGradSetR (concaveEnvelope w n) (cubeHull d n) (cubeHullClosure d n))

/-- Lemma 5.4 (mu-is-bounded). There are `C := C_{η_max, l, M, d}` and
`C* := C*_{η_min, l, M, d}` with `μ(Q_n, η, l, M) < C |Q_n|` and `μ*(Q_n, η, l, M) < C* |Q_n|`.
For `l ≤ -η_max - Tr(M)`, `μ(Q_n, η, l, M) = 0`, and for `l ≥ (2d - 1) - η_min - Tr(M)`,
`μ*(Q_n, η, l, M) = 0`.

Reading. The lemma is deterministic: `η` is any configuration with `η ≤ η_max`
(resp. `η ≥ η_min`), the only bound the proof uses for `μ` (resp. `μ*`). The strict bounds are
stated for `n ≥ 1`; for `n = 0`, `Q_0 = ∅` and both sides vanish. They are comparisons in
`[0, ∞]`, so they include `μ < ∞`.

[C proposed: the vanishing range of `μ` is `l ≤ -max(η_max, 0) - Tr(M)`.] As printed it is false
when `η_max < 0`: for `d = 2`, `η ≡ η_max = -1`, `M = 0`, `l = 1 = -η_max - Tr(M)` and `n = 1`,
the zero toppling gives `w = -q_1 ∈ S(Q_1, η, 1, 0)`, and `∂⁺(w, 0, Q_1) = [-1/4, 1/4]²` has
measure `1/4 > 0`. The proof uses `Δ_{ℤ^d} u ≥ min(-η_max, 0)` and then replaces
the minimum by `-η_max`, which needs `η_max ≥ 0`. The two ranges agree when `η_max ≥ 0`, which the
standing assumptions force (high density gives `η_max ≥ E η(0) > 2d - 1`). -/
def MuBoundedStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
    (∀ (ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ η : Site d → ℤ, (∀ x, η x ≤ ηmax) →
        mu (cubeZ0 (n : ℝ)) η l M <
          ENNReal.ofReal (C * ((cubeZ0 (d := d) (n : ℝ)).ncard : ℝ))) ∧
    (∀ (ηmin : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ η : Site d → ℤ, (∀ x, ηmin ≤ η x) →
        muStar (cubeZ0 (n : ℝ)) η l M <
          ENNReal.ofReal (C * ((cubeZ0 (d := d) (n : ℝ)).ncard : ℝ))) ∧
    (∀ (ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm →
      l ≤ -((max ηmax 0 : ℤ) : ℝ) - M.trace →
      ∀ (n : ℕ) (η : Site d → ℤ), (∀ x, η x ≤ ηmax) → mu (cubeZ0 (n : ℝ)) η l M = 0) ∧
    (∀ (ηmin : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm →
      (2 * (d : ℝ) - 1) - (ηmin : ℝ) - M.trace ≤ l →
      ∀ (n : ℕ) (η : Site d → ℤ), (∀ x, ηmin ≤ η x) → muStar (cubeZ0 (n : ℝ)) η l M = 0)

/-- Proposition 5.2 (harnack, Lemma 2.17). Fix `0 < β < 1`. For any
`f : ℤ^d → ℝ` nonnegative, with `f(0) = 0` and `|Δ_{ℤ^d} f| ≤ λ` in `B_R`, there is a constant
`C_{β,λ}` such that `f(x) ≤ C_{β,λ} |x|²` for `x ∈ B_{βR}`.

The subscript makes `C` depend only on `β` and `λ` (and the dimension), so `C` is chosen before
`R` and `f`. -/
def HarnackQuadraticStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ β : ℝ, 0 < β → β < 1 → ∀ lam : ℝ, ∃ C : ℝ,
    ∀ (R : ℝ) (f : Site d → ℝ), (∀ x, 0 ≤ f x) → f 0 = 0 →
      (∀ x ∈ ballZ0 R, |lapR f x| ≤ lam) →
      ∀ x ∈ ballZ0 (β * R), f x ≤ C * ‖toE x‖ ^ 2

/-- Proposition 5.3 (subadditive; Akcoglu-Krengel, Dal Maso-Modica, as stated in
Armstrong-Smart), the multiparameter subadditive ergodic theorem. Let `f : Ω → 𝓜_C` be a
subadditive process. There exist an event `Ω_0` of full probability and a constant `0 ≤ a ≤ C`
such that for every `η ∈ Ω_0` and every bounded Lipschitz domain `W`,
`lim_{n → ∞} f(nW ∩ ℤ^d, η) / |nW ∩ ℤ^d| = a`.

The law is a `RandomEnvironment` (stationary and ergodic). `IsSubadditiveProcess`
includes measurability and the stationarity `f(A, T_y η) = f(y + A, η)`, which the printed
statement omits although the theorem fails without it (see `IsSubadditiveProcess`): a missing
hypothesis of the printed statement, standard in the cited sources. The event is uniform in `W`,
as printed. `|nW ∩ ℤ^d|` is the cardinality of `discretize W n`, finite because `W` is bounded. -/
def SubadditiveErgodicStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (E : RandomEnvironment d) (C : ℝ) (f : Config d → Set (Site d) → ℝ),
    IsSubadditiveProcess C f →
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ C ∧ ∀ᵐ η ∂E.P, ∀ W : Set (Rd d), IsLipschitzDomain W →
      Tendsto (fun n : ℕ => f η (discretize W n) / ((discretize W n).ncard : ℝ)) atTop (𝓝 a)

/-- Lemma 5.5 (sub-additive-ergodic). For each `M ∈ 𝕊^d` and `l ∈ ℝ` there is an
event `Ω_{l,M}` of full probability such that for every `η ∈ Ω_{l,M}` and every bounded Lipschitz
domain `W`,
`μ(l, M) := lim_{n → ∞} μ(nW ∩ ℤ^d, η, l, M) / |nW ∩ ℤ^d|` and
`μ*(l, M) := lim_{n → ∞} μ*(nW ∩ ℤ^d, η, l, M) / |nW ∩ ℤ^d|`.
Moreover there are constants `C := C_{η_max, l, M, d}` and `C* := C*_{η_min, l, M, d}` with
`0 ≤ μ(l, M) ≤ C` and `0 ≤ μ*(l, M) ≤ C*`.

Reading. The printed `:=` defines `μ(l, M)` as the limit, asserting that it exists and does not
depend on `η` or `W`; here the limit is identified with the deterministic `muBar E l M`
(resp. `muStarBar E l M`, `Defs/Effective.lean`), which is what that definition means. `μ`, `μ*`
enter through `ENNReal.toReal`; the conjunct `μ(nW ∩ ℤ^d, η, l, M) ≠ ∞` (and the same for `μ*`)
rules out the junk reading in which `toReal ∞ = 0` on both sides would make the limits trivial.
The constants depend only on the listed parameters, hence are chosen before the environment,
of which only `η_max` (resp. `η_min`) is fixed. -/
def MuConvergenceStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
    (∀ (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → ∀ l : ℝ,
      ∀ᵐ η ∂E.P, ∀ W : Set (Rd d), IsLipschitzDomain W →
        (∀ n : ℕ, mu (discretize W n) η l M ≠ ⊤ ∧ muStar (discretize W n) η l M ≠ ⊤) ∧
        Tendsto (fun n : ℕ => (mu (discretize W n) η l M).toReal /
          ((discretize W n).ncard : ℝ)) atTop (𝓝 (muBar E l M)) ∧
        Tendsto (fun n : ℕ => (muStar (discretize W n) η l M).toReal /
          ((discretize W n).ncard : ℝ)) atTop (𝓝 (muStarBar E l M))) ∧
    (∀ (ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → ∃ C : ℝ,
      ∀ E : RandomEnvironment d, E.ηmax = ηmax → 0 ≤ muBar E l M ∧ muBar E l M ≤ C) ∧
    (∀ (ηmin : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → ∃ C : ℝ,
      ∀ E : RandomEnvironment d, E.ηmin = ηmin → 0 ≤ muStarBar E l M ∧ muStarBar E l M ≤ C)

end RandomSandpile

import RandomSandpile.Defs.Viscosity
import RandomSandpile.Defs.Odometer
import Mathlib.MeasureTheory.Integral.Average

/-! # Proposed literature inputs

Statements from the literature that the paper cites and that this library does not prove. This file
contains definitions only. Each docstring gives the source, the statement in the form used, the
consumer, and why the Lean form follows from the source. A statement is an explicit hypothesis only where
a released theorem takes it as an argument (see `Assembly/Audit.lean`); otherwise it is stated but not
assumed by any released theorem. Results that the paper cites and that can be proved in the library
are not listed here.

Items headed Literature input state a result of the source. Items headed Provable give the exact
interface a consumer needs, with a proof sketch; they are candidates to be proved in the library rather
than assumed.

Conventions. `Δ_{ℤ^d}` is `lap` (integer-valued) or `lapR` (real-valued),
`Δu(x) = ∑_{y ∼ x} (u(y) - u(x))`, with no factor `1/(2d)`. In the terminology of
Crandall-Ishii-Lions, "`Δu ≥ -K` in `U` in the viscosity sense" (`u` is a viscosity subsolution of
`-Δu - K = 0`) is `ViscFromAboveGE (fun X => X.trace + K) U u`, and "`Δu ≤ K` in `U` in the
viscosity sense" (`u` is a viscosity supersolution of `-Δu + K = 0`) is
`ViscFromBelowLE (fun X => X.trace - K) U u`. `D²u(a) < -δI` for the matrices `X` of
second-order Peano expansions is `(-(δ • 1) - X).PosDef`, as in `PegdenSmartRegularityStmt`. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter

namespace RandomSandpile

/-- **Literature input. Pegden-Smart, Proposition 2.5 (touching at a point of twice differentiability).**

Source: W. Pegden and C. K. Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013),
627-642 (arXiv:1105.0111v2), Proposition 2.5, p. 6. As used for Lemma 7.6(1): two continuous functions with bounded
Laplacian whose difference exceeds its boundary maximum in the interior have a point where both
are twice differentiable, the difference is above the boundary maximum, and
`D²(u - v)(a) < -δI`. The set of such points has positive measure, which is what lets Lemma 7.6(1)
choose `a` off `∂W`.

Statement. Let `d ≥ 2`, `U ⊆ ℝ^d` bounded and open, `K ∈ ℝ`, and `u, v ∈ C(Ū)` with
`|Δu| ≤ K`, `|Δv| ≤ K` in `U` in the viscosity sense. Let `m` bound `u - v` from above on `∂U`, and
suppose `u - v > m` somewhere in `U`. Then the set of `a ∈ U` with `u(a) - v(a) > m` at which `u`
and `v` have second-order Peano expansions with symmetric matrices `X`, `X'` and `X - X' < -δI` for
some `δ > 0` has positive (outer) Lebesgue measure.

Why it holds. By Calderón-Zygmund theory a continuous `u` with `|Δu| ≤ K` in the viscosity sense
lies in `W^{2,p}_loc(U)` for every `p < ∞` and is twice differentiable a.e. (A. P. Calderón,
A. Zygmund, *Local properties of solutions of elliptic partial differential equations*, Studia
Math. 20 (1961) 171-225; Gilbarg-Trudinger, *Elliptic PDE of second order*, Theorem 9.11;
viscosity and distributional solutions agree by H. Ishii, Funkcial. Ekvac. 38 (1995) 101-120, Theorem 1, p. 103). For `w = u - v + (δ/2)|x - x*|²` with `δ` small, every slope `p` with
`|p| < η` is attained on the upper contact set of `w`, so by the ABP area-formula argument for
`W^{2,d}` functions (Gilbarg-Trudinger, Lemma 9.2 and Theorem 9.1) that set has positive
measure; at its points of twice differentiability `D²w ≤ 0`, i.e. `D²(u - v) ≤ -δI`.

Why not here: Calderón-Zygmund estimates and the `W^{2,p}` ABP inequality are not in Mathlib.
Consumer: Lemma 7.6(1) (`PegdenSmartRegularityStmt`), which must also prove that the limits
`v`, `v'` satisfy `|Δ| ≤ K` in the viscosity sense (consistency from `|Δ_{ℤ^d} v_n| ≤ C`) and that
the frontier of a Lipschitz domain is Lebesgue-null. -/
def PegdenSmartTouchingStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ U : Set (Rd d), IsOpen U → Bornology.IsBounded U →
    ∀ (K : ℝ) (u v : Rd d → ℝ), ContinuousOn u (closure U) → ContinuousOn v (closure U) →
      ViscFromAboveGE (fun X => X.trace + K) U u → ViscFromBelowLE (fun X => X.trace - K) U u →
      ViscFromAboveGE (fun X => X.trace + K) U v → ViscFromBelowLE (fun X => X.trace - K) U v →
      ∀ m : ℝ, (∀ x ∈ frontier U, u x - v x ≤ m) → (∃ x ∈ U, m < u x - v x) →
        0 < volume {a : Rd d | a ∈ U ∧ m < u a - v a ∧
          ∃ (p p' : Rd d) (X X' : Matrix (Fin d) (Fin d) ℝ),
            X.IsSymm ∧ X'.IsSymm ∧ HasSecondOrderTaylorAt u a p X ∧
            HasSecondOrderTaylorAt v a p' X' ∧
            ∃ δ : ℝ, 0 < δ ∧ (-(δ • (1 : Matrix (Fin d) (Fin d) ℝ)) - (X - X')).PosDef}

/-- **Pegden-Smart, Lemma 4.1 (Hessians of odometer limits are integer-superharmonic matrices), local form.**

Source: W. Pegden, C. K. Smart, *Convergence of the Abelian sandpile*, Duke Math. J. 162 (2013),
627-642, Lemma 4.1. Recalled content: if the scaling
limit `v` of the single-source odometers is twice differentiable at a point `x ≠ 0`, then
`D²v(x) ∈ Γ̄`, where `Γ` is the set of symmetric `A` for which some `u : ℤ^d → ℤ` has
`Δ_{ℤ^d} u ≤ 2d - 1` and `u(z) ≥ ½ zᵀAz` for all `z`. Since `Γ` is closed downward, `A ∈ Γ̄` gives
`A - εI ∈ Γ` for every `ε > 0`, which is the form of Lemma 7.6(2).

Statement (the local content of the proof, in the form the consumer has). Let `d ≥ 2`, `n_k`
strictly increasing, `v_k : ℤ^d → ℤ` with `Δ_{ℤ^d} v_k(z) ≤ 2d - 1` whenever `z / n_k ∈ B_r(a)`, and
`n_k⁻² v_k([n_k x]) → v₀` uniformly on `B_r(a)` (`rescaleOdo`). If `v₀` has a second-order Peano
expansion at `a` with symmetric matrix `X`, then for every `ε > 0` there is `u : ℤ^d → ℤ` with
`Δ_{ℤ^d} u ≤ 2d - 1` and `u(z) ≥ ½ zᵀ(X - εI)z` on all of `ℤ^d`.

Proof sketch (elementary). On the lattice ball of radius `R = ρ n_k` about `[n_k a]`,
`v_k = c + p_k·z + q_X(z) + O(θ R²)` with `θ → 0` (Taylor, then `k` large). Take a rational
symmetric `A` with `X - (ε/2)I ≤ A ≤ X - (ε/4)I`, and `N` with `N A` integral and `N ≪ R`. For
`y ∈ Nℤ^d` put `φ_y(z) = v_k(z - y + [n_k a]) + (A y)·z + c_y` on `|z - y| < R`, with `c_y ∈ ℤ`
within `1` of `p_k·y - q_A(y)`; then `φ_y ≈ c + p_k·z + q_A(z) + q_{X-A}(z - y)`, so the quadratic
gap forces `u := min_y φ_y` to be attained with `|z - y| < R/2`, whence `Δ_{ℤ^d} u ≤ 2d - 1`,
`u ≥ q_A + p_k·z - θR² - 1 ≥ q_{X - εI} - C`; add an integer constant.

Consumer: Lemma 7.6(2) and the core of 7.6(3). Note: the contradiction for `a ∉ W̄` in the proof of
Theorem 1.1 (the argument of Pegden-Smart, Theorem 4.2) compares `ψ ≈ u + affine` with the odometer
of `η` near `n a` by the least action principle; this needs `u` for `X' = D²v'(a)` (the Hessian of
the function that is smaller at `a`), not for `X = D²v(a)` as printed in Lemma 7.6(2). This
statement applies to `v'` as well, since `v'` is also a limit of free odometers and `a ∉ W̄`. -/
def PegdenSmartIntegerSuperharmonicStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ n : ℕ → ℕ, StrictMono n →
    ∀ (v : ℕ → Site d → ℤ) (v₀ : Rd d → ℝ) (a : Rd d) (r : ℝ), 0 < r →
      (∀ k, ∀ z : Site d, ‖((n k : ℝ))⁻¹ • toE z - a‖ < r → lap (v k) z ≤ 2 * (d : ℤ) - 1) →
      TendstoUniformlyOn (fun k => rescaleOdo (v k) (n k)) v₀ atTop (Metric.ball a r) →
      ∀ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ), X.IsSymm → HasSecondOrderTaylorAt v₀ a p X →
        ∀ ε : ℝ, 0 < ε → ∃ u : Site d → ℤ, ∀ x : Site d,
          lap u x ≤ 2 * (d : ℤ) - 1 ∧
            qMZ (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ (u x : ℝ)

/-- **Literature input. Gutiérrez, weak continuity of Monge-Ampère measures under uniform convergence.**

Source: C. E. Gutiérrez, *The Monge-Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
Equations and Their Applications 89, Birkhäuser, 2016 (cited in the paper as Lemma 1.6.1 for compactness of the rescaled envelopes and for
weak convergence of Monge-Ampère measures). In
the first edition (PNLDE 44, 2001) the weak convergence statement is Lemma 1.2.3 (with Lemma 1.2.2):
if `u_k`, `u` are convex in an open set `Ω` and `u_k → u` uniformly on compact subsets of `Ω`, then
`Mu_k → Mu` weakly, i.e. `∫ f dMu_k → ∫ f dMu` for every `f ∈ C_c(Ω)`, where `Mu(E) = |∂u(E)|` is
the Lebesgue measure of the image of `E` under the normal mapping
`∂u(x) = {p : u(y) ≥ u(x) + p·(y - x) for all y ∈ Ω}` (Theorem 1.1.13).

Lean form: the two portmanteau inequalities (compact sets, open sets), which follow from weak
convergence of the Radon measures `Mu_k`; this avoids building `Mu` as a `Measure`. The concave case follows by applying it to `-u` (the image of `∂⁺u` is the reflection of `∂(-u)`).
`ConvexOn ℝ Ω` includes convexity of `Ω`, which holds for the consumer's balls.

Why not here: the Monge-Ampère measure (its countable additivity) and Aleksandrov's lemma that the
slopes supporting at two points form a null set are not in Mathlib. The compactness half of the
citation is not proposed: Arzelà-Ascoli and `ConvexOn.locallyLipschitzOn` give it.
Consumer: Lemma 6.2 (`StrictConcavityStmt`). -/
def GutierrezWeakContinuityStmt : Prop :=
  ∀ (d : ℕ) (Ω : Set (Rd d)), IsOpen Ω → ∀ (u : ℕ → Rd d → ℝ) (u₀ : Rd d → ℝ),
    (∀ k, ConvexOn ℝ Ω (u k)) → ConvexOn ℝ Ω u₀ →
    (∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn u u₀ atTop K) →
      (∀ K ⊆ Ω, IsCompact K →
        limsup (fun k => volume {p : Rd d | ∃ x ∈ K, ∀ y ∈ Ω,
            u k x + inner ℝ p (y - x) ≤ u k y}) atTop ≤
          volume {p : Rd d | ∃ x ∈ K, ∀ y ∈ Ω, u₀ x + inner ℝ p (y - x) ≤ u₀ y}) ∧
      (∀ V ⊆ Ω, IsOpen V →
        volume {p : Rd d | ∃ x ∈ V, ∀ y ∈ Ω, u₀ x + inner ℝ p (y - x) ≤ u₀ y} ≤
          liminf (fun k => volume {p : Rd d | ∃ x ∈ V, ∀ y ∈ Ω,
            u k x + inner ℝ p (y - x) ≤ u k y}) atTop)

/-- **Literature input. Super-mean-value property of viscosity supersolutions of the Laplace equation.**

Sources: H. Ishii, *On the equivalence of two notions of weak solutions, viscosity solutions and
distribution solutions*, Funkcial. Ekvac. 38 (1995), 101-120 (a continuous viscosity supersolution
of `-Δv = 0` is a distributional supersolution), together with classical
potential theory (a continuous function with `Δv ≤ 0` in the sense of distributions is
superharmonic and satisfies `v(x) ≥ ⨍_{B_ρ(x)} v` whenever `B̄_ρ(x) ⊆ U`; e.g. D. H. Armitage,
S. J. Gardiner, *Classical Potential Theory*, Springer 2001, Section 3.2). A direct proof
compares `v` with the Poisson integral of `v|_{∂B_ρ(x)}`.

Statement. Let `d ≥ 1`, `U ⊆ ℝ^d` open, `v ∈ C(U)` a viscosity supersolution of `-Δv = 0` in `U`.
Then `⨍_{B_ρ(x)} v ≤ v(x)` for every closed ball `B̄_ρ(x) ⊆ U`, `ρ > 0`.

Why not here: the Dirichlet problem on balls of `ℝ^d` (Poisson kernel) and the
viscosity-distribution equivalence are not in Mathlib. Consumer: `CaffarelliCabreContactStmt`
below, hence Lemma 6.2. -/
def ViscositySuperharmonicMeanValueStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ U : Set (Rd d), IsOpen U → ∀ v : Rd d → ℝ, ContinuousOn v U →
    ViscFromBelowLE (fun X => X.trace) U v →
      ∀ (x : Rd d) (ρ : ℝ), 0 < ρ → Metric.closedBall x ρ ⊆ U →
        ⨍ y in Metric.ball x ρ, v y ≤ v x

/-- **Caffarelli-Cabré, Lemmas 3.3 and 3.5 (second-order bound of the envelope at contact points), concave and
Laplacian form.** Provable from `ViscositySuperharmonicMeanValueStmt`.

Source: L. A. Caffarelli, X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
Publications 43, 1995, Chapter 3, Lemmas 3.3 and 3.5. Recalled content: for a viscosity
supersolution `u` of `M⁻(D²u, λ, Λ) ≤ f` in `B_1` with `u ≥ 0` on `∂B_1`, the convex envelope
`Γ_u` of `-u⁻` in `B_3` is touched from above at every contact point `x₀ ∈ {u = Γ_u}` by a
paraboloid of opening `C sup f⁺` near `x₀`, hence is `C^{1,1}` there, with
`|∂Γ_u(B_r(x₀))| ≤ C (sup_{B_r(x₀)} f⁺)^d |B_r|`.

Statement (λ = Λ = 1, concave envelope, sign changed, localised). There is `C = C(d)` such that:
if `U` is convex and open, `w ∈ C(U)` has `Δw ≥ -K` (`K ≥ 0`) in `U` in the viscosity sense, `Γ` is
concave on `U` with `Γ ≥ w` on `U`, `Γ(x₀) = w(x₀)`, `p` is a supporting slope of `Γ` at `x₀`, and
`B_r(x₀) ⊆ U`, then `Γ(y) ≥ Γ(x₀) + p·(y - x₀) - C K |y - x₀|²` for `|y - x₀| < r/2`.

Proof sketch from `ViscositySuperharmonicMeanValueStmt`: with `ℓ(y) = Γ(x₀) + p·(y - x₀)`,
`v = ℓ - w ≥ 0` vanishes at `x₀` and `v - K|y - x₀|²/(2d)` is viscosity superharmonic, so
`⨍_{B_ρ(x₀)} v ≤ Kρ²/(2(d+2))`; `f = ℓ - Γ` is convex with `0 ≤ f ≤ v`, so for `|y - x₀| = s` and
`ρ = 2s`, `f(y) ≤ ⨍_{B_s(y)} f ≤ 2^d ⨍_{B_ρ(x₀)} f ≤ 2^{d+1} K s²/(d+2)`.

Consumer: Lemma 6.2 ("`φ̄` has Lipschitz gradient and `|D²φ̄| ≤ C` a.e."). Caveat for the
consumer: the bound is local at contact points; at a non-contact point the envelope is affine on a
simplex with contact vertices (Proposition 5.1) and the bound transfers only through vertices at a
distance from the boundary of the domain of the envelope bounded below. For an envelope taken over
`B_1` itself, vertices on `∂B_1`, where no equation holds, can create ridges of high curvature
inside `B_δ`, so a uniform `C` requires an extra argument (Caffarelli and Cabré avoid this by taking the envelope
over `B_3` of a function extended by `0`). -/
def CaffarelliCabreContactStmt : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ U : Set (Rd d), IsOpen U → Convex ℝ U →
    ∀ K : ℝ, 0 ≤ K → ∀ w Γ : Rd d → ℝ, ContinuousOn w U →
      ViscFromAboveGE (fun X => X.trace + K) U w →
      ConcaveOn ℝ U Γ → (∀ y ∈ U, w y ≤ Γ y) →
      ∀ x₀ ∈ U, Γ x₀ = w x₀ → ∀ p : Rd d, (∀ y ∈ U, Γ y ≤ Γ x₀ + inner ℝ p (y - x₀)) →
        ∀ r : ℝ, Metric.ball x₀ r ⊆ U → ∀ y ∈ Metric.ball x₀ (r / 2),
          Γ x₀ + inner ℝ p (y - x₀) - C * K * ‖y - x₀‖ ^ 2 ≤ Γ y

/-- **Literature input. Lawler-Limic, difference estimate for discrete harmonic functions.**

Source: G. F. Lawler, V. Limic, *Random Walk: A Modern Introduction*, Cambridge Studies in Advanced
Mathematics 123, Cambridge University Press, 2010, Section 6.3 ("Difference estimates and Harnack
inequality"), Theorem 6.3.8(a) (specialized to simple random walk; small `n` by the trivial bound `2M`): for every `p ∈ 𝒫_d` there is `c` such that if
`f : B̄_n → ℝ` is harmonic in `B_n` (`ℒf = 0`), then `|∇_j f(0)| ≤ c ‖f‖_∞ n⁻¹`. For the simple
random walk `ℒf = Δ_{ℤ^d} f / (2d)`, so harmonicity is `lapR f = 0`; `B̄_n = B_n ∪ ∂B_n` is
`dClosure (ballZ0 n)`.

Statement. For `d ≥ 1` there is `C` such that for `n ≥ 1`, `f : ℤ^d → ℝ` with `lapR f = 0` on
`B_n` and `|f| ≤ M` on `B̄_n`, and every direction `i`, `|f(e_i) - f(0)| ≤ C M / n`.

Consumers: the (difference) estimate of Lemma 7.3 (`|∇_y g_n(x, y)| ≤ C_δ
(1 + |x - y|)^{1-d}` for `|x|, |y| < (1-δ)n`), by applying it to `g_n(x, ·) - g_n(x, y)` on the ball
about `y` of radius `min(|x - y|, δn)/2` together with Lattice-Probability's Green function bounds;
and the interior difference estimates for `g_{W_n}(x, ·)` that Lemma 8.1 needs.
Could be proved here (reflection coupling, or the Poisson kernel with
`LatticeProb.exists_srwGreenInf_gradient`); proposed because neither route is in
Lattice-Probability. -/
def LawlerLimicHarmonicDifferenceStmt : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (f : Site d → ℝ) (M : ℝ),
    (∀ z ∈ ballZ0 (n : ℝ), lapR f z = 0) → (∀ z ∈ dClosure (ballZ0 (n : ℝ)), |f z| ≤ M) →
      ∀ i : Fin d, |f (unit i) - f 0| ≤ C * M / n

end RandomSandpile

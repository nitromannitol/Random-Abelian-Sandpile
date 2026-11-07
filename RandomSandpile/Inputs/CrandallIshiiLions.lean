import RandomSandpile.Defs.Viscosity

/-! # Crandall-Ishii-Lions, *User's guide*: Theorem 3.2, Theorem 4.1, Lemma 6.1

Literature inputs from Crandall, Ishii and Lions for the Perron construction and the stability step of the
two-dimensional proof of Theorem 9.2. Definitions and stated results only: nothing here is proved.

Source: M. G. Crandall, H. Ishii, P.-L. Lions, *User's guide to viscosity solutions of second order
partial differential equations*, Bull. Amer. Math. Soc. (N.S.) 27 (1992), no. 1, 1-67,
DOI 10.1090/S0273-0979-1992-00266-5.

Conventions of the source (CIL p. 1-2, (0.1)-(0.3); §2, (2.3)-(2.5), Def. 2.2).
* `F(x, r, p, X)` with `x, p ∈ ℝ^N`, `r ∈ ℝ`, `X ∈ 𝒮(N)` (symmetric). `F` is *proper* (0.1) if
  `F(x, r, p, X) ≤ F(x, s, p, Y)` whenever `r ≤ s` and `Y ≤ X`.
* The second-order superjet `J^{2,+}_𝒪 u(x̂)` is the set of `(p, X) ∈ ℝ^N × 𝒮(N)` with
  `u(x) ≤ u(x̂) + ⟨p, x - x̂⟩ + ½⟨X(x - x̂), x - x̂⟩ + o(|x - x̂|²)` as `𝒪 ∋ x → x̂` (CIL (2.3) and
  p. 10); the subjet `J^{2,-}_𝒪 u = -J^{2,+}_𝒪(-u)`. Here `½⟨Xh, h⟩ = qM X h`.
* A (viscosity) subsolution of `F = 0` on `𝒪` is `u ∈ USC(𝒪)` with `F(x, u(x), p, X) ≤ 0` for all
  `x ∈ 𝒪`, `(p, X) ∈ J^{2,+}_𝒪 u(x)` (Def. 2.2, (2.4)); a supersolution is `u ∈ LSC(𝒪)` with
  `F(x, u(x), p, X) ≥ 0` on `J^{2,-}_𝒪 u(x)` ((2.5)); a solution is both.
* The closures `J̄^{2,±}_𝒪 u(x)` (CIL (2.6)-(2.7), used in Theorem 3.2): limits of
  `(p_n, X_n) ∈ J^{2,±}_𝒪 u(x_n)` with `(x_n, u(x_n)) → (x, u(x))`.

The library's test-function predicates (`ViscFromAboveLE`...) are the `C²`-test form of
Def. 2.2 for operators `F(X)`; the adapter between the two forms is proved where these inputs are
used, not assumed. -/

noncomputable section

open Filter Topology

namespace RandomSandpile

namespace CrandallIshiiLions

variable {N : ℕ}

/-- The second-order superjet `J^{2,+}_𝒪 u(a)` (CIL (2.3), p. 10): pairs `(p, X)`, `X` symmetric,
with `u(x) ≤ u(a) + ⟨p, x - a⟩ + ½⟨X(x - a), x - a⟩ + o(|x - a|²)` as `𝒪 ∋ x → a`; the `o(·)` is
written out as: for every `ε > 0`, eventually `≤ … + ε|x - a|²`. -/
def superJet2 (O : Set (Rd N)) (u : Rd N → ℝ) (a : Rd N) :
    Set (Rd N × Matrix (Fin N) (Fin N) ℝ) :=
  {pX | pX.2.IsSymm ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ x in 𝓝[O] a,
    u x ≤ u a + inner ℝ pX.1 (x - a) + qM pX.2 (x - a) + ε * ‖x - a‖ ^ 2}

/-- The second-order subjet `J^{2,-}_𝒪 u(a) = -J^{2,+}_𝒪(-u)(a)` (CIL p. 10). -/
def subJet2 (O : Set (Rd N)) (u : Rd N → ℝ) (a : Rd N) :
    Set (Rd N × Matrix (Fin N) (Fin N) ℝ) :=
  {pX | pX.2.IsSymm ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ x in 𝓝[O] a,
    u a + inner ℝ pX.1 (x - a) + qM pX.2 (x - a) - ε * ‖x - a‖ ^ 2 ≤ u x}

/-- The closed superjet `J̄^{2,+}_𝒪 u(a)` (CIL (2.6)): `(p, X)` such that there are `x_n ∈ 𝒪` and
`(p_n, X_n) ∈ J^{2,+}_𝒪 u(x_n)` with `(x_n, u(x_n), p_n, X_n) → (a, u(a), p, X)`. -/
def closedSuperJet2 (O : Set (Rd N)) (u : Rd N → ℝ) (a : Rd N) :
    Set (Rd N × Matrix (Fin N) (Fin N) ℝ) :=
  {pX | ∃ (x : ℕ → Rd N) (q : ℕ → Rd N × Matrix (Fin N) (Fin N) ℝ),
    (∀ n, x n ∈ O) ∧ (∀ n, q n ∈ superJet2 O u (x n)) ∧ Tendsto x atTop (𝓝 a) ∧
      Tendsto (fun n => u (x n)) atTop (𝓝 (u a)) ∧ Tendsto q atTop (𝓝 pX)}

/-- The closed subjet `J̄^{2,-}_𝒪 u(a)` (CIL (2.7)). -/
def closedSubJet2 (O : Set (Rd N)) (u : Rd N → ℝ) (a : Rd N) :
    Set (Rd N × Matrix (Fin N) (Fin N) ℝ) :=
  {pX | ∃ (x : ℕ → Rd N) (q : ℕ → Rd N × Matrix (Fin N) (Fin N) ℝ),
    (∀ n, x n ∈ O) ∧ (∀ n, q n ∈ subJet2 O u (x n)) ∧ Tendsto x atTop (𝓝 a) ∧
      Tendsto (fun n => u (x n)) atTop (𝓝 (u a)) ∧ Tendsto q atTop (𝓝 pX)}

/-- `F` is proper (CIL (0.1)): `F(x, r, p, X) ≤ F(x, s, p, Y)` whenever `r ≤ s` and `Y ≤ X`
(`X - Y` positive semidefinite), `X, Y ∈ 𝒮(N)`. -/
def IsProper (F : Rd N → ℝ → Rd N → Matrix (Fin N) (Fin N) ℝ → ℝ) : Prop :=
  ∀ (x : Rd N) (r s : ℝ) (p : Rd N) (X Y : Matrix (Fin N) (Fin N) ℝ), X.IsSymm → Y.IsSymm →
    r ≤ s → (X - Y).PosSemidef → F x r p X ≤ F x s p Y

/-- Viscosity subsolution of `F = 0` on `𝒪` (CIL Def. 2.2, (2.4)): `u ∈ USC(𝒪)` and
`F(x, u(x), p, X) ≤ 0` for `x ∈ 𝒪`, `(p, X) ∈ J^{2,+}_𝒪 u(x)`. -/
def IsSubsolution (F : Rd N → ℝ → Rd N → Matrix (Fin N) (Fin N) ℝ → ℝ) (O : Set (Rd N))
    (u : Rd N → ℝ) : Prop :=
  UpperSemicontinuousOn u O ∧ ∀ x ∈ O, ∀ pX ∈ superJet2 O u x, F x (u x) pX.1 pX.2 ≤ 0

/-- Viscosity supersolution of `F = 0` on `𝒪` (CIL Def. 2.2, (2.5)): `u ∈ LSC(𝒪)` and
`F(x, u(x), p, X) ≥ 0` for `x ∈ 𝒪`, `(p, X) ∈ J^{2,-}_𝒪 u(x)`. -/
def IsSupersolution (F : Rd N → ℝ → Rd N → Matrix (Fin N) (Fin N) ℝ → ℝ) (O : Set (Rd N))
    (u : Rd N → ℝ) : Prop :=
  LowerSemicontinuousOn u O ∧ ∀ x ∈ O, ∀ pX ∈ subJet2 O u x, 0 ≤ F x (u x) pX.1 pX.2

/-- Subsolution of the Dirichlet problem (DP) `F = 0` in `Ω`, `u = 0` on `∂Ω` (CIL §4):
`u ∈ USC(Ω̄)`, a subsolution of `F = 0` in `Ω`, and `u ≤ 0` on `∂Ω`. -/
def IsSubsolutionDP (F : Rd N → ℝ → Rd N → Matrix (Fin N) (Fin N) ℝ → ℝ) (Ω : Set (Rd N))
    (u : Rd N → ℝ) : Prop :=
  UpperSemicontinuousOn u (closure Ω) ∧ IsSubsolution F Ω u ∧ ∀ x ∈ frontier Ω, u x ≤ 0

/-- Supersolution of (DP): `u ∈ LSC(Ω̄)`, a supersolution of `F = 0` in `Ω`, `u ≥ 0` on `∂Ω`. -/
def IsSupersolutionDP (F : Rd N → ℝ → Rd N → Matrix (Fin N) (Fin N) ℝ → ℝ) (Ω : Set (Rd N))
    (u : Rd N → ℝ) : Prop :=
  LowerSemicontinuousOn u (closure Ω) ∧ IsSupersolution F Ω u ∧ ∀ x ∈ frontier Ω, 0 ≤ u x

/-- The lower semicontinuous envelope (CIL (4.1), relative to `Ω̄`) vanishes at `x`:
`u_*(x) = liminf_{Ω̄ ∋ y → x} u(y) = 0`, written as `liminf ≥ 0` and `liminf ≤ 0`. -/
def LowerEnvelopeZeroAt (Ω : Set (Rd N)) (u : Rd N → ℝ) (x : Rd N) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝[closure Ω] x, -ε < u y) ∧
    ∀ ε : ℝ, 0 < ε → ∃ᶠ y in 𝓝[closure Ω] x, u y < ε

/-- The upper semicontinuous envelope (CIL (4.1), relative to `Ω̄`) vanishes at `x`:
`u^*(x) = limsup_{Ω̄ ∋ y → x} u(y) = 0`. -/
def UpperEnvelopeZeroAt (Ω : Set (Rd N)) (u : Rd N → ℝ) (x : Rd N) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝[closure Ω] x, u y < ε) ∧
    ∀ ε : ℝ, 0 < ε → ∃ᶠ y in 𝓝[closure Ω] x, -ε < u y

/-- **Literature input. Crandall-Ishii-Lions, Theorem 3.2 (theorem of sums), in the form printed on p. 17,
(3.9)-(3.10)**: `k = 2`, `𝒪₁ = 𝒪₂ = 𝒪`, `u₁ = u`, `u₂ = -v`,
`φ(x, y) = (α/2)|x - y|²`, `ε = 1/α`: "at a maximum `(x̂, ŷ)` of `u(x) - v(y) - (α/2)|x - y|²`
there exist `X, Y ∈ 𝒮(N)` such that `(α(x̂ - ŷ), X) ∈ J̄^{2,+}_𝒪 u(x̂)`,
`(α(x̂ - ŷ), Y) ∈ J̄^{2,-}_𝒪 v(ŷ)` and
`-3α [[I, 0], [0, I]] ≤ [[X, 0], [0, -Y]] ≤ 3α [[I, -I], [-I, I]]`."

Reading. Theorem 3.2 needs a local maximum relative to `𝒪 × 𝒪`, `𝒪` locally compact; we state it
for open `𝒪` (open sets are locally compact), a special case. The block inequalities are written
with quadratic forms: for all `ξ, ζ`, `-3α(|ξ|² + |ζ|²) ≤ ξᵀXξ - ζᵀYζ ≤ 3α|ξ - ζ|²`. -/
def CILTheoremOfSumsStmt : Prop :=
  ∀ (N : ℕ) (O : Set (Rd N)), IsOpen O → ∀ u v : Rd N → ℝ,
    UpperSemicontinuousOn u O → LowerSemicontinuousOn v O → ∀ α : ℝ, 0 < α →
      ∀ x y : Rd N, x ∈ O → y ∈ O →
        IsLocalMaxOn (fun z : Rd N × Rd N => u z.1 - v z.2 - α / 2 * ‖z.1 - z.2‖ ^ 2)
          (O ×ˢ O) (x, y) →
        ∃ X Y : Matrix (Fin N) (Fin N) ℝ, X.IsSymm ∧ Y.IsSymm ∧
          (α • (x - y), X) ∈ closedSuperJet2 O u x ∧ (α • (x - y), Y) ∈ closedSubJet2 O v y ∧
          (∀ ξ ζ : Rd N, -(3 * α) * (‖ξ‖ ^ 2 + ‖ζ‖ ^ 2) ≤
            matrixBilin X ξ ξ - matrixBilin Y ζ ζ) ∧
          ∀ ξ ζ : Rd N, matrixBilin X ξ ξ - matrixBilin Y ζ ζ ≤ 3 * α * ‖ξ - ζ‖ ^ 2

/-- **Literature input. Crandall-Ishii-Lions, Theorem 4.1 (Perron's method)** (p. 22):
"Let comparison hold for (DP); i.e., if `w` is a subsolution of (DP) and `v` is a supersolution of
(DP), then `w ≤ v`. Suppose also that there is a subsolution `u̲` and a supersolution `ū` of (DP)
that satisfy the boundary condition `u̲_*(x) = ū^*(x) = 0` for `x ∈ ∂Ω`. Then
`W(x) = sup {w(x) : u̲ ≤ w ≤ ū and w is a subsolution of (DP)}` is a solution of (DP)."

Standing assumptions of CIL §4: `Ω ⊆ ℝ^N` is an arbitrary open set, `F` is proper
and continuous (here: continuous on all of `ℝ^N × ℝ × ℝ^N × 𝕄_N`, a special case). A solution of
(DP) is `u ∈ C(Ω̄)` that is a solution of `F = 0` in `Ω` with `u = 0` on `∂Ω`. The orders
`w ≤ v`, `u̲ ≤ w ≤ ū` are pointwise on `Ω̄`. -/
def CILPerronStmt : Prop :=
  ∀ (N : ℕ) (F : Rd N → ℝ → Rd N → Matrix (Fin N) (Fin N) ℝ → ℝ) (Ω : Set (Rd N)),
    IsOpen Ω → IsProper F →
    Continuous (fun w : Rd N × ℝ × Rd N × Matrix (Fin N) (Fin N) ℝ =>
      F w.1 w.2.1 w.2.2.1 w.2.2.2) →
    (∀ w v : Rd N → ℝ, IsSubsolutionDP F Ω w → IsSupersolutionDP F Ω v →
      ∀ x ∈ closure Ω, w x ≤ v x) →
    ∀ ul uu : Rd N → ℝ, IsSubsolutionDP F Ω ul → IsSupersolutionDP F Ω uu →
      (∀ x ∈ frontier Ω, LowerEnvelopeZeroAt Ω ul x ∧ UpperEnvelopeZeroAt Ω uu x) →
      let W : Rd N → ℝ := fun x => sSup ((fun w : Rd N → ℝ => w x) ''
        {w | (∀ y ∈ closure Ω, ul y ≤ w y ∧ w y ≤ uu y) ∧ IsSubsolutionDP F Ω w})
      ContinuousOn W (closure Ω) ∧ IsSubsolution F Ω W ∧ IsSupersolution F Ω W ∧
        ∀ x ∈ frontier Ω, W x = 0

/-- **Literature input. Crandall-Ishii-Lions, Lemma 6.1** (p. 33): "Let `u_n ∈ USC(𝒪)` for
`n = 1, 2, …` and `U` be given by (6.1), `z ∈ 𝒪` and `U(z) < ∞`. If `(p, X) ∈ J^{2,+}_𝒪 U(z)`,
then there exist sequences `n_j → ∞`, `x_j ∈ 𝒪`, `(p_j, X_j) ∈ J^{2,+}_𝒪 u_{n_j}(x_j)` such that
`(x_j, u_{n_j}(x_j), p_j, X_j) → (z, U(z), p, X)`."

Reading. (6.1) is `U(z) = limsup* u_n(z) = lim_{j→∞} sup {u_n(x) : n ≥ j, x ∈ 𝒪, |z - x| < 1/j}`.
We state the lemma for real-valued `U` on `𝒪` (finite at every point, a special case), with (6.1)
written out: (a) for every `ε > 0` there is `j` with `u_n(x) < U(z) + ε` for `n ≥ j`, `x ∈ 𝒪`,
`|z - x| < 1/j`; (b) for every `ε > 0` and `j` there are `n ≥ j` and `x ∈ 𝒪`, `|z - x| < 1/j`,
with `u_n(x) > U(z) - ε`. `𝒪` is taken open (locally compact, the standing assumption of §6). -/
def CILLimsupJetStmt : Prop :=
  ∀ (N : ℕ) (O : Set (Rd N)), IsOpen O → ∀ (u : ℕ → Rd N → ℝ) (U : Rd N → ℝ),
    (∀ n, UpperSemicontinuousOn (u n) O) →
    (∀ z ∈ O, ∀ ε : ℝ, 0 < ε → ∃ j : ℕ, 0 < j ∧ ∀ n, j ≤ n → ∀ x ∈ O,
      ‖z - x‖ < 1 / (j : ℝ) → u n x < U z + ε) →
    (∀ z ∈ O, ∀ ε : ℝ, 0 < ε → ∀ j : ℕ, 0 < j → ∃ n, j ≤ n ∧ ∃ x ∈ O,
      ‖z - x‖ < 1 / (j : ℝ) ∧ U z - ε < u n x) →
    ∀ z ∈ O, ∀ pX ∈ superJet2 O U z,
      ∃ (n : ℕ → ℕ) (x : ℕ → Rd N) (q : ℕ → Rd N × Matrix (Fin N) (Fin N) ℝ),
        Tendsto n atTop atTop ∧ (∀ j, x j ∈ O) ∧ (∀ j, q j ∈ superJet2 O (u (n j)) (x j)) ∧
        Tendsto x atTop (𝓝 z) ∧ Tendsto (fun j => u (n j) (x j)) atTop (𝓝 (U z)) ∧
        Tendsto q atTop (𝓝 pX)

end CrandallIshiiLions

end RandomSandpile

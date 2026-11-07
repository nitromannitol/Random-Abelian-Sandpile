import RandomSandpile.Defs.Effective

/-! # Statements of Section 6: the effective equation

* `MuMonotoneStmt` — Lemma 6.1 (`monotonicity`);
* `StrictConcavityStmt` — Lemma 6.2 (`strict-convexity`), with the correction [C2], the intended reading [C4] and the correction [C11] (the
  constant depends on `β`);
* `MuLipschitzStmt` — Lemma 6.3 (`continuity`), with the correction [C1];
* `EffectiveOperatorBasicStmt` — Lemma 6.4 (`lemma:basic_effective`).

The auxiliary definition `convexEnvelopeOn` (the convex envelope, dual of `concaveEnvelopeOn`),
needed for the `μ*` half of Lemma 6.2 ("an analogous result holds for `μ*` with a sign
change"), lives in `Defs/Mu.lean`.

Standing assumptions: `d ≥ 2`, and the law of `η` is a `RandomEnvironment d`
(uniformly bounded by `ηmin, ηmax`, stationary, ergodic). Section 6 never uses high density.
Lemma 6.1 is deterministic and holds in every dimension, so it carries no hypothesis on `d`., every constant `C` is positive. A constant `C_{ηmin, ηmax, …}` is chosen after
the listed parameters and before the environment, which is then only constrained to have the
bounds `ηmin, ηmax`. -/

open MeasureTheory LatticeProb Filter
open scoped ENNReal

namespace RandomSandpile

/-- Lemma 6.1 (monotonicity). For every `s ≥ 0`,
`μ(B_n, η, l + s, M) ≥ μ(B_n, η, l, M)` and `μ*(B_n, η, l - s, M) ≥ μ*(B_n, η, l, M)`.

The lemma is deterministic. It holds for a fixed configuration `η : ℤ^d → ℤ`, every radius
`n ∈ ℕ`, every level `l ∈ ℝ` and every matrix `M`. The proof uses neither symmetry of `M` (since
`q_M` only sees the symmetric part of `M`) nor `d ≥ 2`, so neither is assumed. Both quantities are
compared in `[0, ∞]`, where `mu` and `muStar` take their values. -/
def MuMonotoneStmt : Prop :=
  ∀ (d : ℕ) (η : Site d → ℤ) (n : ℕ) (l s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), 0 ≤ s →
    mu (ballZ0 (n : ℝ)) η l M ≤ mu (ballZ0 (n : ℝ)) η (l + s) M ∧
      muStar (ballZ0 (n : ℝ)) η l M ≤ muStar (ballZ0 (n : ℝ)) η (l - s) M

/-- Lemma 6.2 (strict-convexity), with the correction [C2], the
intended reading [C4] and the correction [C11].

Printed: "Suppose that `α := μ(l_M, M) > 0`. There exists a constant
`C := C_{ηmin, ηmax, l, M, d}` so that for each `η` in a set `Ω_{l,M}` of full probability and
`0 < β < 1` the following holds. There is an `n_0 ∈ ℕ` so that for all `n ≥ n_0`, there exists
`w_n ∈ S(B_n, η, l, M)` so that for each `x_0 ∈ {Γ_{w_n} = w_n} ∩ B_{βn}` and
`p_0 ∈ ∂⁺(w_n, x_0, B_n)`, `w_n(y) ≤ w_n(x_0) + p_0 · (y - x) - C α n²` for all `y ∈ ∂B_n`.
An analogous result holds for `μ*` with a sign change."

[C2]: `α := μ(l, M) > 0` and `p_0 · (y - x_0)`. These fix
index typos: the conclusion concerns a free `l`, the proof uses Lemma 5.5 at `(l, M)`, and the
contact point is `x_0`.

[C11]: the constant also depends on `β`,
`C := C_{ηmin, ηmax, l, M, d, β}`. The proof bends the supporting plane at a contact
point `x₀ ∈ B_{βn}` by `≍ α (1-β) n |y - x₀|` at `y ∈ ∂B_n`, and `|y - x₀| ≥ (1-β) n`, so it gives
`C(β) = c (1-β)²` with `c = c_{ηmin, ηmax, l, M, d}`. The statement is drafted in that explicit
form: the drop is `c (1-β)² α n²`, with `c` chosen before `β`. For each `β` this is the printed
conclusion with `C = c (1-β)²`. The full-probability set `Ω_{l,M}` still does not depend on `β`.

[C4] (intended reading: a proof gap, not a statement correction): as
printed (even with [C2]) the statement is trivially true, because nothing links `w_n` to `μ`. `𝓛(η, B_n)` allows arbitrary topplings of `∂B_n` (`locLegal`). So
`u := K · 1_{∂B_n}` is locally legal, and for `K > 2 max_{B̄_n} |q_l + q_M|` the function
`w_n := u - q_l - q_M` lies strictly below its concave envelope at every point of `B_n` (every
point of `B_n` lies in the convex hull of `∂B_n`). The contact set in `B_{βn}` is then empty, and
the conclusion holds vacuously. In the same way, for `μ*` take `v := K (R² - |x|²)` on `B̄_n`
(`R² ≥ max_{B̄_n} |x|²` an integer, `K` large): it is stabilizing, and `v - q_l - q_M` is
strictly concave, so no point of `B_n` touches its convex envelope.
The proof chooses `w_n` satisfying (spreadout),
`α/2 ≤ |∂⁺(Γ_{w_n}, B_{βn})| / |B_{βn}|`, and Lemma 6.3's proof applies the
bending to `w_n` close to achieving the supremum in `μ(B_n, η, l, M)`. The proposed correction
adds the first inequality of (spreadout) as a conjunct about the same `w_n`. It is written with the
lattice supergradients of `w_n` at points of `B_{βn}` (tested on `B̄_n`), which has the same
Lebesgue measure as `∂⁺(Γ_{w_n}, B_{βn})`. The reason: `Γ_{w_n}` is polyhedral, its vertices are
contact points `x`, where `∂⁺(Γ_{w_n}, x) = ∂⁺(w_n, x, B_n)`, and its other faces contribute a
null set; `∂⁺(w_n, x, B_n) = ∅` off the contact set. The witnesses above violate this conjunct
when `α > 0`.

Reading. `B_r = ballZ0 r`, `∂B_n = bdry (ballZ0 n)`, `|B_{βn}| = (ballZ0 (β n)).ncard`. The
contact set `{Γ_{w_n} = w_n}` uses `concaveEnvelopeOn (ballZ0 n) w_n` at lattice points.
`∂⁺(w_n, x_0, B_n) = supGrad w_n x_0 (ballZ0 n)`, and `α = muBar E l M`. The dual statement
uses `μ*`, `S*`, the convex envelope `convexEnvelopeOn`, subgradients `subGrad`, and the reversed
inequality `w_n(y) ≥ w_n(x_0) + p_0 · (y - x_0) + C α* n²` with `α* = muStarBar E l M`. One
constant serves both halves (take the smaller of the two, since a smaller `C > 0` weakens the
bending). `C > 0` is the paper's convention, and it is essential: with `C = 0` the
bending is the definition of `p_0 ∈ ∂⁺(w_n, x_0, B_n)` (since `∂B_n ⊆ B̄_n`). The full-probability
set `Ω_{l,M}` does not depend on `β`, so `∀ᵐ η` comes before `∀ β`. With [C11] the drop is
`C (1-β)² α n²` (resp. `C (1-β)² α* n²`). The body is that of `StrictConcavityBetaStmt`
(`Steps/Sec6/StrictConcavity.lean`), which is proved. -/
def StrictConcavityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
      (0 < muBar E l M →
        ∀ᵐ η ∂E.P, ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∃ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M,
            ENNReal.ofReal (muBar E l M / 2 * ((ballZ0 (d := d) (β * n)).ncard : ℝ)) ≤
                volume (⋃ x ∈ ballZ0 (β * n), supGrad w x (ballZ0 (n : ℝ))) ∧
              ∀ x₀ ∈ ballZ0 (β * n), concaveEnvelopeOn (ballZ0 (n : ℝ)) w (toE x₀) = w x₀ →
                ∀ p₀ ∈ supGrad w x₀ (ballZ0 (n : ℝ)), ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                  w y ≤ w x₀ + inner ℝ p₀ (toE y - toE x₀) -
                    C * (1 - β) ^ 2 * muBar E l M * (n : ℝ) ^ 2) ∧
      (0 < muStarBar E l M →
        ∀ᵐ η ∂E.P, ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∃ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M,
            ENNReal.ofReal (muStarBar E l M / 2 * ((ballZ0 (d := d) (β * n)).ncard : ℝ)) ≤
                volume (⋃ x ∈ ballZ0 (β * n), subGrad w x (ballZ0 (n : ℝ))) ∧
              ∀ x₀ ∈ ballZ0 (β * n), convexEnvelopeOn (ballZ0 (n : ℝ)) w (toE x₀) = w x₀ →
                ∀ p₀ ∈ subGrad w x₀ (ballZ0 (n : ℝ)), ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                  w x₀ + inner ℝ p₀ (toE y - toE x₀) +
                    C * (1 - β) ^ 2 * muStarBar E l M * (n : ℝ) ^ 2 ≤ w y)

/-- Lemma 6.3 (continuity), with the correction [C1].

Printed: "There is a constant `C_{ηmin, ηmax, l, M, d}` so that for all `0 < s < 1`,
`μ(l, M) ≤ μ(l - s, M) + sC` and `μ*(l, M) ≥ μ*(l + s, M) + sC`."

[C1]: the second inequality reads
`μ*(l, M) ≤ μ*(l + s, M) + sC`. As printed it forces `C ≤ 0` wherever `μ*` vanishes
(Lemma 5.4). Then the first inequality and Lemma 6.1 make `μ(·, M)` constant, which contradicts
Lemma 5.4 and the definition of `F̄_η`. The first inequality is as printed.

`μ(l, M)` and `μ*(l, M)` are the deterministic limits `muBar`, `muStarBar` of Lemma 5.5. Their
finiteness is the content of Lemmas 5.4-5.5 and is not repeated here. A single constant serves
both inequalities, as printed. -/
def MuLipschitzStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
      ∀ s : ℝ, 0 < s → s < 1 →
        muBar E l M ≤ muBar E (l - s) M + s * C ∧
          muStarBar E l M ≤ muStarBar E (l + s) M + s * C

/-- Lemma 6.4 (basic properties of the effective equation). For every
`M, N ∈ 𝐒^d`:
1. degenerate elliptic: if `M ≤ N`, then `F̄_η(M) ≥ F̄_η(N)`;
2. Lipschitz continuous: `|F̄_η(M) - F̄_η(N)| ≤ C |M - N|₂`;
3. bounded: `|F̄_η(M)| < ∞`.

Reading. `𝐒^d` is the set of symmetric real matrices (`Matrix.IsSymm`). `M ≤ N` means
`N - M ≥ 0`, i.e. `N - M` has nonnegative eigenvalues, which is `(N - M).PosSemidef`.
`|A|₂` is "the largest in magnitude eigenvalue of `A`". For symmetric `A` this is the
operator norm of `A` on Euclidean `ℝ^d`, which is used here: `‖Matrix.toEuclideanCLM A‖` (the norm
of Mathlib's `Matrix.Norms.L2Operator`, `Matrix.l2_opNorm_def`).

`F̄_η(M) = effOp E M = sSup (muEqSet E M)`. Item 3 is stated as
`IsGreatest (muEqSet E M) (effOp E M)`: the largest `l` with `μ(l, M) = μ*(l, M)` exists
. Merely asserting that the real number `effOp E M` is finite would be vacuous, since
`sSup` returns the junk value `0` on empty or unbounded sets. With item 3, items 1 and 2 are
about genuine maxima.

Item 2 needs a constant uniform in `M, N`; otherwise it would follow from item 3 alone. The
paper's `C` is a generic positive constant, read as `C_{ηmin, ηmax, d}`; the proof
 gives `C = 1`. Section 6 does not use high density. -/
def EffectiveOperatorBasicStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin ηmax : ℤ),
    ∃ C : ℝ, 0 < C ∧ ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
      ∀ M N : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → N.IsSymm →
        ((N - M).PosSemidef → effOp E N ≤ effOp E M) ∧
          |effOp E M - effOp E N| ≤
            C * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (M - N)‖ ∧
          IsGreatest (muEqSet E M) (effOp E M)

end RandomSandpile

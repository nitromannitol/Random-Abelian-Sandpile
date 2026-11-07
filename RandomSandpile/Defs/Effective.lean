import RandomSandpile.Defs.Mu
import RandomSandpile.Defs.Environment

/-! # The deterministic limits `μ(l, M)`, `μ*(l, M)` and the effective operators `F̄_η`, `F̄_0`

* `muBar E l M`, `muStarBar E l M`: the almost-sure constants `μ(l, M)`, `μ*(l, M)` of Lemma 5.5, defined without reference to a particular sample `η`;
* `muEqSet E M`: the set of `l` with `μ(l, M) = μ*(l, M)`;
* `effOp E M`: the effective operator `F̄_η(M) = l_M`, the largest such `l`;
* `effOp0 d M`: the single-source operator `F̄_0(M)` of Pegden and Smart. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal

namespace RandomSandpile

variable {d : ℕ}

/-! ### The deterministic limits of Lemma 5.5 -/

/-- The deterministic limit `μ(l, M)` of Lemma 5.5, defined independently of the
sample: the `P`-average of `limsup_n μ(B_n, η, l, M) / |B_n|`, with `B_n = {|y|₂ < n}` the
discrete ball, computed in `[0, ∞]`.

Lemma 5.5 (`MuConvergenceStmt`) asserts that for `P`-a.e. `η` and every bounded Lipschitz domain
`W`, `μ(nW ∩ ℤ^d, η, l, M) / |nW ∩ ℤ^d|` converges to `muBar E l M`. This identification is the
content of the lemma, not of the definition; it is consistent with the definition because `B_n`
is `nW ∩ ℤ^d` for the open unit ball `W`: once the normalized quantities converge along the balls
to a finite constant `c` for `P`-a.e. `η`, the integrand equals `c` a.e. and
`∫⁻ c ∂P = c` (`P` is a probability measure). Using `∫⁻` of an `ℝ≥0∞`-valued `limsup` rather than
a Bochner integral avoids any measurability or integrability side condition in this argument
(`lintegral_congr_ae` needs neither). -/
noncomputable def muBar (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (∫⁻ η, limsup (fun n : ℕ => mu (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P).toReal

/-- The deterministic limit `μ*(l, M)` of Lemma 5.5: the `P`-average of
`limsup_n μ*(B_n, η, l, M) / |B_n|`, computed in `[0, ∞]`. As for `muBar`, Lemma 5.5
(`MuConvergenceStmt`) identifies it with the almost-sure limit of
`μ*(nW ∩ ℤ^d, η, l, M) / |nW ∩ ℤ^d|` for every bounded Lipschitz domain `W`. -/
noncomputable def muStarBar (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    ℝ :=
  (∫⁻ η, limsup (fun n : ℕ => muStar (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P).toReal

/-! ### The effective operator `F̄_η` -/

/-- The set of levels `l ∈ ℝ` with `μ(l, M) = μ*(l, M)`. By Lemma 6.1
(`MuMonotoneStmt`) `μ(·, M)` is nondecreasing and `μ*(·, M)` nonincreasing, so this set is an
interval. -/
def muEqSet (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) : Set ℝ :=
  {l | muBar E l M = muStarBar E l M}

/-- The *effective operator* `F̄_η(M) = l_M`, the largest `l ∈ ℝ` with `μ(l, M) = μ*(l, M)`, written as `sSup (muEqSet E M)`.

That the supremum is attained, i.e. that `muEqSet E M` is nonempty, bounded above and contains
its supremum, is part of Lemma 6.4(3) (`EffectiveOperatorBasicStmt`, "`|F̄_η(M)| < ∞`"); the
paper derives it from the bounds of Lemma 5.4, the Lipschitz continuity of Lemma 6.3 and the
intermediate value theorem. If the set were empty or unbounded above, `sSup` would
return the junk value `0`. The opening of Section 6 describes `l_M` as the largest `l`
with `μ(l_M, M) = μ*(l_M, M) = 0`; the definition, and Lemma 7.5
(`FlatStmt`) shows that both values vanish at `l_M`, so the two descriptions agree. -/
noncomputable def effOp (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup (muEqSet E M)

/-! ### The single-source operator `F̄_0` -/

/-- The single-source operator of Pegden and Smart:
`F̄_0(M) = inf {s ∈ ℝ : ∃ u : ℤ^d → ℤ, ∀ y ∈ ℤ^d, Δ_{ℤ^d} u(y) ≤ 2d - 1 and
u(y) ≥ ½ yᵀ (M - s I) y}`.

Here `u` is an arbitrary integer function (no sign or support condition), and `½ yᵀ N y` is
`qMZ N y`. If the set were empty or unbounded below, `sInf` would return the junk value `0`. -/
noncomputable def effOp0 (d : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sInf {s : ℝ | ∃ u : Site d → ℤ, ∀ y : Site d,
    lap u y ≤ 2 * (d : ℤ) - 1 ∧ qMZ (M - s • (1 : Matrix (Fin d) (Fin d) ℝ)) y ≤ (u y : ℝ)}

end RandomSandpile

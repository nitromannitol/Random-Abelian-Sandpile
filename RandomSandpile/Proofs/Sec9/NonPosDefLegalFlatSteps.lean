import RandomSandpile.Proofs.Sec9.SingleSourceH0Equal

/-!
# Operator fact (11): the step statements

Goal: `NonPosDefLegalFlatStmt d` (11): `Q` symmetric, not
positive definite, `F*(Q) = H(Q) ≥ 0` implies `μ̄(0, Q) = 0`.

## Decomposition (differs from the note in one place)

The note proves (11) by envelope compactness and Monge-Ampère measures (its §2, §6) to obtain a
contact point `x₀` with a strict quadratic gap. The Lean development already has this bend for
every contact point of a near-maximizer: Lemma 6.2 with `C = c(1-β)²` (`StrictConcavityStmt`,
`strictConcavity_closed`, proved). So the analytic part is replaced by

* ** `ContactBendStmt`** — from `μ̄(0, A) > 0`: legal `u` on `B_n`, a contact point `x₀` and a
  slope `p₀` with `u ≤ P - δ n²` on `∂B_n`, `P(y) = u(x₀) + q_A(y) - q_A(x₀) + p₀·(y - x₀)`.
  Derived from `strictConcavity_closed` (no Alexandrov, no Monge-Ampère).
* ** `StableQuadApproxStmt`** — the note's (9): for `F*(A) ≥ 0`, almost surely, integer
  functions stabilizing on `B_R` with `|v - q_A - c| ≤ ε R²` on the closure. It splits into
  * ** `FlatCorrectorStmt`** — the case `F*(A) = 0` (flat correctors: shift identity
    `μ*(A, η, l, M) = μ*(A, η + 2dk, l, M - 2kI)`, `FlatStmt` for the lifted law, ABP on both
    sides;), and
  * ** `IntegerConcaveStmt`** — `ψ_s` with `Δψ_s ≤ 0`, `0 ≤ ψ_s + s|z|²/2 ≤ d/(8s) + 1`
    (note §4), which gives the case `F*(A) > 0` from `A + (F*(A)/d) I`.
* ** `BoundaryMinStmt`** — the note's (10): for `A` not positive definite,
  `min_{B̄_R} (q_A + L) ≥ min_{∂B_R} (q_A + L) - C (R + 1)` uniformly in the affine `L`.
* ** `locLegal_le_of_bdry`** — least action for locally legal against stabilizing, proved.

`nonPosDefLegalFlat_of_steps`: (11) from, (file `NonPosDefLegalFlat.lean`).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

/-- ** Flat correctors** (; the note's (9) for `H(A) = 0`):
if `F*_η(A) = 0`, almost surely for every `ε > 0` and all large `R` there is an integer function
`v`, stabilizing in `B_R`, with `|v - q_A - c| ≤ ε R²` on `B̄_R` for some constant `c`. -/
def FlatCorrectorStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm → effOpStar E A = 0 →
      ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ (v : Site d → ℤ) (c : ℝ),
        (∀ x ∈ ballZ0 (R : ℝ), lap v x + η x ≤ 2 * (d : ℤ) - 1) ∧
        ∀ z ∈ dClosure (ballZ0 (R : ℝ)), |(v z : ℝ) - qMZ A z - c| ≤ ε * (R : ℝ) ^ 2

/-- ** The integer concave correction** `ψ_s` (note §4): `ψ_s(z) = min_{p ∈ ℤ^d}
{p · z + ⌈|p|²/(2s)⌉}` has `Δψ_s ≤ 0` and `0 ≤ ψ_s + s|z|²/2 ≤ d/(8s) + 1`. -/
def IntegerConcaveStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ s : ℝ, 0 < s → ∃ ψ : Site d → ℤ, (∀ x, lap ψ x ≤ 0) ∧
    ∀ z : Site d, 0 ≤ (ψ z : ℝ) + s * ‖toE z‖ ^ 2 / 2 ∧
      (ψ z : ℝ) + s * ‖toE z‖ ^ 2 / 2 ≤ d / (8 * s) + 1

/-- ** Stable quadratic approximants** (the note's (9)), for all `A` with `F*(A) ≥ 0`. -/
def StableQuadApproxStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm → 0 ≤ effOpStar E A →
      ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ (v : Site d → ℤ) (c : ℝ),
        (∀ x ∈ ballZ0 (R : ℝ), lap v x + η x ≤ 2 * (d : ℤ) - 1) ∧
        ∀ z ∈ dClosure (ballZ0 (R : ℝ)), |(v z : ℝ) - qMZ A z - c| ≤ ε * (R : ℝ) ^ 2

/-- ** Boundary minimum estimate** (the note's (10)): for `A` symmetric and not positive
definite there is `C` such that for every `R`, every slope `p` and every `y ∈ B̄_R` some boundary
site `b ∈ ∂B_R` has `(q_A + p·)(b) ≤ (q_A + p·)(y) + C (R + 1)`. -/
def BoundaryMinStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm → ¬ A.PosDef →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℕ) (p : Rd d), ∀ y ∈ dClosure (ballZ0 (R : ℝ)),
      ∃ b ∈ bdry (ballZ0 (R : ℝ)),
        qMZ A b + inner ℝ p (toE b) ≤ qMZ A y + inner ℝ p (toE y) + C * ((R : ℝ) + 1)

/-- ** Contact bend** (Lemma 6.2 at a positive-curvature level): if `μ̄(0, A) > 0` there is
`δ > 0` such that, almost surely and for all large `n`, there are a locally legal `u` on `B_n`, a
site `x₀ ∈ B_n` and a slope `p₀` with
`u(y) ≤ u(x₀) + q_A(y) - q_A(x₀) + p₀·(y - x₀) - δ n²` on `∂B_n`. -/
def ContactBendStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm →
    0 < muBar E 0 A → ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ η ∂E.P, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ (u : Site d → ℤ) (x₀ : Site d) (p₀ : Rd d),
        u ∈ locLegal η (ballZ0 (n : ℝ)) ∧ x₀ ∈ ballZ0 (n : ℝ) ∧
        ∀ y ∈ bdry (ballZ0 (n : ℝ)),
          (u y : ℝ) ≤ u x₀ + (qMZ A y - qMZ A x₀) + inner ℝ p₀ (toE y - toE x₀) - δ * (n : ℝ) ^ 2

end SingleSourceH0

end RandomSandpile

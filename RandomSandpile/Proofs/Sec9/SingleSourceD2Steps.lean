import RandomSandpile.Proofs.Sec9.SingleSourceFstarDilation
import RandomSandpile.Proofs.Sec9.SingleSourceD2StarDim
import RandomSandpile.Draft.Section9
import RandomSandpile.Inputs.PegdenSmartProp25
import RandomSandpile.Inputs.CrandallIshiiLions

/-!
# Theorem 9.2 in dimension two: step statements and the top-level reduction

Plan:; proof: (§§1-8), with
 §§2-4 for the operator facts.

Target: `SingleSourceTheoremD2Stmt`, the body of the `SingleSourceTheoremStmt`
(`Draft/Section9.lean`) at `d = 2`; `singleSourceTheoremD2_of_stmt` checks that it is the `d = 2`
instance.

Notation. `U* = v* + G` with `v* = singleSourceObstacleSolutionStar E` (the starred limit) and
`G = fundamentalSolution 2`; `F* = effOpStar E`, `F̄ = effOp E`.

Steps:
* `EffOpLeStarD2Stmt`: `F̄ ≤ F*`.
* `EffOpEqStarOfNotPosDefD2Stmt`: `F̄(M) = F*(M)` when `M + F̄(M) I/2` is not positive definite
. Consequence: `effOp_nonneg_of_not_posDef`.
* `SSLimitWeakLaplaceD2Stmt`: subsequential limits have a locally bounded weak Laplacian off 0.
* `EffOpStarTraceBoundsD2Stmt`: `-2 ≤ f ≤ 3 - η_min`, `F*(0) ≥ 0`.
* `PlanarExclusionStmt` [C5]: SIMPLE-PROOF Theorem 4.1.
* `SSNoPosDefLowerTestD2Stmt`: no positive definite lower test of `U*` at positive points
.
* `SSLimitSuperEffD2Stmt`: `F̄(D²U*) ≥ 0` off the origin, tested from below.

Reduction proved here: `singleSourceTheoremD2_of_star`: the starred theorem, and
give `SingleSourceTheoremD2Stmt`.
-/

noncomputable section

open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

/-! ### The target -/

/-- **Theorem 9.2 in dimension two** (corrected sign [C3]): the body of `SingleSourceTheoremStmt`
with `d = 2`. -/
def SingleSourceTheoremD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    IsLeast (singleSourceObstacleSet E) (singleSourceObstacleSolution E) ∧
    ∀ᵐ η ∂E.P,
      (∀ n : ℕ, (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty) ∧
        TendstoLocallyUniformlyOn
          (fun n : ℕ => rescaleSingleSource (singleSourceOdometer η n) n)
          (fun x => singleSourceObstacleSolution E x + fundamentalSolution 2 x) atTop
          {x : Rd 2 | x ≠ 0}

/-- `SingleSourceTheoremD2Stmt` is the `d = 2` instance of the statement. -/
theorem singleSourceTheoremD2_of_stmt (h : SingleSourceTheoremStmt) : SingleSourceTheoremD2Stmt :=
  fun E hE => h 2 le_rfl E hE

/-! ### Planar vocabulary -/

/-- `A_z = ½ [[z₀, z₁], [z₁, -z₀]]`, the trace-free symmetric matrix with coordinates `z`
. -/
def traceFreeMat (z : Rd 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z 0 / 2, z 1 / 2; z 1 / 2, -(z 0) / 2]

/-- `Z_M = (M₀₀ - M₁₁, 2 M₀₁)`, the trace-free coordinates of `M`; `M = A_{Z_M} + (tr M / 2) I`
for symmetric `M`. -/
def traceFreeCoord (M : Matrix (Fin 2) (Fin 2) ℝ) : Rd 2 :=
  WithLp.toLp 2 ![M 0 0 - M 1 1, 2 * M 0 1]

/-- The trace graph `f(z) = F(A_z)` of an operator `F`. -/
def traceGraph (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (z : Rd 2) : ℝ :=
  F (traceFreeMat z)

/-- The regularized operator `F_ε(M) = (1 - ε) f(Z_M) + ε (K + 1) - tr M`. -/
def regOp (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (K ε : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (1 - ε) * traceGraph F (traceFreeCoord M) + ε * (K + 1) - M.trace

/-- The scalar shift identity `F(M + tI) = F(M) - 2t` on symmetric matrices (SIMPLE-PROOF §1,
item 3; for `F*` this is `effOpStar_add_smul_one`). -/
def HasTraceShift (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm → ∀ t : ℝ,
    F (M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = F M - 2 * t

/-- The positive comparison set `P_Q = {x ≠ 0 : u(x) > Q(x)} ∪ {0}`. -/
def posSet (u Q : Rd 2 → ℝ) : Set (Rd 2) :=
  {x | x ≠ 0 ∧ Q x < u x} ∪ {0}

/-- The negative comparison set `N_Q = {x ≠ 0 : u(x) < Q(x)}`. -/
def negSet (u Q : Rd 2 → ℝ) : Set (Rd 2) :=
  {x | x ≠ 0 ∧ u x < Q x}

/-- A source profile for `F`: `u` is continuous off the origin, nonnegative off
the origin, zero outside a bounded set, tends to `+∞` at the source, is a viscosity supersolution
of `F = 0` off the origin and a viscosity subsolution of `F = 0` where it is positive (off the
origin). The value `u(0)` plays no role. -/
structure IsSourceProfile (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (u : Rd 2 → ℝ) : Prop where
  continuousOn : ContinuousOn u {x | x ≠ 0}
  nonneg : ∀ x : Rd 2, x ≠ 0 → 0 ≤ u x
  eventually_zero : ∃ R : ℝ, ∀ x : Rd 2, R ≤ ‖x‖ → u x = 0
  tendsto_atTop : Tendsto u (𝓝[≠] 0) atTop
  supersolution : ViscFromBelowGE F {x | x ≠ 0} u
  subsolution : ViscFromAboveLE F {x | x ≠ 0 ∧ 0 < u x} u

/-- No positive definite lower test at a positive point off the origin (SIMPLE-PROOF Lemmas 5.1,
5.2): if `φ` is `C²` near `a ≠ 0`, `u(a) > 0` and `u - φ` has a local minimum at `a`, then
`D²φ(a)` is not positive definite. -/
def NoPosDefLowerTest (u : Rd 2 → ℝ) : Prop :=
  ∀ a : Rd 2, a ≠ 0 → 0 < u a → ∀ φ : Rd 2 → ℝ, ContDiffAt ℝ 2 φ a →
    IsLocalMin (fun y => u y - φ y) a → ¬ (hessian φ a).PosDef

/-- `u` has a locally bounded weak Laplacian on `V`: every point of `V` is the centre of a ball in
`V` on which `u` is a weak solution of `Δu = s` with `s` measurable and bounded (an
`L^∞` density, taken with a bounded representative). -/
def LocWeakLaplaceBdd (V : Set (Rd 2)) (u : Rd 2 → ℝ) : Prop :=
  ∀ a ∈ V, ∃ r : ℝ, 0 < r ∧ ball a r ⊆ V ∧ ∃ (s : Rd 2 → ℝ) (C : ℝ), Measurable s ∧
    (∀ x, |s x| ≤ C) ∧ IsWeakSolutionLaplace (ball a r) u s

/-! ### Step statements -/

/-- `F̄_η ≤ F*_η`: from the absence of a common-zero
interval of `μ*` and `μ` and `isGreatest_effOp`. -/
def EffOpLeStarD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm → effOp E M ≤ effOpStar E M

/-- Flatness at a critical matrix: if
`M + F̄_η(M) I / 2` is not positive definite, then `F̄_η(M) = F*_η(M)`. -/
def EffOpEqStarOfNotPosDefD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm →
      ¬ (M + (effOp E M / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef →
        effOp E M = effOpStar E M

/-- Almost surely every subsequential limit of the rescaled single-source odometers has a
locally bounded weak Laplacian off the origin (from `|Δ_{ℤ²} v_n| ≤ C` off the origin by summation
by parts, as in Pegden-Smart's proof of Lemma 3.1). -/
def SSLimitWeakLaplaceD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    ∀ᵐ η ∂E.P, ∀ u : Rd 2 → ℝ, IsSSSubseqLimit η u → LocWeakLaplaceBdd {x | x ≠ 0} u

/-- Trace-graph bounds for `F*`: `-2 ≤ f ≤ 3 - η_min` and
`F*(0) ≥ 0`, where `f(z) = F*(A_z)`. -/
def EffOpStarTraceBoundsD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    (∀ z : Rd 2, -2 ≤ traceGraph (effOpStar E) z ∧
      traceGraph (effOpStar E) z ≤ ((3 - E.ηmin : ℤ) : ℝ)) ∧ 0 ≤ effOpStar E 0

/-- **(C5) Abstract planar exclusion**: for a degenerate elliptic `F`
with the shift identity whose trace graph has Lipschitz constant `k < 1`, a source profile has no
positive definite Peano Hessian at a positive point off the origin. -/
def PlanarExclusionStmt : Prop :=
  ∀ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, HasTraceShift F → DegenerateElliptic F →
    ∀ k : ℝ, k < 1 → (∀ z z' : Rd 2, |traceGraph F z - traceGraph F z'| ≤ k * ‖z - z'‖) →
    ∀ u : Rd 2 → ℝ, IsSourceProfile F u →
      ∀ a : Rd 2, a ≠ 0 → 0 < u a → ∀ (p : Rd 2) (X : Matrix (Fin 2) (Fin 2) ℝ),
        X.IsSymm → HasSecondOrderTaylorAt u a p X → ¬ X.PosDef

/-- The starred limit `U* = v* + G` has no positive definite lower test at a positive
point off the origin. -/
def SSNoPosDefLowerTestD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    NoPosDefLowerTest (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x)

/-- The starred limit is a viscosity supersolution of `F̄_η = 0` off the origin
. -/
def SSLimitSuperEffD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    ViscFromBelowGE (effOp E) {x : Rd 2 | x ≠ 0}
      (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution 2 x)

/-! ### Consequence of: D2-PROOF (4.4) -/

/-- Adding a nonnegative multiple of the identity keeps a matrix positive definite. -/
theorem posDef_add_smul_one {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.PosDef) {c : ℝ} (hc : 0 ≤ c) :
    (Q + c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef :=
  hQ.add_posSemidef (Matrix.PosSemidef.smul Matrix.PosSemidef.one hc)

/-- D2-PROOF (4.4): if `H` is not positive definite and `F*(H) ≥ 0`, then `F̄(H) ≥ 0`. -/
theorem effOp_nonneg_of_not_posDef (hOP2 : EffOpEqStarOfNotPosDefD2Stmt) (E : RandomEnvironment 2)
    (hE : E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2) {H : Matrix (Fin 2) (Fin 2) ℝ} (hH : H.IsSymm)
    (hnot : ¬ H.PosDef) (hstar : 0 ≤ effOpStar E H) : 0 ≤ effOp E H := by
  by_contra hneg'
  have hneg : effOp E H < 0 := not_le.mp hneg'
  have hQ : ¬ (H + (effOp E H / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef := by
    intro hQ
    apply hnot
    have hc : (0 : ℝ) ≤ -(effOp E H / 2) := by linarith
    have hsum := posDef_add_smul_one hQ hc
    have heq : H + (effOp E H / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (-(effOp E H / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = H := by
      rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
    rwa [heq] at hsum
  have h := hOP2 E hE H hH hQ
  linarith

/-! ### The top-level reduction -/

/-- Theorem 9.2 in dimension two from the starred theorem, and. puts
every member of the `F̄`-set in the `F*`-set, so `v*` lies below it; puts `v*` in the `F̄`-set.
Hence `v*` is the least element, `singleSourceObstacleSolution E = v*`, and the starred convergence
is the asserted convergence. -/
theorem singleSourceTheoremD2_of_star (hStar : SingleSourceTheoremStarD2Stmt)
    (hOP1 : EffOpLeStarD2Stmt) (hF2 : SSLimitSuperEffD2Stmt) : SingleSourceTheoremD2Stmt := by
  intro E hE
  obtain ⟨hleast, hae⟩ := hStar E hE
  have hE1 : E.ηmax ≤ 2 * ((2 : ℕ) : ℤ) - 1 := by rw [hE]; norm_num
  have hmem : singleSourceObstacleSolutionStar E ∈ singleSourceObstacleSet E :=
    ⟨hleast.1.1, hleast.1.2.1, hF2 E hE⟩
  have hlow : singleSourceObstacleSolutionStar E ∈ lowerBounds (singleSourceObstacleSet E) := by
    intro w hw
    apply hleast.2
    refine ⟨hw.1, hw.2.1, ?_⟩
    rw [viscFromBelowMuStar_iff (by norm_num) E hE1]
    intro x hx φ hφ hmin
    exact (hw.2.2 x hx φ hφ hmin).trans
      (hOP1 E hE _ (hessian_isSymm_of_contDiffAt hφ))
  have hL : IsLeast (singleSourceObstacleSet E) (singleSourceObstacleSolutionStar E) :=
    ⟨hmem, hlow⟩
  rw [singleSourceObstacleSolution_eq_of_isLeast hL]
  exact ⟨hL, hae⟩

end SingleSourceD2

end RandomSandpile

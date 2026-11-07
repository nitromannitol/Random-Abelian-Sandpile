import RandomSandpile.Draft.Section9
import RandomSandpile.Steps.Sec7.MainTheorem

/-!
# Theorem 9.1 (sandpiles with the open boundary condition): the decomposition

Target: `OpenBoundaryTheoremStmt` (`Draft/Section9.lean`). The paper gives no proof
("the exact same argument given in this paper also works"); the decomposition mirrors that of Theorem 1.1
(`Steps/Sec7/MainTheorem.lean`), with the open-boundary odometer
`v_n = openOdometer η W_n` (the least stabilizing toppling of `η` in `W_n` vanishing on `∂W_n`,
legal by Proposition 3.1) in place of the free one, and the Dirichlet problem
`F̄_η(D²v̄) = 0` in `W`, `v̄ = 0` on `∂W` in place of the obstacle problem.

Steps (exact statements below; `openBoundaryTheorem_of_steps` assembles them):
* `OpenCompactnessStmt`: Arzelà-Ascoli for the rescaled open odometers (Lemma 7.2 for the
  open boundary condition: the interior estimates of Lemma 7.2 and a barrier at `∂W` from the
  Lipschitz boundary). The boundary condition of the limit is then elementary
  (`IsOpenOdoSubseqLimit.eq_zero_of_not_mem`, `Proofs/Sec9/OpenBoundary.lean`): the `v̄_n` vanish
  off `W`, and every point of `∂W` is a limit of points off `W̄` (Lipschitz boundary).
* `OpenLimitSubsolutionStmt`, `OpenLimitSupersolutionStmt`: every subsequential limit is a
  Crandall-Ishii-Lions viscosity sub- and supersolution of `F̄_η(D²v) = 0` in `W`. They reduce
  (`Proofs/Sec9/OpenBoundaryVisc.lean`) to Lemma 6.4(1), `MuVanishStmt` and the interior
  maximum and minimum principles `OpenInteriorMaxPrincipleStmt`, `OpenInteriorMinPrincipleStmt`,
  the open-boundary forms of Theorem 1.1's steps: inside `W_n` the open odometer is a
  legal stabilizing toppling of `η` (Proposition 3.1), which is all those steps use.
* `EffComparisonStmt`: the comparison principle for `F̄_η(D²u) = 0` on bounded open sets
. It reduces to the shift identity `F̄_η(M + tI) = F̄_η(M) - d t`
  (`EffShiftStmt`, `effOp_add_smul_one`), Lemma 6.4(1) and the
  Crandall-Ishii-Lions comparison principle for degenerate elliptic operators with that shift
  property (`ShiftComparisonStmt`; route: Jensen's lemma with Alexandrov's theorem and
  sup-convolutions, `ComparisonShiftStmt` in `Infra/Touching.lean` once stated).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- `v` is a subsequential uniform limit of the rescaled open-boundary odometers
`v̄_n = n⁻² v_n([n ·])`, `v_n = openOdometer η W_n`. -/
def IsOpenOdoSubseqLimit (η : Site d → ℤ) (W : Set (Rd d)) (v : Rd d → ℝ) : Prop :=
  ∃ nk : ℕ → ℕ, StrictMono nk ∧
    TendstoUniformly (fun k => rescaleOdo (openOdometer η (discretize W (nk k))) (nk k)) v atTop

/-! ### Compactness -/

/-- **Step: compactness of the rescaled open odometers** (Lemma 7.2 for the open boundary
condition). For a bounded `η` and a bounded Lipschitz domain `W`, every subsequence of
`v̄_n = n⁻² v_n([n ·])` has a further subsequence converging uniformly on `ℝ^d` to a continuous
function. Route: `0 ≤ v_n ≤ freeOdometer η W_n` on `W_n` (`openOdometer_le`: the free odometer
restricted to `W_n` is stabilizing in `W_n` and vanishes on `∂W_n`), so `v_n ≤ C n²`;
`|Δ v_n| ≤ C` in `W_n` and the interior gradient estimate of Lemma 7.2; at `∂W_n` a barrier from
the uniform exterior cone condition of the Lipschitz domain, `v_n(y) ≤ C n² ω(dist(y/n, ∂W))`;
an Arzelà-Ascoli theorem with a modulus of continuity up to an error `o(1)` (limits need not be
Lipschitz at re-entrant corners). -/
def OpenCompactnessStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ (ηmin ηmax : ℤ) (η : Site d → ℤ), (∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) →
      ∀ nk : ℕ → ℕ, StrictMono nk →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ vbar : Rd d → ℝ, Continuous vbar ∧
          TendstoUniformly
            (fun j => rescaleOdo (openOdometer η (discretize W (nk (φ j)))) (nk (φ j)))
            vbar atTop

/-! ### The limits are viscosity solutions -/

/-- **Step: maximum principle in `W` from `μ(l, M) = 0`** for open-boundary limits (Theorem
1.1's `InteriorMaxPrincipleStmt` with the open odometer). Same route: Lemma 5.2 (perturbed
subsolutions) on `B_{rn}(na) ∩ ℤ^d ⊆ W_n` for the legal toppling `v_n` (Proposition 3.1), affine
invariance of `μ`, rescaling and Lemma 5.5. -/
def OpenInteriorMaxPrincipleStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → muBar E l M = 0 →
      ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOpenOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v x - (inner ℝ p (x - a) + qM M (x - a) + ql l (x - a)) ≤
              v y - (inner ℝ p (y - a) + qM M (y - a) + ql l (y - a))

/-- **Step: minimum principle in `W` from `μ*(l, M) = 0`** for open-boundary limits (Theorem
1.1's `InteriorMinPrincipleStmt` with the open odometer). Same route: Lemma 5.2 (perturbed
supersolutions) on `B_{rn}(na) ∩ ℤ^d ⊆ W_n` for the stabilizing toppling `v_n`. -/
def OpenInteriorMinPrincipleStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → muStarBar E l M = 0 →
      ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOpenOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v y - (inner ℝ p (y - a) + qM M (y - a) + ql l (y - a)) ≤
              v x - (inner ℝ p (x - a) + qM M (x - a) + ql l (x - a))

/-- **Step: the limit is a viscosity subsolution of `F̄_η(D²v) = 0` in `W`** (tested from
above: `F̄_η(D²φ(x)) ≤ 0` at local maxima of `v - φ`). Reduced to in
`openLimitSubsolution_of_steps`. -/
def OpenLimitSubsolutionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ W : Set (Rd d), IsLipschitzDomain W →
      ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOpenOdoSubseqLimit η W v → ViscFromAboveLE (effOp E) W v

/-- **Step: the limit is a viscosity supersolution of `F̄_η(D²v) = 0` in `W`** (tested from
below: `F̄_η(D²φ(x)) ≥ 0` at local minima of `v - φ`). Reduced to in
`openLimitSupersolution_of_steps`. -/
def OpenLimitSupersolutionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ W : Set (Rd d), IsLipschitzDomain W →
      ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, IsOpenOdoSubseqLimit η W v → ViscFromBelowGE (effOp E) W v

/-! ### Comparison principle -/

/-- **Step: comparison principle for `F̄_η(D²u) = 0`**. On a bounded open
`U`, a continuous viscosity subsolution lies below a continuous viscosity supersolution if it does
so on `∂U`. Reduced in `effComparison_of_shift` to `EffShiftStmt` and `ShiftComparisonStmt`. -/
def EffComparisonStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ U : Set (Rd d), IsOpen U → Bornology.IsBounded U →
      ∀ u w : Rd d → ℝ, ContinuousOn u (closure U) → ContinuousOn w (closure U) →
        ViscFromAboveLE (effOp E) U u → ViscFromBelowGE (effOp E) U w →
          (∀ x ∈ frontier U, u x ≤ w x) → ∀ x ∈ closure U, u x ≤ w x

/-- **Step: the shift identity** `F̄_η(M + tI) = F̄_η(M) - d t` (: from
`μ(l, M) = μ(l - d t, M + tI)` and the same for `μ*`, the `q_{tI} = q_{dt}` normalisation;
`effOp_add_smul_one`, Proofs/Sec6/EffectiveOperatorBasic*.lean). -/
def EffShiftStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, HighDensity E.P →
    ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ t : ℝ,
      effOp E (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) = effOp E M - d * t

/-- **Step: the Crandall-Ishii-Lions comparison principle** for `F(D²u) = 0`, `F` degenerate
elliptic with the shift property `F(M + tI) = F(M) - d t` on symmetric matrices (which makes `F`
Lipschitz and `u + ε|x|²/2` a strict subsolution). Route: Jensen's lemma (Alexandrov's theorem
and sup- and inf-convolutions, `Infra/Touching.lean`, `Infra/SupConvolution.lean`) or Ishii's theorem
of sums; Crandall-Ishii-Lions, *User's guide*, Bull. AMS 27 (1992), Section 3 and Section 5.C. -/
def ShiftComparisonStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ F : Matrix (Fin d) (Fin d) ℝ → ℝ, DegenerateElliptic F →
    (∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ t : ℝ,
      F (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) = F M - d * t) →
    ∀ U : Set (Rd d), IsOpen U → Bornology.IsBounded U →
      ∀ u w : Rd d → ℝ, ContinuousOn u (closure U) → ContinuousOn w (closure U) →
        ViscFromAboveLE F U u → ViscFromBelowGE F U w →
          (∀ x ∈ frontier U, u x ≤ w x) → ∀ x ∈ closure U, u x ≤ w x

/-- from the shift identity, Lemma 6.4(1) and the abstract comparison principle. -/
theorem effComparison_of_shift (h64 : EffectiveOperatorBasicStmt) (hShift : EffShiftStmt)
    (hCIL : ShiftComparisonStmt) : EffComparisonStmt := by
  intro d hd E hHD U hU hUb u w hu hw hsub hsup hbd
  have hDE : DegenerateElliptic (effOp E) := by
    obtain ⟨C, -, hC⟩ := h64 d hd E.ηmin E.ηmax
    intro X Y hX hY hXY
    exact (hC E rfl rfl X Y hX hY).1 hXY
  exact hCIL d (by omega) (effOp E) hDE (hShift d hd E hHD) U hU hUb u w hu hw hsub hsup hbd

/-! ### Analytic input of compactness -/

/-- **Step: interior Lipschitz estimate for lattice functions with a bounded Laplacian**
(the interior counterpart of Lemma 7.2's `LapGradientBoundStmt`, cited there to
Kuo-Trudinger). For `d ≥ 2` there is `C > 0` such that: if `u : ℤ^d → ℤ` is nonnegative, vanishes
off a set `A` contained in the open cube `{|x|_∞ < R}` and `|Δ u| ≤ M` on `A`, then for lattice points
`x, y` at Euclidean distance at least `r > 0` from `ℤ^d ∖ A` with `|x - y| ≤ r / 2`,
`|u(x) - u(y)| ≤ C M (R + 1) (1 + ((R + 1) / r)^{d-1}) |x - y|`.
Route: the Green representation of `lapGradientBound_core` (Proofs/Sec7/CompactnessGradient.lean),
`∇u(z) = -(2d)⁻¹ ∑_w ∇g(z - w) Δu(w)` along the segment `[x, y]` (at distance `≥ r/2` from
`ℤ^d ∖ A`); the charges in `A` contribute `C M (R + 1)` (radial sum of `|∇g| ≤ C (1 + |·|)^{1-d}`),
the charges `Δu ≥ 0` on `∂A` (`u ≥ 0`, `u = 0` off `A`) have total mass `-∑_A Δu ≤ M |A|` and
contribute `C M (R + 1)^d (r/2)^{1-d}`. -/
def LapLipschitzInteriorStmt : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (u : Site d → ℤ) (A : Set (Site d)) (M : ℝ) (R : ℕ) (r : ℝ),
      (∀ x, 0 ≤ u x) → (∀ x, x ∉ A → u x = 0) → (∀ x ∈ A, ∀ i, |x i| < (R : ℤ)) →
      (∀ x ∈ A, |(lap u x : ℝ)| ≤ M) → 0 < r →
      ∀ x y : Site d, (∀ z, z ∉ A → r ≤ ‖toE (z - x)‖) → (∀ z, z ∉ A → r ≤ ‖toE (z - y)‖) →
        ‖toE (x - y)‖ ≤ r / 2 →
        |(u x : ℝ) - u y| ≤
          C * M * ((R : ℝ) + 1) * (1 + (((R : ℝ) + 1) / r) ^ (d - 1)) * ‖toE (x - y)‖

end RandomSandpile

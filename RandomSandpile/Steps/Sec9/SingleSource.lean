import RandomSandpile.Draft.Section9Partial
import RandomSandpile.Draft.Section6

/-!
# Theorem 9.2 (single source on a random background), partial variant: the decomposition

Target: `SingleSourceTheoremFlatStmt` (`Draft/Section9Partial.lean`; Theorem 9.2 with flatness of
`F̄_η` as an extra hypothesis). The paper gives no proof ("straightforward
modifications of the arguments appearing above and in"). The decomposition follows
Pegden-Smart's proof for the zero background (Pegden-Smart, *Convergence of the Abelian
sandpile*, Duke Math. J. 162 (2013), arXiv:1105.0111: Lemma 3.1, Theorem 4.2, Remark 4.3) and the
identification steps of Theorem 1.1 (`Steps/Sec7/MainTheorem.lean`), with the scaling
`v̄_n(x) = n^{-2/d} v_n([n^{1/d} x])` and the fundamental solution `G = fundamentalSolution d`.

Steps (exact statements below; `singleSourceTheoremFlat_of_steps`,
`Proofs/Sec9/SingleSource.lean`, assembles them):
* `SSNonemptyStmt` (proved, `ssNonempty`): with background `η ≤ 2d - 2`, the pile `η + n δ_0` has a
  stabilizing toppling function (a one-dimensional triangular profile).
* `SSCompactnessStmt`: every subsequence of `v̄_n` has a further subsequence with
  `v̄_n - G → v` locally uniformly away from `0`, `v ∈ C(ℝ^d)` (Pegden-Smart Lemma 3.1 for the random
  background).
* `SSLimitSupersolutionStmt`: limits are viscosity supersolutions of `F̄_η(D²u) ≥ 0` off `0`;
  reduced to Lemma 6.4(1), `MuVanishFlatStmt` and the interior minimum principle
  `SSInteriorMinPrincipleStmt` (`ssLimitSupersolution_of_steps`).
* `SSLimitMinimalStmt`: limits lie below every member of the obstacle set (Pegden-Smart Theorem 4.2
  and Remark 4.3 with `F̄_η` and flatness; see the caveat in its docstring).
Uniqueness of the limit and the identification with the least element are then elementary.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- `u` is a subsequential limit, locally uniformly on `ℝ^d ∖ {0}`, of the rescaled single-source
odometers `v̄_n(x) = n^{-2/d} v_n([n^{1/d} x])`, `v_n = singleSourceOdometer η n`. -/
def IsSSSubseqLimit (η : Site d → ℤ) (u : Rd d → ℝ) : Prop :=
  ∃ nk : ℕ → ℕ, StrictMono nk ∧
    TendstoLocallyUniformlyOn
      (fun k => rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k)) u atTop
      {x : Rd d | x ≠ 0}

/-- The flatness hypothesis of `SingleSourceTheoremFlatStmt`. -/
def FlatEff (E : RandomEnvironment d) : Prop :=
  ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm →
    muBar E (effOp E M) M = 0 ∧ muStarBar E (effOp E M) M = 0

/-- **Step (N): finiteness of the odometers.** A background `η ≤ 2d - 2` plus `n` chips at the
origin has a stabilizing toppling function on `ℤ^d` (`d ≥ 1`). Proved (`ssNonempty`). -/
def SSNonemptyStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ η : Site d → ℤ, (∀ x, η x ≤ 2 * (d : ℤ) - 2) → ∀ n : ℕ,
    (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty

/-- **Step: compactness** (for the background `η_min ≤ η ≤ 2d - 2`). Every
subsequence of the rescaled single-source odometers has a further subsequence such that
`v̄_n - G` converges locally uniformly to a continuous `v` on `ℝ^d ∖ {0}`; equivalently
`v̄_n → v + G` there with `v ∈ C(ℝ^d)` (Pegden-Smart obtain the convergence of `v̄_n - Φ_n` on all of
`ℝ^d`, `Φ_n` the rescaled lattice Green function). Route of Pegden-Smart: the toppled set lies in
`B_{R n^{1/d}}` (an outer bound of Levine-Peres type for the background `η ≤ 2d - 2`),
the maximum principle bounds `v̄_n - Φ_n`, `|Δ(v̄_n - Φ_n)| ≤ C`, discrete regularity
 and the convergence `Φ_n → G` away from `0` (Green function asymptotics,
Lattice-Probability `GreenAsymptotic`). -/
def SSCompactnessStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin : ℤ) (η : Site d → ℤ),
    (∀ x, ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2) →
    ∀ nk : ℕ → ℕ, StrictMono nk →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : Rd d → ℝ, Continuous v ∧
        TendstoLocallyUniformlyOn
          (fun j => rescaleSingleSource (singleSourceOdometer η (nk (φ j))) (nk (φ j)))
          (fun x => v x + fundamentalSolution d x) atTop {x : Rd d | x ≠ 0}

/-- **Step: minimum principle off the origin from `μ*(l, M) = 0`** (Theorem 1.1's
`InteriorMinPrincipleStmt` for the single-source limits). Route: Lemma 5.2 (perturbed
supersolutions) on `B_{rh}(ha) ∩ ℤ^d`, `h = n^{1/d}`, for the stabilizing `v_n` (away from the
origin `Δ v_n + η ≤ 2d - 1`), affine invariance of `μ*`, rescaling and Lemma 5.5 along the
scales `h`. -/
def SSInteriorMinPrincipleStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → muStarBar E l M = 0 →
      ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ {x : Rd d | x ≠ 0} →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            u y - (inner ℝ p (y - a) + qM M (y - a) + ql l (y - a)) ≤
              u x - (inner ℝ p (x - a) + qM M (x - a) + ql l (x - a))

/-- **Step: vanishing ranges of `μ`, `μ*` under flatness** (Theorem 1.1's `MuVanishStmt` with
the flatness hypothesis in place of Lemma 7.5). Route: Lemma 6.1 (`MuMonotoneStmt`: `μ`
nondecreasing, `μ*` nonincreasing in `l`) and the finiteness of the averages defining `muBar`,
`muStarBar` (Lemma 5.4 on balls). -/
def MuVanishFlatStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, FlatEff E →
    ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ l : ℝ,
      (l ≤ effOp E M → muBar E l M = 0) ∧ (effOp E M ≤ l → muStarBar E l M = 0)

/-- **Step: the limits are viscosity supersolutions of `F̄_η(D²u) ≥ 0` off the origin** ([C3]
sign, tested from below). Reduced in `ssLimitSupersolution_of_steps`. -/
def SSLimitSupersolutionStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 → FlatEff E →
    ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
      ViscFromBelowGE (effOp E) {x : Rd d | x ≠ 0} u

/-- **Minimality of the limits** (Pegden-Smart Theorem 4.2 and Remark 4.3, with `F̄_η` and
flatness). Almost surely, if `v + G` is a subsequential limit with `v ∈ C(ℝ^d)`, then `v ≤ w` for
every `w` in the obstacle set `singleSourceObstacleSet E`. Route of Pegden-Smart: at a point `a ≠ 0` of
Pegden-Smart's touching set for `v - w` (`PegdenSmartTouchingStmt`), lower the
odometers near `n^{1/d} a` with the quadratic competitor built from `F̄_η(D²(w + G)(a)) ≥ 0`
(flatness: `μ* = 0` there) and the least action principle; where the limit is positive the
maximum principle (`μ = 0`) applies. CAVEAT (to check before proving): the obstacle set of
`singleSourceObstacleSet` imposes its constraints on `ℝ^d ∖ {0}` only, while Pegden-Smart's obstacle
problem (Remark 4.3, (4.3)) also imposes `Δ w' ≤ 2d - 1` on all of `ℝ^d`, the origin included; the
touching point `a` must avoid `0`, and whether the isolated singularity is removable for `F̄_η`
(not known to be uniformly elliptic) is not settled. -/
def SSLimitMinimalStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 → FlatEff E →
    ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, Continuous v →
      IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
        ∀ w ∈ singleSourceObstacleSet E, ∀ x, v x ≤ w x

end RandomSandpile

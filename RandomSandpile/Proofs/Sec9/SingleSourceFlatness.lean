import RandomSandpile.Proofs.Sec9.SingleSource
import RandomSandpile.Proofs.Sec9.SingleSourceMinPrinciple
import RandomSandpile.Proofs.Sec7.FlatTilted

/-!
# Theorem 9.2 with the `μ*`-operator `F*` (no flatness, no density assumption)

 §5. The supersolution step of the partial variant
`SingleSourceTheoremFlatStmt` needs flatness of `F̄_η` on `{F̄_η < 0}`, its minimality step on
`{F̄_η ≥ 0}`; both ranges meet every line `M + ℝ I`, so both are the full flatness `FlatEff`
(`flatEff_of_flat_on_neg`, `flatEff_of_flat_on_nonneg`), which fails for every background with
`η ≤ d - 1` (`not_flatEff_of_le`). This file states and reduces the variant of Theorem 9.2 in which
the constraint `F̄_η(D²(v̄ + G)) ≥ 0` is replaced by `F*(D²(v̄ + G)) ≥ 0`, where
`F*(M) = sup {l : μ*(l, M) > 0}`; tested from below, `F*(D²φ(x)) ≥ 0` reads
`μ*(l, D²φ(x)) > 0` for every `l < 0` (`ViscFromBelowMuStar`).

* `viscFromBelowMuStar_of_minPrinciple`: the deterministic core (adapted from Theorem 1.1's
  `viscFromBelowGE_effOp_of_minPrinciple`): the minimum principle at the rational `(q, A)` with
  `μ*(q, A) = 0` gives `F*(D²v) ≥ 0` from below.
* `ssLimitSuperStar_of_minPrinciple`: step, from `SSInteriorMinPrincipleStmt` alone.
* `singleSourceTheoremStar_of_steps`: `SingleSourceTheoremStarStmt` from compactness, and
  minimality `SSLimitMinimalStarStmt` (Pegden-Smart Theorem 4.2 with a `μ*`-competitor;
  it contains the origin case ).
* `singleSourceTheoremStar_of_compactness_minimal`: from compactness and minimality only (the minimum principle
  from compactness and Lemma 5.5, `ssInteriorMinPrinciple_of_compactness`).
* `obstacleSetStar_subset_of_flatEff`: under `FlatEff` the `F*`-set lies in the printed set.

This is a variant, not a correction: the printed statement stays `SingleSourceTheoremStmt`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

open EffectiveOperatorBasic

variable {d : ℕ}

/-! ### The `μ*`-constraint and its obstacle problem -/

/-- `F*(D²u) ≥ 0` in `U`, tested from below, where `F*(M) = sup {l : μ*(l, M) > 0}`: whenever `φ`
is `C²` near `x ∈ U` and `u - φ` has a local minimum at `x`, then `μ*(l, D²φ(x)) > 0` for every
`l < 0`. -/
def ViscFromBelowMuStar (E : RandomEnvironment d) (U : Set (Rd d)) (u : Rd d → ℝ) : Prop :=
  ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMin (fun y => u y - φ y) x →
    ∀ l : ℝ, l < 0 → 0 < muStarBar E l (hessian φ x)

/-- The constraint set of the `F*`-variant of Theorem 9.2:
`{v ∈ C(ℝ^d) : v ≥ -G and F*(D²(v + G)) ≥ 0}`, both constraints on `ℝ^d ∖ {0}` as in
`singleSourceObstacleSet`. -/
def singleSourceObstacleSetStar (E : RandomEnvironment d) : Set (Rd d → ℝ) :=
  {v | Continuous v ∧ (∀ x : Rd d, x ≠ 0 → -fundamentalSolution d x ≤ v x) ∧
    ViscFromBelowMuStar E {x | x ≠ 0} (fun x => v x + fundamentalSolution d x)}

/-- The pointwise infimum of `singleSourceObstacleSetStar E` (junk value `0` as in
`singleSourceObstacleSolution`). -/
def singleSourceObstacleSolutionStar (E : RandomEnvironment d) : Rd d → ℝ :=
  fun x => sInf ((fun v : Rd d → ℝ => v x) '' singleSourceObstacleSetStar E)

theorem singleSourceObstacleSolutionStar_eq_of_isLeast {E : RandomEnvironment d} {v : Rd d → ℝ}
    (hv : IsLeast (singleSourceObstacleSetStar E) v) : singleSourceObstacleSolutionStar E = v := by
  funext x
  refine IsLeast.csInf_eq ⟨⟨v, hv.1, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hv.2 hw x

/-- **Theorem 9.2, `F*`-variant**: the conclusion of `SingleSourceTheoremStmt` with the obstacle set
`singleSourceObstacleSetStar` (no flatness hypothesis, no density hypothesis). -/
def SingleSourceTheoremStarStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    IsLeast (singleSourceObstacleSetStar E) (singleSourceObstacleSolutionStar E) ∧
    ∀ᵐ η ∂E.P,
      (∀ n : ℕ, (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty) ∧
        TendstoLocallyUniformlyOn
          (fun n : ℕ => rescaleSingleSource (singleSourceOdometer η n) n)
          (fun x => singleSourceObstacleSolutionStar E x + fundamentalSolution d x) atTop
          {x : Rd d | x ≠ 0}

/-- **Step**: the limits satisfy `F*(D²u) ≥ 0` off the origin, tested from below. -/
def SSLimitSuperStarStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u → ViscFromBelowMuStar E {x : Rd d | x ≠ 0} u

/-- **Step: minimality of the limits** for the `F*`-set. Route: at a point `a` where
`v - w` is maximal, `a ≠ 0` after Pegden-Smart Proposition 2.5 (`PegdenSmartTouchingStmt`), with
`D²(v + G)(a) < D²(w + G)(a) - δ I`, `μ*(-dδ/2, D²(w + G)(a)) > 0` gives a stabilizing function on
`B_{rh}(ha)` above `q_{D²(w+G)(a) - δI/2}` + affine with an inner contact point; with an integer
affine correction it undercuts `v_n` near `ha` and lies above it on the sphere, so its minimum with
`v_n` contradicts the leastness of the odometer.
The case where the maximum is attained only at the origin is part of this step. -/
def SSLimitMinimalStarStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, Continuous v →
      IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
        ∀ w ∈ singleSourceObstacleSetStar E, ∀ x, v x ≤ w x

/-! ### Step -/

/-- The deterministic core of step: a function satisfying the minimum principle relative to
the quadratics `p·(· - a) + q_M(· - a) + q_q(· - a)` on the closed balls of the open set `W`, at all
rational parameters with `μ*(q, M) = 0`, satisfies `F*(D²v) ≥ 0` in `W` tested from below: at a
local minimum of `v - φ`, `μ*(l, D²φ(x)) > 0` for every `l < 0`. Adapted from
`viscFromBelowGE_effOp_of_minPrinciple` (Theorem 1.1); no flatness is used. -/
theorem viscFromBelowMuStar_of_minPrinciple (hd : 2 ≤ d)
    (E : RandomEnvironment d) {W : Set (Rd d)} (hWo : IsOpen W) {v : Rd d → ℝ}
    (hη : ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), muStarBar E (q : ℝ) (symQ A) = 0 →
      ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
        ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
          v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) ≤
            v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a))) :
    ViscFromBelowMuStar E W v := by
  refine fun x hxW φ (hφ : ContDiffAt ℝ 2 φ x)
    (hloc : IsLocalMin (fun y => v y - φ y) x) l₀ hl₀ => ?_
  by_contra hneg
  set H := hessian φ x with hH_def
  have hzero : muStarBar E l₀ H = 0 :=
    le_antisymm (not_lt.1 hneg) (muStarBar_nonneg E l₀ H)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  -- symmetry of the Hessian of a `C²` function
  have hsym := ContDiffAt.isSymmSndFDerivAt hφ (by simp)
  have hH : H.IsSymm := by
    ext i j
    simp only [hH_def, hessian, Matrix.transpose_apply, Matrix.of_apply]
    exact hsym _ _
  -- the rational matrix `M ≥ H`
  set τ : ℝ := -l₀ / (4 * d) with hτ_def
  have hτ : 0 < τ := by rw [hτ_def]; apply div_pos <;> linarith
  have hHτ : (H + τ • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    hH.add (Matrix.isSymm_one.smul _)
  obtain ⟨A, hA⟩ := exists_symQ_near (H + τ • (1 : Matrix (Fin d) (Fin d) ℝ)) hHτ
    (ε := τ / (4 * (d : ℝ) ^ 2)) (by positivity)
  set M := symQ A with hM_def
  have hMerr : ∀ z : Rd d,
      |qM M z - qM (H + τ • (1 : Matrix (Fin d) (Fin d) ℝ)) z| ≤ τ / 4 * ‖z‖ ^ 2 := fun z => by
    rw [← qM_sub_mat]
    refine (abs_qM_le _ (by positivity) hA z).trans (le_of_eq ?_)
    field_simp
  have hMH : ∀ z : Rd d, τ / 4 * ‖z‖ ^ 2 ≤ qM M z - qM H z ∧
      qM M z - qM H z ≤ 3 * τ / 4 * ‖z‖ ^ 2 := fun z => by
    have h1 := abs_le.1 (hMerr z)
    rw [qM_add_mat, qM_smul_one] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hPSD : (M - H).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
    · exact Matrix.isHermitian_iff_isSymm.2 ((symQ_isSymm A).sub hH)
    · have h1 := (hMH (WithLp.toLp 2 w)).1
      have h2 : 0 ≤ qM (M - H) (WithLp.toLp 2 w) := by
        rw [qM_sub_mat]; nlinarith [sq_nonneg ‖(WithLp.toLp 2 w : Rd d)‖]
      unfold qM at h2
      simp only [star_trivial]
      simpa using h2
  -- the rational level `q ∈ (l₀, l₀ / 2)`
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show l₀ < l₀ / 2 by linarith)
  have hqM : muStarBar E (q : ℝ) M = 0 := by
    have hHM : H + (M - H) = M := by abel
    have h1 : muStarBar E (q : ℝ) M ≤ muStarBar E (q : ℝ) H := by
      have := (muBar_le_add muMatrixMonotone (by omega) E (q : ℝ) H (M - H) hPSD).2
      rwa [hHM] at this
    have h2 : muStarBar E (q : ℝ) H ≤ muStarBar E l₀ H :=
      muStarBar_anti muMonotone (by omega) E H hq1.le
    exact le_antisymm (by linarith) (muStarBar_nonneg E _ M)
  -- radii
  obtain ⟨ρ₀, hρ₀, hρ₀W⟩ := Metric.isOpen_iff.1 hWo x hxW
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ (κ := τ / 8) (by positivity)
  obtain ⟨ρ₂, hρ₂, hmin⟩ := Metric.eventually_nhds_iff.1 hloc
  set r := min ρ₀ (min ρ₁ ρ₂) / 2 with hr_def
  have hm : 0 < min ρ₀ (min ρ₁ ρ₂) := lt_min hρ₀ (lt_min hρ₁ hρ₂)
  have hr : 0 < r := half_pos hm
  have hrm : r < min ρ₀ (min ρ₁ ρ₂) := half_lt_self hm
  have hr0 : r < ρ₀ := hrm.trans_le (min_le_left _ _)
  have hr1 : r < ρ₁ := hrm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr2 : r < ρ₂ := hrm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrW : Metric.closedBall x r ⊆ W := (Metric.closedBall_subset_ball hr0).trans hρ₀W
  set p : Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x) with hp_def
  obtain ⟨y, hy, hle'⟩ := hη q A hqM x p r hr hrW x (Metric.mem_closedBall_self hr.le)
  simp only [sub_self, inner_zero_right, qM_zero_right, ql_zero_right, add_zero] at hle'
  have hya : ‖y - x‖ = r := by rw [← dist_eq_norm]; exact Metric.mem_sphere.1 hy
  have hp : inner ℝ p (y - x) = fderiv ℝ φ x (y - x) := by
    rw [hp_def, InnerProductSpace.toDual_symm_apply]
  have h1 := abs_le.1 (hT y (by rw [hya]; exact hr1))
  have h2 : v x - φ x ≤ v y - φ y := hmin (show dist y x < ρ₂ by rw [dist_eq_norm, hya]; exact hr2)
  have h3 := (hMH (y - x)).2
  have hH2 : 0 < ‖y - x‖ ^ 2 := by rw [hya]; positivity
  have hq : (q : ℝ) * ‖y - x‖ ^ 2 / (2 * d) < -τ * ‖y - x‖ ^ 2 := by
    rw [div_lt_iff₀ (by positivity), hτ_def]
    have : (q : ℝ) < l₀ / 2 := hq2
    have e : -(-l₀ / (4 * d)) * ‖y - x‖ ^ 2 * (2 * d) = l₀ / 2 * ‖y - x‖ ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith
  have hτH := mul_pos hτ hH2
  unfold ql at hle'
  rw [hp] at hle'
  nlinarith [h1.1, h2, h3, hq, hH2, hτH]

/-- **Step** from the interior minimum principle (`SSInteriorMinPrincipleStmt`); no
flatness. -/
theorem ssLimitSuperStar_of_minPrinciple (hMinP : SSInteriorMinPrincipleStmt) :
    SSLimitSuperStarStmt := by
  intro d hd E hmax
  have hrat : ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), muStarBar E (q : ℝ) (symQ A) = 0 →
      ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ {x : Rd d | x ≠ 0} →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            u y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) ≤
              u x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro A
    by_cases hq : muStarBar E (q : ℝ) (symQ A) = 0
    · filter_upwards [hMinP d hd E hmax q (symQ A) (symQ_isSymm A) hq] with η hη
      exact fun _ => hη
    · exact Eventually.of_forall fun η h => absurd h hq
  filter_upwards [hrat] with η hη
  exact fun u hu => viscFromBelowMuStar_of_minPrinciple hd E isOpen_ne
    fun q A hq => hη q A hq u hu

/-! ### The reduction -/

/-- **Theorem 9.2, `F*`-variant** from compactness, and minimality. -/
theorem singleSourceTheoremStar_of_steps (hComp : SSCompactnessStmt)
    (hSup : SSLimitSuperStarStmt) (hMin : SSLimitMinimalStarStmt) :
    SingleSourceTheoremStarStmt := by
  intro d hd E hmax
  have hd1 : 1 ≤ d := by omega
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  have hG : ∀ᵐ η ∂E.P, (∀ x, E.ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2) ∧
      (∀ u, IsSSSubseqLimit η u → ViscFromBelowMuStar E {x : Rd d | x ≠ 0} u) ∧
      (∀ v : Rd d → ℝ, Continuous v →
        IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
          ∀ w ∈ singleSourceObstacleSetStar E, ∀ x, v x ≤ w x) := by
    filter_upwards [hbdd, hSup d hd E hmax, hMin d hd E hmax] with η h1 h2 h3
    exact ⟨fun x => ⟨(h1 x).1, hmax ▸ (h1 x).2⟩, h2, h3⟩
  have hmem : ∀ η : Site d → ℤ,
      (∀ u, IsSSSubseqLimit η u → ViscFromBelowMuStar E {x : Rd d | x ≠ 0} u) →
      ∀ v : Rd d → ℝ, Continuous v →
        IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
          v ∈ singleSourceObstacleSetStar E := fun η hηV v hvc hv =>
    ⟨hvc, fun x hx => by have := hv.nonneg hx; linarith, hηV _ hv⟩
  obtain ⟨η₀, hη₀b, hη₀V, hη₀M⟩ := hG.exists
  obtain ⟨φ, hφ, v₀, hv₀c, hv₀⟩ := hComp d hd E.ηmin η₀ hη₀b id strictMono_id
  have hv₀L : IsSSSubseqLimit η₀ (fun x => v₀ x + fundamentalSolution d x) := ⟨φ, hφ, hv₀⟩
  have hLeast : IsLeast (singleSourceObstacleSetStar E) v₀ :=
    ⟨hmem η₀ hη₀V v₀ hv₀c hv₀L, fun w hw x => hη₀M v₀ hv₀c hv₀L w hw x⟩
  rw [singleSourceObstacleSolutionStar_eq_of_isLeast hLeast]
  refine ⟨hLeast, ?_⟩
  filter_upwards [hG] with η hη
  refine ⟨ssNonempty d hd1 η (fun x => (hη.1 x).2), ?_⟩
  refine tendstoLocallyUniformlyOn_of_subseq isOpen_ne fun nk hnk => ?_
  obtain ⟨ψ, hψ, v', hv'c, hv'⟩ := hComp d hd E.ηmin η hη.1 nk hnk
  have hv'L : IsSSSubseqLimit η (fun x => v' x + fundamentalSolution d x) :=
    ⟨nk ∘ ψ, hnk.comp hψ, hv'⟩
  have heq : v' = v₀ := funext fun x =>
    le_antisymm (hη.2.2 v' hv'c hv'L v₀ hLeast.1 x) (hLeast.2 (hmem η hη.2.1 v' hv'c hv'L) x)
  rw [heq] at hv'
  exact ⟨ψ, hψ, hv'⟩

/-- **Theorem 9.2, `F*`-variant** from compactness and minimality only. -/
theorem singleSourceTheoremStar_of_compactness_minimal (hComp : SSCompactnessStmt)
    (hMin : SSLimitMinimalStarStmt) : SingleSourceTheoremStarStmt :=
  singleSourceTheoremStar_of_steps hComp
    (ssLimitSuperStar_of_minPrinciple
      (ssInteriorMinPrinciple_of_compactness muConvergence_unconditional hComp)) hMin

/-! ### Relation with the printed obstacle set -/

/-- Under flatness, `F*(M) ≥ 0` (tested from below) implies `F̄_η(M) ≥ 0`: if `F̄_η(M) < 0`, then
`μ*(l, M) ≤ μ*(F̄_η(M), M) = 0` for `l ∈ (F̄_η(M), 0)`. -/
theorem effOp_nonneg_of_muStarBar_pos (hd : 2 ≤ d) (E : RandomEnvironment d)
    {M : Matrix (Fin d) (Fin d) ℝ} (hflat : FlatAt E M)
    (hpos : ∀ l : ℝ, l < 0 → 0 < muStarBar E l M) : 0 ≤ effOp E M := by
  by_contra hneg
  have hlt : effOp E M < 0 := not_le.1 hneg
  have h1 := hpos (effOp E M / 2) (by linarith)
  have h2 : muStarBar E (effOp E M / 2) M ≤ muStarBar E (effOp E M) M :=
    muStarBar_anti muMonotone (by omega) E M (by linarith)
  linarith [hflat.2]

/-- Under `FlatEff`, the `F*`-set lies in the printed obstacle set of Theorem 9.2. -/
theorem obstacleSetStar_subset_of_flatEff (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hflat : FlatEff E) : singleSourceObstacleSetStar E ⊆ singleSourceObstacleSet E := by
  rintro v ⟨hvc, hvG, hvS⟩
  refine ⟨hvc, hvG, fun x hx φ hφ hloc => ?_⟩
  have hsym := ContDiffAt.isSymmSndFDerivAt hφ (by simp)
  have hH : (hessian φ x).IsSymm := by
    ext i j
    simp only [hessian, Matrix.transpose_apply, Matrix.of_apply]
    exact hsym _ _
  exact effOp_nonneg_of_muStarBar_pos hd E (hflat _ hH) (hvS x hx φ hφ hloc)

end RandomSandpile

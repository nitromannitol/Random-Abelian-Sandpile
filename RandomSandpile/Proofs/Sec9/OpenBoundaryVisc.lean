import RandomSandpile.Steps.Sec9.OpenBoundary
import RandomSandpile.Proofs.Sec7.MainTheoremViscEff

/-!
# Theorem 9.1, steps: open-boundary limits are viscosity solutions

* `viscFromAboveLE_effOp_of_maxPrinciple`: the deterministic core of the subsolution test, the
  mirror of Theorem 1.1's `viscFromBelowGE_effOp_of_minPrinciple`. Let a `C²` test function `φ`
  touch `v` from above at `x ∈ W` and suppose `l₀ = F̄_η(D²φ(x)) > 0`. Take a rational symmetric
  `M ≤ D²φ(x)` within `τ/4` of `D²φ(x) - τI`, `τ = l₀/(4d)`; then `F̄_η(M) ≥ l₀` (Lemma 6.4(1)),
  so `μ(q, M) = 0` for a rational `q ∈ (l₀/2, l₀)` (`MuVanishStmt`). By Taylor's theorem for `φ`,
  `v - (Dφ(x)·(· - x) + q_M(· - x) + q_q(· - x))` has a strict local maximum at `x` (its quadratic
  part has Hessian `D²φ(x) - M - (q/d)I ≤ (3τ/2)I - (l₀/(2d))I = -(τ/2)I`), contradicting the
  maximum principle on a small sphere.
* `openLimitSubsolution_of_steps`, `openLimitSupersolution_of_steps`:, from Lemma 6.4(1),
  `MuVanishStmt` and the open-boundary interior principles.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- The deterministic core of step: a function satisfying the maximum principle relative to
the quadratics `p·(· - a) + q_M(· - a) + q_q(· - a)` on the closed balls of the open set `W`, at all
rational parameters with `q ≤ F̄_η(M)`, is a viscosity subsolution of `F̄_η(D²v) ≤ 0` in `W`. -/
theorem viscFromAboveLE_effOp_of_maxPrinciple (h64 : EffectiveOperatorBasicStmt) (hd : 2 ≤ d)
    (E : RandomEnvironment d) {W : Set (Rd d)} (hWo : IsOpen W) {v : Rd d → ℝ}
    (hη : ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), (q : ℝ) ≤ effOp E (symQ A) →
      ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
        ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
          v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) ≤
            v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a))) :
    ViscFromAboveLE (effOp E) W v := by
  refine fun x hxW φ (hφ : ContDiffAt ℝ 2 φ x)
    (hloc : IsLocalMax (fun y => v y - φ y) x) => ?_
  by_contra hneg
  have hl₀ : 0 < effOp E (hessian φ x) := not_le.1 hneg
  set H := hessian φ x with hH_def
  set l₀ := effOp E H with hl₀_def
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  -- symmetry of the Hessian of a `C²` function
  have hsym := ContDiffAt.isSymmSndFDerivAt hφ (by simp)
  have hH : H.IsSymm := by
    ext i j
    simp only [hH_def, hessian, Matrix.transpose_apply, Matrix.of_apply]
    exact hsym _ _
  -- the rational matrix `M ≤ H`
  set τ : ℝ := l₀ / (4 * d) with hτ_def
  have hτ : 0 < τ := by rw [hτ_def]; positivity
  have hHτ : (H + (-τ) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    hH.add (Matrix.isSymm_one.smul _)
  obtain ⟨A, hA⟩ := exists_symQ_near (H + (-τ) • (1 : Matrix (Fin d) (Fin d) ℝ)) hHτ
    (ε := τ / (4 * (d : ℝ) ^ 2)) (by positivity)
  set M := symQ A with hM_def
  have hMerr : ∀ z : Rd d,
      |qM M z - qM (H + (-τ) • (1 : Matrix (Fin d) (Fin d) ℝ)) z| ≤ τ / 4 * ‖z‖ ^ 2 := fun z => by
    rw [← qM_sub_mat]
    refine (abs_qM_le _ (by positivity) hA z).trans (le_of_eq ?_)
    field_simp
  have hMH : ∀ z : Rd d, -(3 * τ / 4 * ‖z‖ ^ 2) ≤ qM M z - qM H z ∧
      qM M z - qM H z ≤ -(τ / 4 * ‖z‖ ^ 2) := fun z => by
    have h1 := abs_le.1 (hMerr z)
    rw [qM_add_mat, qM_smul_one] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hPSD : (H - M).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
    · exact Matrix.isHermitian_iff_isSymm.2 (hH.sub (symQ_isSymm A))
    · have h1 := (hMH (WithLp.toLp 2 w)).2
      have h2 : 0 ≤ qM (H - M) (WithLp.toLp 2 w) := by
        rw [qM_sub_mat]; nlinarith [sq_nonneg ‖(WithLp.toLp 2 w : Rd d)‖]
      unfold qM at h2
      simp only [star_trivial]
      simpa using h2
  have hle : l₀ ≤ effOp E M := by
    obtain ⟨C, -, hC⟩ := h64 d hd E.ηmin E.ηmax
    exact (hC E rfl rfl M H (symQ_isSymm A) hH).1 hPSD
  -- the rational level `q ∈ (l₀ / 2, l₀)`
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show l₀ / 2 < l₀ by linarith)
  have hqM : (q : ℝ) ≤ effOp E M := hq2.le.trans hle
  -- radii
  obtain ⟨ρ₀, hρ₀, hρ₀W⟩ := Metric.isOpen_iff.1 hWo x hxW
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ (κ := τ / 8) (by positivity)
  obtain ⟨ρ₂, hρ₂, hmax⟩ := Metric.eventually_nhds_iff.1 hloc
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
  have h2 : v y - φ y ≤ v x - φ x := hmax (show dist y x < ρ₂ by rw [dist_eq_norm, hya]; exact hr2)
  have h3 := (hMH (y - x)).1
  have hH2 : 0 < ‖y - x‖ ^ 2 := by rw [hya]; positivity
  have hq : τ * ‖y - x‖ ^ 2 < (q : ℝ) * ‖y - x‖ ^ 2 / (2 * d) := by
    rw [lt_div_iff₀ (by positivity), hτ_def]
    have : l₀ / 2 < (q : ℝ) := hq1
    have e : l₀ / (4 * d) * ‖y - x‖ ^ 2 * (2 * d) = l₀ / 2 * ‖y - x‖ ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith
  have hτH := mul_pos hτ hH2
  unfold ql at hle'
  rw [hp] at hle'
  nlinarith [h1.2, h2, h3, hq, hH2, hτH]

/-! ### The interior principles at rational parameters -/

theorem ae_openInteriorMaxPrinciple_rat (hVan : MuVanishStmt)
    (hMax : OpenInteriorMaxPrincipleStmt) (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hHD : HighDensity E.P) (W : Set (Rd d)) (hW : IsLipschitzDomain W) :
    ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), (q : ℝ) ≤ effOp E (symQ A) →
      ∀ v : Rd d → ℝ, IsOpenOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) ≤
              v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) := by
  rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro A
  by_cases hq : (q : ℝ) ≤ effOp E (symQ A)
  · filter_upwards [hMax d hd E W hW q (symQ A) (symQ_isSymm A)
      ((hVan d hd E hHD (symQ A) (symQ_isSymm A) q).1 hq)] with η hη
    exact fun _ => hη
  · exact Eventually.of_forall fun η h => absurd h hq

theorem ae_openInteriorMinPrinciple_rat (hVan : MuVanishStmt)
    (hMin : OpenInteriorMinPrincipleStmt) (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hHD : HighDensity E.P) (W : Set (Rd d)) (hW : IsLipschitzDomain W) :
    ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), effOp E (symQ A) ≤ (q : ℝ) →
      ∀ v : Rd d → ℝ, IsOpenOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) ≤
              v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) := by
  rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro A
  by_cases hq : effOp E (symQ A) ≤ (q : ℝ)
  · filter_upwards [hMin d hd E W hW q (symQ A) (symQ_isSymm A)
      ((hVan d hd E hHD (symQ A) (symQ_isSymm A) q).2 hq)] with η hη
    exact fun _ => hη
  · exact Eventually.of_forall fun η h => absurd h hq

/-! ### The reductions -/

/-- **Step** of Theorem 9.1 from Lemma 6.4(1), `MuVanishStmt` and the open-boundary
interior maximum principle. -/
theorem openLimitSubsolution_of_steps (h64 : EffectiveOperatorBasicStmt) (hVan : MuVanishStmt)
    (hMax : OpenInteriorMaxPrincipleStmt) : OpenLimitSubsolutionStmt := by
  intro d hd E hHD W hW
  filter_upwards [ae_openInteriorMaxPrinciple_rat hVan hMax hd E hHD W hW] with η hη
  exact fun v hv => viscFromAboveLE_effOp_of_maxPrinciple h64 hd E hW.2.1
    fun q A hq => hη q A hq v hv

/-- **Step** of Theorem 9.1 from Lemma 6.4(1), `MuVanishStmt` and the open-boundary
interior minimum principle. -/
theorem openLimitSupersolution_of_steps (h64 : EffectiveOperatorBasicStmt) (hVan : MuVanishStmt)
    (hMin : OpenInteriorMinPrincipleStmt) : OpenLimitSupersolutionStmt := by
  intro d hd E hHD W hW
  filter_upwards [ae_openInteriorMinPrinciple_rat hVan hMin hd E hHD W hW] with η hη
  exact fun v hv => viscFromBelowGE_effOp_of_minPrinciple h64 hd E hW.2.1
    fun q A hq => hη q A hq v hv

end RandomSandpile

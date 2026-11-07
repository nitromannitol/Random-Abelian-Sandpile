import RandomSandpile.Proofs.Sec9.RecurrentInteriorMin

/-! # Recurrent viscosity supersolution -/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric Topology
open scoped ENNReal Matrix

namespace RandomSandpile

variable {d : ℕ}

/-- Source: `RandomSandpile/Proofs/Sec7/MainTheoremViscEff.lean`,
`viscFromBelowGE_effOp_of_minPrinciple`, generalized to a degenerate
elliptic operator. -/
theorem viscFromBelowGE_of_rational_minPrinciple (hd : 2 ≤ d)
    (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (hEll : DegenerateElliptic F) {W : Set (Rd d)} (hWo : IsOpen W) {v : Rd d → ℝ}
    (hη : ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), F (symQ A) ≤ (q : ℝ) →
      ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
        ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
          v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) ≤
            v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a))) :
    ViscFromBelowGE (F) W v := by
  refine fun x hxW φ (hφ : ContDiffAt ℝ 2 φ x)
    (hloc : IsLocalMin (fun y => v y - φ y) x) => ?_
  by_contra hneg
  have hl₀ : F (hessian φ x) < 0 := not_le.1 hneg
  set H := hessian φ x with hH_def
  set l₀ := F H with hl₀_def
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsym := ContDiffAt.isSymmSndFDerivAt hφ (by simp)
  have hH : H.IsSymm := by
    ext i j
    simp only [hH_def, hessian, Matrix.transpose_apply, Matrix.of_apply]
    exact hsym _ _
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
  have hle : F M ≤ l₀ := by
    exact hEll H M hH (symQ_isSymm A) hPSD
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show l₀ < l₀ / 2 by linarith)
  have hqM : F M ≤ (q : ℝ) := hle.trans hq1.le
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

/-- The standard lower mass vanishes simultaneously at all rational
curvatures above the recurrent effective operator. -/
theorem ae_recurrent_lower_ball_mass_rat (hd : 2 ≤ d) (E : RandomEnvironment d) :
    ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ),
      effOpRecurrent E (symQ A) ≤ (q : ℝ) →
      ∀ (a : Rd d) (r : ℝ), 0 < r →
        (∀ n, muStar (discretize (ball a r) n) η q (symQ A) ≠ ⊤) ∧
        Tendsto (fun n : ℕ => (muStar (discretize (ball a r) n) η q (symQ A)).toReal /
          ((discretize (ball a r) n).ncard : ℝ)) atTop (𝓝 0) := by
  rw [ae_all_iff]
  intro q
  rw [ae_all_iff]
  intro A
  by_cases hq : effOpRecurrent E (symQ A) ≤ (q : ℝ)
  · have hz : muStarBar E q (symQ A) = 0 := by
      rw [← muStarRecurrentBar_eq hd E]
      apply le_antisymm _ ENNReal.toReal_nonneg
      exact (muStarRecurrentBar_anti hd E (symQ A) hq).trans_eq
        (recurrentCommonZero_at_operator recurrent_common_zero hd E (symQ A)).2
    filter_upwards [(muConvergence_unconditional d hd).1 E (symQ A) (symQ_isSymm A) q] with η hη
    intro _ a r hr
    obtain ⟨hfin, _, hlim⟩ := hη (ball a r) (StrictConcavityBall.isLipschitzDomain_ball a hr)
    rw [hz] at hlim
    exact ⟨fun n => (hfin n).2, hlim⟩
  · exact Eventually.of_forall fun η h => absurd h hq

/-- Single-source subsequential limits are viscosity supersolutions for the
recurrent effective operator away from the source. -/
theorem recurrentSSSupersolution : RecurrentSSSupersolutionStmt := by
  intro d hd E
  filter_upwards [ae_recurrent_lower_ball_mass_rat hd E, recurrentSSCompactness d hd E] with η hmass hcomp
  intro hfinite htail u hu
  obtain ⟨nk, hnk, hconv⟩ := hu
  obtain ⟨φ, hφ, v, hvc, hconvφ⟩ := hcomp hfinite htail nk hnk
  have huv : Set.EqOn u (fun y => v y + fundamentalSolution d y) {x : Rd d | x ≠ 0} :=
    fun y hy => tendsto_nhds_unique ((hconv.tendsto_at hy).comp hφ.tendsto_atTop)
      (hconvφ.tendsto_at hy)
  have hucont : ContinuousOn u {x : Rd d | x ≠ 0} :=
    (hvc.continuousOn.add (SingleSourceMin.continuousOn_fundamentalSolution d)).congr huv
  apply viscFromBelowGE_of_rational_minPrinciple hd (effOpRecurrent E)
    (recurrent_degenerateElliptic hd E) isOpen_ne
  intro q A hq a p r hr hball x hx
  obtain ⟨hfinμ, hlimμ⟩ := hmass q A hq a r hr
  exact recurrent_interior_min_of_vanishing hd hfinite hnk hconv hucont a p r hr hball
    q (symQ A) (symQ_isSymm A) hfinμ hlimμ hx

/-- The recurrent single-source convergence theorem under the vanishing-tail
condition, with Alexandrov's theorem as an explicit input. -/
theorem singleSourceRecurrentVT (hA : AlexandrovStmt) : SingleSourceTheoremRecurrentVTStmt :=
  singleSourceRecurrentVT_of_supersolution hA recurrentSSSupersolution

/-- The recurrent single-source convergence theorem under the height bound,
with explicit Fey–Levine–Peres and Alexandrov inputs. -/
theorem singleSourceRecurrent (hFLP : External.FeyLevinePeresRadius) (hA : AlexandrovStmt) :
    SingleSourceTheoremRecurrentStmt :=
  singleSourceRecurrent_of_supersolution hFLP hA recurrentSSSupersolution

end RandomSandpile

import RandomSandpile.Proofs.Sec9.RecurrentInteriorMax
import RandomSandpile.Proofs.Sec9.RecurrentOperatorBasic
import RandomSandpile.Proofs.Sec9.OpenBoundaryVisc
import RandomSandpile.Proofs.Sec9.RecurrentCorrectorEquicontinuity
import RandomSandpile.Proofs.Sec9.RecurrentCompactnessAssembly
import RandomSandpile.Steps.Sec9.RecurrentComparison

/-! # Viscosity inequalities on the positivity set -/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric Topology
open scoped ENNReal Matrix

namespace RandomSandpile

variable {d : ℕ}

/-- Source: `RandomSandpile/Proofs/Sec9/OpenBoundaryVisc.lean`,
`viscFromAboveLE_effOp_of_maxPrinciple`, generalized to any degenerate
elliptic operator. -/
theorem viscFromAboveLE_of_rational_maxPrinciple (hd : 2 ≤ d)
    (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (hEll : DegenerateElliptic F) {W : Set (Rd d)} (hWo : IsOpen W) {v : Rd d → ℝ}
    (hη : ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), (q : ℝ) ≤ F (symQ A) →
      ∀ (a p : Rd d) (r R : ℝ), 0 < r → r < R → Metric.closedBall a R ⊆ W →
        ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
          v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) ≤
            v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a))) :
    ViscFromAboveLE (F) W v := by
  refine fun x hxW φ (hφ : ContDiffAt ℝ 2 φ x)
    (hloc : IsLocalMax (fun y => v y - φ y) x) => ?_
  by_contra hneg
  have hl₀ : 0 < F (hessian φ x) := not_le.1 hneg
  set H := hessian φ x with hH_def
  set l₀ := F H with hl₀_def
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsym := ContDiffAt.isSymmSndFDerivAt hφ (by simp)
  have hH : H.IsSymm := by
    ext i j
    simp only [hH_def, hessian, Matrix.transpose_apply, Matrix.of_apply]
    exact hsym _ _
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
  have hle : l₀ ≤ F M := by
    exact hEll M H (symQ_isSymm A) hH hPSD
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show l₀ / 2 < l₀ by linarith)
  have hqM : (q : ℝ) ≤ F M := hq2.le.trans hle
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
  have hrW : Metric.closedBall x ((r + ρ₀) / 2) ⊆ W :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρ₀W
  set p : Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x) with hp_def
  obtain ⟨y, hy, hle'⟩ := hη q A hqM x p r ((r + ρ₀) / 2) hr (by linarith) hrW x
    (Metric.mem_closedBall_self hr.le)
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

/-- The recurrent upper mass vanishes simultaneously at all rational
curvatures below the recurrent effective operator. -/
theorem ae_recurrent_ball_mass_rat (hd : 2 ≤ d) (E : RandomEnvironment d) :
    ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ),
      (q : ℝ) ≤ effOpRecurrent E (symQ A) →
      ∀ (a : Rd d) (r : ℝ), 0 < r →
        (∀ n, muRecurrent (discretize (ball a r) n) η q (symQ A) ≠ ⊤) ∧
        Tendsto (fun n : ℕ => (muRecurrent (discretize (ball a r) n) η q (symQ A)).toReal /
          (n : ℝ) ^ d) atTop (𝓝 0) := by
  rw [ae_all_iff]
  intro q
  rw [ae_all_iff]
  intro A
  by_cases hq : (q : ℝ) ≤ effOpRecurrent E (symQ A)
  · have hz : muRecurrentBar E q (symQ A) = 0 := by
      apply le_antisymm _ (muRecurrent_convergence hd E q (symQ A)).1
      exact (muRecurrentBar_mono hd E (symQ A) hq).trans_eq
        (recurrentCommonZero_at_operator recurrent_common_zero hd E (symQ A)).1
    filter_upwards [ae_recurrent_ball_mass_vanishing hd E q (symQ A) hz] with η hη
    exact fun _ => hη
  · exact Eventually.of_forall fun η h => absurd h hq

/-- Single-source subsequential limits are viscosity subsolutions for the
recurrent effective operator on their positive set away from the source. -/
theorem recurrentSSPositiveSubsolution : RecurrentSSPositiveSubsolutionStmt := by
  intro d hd E
  filter_upwards [ae_recurrent_ball_mass_rat hd E, recurrentSSCompactness d hd E] with η hmass hcomp
  intro hfinite htail u hu
  obtain ⟨nk, hnk, hconv⟩ := hu
  obtain ⟨φ, hφ, v, hvc, hconvφ⟩ := hcomp hfinite htail nk hnk
  have huv : Set.EqOn u (fun y => v y + fundamentalSolution d y) {x : Rd d | x ≠ 0} :=
    fun y hy => tendsto_nhds_unique ((hconv.tendsto_at hy).comp hφ.tendsto_atTop)
      (hconvφ.tendsto_at hy)
  have hucont : ContinuousOn u {x : Rd d | x ≠ 0} :=
    (hvc.continuousOn.add (SingleSourceMin.continuousOn_fundamentalSolution d)).congr huv
  have hopen : IsOpen {x : Rd d | x ≠ 0 ∧ 0 < u x} := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hx0 := isOpen_ne.mem_nhds hx.1
    filter_upwards [hx0, (hucont.continuousAt hx0).eventually (Ioi_mem_nhds hx.2)] with y hy0 hyp
    exact ⟨hy0, hyp⟩
  apply viscFromAboveLE_of_rational_maxPrinciple hd (effOpRecurrent E)
    (recurrent_degenerateElliptic hd E) hopen
  intro q A hq a p r R hr hrR hball x hx
  obtain ⟨hfinμ, hlimμ⟩ := hmass q A hq a r hr
  have hK0 : closedBall a R ⊆ {x : Rd d | x ≠ 0} := fun y hy => (hball hy).1
  exact recurrent_interior_max_of_vanishing hd hfinite hnk hconv hr hrR hK0
    (hucont.mono hK0) (fun y hy => (hball hy).2) q (symQ A) (symQ_isSymm A) hfinμ hlimμ hx

/-- The vanishing-tail convergence theorem now requires only the recurrent
supersolution step and the explicit Alexandrov input. -/
theorem singleSourceRecurrentVT_of_supersolution (hA : AlexandrovStmt)
    (hsuper : RecurrentSSSupersolutionStmt) : SingleSourceTheoremRecurrentVTStmt :=
  singleSourceRecurrentVT_of_viscosity hA hsuper recurrentSSPositiveSubsolution

/-- The height-bound convergence theorem additionally requires the explicit
Fey–Levine–Peres outer-radius input. -/
theorem singleSourceRecurrent_of_supersolution (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (hsuper : RecurrentSSSupersolutionStmt) :
    SingleSourceTheoremRecurrentStmt :=
  singleSourceRecurrent_of_viscosity hFLP hA hsuper recurrentSSPositiveSubsolution

end RandomSandpile

import RandomSandpile.Proofs.Sec9.FlatCorrectorExtract

/-!
# Operator fact (11): the lifted environment `η + K`

`liftEnv E K`: the law of `η + K` (a constant `K : ℤ` added to every site) is again a random
environment (bounded by `η_min + K`, `η_max + K`, stationary, ergodic), and for `K` large it has
high density. Used for the shift identity of ((1): `μ*(A, η, l, M) =
μ*(A, η + 2dk, l, M - 2kI)`) that places a bounded law in the paper's high-density regime.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal

namespace RandomSandpile

variable {d : ℕ}

/-- Adding the constant `K` to a configuration, as a measurable equivalence. -/
def addConstEquiv (d : ℕ) (K : ℤ) : Config d ≃ᵐ Config d :=
  MeasurableEquiv.addRight (fun _ : Site d => K)

theorem addConstEquiv_apply (K : ℤ) (η : Config d) (x : Site d) : addConstEquiv d K η x = η x + K :=
  rfl

theorem shift_addConst (K : ℤ) (y : Site d) (η : Config d) :
    shift y (addConstEquiv d K η) = addConstEquiv d K (shift y η) := rfl

/-- The environment of `η + K`. -/
def liftEnv (E : RandomEnvironment d) (K : ℤ) : RandomEnvironment d where
  P := E.P.map (addConstEquiv d K)
  isProb := Measure.isProbabilityMeasure_map (addConstEquiv d K).measurable.aemeasurable
  ηmin := E.ηmin + K
  ηmax := E.ηmax + K
  bounded := fun x => by
    have hm : MeasurableSet {η : Config d | E.ηmin + K ≤ η x ∧ η x ≤ E.ηmax + K} :=
      (measurableSet_le measurable_const (measurable_pi_apply x)).inter
        (measurableSet_le (measurable_pi_apply x) measurable_const)
    rw [ae_map_iff (addConstEquiv d K).measurable.aemeasurable hm]
    filter_upwards [E.bounded x] with η h
    simp only [addConstEquiv_apply]
    omega
  stationary := fun y => by
    refine ⟨measurable_shift y, ?_⟩
    rw [Measure.map_map (measurable_shift y) (addConstEquiv d K).measurable]
    have : (shift y ∘ addConstEquiv d K) = (addConstEquiv d K ∘ shift y) :=
      funext fun η => shift_addConst K y η
    rw [this, ← Measure.map_map (addConstEquiv d K).measurable (measurable_shift y),
      (E.stationary y).map_eq]
  ergodic := fun S hS hinv => by
    rw [(addConstEquiv d K).map_apply]
    refine E.ergodic _ ((addConstEquiv d K).measurable hS) fun y => ?_
    have h1 : shift y ⁻¹' ((addConstEquiv d K) ⁻¹' S) = (addConstEquiv d K) ⁻¹' (shift y ⁻¹' S) := by
      ext η; simp [shift_addConst]
    rw [h1, hinv y]

theorem liftEnv_ηmin (E : RandomEnvironment d) (K : ℤ) : (liftEnv E K).ηmin = E.ηmin + K := rfl

theorem liftEnv_ηmax (E : RandomEnvironment d) (K : ℤ) : (liftEnv E K).ηmax = E.ηmax + K := rfl

/-- High density of the lift for large `K`. -/
theorem liftEnv_highDensity (E : RandomEnvironment d) (K : ℤ) (hK : 2 * (d : ℤ) - 1 < E.ηmin + K) :
    HighDensity (liftEnv E K).P := by
  unfold HighDensity meanEta
  show 2 * (d : ℝ) - 1 < ∫ η, (η 0 : ℝ) ∂(E.P.map (addConstEquiv d K))
  rw [(addConstEquiv d K).measurableEmbedding.integral_map (fun η : Config d => (η 0 : ℝ))]
  have hint : Integrable (fun η : Config d => (η 0 : ℝ)) E.P := by
    refine Integrable.of_bound (C := max |(E.ηmin : ℝ)| |(E.ηmax : ℝ)|) ?_ ?_
    · have hm : Measurable (fun η : Config d => ((η 0 : ℤ) : ℝ)) :=
        measurable_from_top.comp (measurable_pi_apply (0 : Site d))
      exact hm.aestronglyMeasurable
    · filter_upwards [E.bounded 0] with η h
      rw [Real.norm_eq_abs, abs_le]
      have h1 : (E.ηmin : ℝ) ≤ η 0 := by exact_mod_cast h.1
      have h2 : (η 0 : ℝ) ≤ E.ηmax := by exact_mod_cast h.2
      have := le_max_left |(E.ηmin : ℝ)| |(E.ηmax : ℝ)|
      have := le_max_right |(E.ηmin : ℝ)| |(E.ηmax : ℝ)|
      constructor <;> [skip; skip] <;> nlinarith [neg_abs_le (E.ηmin : ℝ), le_abs_self (E.ηmax : ℝ),
        abs_nonneg (E.ηmin : ℝ), abs_nonneg (E.ηmax : ℝ), le_abs_self (E.ηmin : ℝ), neg_abs_le (E.ηmax : ℝ)]
  have hge : (E.ηmin : ℝ) + K ≤ ∫ η, ((addConstEquiv d K η) 0 : ℝ) ∂E.P := by
    have : ∫ _η, ((E.ηmin : ℝ) + K) ∂E.P ≤ ∫ η, ((addConstEquiv d K η) 0 : ℝ) ∂E.P := by
      refine integral_mono_ae (integrable_const _) (hint.add (integrable_const (K : ℝ))
        |>.congr (Eventually.of_forall fun η => by simp [addConstEquiv_apply])) ?_
      filter_upwards [E.bounded 0] with η h
      simp only [addConstEquiv_apply]
      have : (E.ηmin : ℝ) ≤ η 0 := by exact_mod_cast h.1
      push_cast; linarith
    simpa using this
  have : (2 * (d : ℝ) - 1) < (E.ηmin : ℝ) + K := by exact_mod_cast hK
  linarith

end RandomSandpile

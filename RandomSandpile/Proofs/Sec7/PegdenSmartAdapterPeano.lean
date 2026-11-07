import RandomSandpile.Proofs.Sec7.MainTheoremUniqueness
import RandomSandpile.Infra.Touching

/-!
# Second-order Peano expansions: algebra

Elementary facts about `HasSecondOrderTaylorAt` used to derive `PegdenSmartTouchingStmt` from
Pegden-Smart's Propositions 2.4 and 2.5 (`Inputs/PegdenSmartProp25.lean`):

* `taylor_sub`: expansions of `u` and `v` give one of `u - v`;
* `taylor_add_sq_norm`: adding `c |x - b|²` adds `2c(a - b)` to the gradient and `2c I` to the
  matrix;
* `taylor_comp_affine`: the expansion of `z ↦ u(c + ρ z)` at `y` from that of `u` at `c + ρ y`;
* `qM_eq_of_taylor`: two expansions of the same function at the same point have the same quadratic
  form (the second symmetric difference `f(a + th) + f(a - th) - 2f(a)` cancels the gradients).
-/

noncomputable section

open Filter Topology Asymptotics

namespace RandomSandpile

variable {d : ℕ}

namespace PegdenSmartAdapter

theorem qM_smul_mat (t : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (h : Rd d) :
    qM (t • M) h = t * qM M h := by
  simp only [qM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-- Expansions of `u` and `v` at `a` give one of `u - v`. -/
theorem taylor_sub {u v : Rd d → ℝ} {a p p' : Rd d} {X X' : Matrix (Fin d) (Fin d) ℝ}
    (hu : HasSecondOrderTaylorAt u a p X) (hv : HasSecondOrderTaylorAt v a p' X') :
    HasSecondOrderTaylorAt (fun x => u x - v x) a (p - p') (X - X') := by
  refine IsLittleO.congr (IsLittleO.sub hu hv) (fun x => ?_) (fun x => rfl)
  simp only [inner_sub_left, qM_sub_mat]
  ring

/-- Adding `c |x - b|²` to `u`. -/
theorem taylor_add_sq_norm {u : Rd d → ℝ} {a p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ}
    (hu : HasSecondOrderTaylorAt u a p X) (c : ℝ) (b : Rd d) :
    HasSecondOrderTaylorAt (fun x => u x + c * ‖x - b‖ ^ 2) a
      (p + (2 * c) • (a - b)) (X + (2 * c) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  refine IsLittleO.congr hu (fun x => ?_) (fun x => rfl)
  have e : ‖x - b‖ ^ 2 = ‖x - a‖ ^ 2 + 2 * inner ℝ (a - b) (x - a) + ‖a - b‖ ^ 2 := by
    rw [show x - b = (x - a) + (a - b) by abel, norm_add_sq_real, real_inner_comm]
  simp only [qM_add_mat, qM_smul_one, inner_add_left, real_inner_smul_left, e]
  ring

/-- The expansion of `z ↦ u(c + ρ z)` at `y` from that of `u` at `c + ρ y`. -/
theorem taylor_comp_affine {u : Rd d → ℝ} {c y p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ} {ρ : ℝ}
    (hu : HasSecondOrderTaylorAt u (c + ρ • y) p X) :
    HasSecondOrderTaylorAt (fun z => u (c + ρ • z)) y (ρ • p) (ρ ^ 2 • X) := by
  have hT : Tendsto (fun z : Rd d => c + ρ • z) (𝓝 y) (𝓝 (c + ρ • y)) :=
    (continuous_const.add (continuous_const_smul ρ)).tendsto y
  have key : ∀ z : Rd d, c + ρ • z - (c + ρ • y) = ρ • (z - y) := fun z => by
    rw [smul_sub]; abel
  have h1 : (fun z => u (c + ρ • z) - u (c + ρ • y) - inner ℝ (ρ • p) (z - y) -
      qM (ρ ^ 2 • X) (z - y)) =o[𝓝 y] fun z => ρ ^ 2 * ‖z - y‖ ^ 2 := by
    refine IsLittleO.congr (IsLittleO.comp_tendsto hu hT) (fun z => ?_) (fun z => ?_)
    · simp only [Function.comp_apply, key, real_inner_smul_left, real_inner_smul_right, qM_smul,
        qM_smul_mat]
    · simp only [Function.comp_apply, key, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  exact h1.trans_isBigO (isBigO_const_mul_self _ _ _)

/-- Two expansions of the same function at the same point have the same quadratic form. -/
theorem qM_eq_of_taylor {f : Rd d → ℝ} {a p p' : Rd d} {X X' : Matrix (Fin d) (Fin d) ℝ}
    (h1 : HasSecondOrderTaylorAt f a p X) (h2 : HasSecondOrderTaylorAt f a p' X') (h : Rd d) :
    qM X h = qM X' h := by
  have hR : (fun x => inner ℝ (p' - p) (x - a) + qM (X' - X) (x - a)) =o[𝓝 a]
      fun x => ‖x - a‖ ^ 2 := by
    refine IsLittleO.congr (IsLittleO.sub h1 h2) (fun x => ?_) (fun x => rfl)
    simp only [inner_sub_left, qM_sub_mat]
    ring
  have hT : Tendsto (fun t : ℝ => a + t • h) (𝓝 0) (𝓝 a) := by
    have := (continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ)
      (f := fun t : ℝ => a + t • h)
    simpa using this
  have hT' : Tendsto (fun t : ℝ => a + (-t) • h) (𝓝 0) (𝓝 a) := by
    have := (continuous_const.add (continuous_neg.smul continuous_const)).tendsto (0 : ℝ)
      (f := fun t : ℝ => a + (-t) • h)
    simpa using this
  have hA : (fun t : ℝ => inner ℝ (p' - p) (t • h) + t ^ 2 * qM (X' - X) h) =o[𝓝 0]
      fun t => t ^ 2 * ‖h‖ ^ 2 := by
    refine IsLittleO.congr (IsLittleO.comp_tendsto hR hT) (fun t => ?_) (fun t => ?_)
    · simp only [Function.comp_apply, add_sub_cancel_left, qM_smul]
    · simp only [Function.comp_apply, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs]
  have hB : (fun t : ℝ => inner ℝ (p' - p) ((-t) • h) + t ^ 2 * qM (X' - X) h) =o[𝓝 0]
      fun t => t ^ 2 * ‖h‖ ^ 2 := by
    refine IsLittleO.congr (IsLittleO.comp_tendsto hR hT') (fun t => ?_) (fun t => ?_)
    · simp only [Function.comp_apply, add_sub_cancel_left, qM_smul, neg_sq]
    · simp only [Function.comp_apply, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs, neg_sq]
  have hC : (fun t : ℝ => (2 * qM (X' - X) h) * t ^ 2) =o[𝓝 0] fun t => ‖h‖ ^ 2 * t ^ 2 := by
    refine IsLittleO.congr (hA.add hB) (fun t => ?_) (fun t => by ring)
    simp only [real_inner_smul_right]
    ring
  generalize hcdef : 2 * qM (X' - X) h = c at hC
  have hc : c = 0 := by
    by_contra hne
    have hpos : 0 < |c| := abs_pos.2 hne
    have hε : 0 < |c| / (2 * (‖h‖ ^ 2 + 1)) := div_pos hpos (by positivity)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hC.def hε)
    have ht := hball (show dist (δ / 2) (0 : ℝ) < δ by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    have ht2 : 0 < (δ / 2) ^ 2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos ht2,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖h‖ ^ 2)] at ht
    have h2' : |c| / (2 * (‖h‖ ^ 2 + 1)) * ‖h‖ ^ 2 < |c| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg ‖h‖]
    nlinarith [mul_lt_mul_of_pos_right h2' ht2]
  rw [hc, qM_sub_mat] at hcdef
  linarith

end PegdenSmartAdapter

end RandomSandpile

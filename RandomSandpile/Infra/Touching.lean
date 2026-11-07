import RandomSandpile.Inputs.Proposed
import RandomSandpile.Inputs.Alexandrov

/-!
# The touching lemma of Pegden and Smart (Prop 2.5): decomposition

Target: `RandomSandpile.PegdenSmartTouchingStmt` (`RandomSandpile/Inputs/Proposed.lean`), consumed
by Lemma 7.6(1) (`pegdenSmartRegularity_of_steps`). Let `w = u - v`, where `u` is a viscosity
subsolution of `-Δu - K = 0` and `v` a viscosity supersolution of `-Δv + K = 0` in `U`, and
`w > m ≥ w|_{∂U}` somewhere. The conclusion has two independent halves.

* **Contact set** (`ContactSetPositiveStmt`). For some `δ > 0` the upper contact set
  `{a ∈ U : w(a) > m, w ≤ w(a) + p·(x - a) - δ|x - a|² on U for some p}` (the points where `w`
  is touched from above by a concave paraboloid of opening `2δ`) has positive Lebesgue measure.
  Route (Jensen's lemma, Crandall-Ishii-Lions *User's guide* §5 and Caffarelli-Cabré Ch. 5):
  replace `u` by its sup-convolution `u^ε` and `v` by its inf-convolution `v_ε`
  (`RandomSandpile/Infra/SupConvolution.lean`); `u^ε - v_ε` is semiconvex, hence twice
  differentiable a.e. by `AlexandrovStmt`, and keeps `Δ(u^ε - v_ε) ≥ -2K` at those points;
  the gradient map of the perturbed maxima is onto a ball of slopes and has Jacobian
  `≤ (2K/d)^d`, so the contact sets of `u^ε - v_ε` have measure bounded below uniformly in `ε`;
  their `limsup` as `ε → 0` lies in the contact set of `w`.
* **Twice differentiability of `u` and `v` themselves** (`BoundedLaplacianPeanoAEStmt`). This is
  *not* a consequence of Alexandrov's theorem: a function with `|Δu| ≤ K` need not be
  semiconvex (it is `W^{2,p}` for `p < ∞` but not `C^{1,1}` in general), and sup-convolutions
  only transfer one-sided (superjet) information to `u` at shifted points. It is the a.e.
  second-order differentiability of `W^{2,p}` functions (Calderón-Zygmund) or, in the viscosity
  route, Caffarelli's `W^{2,ε}` estimate (Caffarelli-Cabré, *Fully nonlinear elliptic
  equations*, Ch. 7) followed by Alexandrov's theorem on the sets `G_M` of two-sided touching
  by paraboloids of opening `M`.

Given both, the conclusion is pointwise (`pegdenSmartTouching_of_steps`): at a contact point
where `u` and `v` have second-order Peano expansions with matrices `X`, `X'`, the second
symmetric differences give `½ hᵀ(X - X')h ≤ -δ|h|²` (`qM_sub_le_of_touching`), so
`-δI - (X - X')` is positive definite (`posDef_of_qM_sub_le`).
-/

noncomputable section

open MeasureTheory Filter Topology Asymptotics

namespace RandomSandpile

variable {d : ℕ}

/-! ### Step statements -/

/-- **Step (Jensen's lemma for `u - v`): the upper contact set has positive measure.** Let
`U ⊆ ℝ^d` be bounded and open, `u, v ∈ C(Ū)`, `u` a viscosity subsolution of `-Δu - K = 0`
(`Δu ≥ -K`) and `v` a viscosity supersolution of `-Δv + K = 0` (`Δv ≤ K`) in `U`
(Crandall-Ishii-Lions). If `u - v ≤ m` on `∂U` and `u - v > m` somewhere in `U`, then for some
`δ > 0` the set of `a ∈ U` with `u(a) - v(a) > m` at which `u - v` is touched from above on `U`
by a concave paraboloid `x ↦ (u - v)(a) + p·(x - a) - δ|x - a|²` has positive (outer)
Lebesgue measure. Proof route: sup- and inf-convolutions and `AlexandrovStmt` (module docstring). -/
def ContactSetPositiveStmt : Prop :=
  ∀ (d : ℕ) (U : Set (Rd d)), IsOpen U → Bornology.IsBounded U →
    ∀ (K : ℝ) (u v : Rd d → ℝ), ContinuousOn u (closure U) → ContinuousOn v (closure U) →
      ViscFromAboveGE (fun X => X.trace + K) U u → ViscFromBelowLE (fun X => X.trace - K) U v →
      ∀ m : ℝ, (∀ x ∈ frontier U, u x - v x ≤ m) → (∃ x ∈ U, m < u x - v x) →
        ∃ δ : ℝ, 0 < δ ∧ 0 < volume {a : Rd d | a ∈ U ∧ m < u a - v a ∧
          ∃ p : Rd d, ∀ x ∈ U, u x - v x ≤ u a - v a + inner ℝ p (x - a) - δ * ‖x - a‖ ^ 2}

/-- **Step (a.e. second-order differentiability of functions with bounded Laplacian).** If `u`
is continuous on the open set `U` and `|Δu| ≤ K` in `U` in the viscosity sense (`u` is a
viscosity subsolution of `-Δu - K = 0` and a viscosity supersolution of `-Δu + K = 0`), then
`u` has a second-order Peano expansion with a symmetric matrix at almost every point of `U`.

Not a consequence of `AlexandrovStmt` (see the module docstring). Sources: A. P. Calderón,
A. Zygmund, *Local properties of solutions of elliptic partial differential equations*, Studia
Math. 20 (1961) 171-225 (`W^{2,p}` functions, `p > d/2`, are twice differentiable a.e.) with the
Calderón-Zygmund `W^{2,p}` estimates; or L. Caffarelli, X. Cabré, *Fully nonlinear elliptic
equations*, AMS Colloq. Publ. 43 (1995), Ch. 7 (`W^{2,δ}` estimate: the set where `u` is not
touched from both sides by paraboloids of opening `M` has measure `≤ C M^{-δ}`), followed by
Alexandrov's theorem applied on those sets. -/
def BoundedLaplacianPeanoAEStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ U : Set (Rd d), IsOpen U → ∀ (K : ℝ) (u : Rd d → ℝ), ContinuousOn u U →
    ViscFromAboveGE (fun X => X.trace + K) U u → ViscFromBelowLE (fun X => X.trace - K) U u →
      volume {a : Rd d | a ∈ U ∧ ¬ PeanoTwiceDifferentiableAt u a} = 0

/-! ### Second-order condition at a touching point -/

theorem qM_smul (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (h : Rd d) :
    qM M (t • h) = t ^ 2 * qM M h := by
  simp only [qM, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

/-- From `∀ ε > 0, A ≤ ε c` with `c ≥ 0`, `A ≤ 0`. -/
theorem nonpos_of_forall_pos_le_mul {A c : ℝ} (hc : 0 ≤ c) (h : ∀ ε > 0, A ≤ ε * c) : A ≤ 0 := by
  by_contra hA
  push Not at hA
  have h1 := h (A / (2 * (c + 1))) (by positivity)
  have h2 : A / (2 * (c + 1)) * c < A := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Second-order condition at a touching point (second symmetric differences).** If `u` and
`v` have second-order Peano expansions at `a ∈ U` with matrices `X`, `X'`, and `u - v` is touched
from above on the open set `U` at `a` by `x ↦ (u - v)(a) + p₀·(x - a) - δ|x - a|²`, then
`½ hᵀ(X - X')h ≤ -δ|h|²` for every `h`. -/
theorem qM_sub_le_of_touching {U : Set (Rd d)} (hU : IsOpen U) {u v : Rd d → ℝ}
    {a p p' p₀ : Rd d} {X X' : Matrix (Fin d) (Fin d) ℝ} {δ : ℝ} (ha : a ∈ U)
    (hu : HasSecondOrderTaylorAt u a p X) (hv : HasSecondOrderTaylorAt v a p' X')
    (hc : ∀ x ∈ U, u x - v x ≤ u a - v a + inner ℝ p₀ (x - a) - δ * ‖x - a‖ ^ 2) (h : Rd d) :
    qM X h - qM X' h ≤ -δ * ‖h‖ ^ 2 := by
  have key : ∀ ε > 0, qM X h - qM X' h + δ * ‖h‖ ^ 2 ≤ ε * ‖h‖ ^ 2 := by
    intro ε hε
    have hR := (hu.sub hv).def hε
    have hU' : ∀ᶠ x in 𝓝 a, x ∈ U := hU.mem_nhds ha
    have hT : Tendsto (fun t : ℝ => a + t • h) (𝓝 0) (𝓝 a) := by
      have : Continuous (fun t : ℝ => a + t • h) := by fun_prop
      simpa using this.tendsto 0
    have hT' : Tendsto (fun t : ℝ => a + (-t) • h) (𝓝 0) (𝓝 a) := by
      have : Continuous (fun t : ℝ => a + (-t) • h) := by fun_prop
      simpa using this.tendsto 0
    have hev := (hT.eventually (hR.and hU')).and (hT'.eventually (hR.and hU'))
    obtain ⟨t, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ht⟩ :=
      ((hev.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
    have ht0 : (0 : ℝ) < t := ht
    have c1 := hc _ h2
    have c2 := hc _ h4
    simp only [add_sub_cancel_left, qM_smul, inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, norm_pow, norm_mul, neg_sq, neg_mul] at h1 h3 c1 c2
    have e1 := (abs_le.mp h1).1
    have e3 := (abs_le.mp h3).1
    have hsum : t ^ 2 * (qM X h - qM X' h + δ * ‖h‖ ^ 2) ≤ t ^ 2 * (ε * ‖h‖ ^ 2) := by
      nlinarith
    exact le_of_mul_le_mul_left hsum (by positivity)
  have := nonpos_of_forall_pos_le_mul (sq_nonneg ‖h‖) key
  linarith

/-- `-δI - (X - X')` is positive definite when `½ hᵀ(X - X')h ≤ -δ|h|²` and `δ > 0`. -/
theorem posDef_of_qM_sub_le {X X' : Matrix (Fin d) (Fin d) ℝ} (hX : X.IsSymm) (hX' : X'.IsSymm)
    {δ : ℝ} (hδ : 0 < δ) (hq : ∀ h : Rd d, qM X h - qM X' h ≤ -δ * ‖h‖ ^ 2) :
    (-(δ • (1 : Matrix (Fin d) (Fin d) ℝ)) - (X - X')).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hX.eq, hX'.eq]
  · intro x hx
    have hq' := hq (WithLp.toLp 2 x)
    have hn : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [dotProduct, sq]
    have hpos : 0 < ‖WithLp.toLp 2 x‖ := by
      rw [norm_pos_iff]
      intro h0
      exact hx (by simpa using congrArg WithLp.ofLp h0)
    have hpos2 : 0 < x ⬝ᵥ x := by rw [← hn]; positivity
    simp only [qM] at hq'
    rw [hn] at hq'
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    nlinarith

/-! ### The reduction -/

/-- ** Prop 2.5 from its steps.** `ContactSetPositiveStmt` is to be proved from
`AlexandrovStmt` through sup-convolutions; `BoundedLaplacianPeanoAEStmt` is the regularity input
that Alexandrov's theorem does not provide. -/
theorem pegdenSmartTouching_of_steps (hC : ContactSetPositiveStmt)
    (hR : BoundedLaplacianPeanoAEStmt) : PegdenSmartTouchingStmt := by
  intro d hd U hU hUb K u v hu hv hu1 hu2 hv1 hv2 m hm hpos
  obtain ⟨δ, hδ, hvol⟩ := hC d U hU hUb K u v hu hv hu1 hv2 m hm hpos
  have hNu := hR d hd U hU K u (hu.mono subset_closure) hu1 hu2
  have hNv := hR d hd U hU K v (hv.mono subset_closure) hv1 hv2
  refine lt_of_lt_of_le hvol (measure_mono_ae ?_)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNu, measure_eq_zero_iff_ae_notMem.mp hNv]
    with a ha1 ha2
  rintro ⟨haU, ham, p₀, hc⟩
  have hdu : PeanoTwiceDifferentiableAt u a := by
    by_contra h0; exact ha1 ⟨haU, h0⟩
  have hdv : PeanoTwiceDifferentiableAt v a := by
    by_contra h0; exact ha2 ⟨haU, h0⟩
  obtain ⟨p, X, hX, hpX⟩ := hdu
  obtain ⟨p', X', hX', hpX'⟩ := hdv
  exact ⟨haU, ham, p, p', X, X', hX, hX', hpX, hpX', δ, hδ,
    posDef_of_qM_sub_le hX hX' hδ (qM_sub_le_of_touching hU haU hpX hpX' hc)⟩

end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceD2Planar

/-!
# Theorem 9.2 in dimension two: the equation-quadratic loop and Theorem 4.1

SIMPLE-PROOF §4. For `H > 0` with `F(H) = 0`, `z₀ = Z_H`, `b > 0`, the loop
`H_θ = A_{z₀ + b e_θ} + ½ f(z₀ + b e_θ) I` (`loopMat`) consists of positive definite solutions of
`F = 0`; `H - H_θ` is positive on `v_θ = (-sin(θ/2), cos(θ/2))` and negative on
`w_θ = (cos(θ/2), sin(θ/2))`, and `v_{θ + 2π} = -v_θ`. `planarExclusion_of_steps` proves
`PlanarExclusionStmt` (Theorem 4.1) from (C2),.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

/-! ### Vectors and trigonometry -/

/-- `x e₀ + y e₁`. -/
def vec2 (x y : ℝ) : Rd 2 := x • EuclideanSpace.single 0 1 + y • EuclideanSpace.single 1 1

theorem vec2_apply (x y : ℝ) : vec2 x y 0 = x ∧ vec2 x y 1 = y := by
  simp [vec2]

theorem continuous_vec2 {α : Type*} [TopologicalSpace α] {x y : α → ℝ} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun q => vec2 (x q) (y q) := by
  unfold vec2; fun_prop

theorem cos_eq_half (θ : ℝ) : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

theorem sin_eq_half (θ : ℝ) : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
  have h := Real.sin_two_mul (θ / 2)
  rwa [show 2 * (θ / 2) = θ by ring] at h

/-- `q_M(x)` in coordinates. -/
theorem qM_two (M : Matrix (Fin 2) (Fin 2) ℝ) (x : Rd 2) :
    qM M x = (x 0 * (M 0 0 * x 0 + M 0 1 * x 1) + x 1 * (M 1 0 * x 0 + M 1 1 * x 1)) / 2 := by
  simp only [qM, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem qM_traceFreeMat (z x : Rd 2) :
    qM (traceFreeMat z) x = (z 0 * (x 0 ^ 2 - x 1 ^ 2) + z 1 * (2 * x 0 * x 1)) / 4 := by
  obtain ⟨h00, h01, h10, h11⟩ := traceFreeMat_apply z
  rw [qM_two, h00, h01, h10, h11]
  ring

/-- `v_θ = (-sin(θ/2), cos(θ/2))`. -/
def vVec (θ : ℝ) : Rd 2 := vec2 (-Real.sin (θ / 2)) (Real.cos (θ / 2))

/-- `w_θ = (cos(θ/2), sin(θ/2))`. -/
def wVec (θ : ℝ) : Rd 2 := vec2 (Real.cos (θ / 2)) (Real.sin (θ / 2))

theorem norm_vVec (θ : ℝ) : ‖vVec θ‖ = 1 := by
  obtain ⟨e0, e1⟩ := vec2_apply (-Real.sin (θ / 2)) (Real.cos (θ / 2))
  have h := norm_sq_two (vec2 (-Real.sin (θ / 2)) (Real.cos (θ / 2)))
  rw [e0, e1, neg_sq, Real.sin_sq_add_cos_sq] at h
  unfold vVec
  nlinarith [norm_nonneg (vec2 (-Real.sin (θ / 2)) (Real.cos (θ / 2)))]

theorem norm_wVec (θ : ℝ) : ‖wVec θ‖ = 1 := by
  obtain ⟨e0, e1⟩ := vec2_apply (Real.cos (θ / 2)) (Real.sin (θ / 2))
  have h := norm_sq_two (vec2 (Real.cos (θ / 2)) (Real.sin (θ / 2)))
  rw [e0, e1, Real.cos_sq_add_sin_sq] at h
  unfold wVec
  nlinarith [norm_nonneg (vec2 (Real.cos (θ / 2)) (Real.sin (θ / 2)))]

theorem norm_vec2_cos_sin (θ : ℝ) : ‖vec2 (Real.cos θ) (Real.sin θ)‖ = 1 := by
  obtain ⟨e0, e1⟩ := vec2_apply (Real.cos θ) (Real.sin θ)
  have h := norm_sq_two (vec2 (Real.cos θ) (Real.sin θ))
  rw [e0, e1, Real.cos_sq_add_sin_sq] at h
  nlinarith [norm_nonneg (vec2 (Real.cos θ) (Real.sin θ))]

theorem vVec_add_two_pi (θ : ℝ) : vVec (θ + 2 * Real.pi) = -vVec θ := by
  have e : (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi := by ring
  unfold vVec vec2
  simp only [e, Real.sin_add_pi, Real.cos_add_pi, neg_neg, neg_smul, neg_add]

theorem linearIndependent_vVec_wVec (θ : ℝ) : LinearIndependent ℝ ![vVec θ, wVec θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrArg (fun x : Rd 2 => x 0) hst
  have h1 := congrArg (fun x : Rd 2 => x 1) hst
  obtain ⟨v0, v1⟩ := vec2_apply (-Real.sin (θ / 2)) (Real.cos (θ / 2))
  obtain ⟨w0, w1⟩ := vec2_apply (Real.cos (θ / 2)) (Real.sin (θ / 2))
  simp only [vVec, wVec, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, v0, v1, w0, w1,
    PiLp.zero_apply] at h0 h1
  have hS := Real.sin_sq_add_cos_sq (θ / 2)
  constructor
  · linear_combination (-Real.sin (θ / 2)) * h0 + Real.cos (θ / 2) * h1 - s * hS
  · linear_combination Real.cos (θ / 2) * h0 + Real.sin (θ / 2) * h1 - t * hS

/-- `|cos θ (h₀² - h₁²) + sin θ (2h₀h₁)| ≤ h₀² + h₁²`. -/
theorem abs_rot_le (θ : ℝ) (h : Rd 2) :
    |Real.cos θ * (h 0 ^ 2 - h 1 ^ 2) + Real.sin θ * (2 * h 0 * h 1)| ≤ h 0 ^ 2 + h 1 ^ 2 := by
  have hcs := Real.cos_sq_add_sin_sq θ
  have hsq : (Real.cos θ * (h 0 ^ 2 - h 1 ^ 2) + Real.sin θ * (2 * h 0 * h 1)) ^ 2 ≤
      (h 0 ^ 2 + h 1 ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (Real.cos θ * (2 * h 0 * h 1) - Real.sin θ * (h 0 ^ 2 - h 1 ^ 2))]
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (by positivity))

/-! ### The loop of matrices -/

/-- `H_θ = A_{z₀ + b e_θ} + ½ f(z₀ + b e_θ) I`, `e_θ = (cos θ, sin θ)`. -/
def loopMat (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (z₀ : Rd 2) (b θ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  traceFreeMat (z₀ + b • vec2 (Real.cos θ) (Real.sin θ)) +
    (traceGraph F (z₀ + b • vec2 (Real.cos θ) (Real.sin θ)) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The equation quadratics `Q_θ(x) = u(a) + p·(x - a) + ½(x - a)ᵀH_θ(x - a)`. -/
def loopQ (u : Rd 2 → ℝ) (a p : Rd 2) (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (z₀ : Rd 2) (b θ : ℝ)
    (x : Rd 2) : ℝ :=
  u a + inner ℝ p (x - a) + qM (loopMat F z₀ b θ) (x - a)

theorem loopMat_isSymm (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (z₀ : Rd 2) (b θ : ℝ) :
    (loopMat F z₀ b θ).IsSymm :=
  (traceFreeMat_isSymm _).add (Matrix.isSymm_one.smul _)

theorem loopMat_eq_zero {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F) (z₀ : Rd 2)
    (b θ : ℝ) : F (loopMat F z₀ b θ) = 0 := by
  unfold loopMat
  rw [hF _ (traceFreeMat_isSymm _), traceGraph]
  ring

theorem loopQ_add_two_pi (u : Rd 2 → ℝ) (a p : Rd 2) (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (z₀ : Rd 2) (b θ : ℝ) : loopQ u a p F z₀ b (θ + 2 * Real.pi) = loopQ u a p F z₀ b θ := by
  unfold loopQ loopMat
  simp only [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem loopQ_self (u : Rd 2 → ℝ) (a p : Rd 2) (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (z₀ : Rd 2)
    (b θ : ℝ) : loopQ u a p F z₀ b θ a = u a := by
  simp [loopQ, qM]

/-- `q_H(h) - q_{H_θ}(h)` in coordinates, for `H = A_{z₀} + ½ f(z₀) I`. -/
theorem qM_sub_loopMat (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (z₀ : Rd 2) (b θ : ℝ) (h : Rd 2) :
    qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h -
        qM (loopMat F z₀ b θ) h =
      -(b / 4) * (Real.cos θ * (h 0 ^ 2 - h 1 ^ 2) + Real.sin θ * (2 * h 0 * h 1)) +
        (traceGraph F z₀ - traceGraph F (z₀ + b • vec2 (Real.cos θ) (Real.sin θ))) / 4 *
          (h 0 ^ 2 + h 1 ^ 2) := by
  obtain ⟨e0, e1⟩ := vec2_apply (Real.cos θ) (Real.sin θ)
  unfold loopMat
  rw [qM_add_smul_one, qM_add_smul_one, qM_traceFreeMat, qM_traceFreeMat, norm_sq_two]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, e0, e1]
  ring

theorem qM_sub_loopMat_v (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (z₀ : Rd 2) (b θ t : ℝ) :
    qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (t • vVec θ) -
        qM (loopMat F z₀ b θ) (t • vVec θ) =
      t ^ 2 * (b / 4 + (traceGraph F z₀ -
        traceGraph F (z₀ + b • vec2 (Real.cos θ) (Real.sin θ))) / 4) := by
  obtain ⟨e0, e1⟩ := vec2_apply (-Real.sin (θ / 2)) (Real.cos (θ / 2))
  rw [qM_sub_loopMat]
  simp only [vVec, PiLp.smul_apply, smul_eq_mul, e0, e1]
  have hS := Real.sin_sq_add_cos_sq (θ / 2)
  have hc := cos_eq_half θ
  have hs := sin_eq_half θ
  linear_combination (-(b / 4) * t ^ 2 * (Real.sin (θ / 2) ^ 2 - Real.cos (θ / 2) ^ 2)) * hc +
    (b / 2 * t ^ 2 * Real.sin (θ / 2) * Real.cos (θ / 2)) * hs +
    (b / 4 * t ^ 2 * (Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 + 1) +
      (traceGraph F z₀ - traceGraph F (z₀ + b • vec2 (Real.cos θ) (Real.sin θ))) / 4 * t ^ 2) * hS

theorem qM_sub_loopMat_w (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (z₀ : Rd 2) (b θ t : ℝ) :
    qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (t • wVec θ) -
        qM (loopMat F z₀ b θ) (t • wVec θ) =
      t ^ 2 * (-(b / 4) + (traceGraph F z₀ -
        traceGraph F (z₀ + b • vec2 (Real.cos θ) (Real.sin θ))) / 4) := by
  obtain ⟨e0, e1⟩ := vec2_apply (Real.cos (θ / 2)) (Real.sin (θ / 2))
  rw [qM_sub_loopMat]
  simp only [wVec, PiLp.smul_apply, smul_eq_mul, e0, e1]
  have hS := Real.sin_sq_add_cos_sq (θ / 2)
  have hc := cos_eq_half θ
  have hs := sin_eq_half θ
  linear_combination (-(b / 4) * t ^ 2 * (Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2)) * hc +
    (-(b / 2) * t ^ 2 * Real.sin (θ / 2) * Real.cos (θ / 2)) * hs +
    (-(b / 4) * t ^ 2 * (Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 + 1) +
      (traceGraph F z₀ - traceGraph F (z₀ + b • vec2 (Real.cos θ) (Real.sin θ))) / 4 * t ^ 2) * hS

/-- The loop matrices are positive definite when `b = c₀`, `q_H ≥ c₀|·|²`, `Lip f ≤ k' < 1`. -/
theorem loopMat_posDef {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {z₀ : Rd 2} {c₀ k' : ℝ} (hc₀ : 0 < c₀)
    (hk'1 : k' < 1)
    (hc₀q : ∀ h : Rd 2, c₀ * ‖h‖ ^ 2 ≤
      qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h)
    (θ : ℝ) (hgap : |traceGraph F z₀ -
      traceGraph F (z₀ + c₀ • vec2 (Real.cos θ) (Real.sin θ))| ≤ k' * c₀) :
    (loopMat F z₀ c₀ θ).PosDef := by
  refine posDef_of_qM_ge (loopMat_isSymm F z₀ c₀ θ) (half_pos hc₀) fun h => ?_
  have e := qM_sub_loopMat F z₀ c₀ θ h
  have h1 := hc₀q h
  have h2 := abs_rot_le θ h
  have hn := norm_sq_two h
  have hpos : 0 ≤ h 0 ^ 2 + h 1 ^ 2 := by positivity
  rw [hn] at h1 ⊢
  have h4 := mul_le_mul_of_nonneg_left (abs_le.1 h2).1 (by linarith : (0 : ℝ) ≤ c₀ / 4)
  have h5 := mul_le_mul_of_nonneg_right (abs_le.1 hgap).2 hpos
  have hkc : k' * c₀ ≤ c₀ := by nlinarith
  have h6 := mul_le_mul_of_nonneg_right hkc hpos
  linarith

/-! ### Rays -/

/-- One ray: if `q_H(h) - q_{H_θ}(h) = t² D` with `|h| = t < ρ`, then
`|u(a + h) - Q_θ(a + h) - t² D| ≤ κ t²`. -/
theorem loop_ray_core {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {u : Rd 2 → ℝ} {a p z₀ : Rd 2}
    {c₀ κ ρ θ t D : ℝ}
    (hT : ∀ h : Rd 2, ‖h‖ < ρ → |u (a + h) - u a - inner ℝ p h -
      qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h| ≤
        κ * ‖h‖ ^ 2)
    (h : Rd 2) (hn : ‖h‖ = t) (htρ : t < ρ)
    (hD : qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h -
      qM (loopMat F z₀ c₀ θ) h = t ^ 2 * D) :
    |u (a + h) - loopQ u a p F z₀ c₀ θ (a + h) - t ^ 2 * D| ≤ κ * t ^ 2 := by
  have h1 := hT h (by rw [hn]; exact htρ)
  rw [hn] at h1
  have e : u (a + h) - loopQ u a p F z₀ c₀ θ (a + h) - t ^ 2 * D =
      u (a + h) - u a - inner ℝ p h -
        qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h := by
    simp only [loopQ, add_sub_cancel_left]
    linarith [hD]
  rwa [e]

theorem loop_rays {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {u : Rd 2 → ℝ} {a p z₀ : Rd 2}
    {c₀ k' ρ θ t : ℝ} (hk'1 : k' < 1) (hc₀ : 0 < c₀)
    (hT : ∀ h : Rd 2, ‖h‖ < ρ → |u (a + h) - u a - inner ℝ p h -
      qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h| ≤
        (1 - k') * c₀ / 8 * ‖h‖ ^ 2)
    (hgap : |traceGraph F z₀ -
      traceGraph F (z₀ + c₀ • vec2 (Real.cos θ) (Real.sin θ))| ≤ k' * c₀)
    (ht : 0 < t) (htρ : t < ρ) :
    loopQ u a p F z₀ c₀ θ (a + t • vVec θ) < u (a + t • vVec θ) ∧
      loopQ u a p F z₀ c₀ θ (a - t • vVec θ) < u (a - t • vVec θ) ∧
      u (a + t • wVec θ) < loopQ u a p F z₀ c₀ θ (a + t • wVec θ) ∧
      u (a - t • wVec θ) < loopQ u a p F z₀ c₀ θ (a - t • wVec θ) := by
  set Fd := traceGraph F z₀ - traceGraph F (z₀ + c₀ • vec2 (Real.cos θ) (Real.sin θ)) with hFd
  have hFl := (abs_le.1 hgap).1
  have hFr := (abs_le.1 hgap).2
  have ht2 : 0 < t ^ 2 := by positivity
  have hk2 : 0 < (1 - k') * c₀ := mul_pos (by linarith) hc₀
  have hm1 := mul_le_mul_of_nonneg_left hFl ht2.le
  have hm2 := mul_le_mul_of_nonneg_left hFr ht2.le
  have hκt := mul_pos (by positivity : (0 : ℝ) < (1 - k') * c₀ / 8) ht2
  have hnv : ∀ s : ℝ, |s| = t → ‖s • vVec θ‖ = t := fun s hs => by
    rw [norm_smul, norm_vVec, mul_one, Real.norm_eq_abs, hs]
  have hnw : ∀ s : ℝ, |s| = t → ‖s • wVec θ‖ = t := fun s hs => by
    rw [norm_smul, norm_wVec, mul_one, Real.norm_eq_abs, hs]
  have hvs : ∀ s : ℝ, |s| = t → qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) (s • vVec θ) - qM (loopMat F z₀ c₀ θ) (s • vVec θ) =
        t ^ 2 * (c₀ / 4 + Fd / 4) := fun s hs => by
    rw [qM_sub_loopMat_v, ← sq_abs s, hs]
  have hws : ∀ s : ℝ, |s| = t → qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) (s • wVec θ) - qM (loopMat F z₀ c₀ θ) (s • wVec θ) =
        t ^ 2 * (-(c₀ / 4) + Fd / 4) := fun s hs => by
    rw [qM_sub_loopMat_w, ← sq_abs s, hs]
  have hp : |t| = t := abs_of_pos ht
  have hm : |-t| = t := by rw [abs_neg, abs_of_pos ht]
  have d1 := loop_ray_core hT _ (hnv t hp) htρ (hvs t hp)
  have d2 := loop_ray_core hT _ (hnv (-t) hm) htρ (hvs (-t) hm)
  have d3 := loop_ray_core hT _ (hnw t hp) htρ (hws t hp)
  have d4 := loop_ray_core hT _ (hnw (-t) hm) htρ (hws (-t) hm)
  have e1 : a - t • vVec θ = a + (-t) • vVec θ := by rw [neg_smul, sub_eq_add_neg]
  have e2 : a - t • wVec θ = a + (-t) • wVec θ := by rw [neg_smul, sub_eq_add_neg]
  rw [e1, e2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [(abs_le.1 d1).1]
  · linarith [(abs_le.1 d2).1]
  · linarith [(abs_le.1 d3).2]
  · linarith [(abs_le.1 d4).2]

/-! ### The label dichotomy and its openness -/

/-- For each parameter, exactly one of `a ± r v_θ` lies in the source component (C2, C3). -/
theorem loop_label (hC2 : ComponentBoundStmt) (hC3 : AlternatingRaysStmt)
    {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hshift : HasTraceShift F) (hdeg : DegenerateElliptic F)
    {u : Rd 2 → ℝ} (hu : IsSourceProfile F u) {a p z₀ : Rd 2} (ha : a ≠ 0) {c₀ r θ : ℝ}
    (hpd : (loopMat F z₀ c₀ θ).PosDef) (hr0 : 0 < r)
    (hrays : ∀ t : ℝ, 0 < t → t ≤ r →
      loopQ u a p F z₀ c₀ θ (a + t • vVec θ) < u (a + t • vVec θ) ∧
      loopQ u a p F z₀ c₀ θ (a - t • vVec θ) < u (a - t • vVec θ) ∧
      u (a + t • wVec θ) < loopQ u a p F z₀ c₀ θ (a + t • wVec θ) ∧
      u (a - t • wVec θ) < loopQ u a p F z₀ c₀ θ (a - t • wVec θ))
    (hoff : ∀ t : ℝ, 0 < t → t ≤ r → a + t • vVec θ ≠ 0 ∧ a - t • vVec θ ≠ 0 ∧
      a + t • wVec θ ≠ 0 ∧ a - t • wVec θ ≠ 0) :
    (a + r • vVec θ ∈ connectedComponentIn (posSet u (loopQ u a p F z₀ c₀ θ)) 0 ↔
      a - r • vVec θ ∉ connectedComponentIn (posSet u (loopQ u a p F z₀ c₀ θ)) 0) := by
  have hC := hC2 F hshift hdeg u hu (u a) p a _ (loopMat_isSymm F z₀ c₀ θ) hpd
    (loopMat_eq_zero hshift z₀ c₀ θ)
  have hneg : IsPreconnected (negSet u (loopQ u a p F z₀ c₀ θ)) := hC.1
  have hcomp : ∀ x ∈ posSet u (loopQ u a p F z₀ c₀ θ), ∀ y ∈ posSet u (loopQ u a p F z₀ c₀ θ),
      x ∉ connectedComponentIn (posSet u (loopQ u a p F z₀ c₀ θ)) 0 →
      y ∉ connectedComponentIn (posSet u (loopQ u a p F z₀ c₀ θ)) 0 →
      y ∈ connectedComponentIn (posSet u (loopQ u a p F z₀ c₀ θ)) x := hC.2
  have hQc : Continuous (loopQ u a p F z₀ c₀ θ) := by
    have hc : Continuous fun x : Rd 2 => qM (loopMat F z₀ c₀ θ) (x - a) :=
      (contDiff_qM _ (n := 0)).continuous.comp (continuous_id.sub continuous_const)
    unfold loopQ
    fun_prop
  have hsep := hC3 (posSet u (loopQ u a p F z₀ c₀ θ)) (negSet u (loopQ u a p F z₀ c₀ θ)) a
    (vVec θ) (wVec θ) r (isOpen_posSet hu.continuousOn hu.tendsto_atTop hQc)
    (isOpen_negSet hu.continuousOn hQc)
    (Set.disjoint_left.2 fun x hxP hxN => by
      rcases hxP with hxP | hxP
      · exact absurd hxN.2 (not_lt.2 hxP.2.le)
      · exact hxN.1 hxP)
    hneg
    (fun haP => by
      rcases haP with haP | haP
      · have h2 := haP.2
        rw [loopQ_self] at h2
        exact lt_irrefl _ h2
      · exact ha haP)
    (fun haN => by
      have h2 := haN.2
      rw [loopQ_self] at h2
      exact lt_irrefl _ h2)
    (linearIndependent_vVec_wVec θ) hr0
    (fun t ht htr => by
      obtain ⟨r1, r2, r3, r4⟩ := hrays t ht htr
      obtain ⟨o1, o2, o3, o4⟩ := hoff t ht htr
      exact ⟨Or.inl ⟨o1, r1⟩, Or.inl ⟨o2, r2⟩, ⟨o3, r3⟩, ⟨o4, r4⟩⟩)
  obtain ⟨r1, r2, -, -⟩ := hrays r hr0 le_rfl
  obtain ⟨o1, o2, -, -⟩ := hoff r hr0 le_rfl
  constructor
  · intro hplus hminus
    apply hsep
    rw [← connectedComponentIn_eq hplus]
    exact hminus
  · intro hminus
    by_contra hplus
    exact hsep (hcomp _ (Or.inl ⟨o1, r1⟩) _ (Or.inl ⟨o2, r2⟩) hplus hminus)

theorem loopMat_apply (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (z₀ : Rd 2) (b θ : ℝ) :
    loopMat F z₀ b θ 0 0 = (z₀ 0 + b * Real.cos θ) / 2 +
        traceGraph F (z₀ + b • vec2 (Real.cos θ) (Real.sin θ)) / 2 ∧
      loopMat F z₀ b θ 0 1 = (z₀ 1 + b * Real.sin θ) / 2 ∧
      loopMat F z₀ b θ 1 0 = (z₀ 1 + b * Real.sin θ) / 2 ∧
      loopMat F z₀ b θ 1 1 = -(z₀ 0 + b * Real.cos θ) / 2 +
        traceGraph F (z₀ + b • vec2 (Real.cos θ) (Real.sin θ)) / 2 := by
  obtain ⟨h00, h01, h10, h11⟩ := traceFreeMat_apply (z₀ + b • vec2 (Real.cos θ) (Real.sin θ))
  obtain ⟨e0, e1⟩ := vec2_apply (Real.cos θ) (Real.sin θ)
  simp only [loopMat, Matrix.add_apply, Matrix.smul_apply, h00, h01, h10, h11,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, PiLp.add_apply,
    PiLp.smul_apply, e0, e1]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- Joint continuity of `(θ, x) ↦ Q_θ(x)`. -/
theorem continuous_loopQ {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hfc : Continuous (traceGraph F))
    (u : Rd 2 → ℝ) (a p z₀ : Rd 2) (b : ℝ) :
    Continuous fun q : ℝ × Rd 2 => loopQ u a p F z₀ b q.1 q.2 := by
  have hv : Continuous fun q : ℝ × Rd 2 => vec2 (Real.cos q.1) (Real.sin q.1) :=
    continuous_vec2 (by fun_prop) (by fun_prop)
  have hz : Continuous fun q : ℝ × Rd 2 => z₀ + b • vec2 (Real.cos q.1) (Real.sin q.1) := by
    fun_prop
  have hfz : Continuous fun q : ℝ × Rd 2 =>
      traceGraph F (z₀ + b • vec2 (Real.cos q.1) (Real.sin q.1)) := hfc.comp hz
  have x0 : Continuous fun q : ℝ × Rd 2 => (q.2 - a) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp
      (continuous_snd.sub continuous_const)
  have x1 : Continuous fun q : ℝ × Rd 2 => (q.2 - a) 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.comp
      (continuous_snd.sub continuous_const)
  have hin : Continuous fun q : ℝ × Rd 2 => inner ℝ p (q.2 - a) :=
    continuous_const.inner (continuous_snd.sub continuous_const)
  have e : (fun q : ℝ × Rd 2 => loopQ u a p F z₀ b q.1 q.2) = fun q =>
      u a + inner ℝ p (q.2 - a) +
        ((q.2 - a) 0 * (((z₀ 0 + b * Real.cos q.1) / 2 +
            traceGraph F (z₀ + b • vec2 (Real.cos q.1) (Real.sin q.1)) / 2) * (q.2 - a) 0 +
          (z₀ 1 + b * Real.sin q.1) / 2 * (q.2 - a) 1) +
        (q.2 - a) 1 * ((z₀ 1 + b * Real.sin q.1) / 2 * (q.2 - a) 0 +
          (-(z₀ 0 + b * Real.cos q.1) / 2 +
            traceGraph F (z₀ + b • vec2 (Real.cos q.1) (Real.sin q.1)) / 2) * (q.2 - a) 1)) / 2 := by
    funext q
    obtain ⟨m00, m01, m10, m11⟩ := loopMat_apply F z₀ b q.1
    rw [loopQ, qM_two, m00, m01, m10, m11]
  rw [e]
  fun_prop

/-! ### Theorem 4.1 -/

/-- **(C5) SIMPLE-PROOF Theorem 4.1 (abstract planar exclusion)** from (C2),. -/
theorem planarExclusion_of_steps (hC2 : ComponentBoundStmt) (hC3 : AlternatingRaysStmt)
    (hC4 : SourceLabelOpenStmt) : PlanarExclusionStmt := by
  intro F hshift hdeg k hk hlip u hu a ha hua p H hHs hT hHpd
  have hFH : F H = 0 := eq_zero_of_taylor_of_profile hshift hu ha hua hHs hT
  obtain ⟨k', hk'⟩ : ∃ k' : ℝ, k' = max k 0 := ⟨_, rfl⟩
  have hk'1 : k' < 1 := by rw [hk']; exact max_lt hk one_pos
  have hlip' : ∀ z z' : Rd 2, |traceGraph F z - traceGraph F z'| ≤ k' * ‖z - z'‖ := fun z z' =>
    (hlip z z').trans (mul_le_mul_of_nonneg_right (by rw [hk']; exact le_max_left _ _)
      (norm_nonneg _))
  have hfc : Continuous (traceGraph F) := by
    refine (LipschitzWith.of_dist_le_mul fun z z' => ?_).continuous (K := 1)
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    exact traceGraph_lipschitz hshift hdeg z z'
  obtain ⟨c₀, hc₀, hc₀q⟩ := exists_qM_ge_of_posDef hHpd
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Rd 2, z₀ = traceFreeCoord H := ⟨_, rfl⟩
  have htrH : H.trace = traceGraph F z₀ := by
    have := eq_traceGraph_sub_trace hshift hHs
    rw [hFH, ← hz₀] at this
    linarith
  have hHdec : H = traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    conv_lhs => rw [eq_traceFreeMat_add hHs]
    rw [← hz₀, htrH]
  rw [hHdec] at hc₀q hT
  have hgapF : ∀ θ : ℝ, |traceGraph F z₀ -
      traceGraph F (z₀ + c₀ • vec2 (Real.cos θ) (Real.sin θ))| ≤ k' * c₀ := by
    intro θ
    have h := hlip' z₀ (z₀ + c₀ • vec2 (Real.cos θ) (Real.sin θ))
    rwa [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hc₀,
      norm_vec2_cos_sin, mul_one] at h
  have hκ : 0 < (1 - k') * c₀ / 8 := by
    have : 0 < 1 - k' := by linarith
    positivity
  obtain ⟨ρ, hρ, hρT⟩ := hT.bound hκ
  have hT' : ∀ h : Rd 2, ‖h‖ < ρ → |u (a + h) - u a - inner ℝ p h -
      qM (traceFreeMat z₀ + (traceGraph F z₀ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h| ≤
        (1 - k') * c₀ / 8 * ‖h‖ ^ 2 := fun h hh => by
    have := hρT (a + h) (by rwa [add_sub_cancel_left])
    rwa [add_sub_cancel_left] at this
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (ρ / 2) (‖a‖ / 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_min (half_pos hρ) (half_pos hna)
  have hrρ : r < ρ := by rw [hr]; linarith [min_le_left (ρ / 2) (‖a‖ / 2)]
  have hra : r < ‖a‖ := by rw [hr]; linarith [min_le_right (ρ / 2) (‖a‖ / 2)]
  have hoff1 : ∀ (t : ℝ) (y : Rd 2), 0 ≤ t → t ≤ r → ‖y‖ = 1 → a + t • y ≠ 0 ∧ a - t • y ≠ 0 := by
    intro t y ht htr hy
    have hty : ‖t • y‖ < ‖a‖ := by
      rw [norm_smul, hy, mul_one, Real.norm_eq_abs, abs_of_nonneg ht]; linarith
    constructor
    · intro h0
      have : t • y = -a := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0
      rw [this, norm_neg] at hty; exact lt_irrefl _ hty
    · intro h0
      have : t • y = a := (sub_eq_zero.1 h0).symm
      rw [this] at hty; exact lt_irrefl _ hty
  have hrays : ∀ θ t : ℝ, 0 < t → t ≤ r →
      loopQ u a p F z₀ c₀ θ (a + t • vVec θ) < u (a + t • vVec θ) ∧
      loopQ u a p F z₀ c₀ θ (a - t • vVec θ) < u (a - t • vVec θ) ∧
      u (a + t • wVec θ) < loopQ u a p F z₀ c₀ θ (a + t • wVec θ) ∧
      u (a - t • wVec θ) < loopQ u a p F z₀ c₀ θ (a - t • wVec θ) := fun θ t ht htr =>
    loop_rays (θ := θ) hk'1 hc₀ hT' (hgapF θ) ht (lt_of_le_of_lt htr hrρ)
  have hoff : ∀ θ t : ℝ, 0 < t → t ≤ r → a + t • vVec θ ≠ 0 ∧ a - t • vVec θ ≠ 0 ∧
      a + t • wVec θ ≠ 0 ∧ a - t • wVec θ ≠ 0 := fun θ t ht htr =>
    ⟨(hoff1 t _ ht.le htr (norm_vVec θ)).1, (hoff1 t _ ht.le htr (norm_vVec θ)).2,
      (hoff1 t _ ht.le htr (norm_wVec θ)).1, (hoff1 t _ ht.le htr (norm_wVec θ)).2⟩
  have hlabel : ∀ θ, (a + r • vVec θ ∈ connectedComponentIn (posSet u (loopQ u a p F z₀ c₀ θ)) 0 ↔
      a - r • vVec θ ∉ connectedComponentIn (posSet u (loopQ u a p F z₀ c₀ θ)) 0) := fun θ =>
    loop_label hC2 hC3 hshift hdeg hu ha (loopMat_posDef hc₀ hk'1 hc₀q θ (hgapF θ)) hr0
      (hrays θ) (hoff θ)
  have hxv : Continuous vVec := by
    unfold vVec
    exact continuous_vec2 (by fun_prop) (by fun_prop)
  have hcp : Continuous fun θ => a + r • vVec θ := by fun_prop
  have hcm : Continuous fun θ => a - r • vVec θ := by fun_prop
  have hopenP := hC4 u hu.continuousOn hu.tendsto_atTop (loopQ u a p F z₀ c₀)
    (continuous_loopQ hfc u a p z₀ c₀) (fun θ => a + r • vVec θ) hcp
    (fun θ => ⟨(hoff θ r hr0 le_rfl).1, (hrays θ r hr0 le_rfl).1⟩)
  have hopenM := hC4 u hu.continuousOn hu.tendsto_atTop (loopQ u a p F z₀ c₀)
    (continuous_loopQ hfc u a p z₀ c₀) (fun θ => a - r • vVec θ) hcm
    (fun θ => ⟨(hoff θ r hr0 le_rfl).2.1, (hrays θ r hr0 le_rfl).2.1⟩)
  obtain ⟨S, hSdef⟩ : ∃ S : Set ℝ,
      S = {θ : ℝ | a + r • vVec θ ∈ connectedComponentIn (posSet u (loopQ u a p F z₀ c₀ θ)) 0} :=
    ⟨_, rfl⟩
  have hSc : Sᶜ =
      {θ : ℝ | a - r • vVec θ ∈ connectedComponentIn (posSet u (loopQ u a p F z₀ c₀ θ)) 0} := by
    ext θ
    rw [hSdef]
    simp only [mem_compl_iff, mem_setOf_eq]
    exact ⟨fun h => by by_contra h'; exact h ((hlabel θ).2 h'), fun h h' => (hlabel θ).1 h' h⟩
  have hclopen : IsClopen S :=
    ⟨isOpen_compl_iff.1 (hSc ▸ hopenM), by rw [hSdef]; exact hopenP⟩
  have h2π : (2 * Real.pi ∈ S) ↔ (0 : ℝ) ∉ S := by
    have e1 : a + r • vVec (0 + 2 * Real.pi) = a - r • vVec 0 := by
      rw [vVec_add_two_pi, smul_neg, sub_eq_add_neg]
    rw [hSdef]
    simp only [mem_setOf_eq]
    rw [show (2 * Real.pi) = 0 + 2 * Real.pi by ring, e1, loopQ_add_two_pi]
    exact ⟨fun h h' => (hlabel 0).1 h' h, fun h => by by_contra h'; exact h ((hlabel 0).2 h')⟩
  rcases isClopen_iff.1 hclopen with h | h
  · have h0 : (0 : ℝ) ∉ S := by rw [h]; exact fun h' => h'
    have h2 := h2π.2 h0
    rw [h] at h2
    exact h2
  · have h0 : (0 : ℝ) ∈ S := by rw [h]; exact mem_univ 0
    have h2 : 2 * Real.pi ∈ S := by rw [h]; exact mem_univ _
    exact h2π.1 h2 h0

end SingleSourceD2

end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceD2Steps

/-!
# Theorem 9.2 in dimension two: `2 × 2` algebra of the trace graph

SIMPLE-PROOF (4.1)-(4.2) and (6.1), (6.4)-(6.6).
* `eq_traceFreeMat_add`: `M = A_{Z_M} + (tr M / 2) I` for symmetric `M`;
* `eq_traceGraph_sub_trace`: `F(M) = f(Z_M) - tr M` under the shift identity;
* `traceGraph_lipschitz`: `|f(z) - f(z')| ≤ |z - z'|` for degenerate elliptic `F` with the shift;
* `regOp`: shift identity, trace graph `(1 - ε) f + ε(K + 1)`, Lipschitz constant `1 - ε`,
  degenerate ellipticity.
-/

noncomputable section

open Matrix

namespace RandomSandpile

namespace SingleSourceD2

theorem traceFreeMat_apply (z : Rd 2) :
    traceFreeMat z 0 0 = z 0 / 2 ∧ traceFreeMat z 0 1 = z 1 / 2 ∧ traceFreeMat z 1 0 = z 1 / 2 ∧
      traceFreeMat z 1 1 = -(z 0) / 2 := by
  simp [traceFreeMat]

theorem traceFreeMat_isSymm (z : Rd 2) : (traceFreeMat z).IsSymm := by
  obtain ⟨h00, h01, h10, h11⟩ := traceFreeMat_apply z
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [h01, h10]

theorem trace_traceFreeMat (z : Rd 2) : (traceFreeMat z).trace = 0 := by
  obtain ⟨h00, -, -, h11⟩ := traceFreeMat_apply z
  rw [Matrix.trace_fin_two, h00, h11]
  ring

theorem traceFreeCoord_apply (M : Matrix (Fin 2) (Fin 2) ℝ) :
    traceFreeCoord M 0 = M 0 0 - M 1 1 ∧ traceFreeCoord M 1 = 2 * M 0 1 := by
  simp [traceFreeCoord]

theorem traceFreeCoord_traceFreeMat (z : Rd 2) : traceFreeCoord (traceFreeMat z) = z := by
  obtain ⟨h00, h01, -, h11⟩ := traceFreeMat_apply z
  obtain ⟨c0, c1⟩ := traceFreeCoord_apply (traceFreeMat z)
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, c0, h00, h11]; ring
  · simp only [Fin.mk_one, c1, h01]; ring

/-- `M = A_{Z_M} + (tr M / 2) I` for symmetric `2 × 2` matrices. -/
theorem eq_traceFreeMat_add {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.IsSymm) :
    M = traceFreeMat (traceFreeCoord M) + (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨c0, c1⟩ := traceFreeCoord_apply M
  obtain ⟨h00, h01, h10, h11⟩ := traceFreeMat_apply (traceFreeCoord M)
  have hs : M 1 0 = M 0 1 := hM.apply 0 1
  rw [Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, h00, c0,
      smul_eq_mul]; ring
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.add_apply, Matrix.smul_apply, h01, c1,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul]; ring
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.add_apply, Matrix.smul_apply, h10, c1, hs,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul]; ring
  · simp only [Fin.mk_one, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, h11, c0,
      smul_eq_mul]; ring

/-- `F(M) = f(Z_M) - tr M` for symmetric `M` under the shift identity. -/
theorem eq_traceGraph_sub_trace {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.IsSymm) :
    F M = traceGraph F (traceFreeCoord M) - M.trace := by
  conv_lhs => rw [eq_traceFreeMat_add hM]
  rw [hF _ (traceFreeMat_isSymm _), traceGraph]
  ring

/-- `‖z‖² = z₀² + z₁²` on `ℝ²`. -/
theorem norm_sq_two (z : Rd 2) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs]

/-- `(A_{z'} + (|z - z'|/2) I) - A_z` is positive semidefinite. -/
theorem posSemidef_traceFreeMat_sub (z z' : Rd 2) :
    (traceFreeMat z' + (‖z - z'‖ / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - traceFreeMat z).PosSemidef := by
  obtain ⟨a00, a01, a10, a11⟩ := traceFreeMat_apply z
  obtain ⟨b00, b01, b10, b11⟩ := traceFreeMat_apply z'
  set w : Rd 2 := z - z' with hw
  have hw0 : w 0 = z 0 - z' 0 := by rw [hw]; rfl
  have hw1 : w 1 = z 1 - z' 1 := by rw [hw]; rfl
  have hn := norm_sq_two w
  have hnn : 0 ≤ ‖w‖ := norm_nonneg w
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, a01, a10, b01, b10]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), a00, a01, a10, a11, b00, b01, b10,
      b11, smul_eq_mul]
    -- `w₀(x₀² - x₁²) + 2 w₁ x₀ x₁ ≤ |w| (x₀² + x₁²)` by Cauchy-Schwarz
    have hcs : (w 0 * (x 0 ^ 2 - x 1 ^ 2) + w 1 * (2 * x 0 * x 1)) ^ 2 ≤
        (‖w‖ * (x 0 ^ 2 + x 1 ^ 2)) ^ 2 := by
      rw [mul_pow, hn]
      nlinarith [sq_nonneg (w 0 * (2 * x 0 * x 1) - w 1 * (x 0 ^ 2 - x 1 ^ 2))]
    have hle := abs_le_of_sq_le_sq' hcs (by positivity)
    rw [hw0, hw1] at hle
    nlinarith [hle.2]

/-- For a degenerate elliptic `F` with the shift identity, the trace graph is
`1`-Lipschitz. -/
theorem traceGraph_lipschitz {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    (hdeg : DegenerateElliptic F) (z z' : Rd 2) :
    |traceGraph F z - traceGraph F z'| ≤ ‖z - z'‖ := by
  have h1 := hdeg _ _ (traceFreeMat_isSymm z)
    ((traceFreeMat_isSymm z').add (Matrix.isSymm_one.smul _)) (posSemidef_traceFreeMat_sub z z')
  have h2 := hdeg _ _ (traceFreeMat_isSymm z')
    ((traceFreeMat_isSymm z).add (Matrix.isSymm_one.smul _)) (posSemidef_traceFreeMat_sub z' z)
  rw [hF _ (traceFreeMat_isSymm z')] at h1
  rw [hF _ (traceFreeMat_isSymm z), norm_sub_rev] at h2
  unfold traceGraph
  rw [abs_le]
  constructor <;> linarith

/-! ### The regularized operator -/

theorem traceFreeCoord_add_smul_one (M : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    traceFreeCoord (M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = traceFreeCoord M := by
  obtain ⟨c0, c1⟩ := traceFreeCoord_apply M
  obtain ⟨d0, d1⟩ := traceFreeCoord_apply (M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ))
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, c0, d0, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul]; ring
  · simp only [Fin.mk_one, c1, d1, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul]; ring

theorem regOp_hasTraceShift (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (K ε : ℝ) :
    HasTraceShift (regOp F K ε) := by
  intro M _ t
  simp only [regOp, traceFreeCoord_add_smul_one, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

theorem traceGraph_regOp (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (K ε : ℝ) (z : Rd 2) :
    traceGraph (regOp F K ε) z = (1 - ε) * traceGraph F z + ε * (K + 1) := by
  simp only [traceGraph, regOp, traceFreeCoord_traceFreeMat, trace_traceFreeMat, sub_zero]

/-- Lipschitz constant `1 - ε` of the regularized trace graph. -/
theorem traceGraph_regOp_lipschitz {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    (hdeg : DegenerateElliptic F) (K : ℝ) {ε : ℝ} (hε1 : ε ≤ 1) (z z' : Rd 2) :
    |traceGraph (regOp F K ε) z - traceGraph (regOp F K ε) z'| ≤ (1 - ε) * ‖z - z'‖ := by
  rw [traceGraph_regOp, traceGraph_regOp]
  have h := traceGraph_lipschitz hF hdeg z z'
  have e : (1 - ε) * traceGraph F z + ε * (K + 1) - ((1 - ε) * traceGraph F z' + ε * (K + 1)) =
      (1 - ε) * (traceGraph F z - traceGraph F z') := by ring
  rw [e, abs_mul, abs_of_nonneg (by linarith)]
  exact mul_le_mul_of_nonneg_left h (by linarith)

/-- `|Z_P| ≤ tr P` for positive semidefinite `P`. -/
theorem norm_traceFreeCoord_le_trace {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.PosSemidef) :
    ‖traceFreeCoord P‖ ≤ P.trace := by
  obtain ⟨c0, c1⟩ := traceFreeCoord_apply P
  have hsym : P 1 0 = P 0 1 := by have := hP.1.apply 0 1; simpa using this
  have q0 := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hP).2 (Pi.single 0 1)
  have q1 := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hP).2 (Pi.single 1 1)
  have q2 := hP.det_nonneg
  simp [dotProduct, Matrix.mulVec, Pi.single_apply] at q0 q1
  rw [Matrix.det_fin_two, hsym] at q2
  rw [Matrix.trace_fin_two]
  have hsq : ‖traceFreeCoord P‖ ^ 2 ≤ (P 0 0 + P 1 1) ^ 2 := by
    rw [norm_sq_two, c0, c1]
    nlinarith
  exact abs_le_of_sq_le_sq' hsq (by linarith) |>.2

/-- The regularized operator is degenerate elliptic (`0 ≤ ε ≤ 1`). -/
theorem regOp_degenerateElliptic {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hF : HasTraceShift F)
    (hdeg : DegenerateElliptic F) (K : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    DegenerateElliptic (regOp F K ε) := by
  intro X Y _ _ hXY
  have hlin : traceFreeCoord Y - traceFreeCoord X = traceFreeCoord (Y - X) := by
    obtain ⟨x0, x1⟩ := traceFreeCoord_apply X
    obtain ⟨y0, y1⟩ := traceFreeCoord_apply Y
    obtain ⟨p0, p1⟩ := traceFreeCoord_apply (Y - X)
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, PiLp.sub_apply, x0, y0, p0, Matrix.sub_apply]; ring
    · simp only [Fin.mk_one, PiLp.sub_apply, x1, y1, p1, Matrix.sub_apply]; ring
  have hZ := norm_traceFreeCoord_le_trace hXY
  have hL := traceGraph_lipschitz hF hdeg (traceFreeCoord Y) (traceFreeCoord X)
  rw [hlin] at hL
  have htr : (Y - X).trace = Y.trace - X.trace := Matrix.trace_sub Y X
  have hf := (abs_le.1 hL).2
  rw [htr] at hZ
  have hn := norm_nonneg (traceFreeCoord (Y - X))
  unfold regOp
  nlinarith [mul_nonneg (sub_nonneg.2 hε1) (sub_nonneg.2 (hf.trans hZ)),
    mul_nonneg hε0 (hn.trans hZ)]

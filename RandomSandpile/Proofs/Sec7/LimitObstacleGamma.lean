import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTrace
import RandomSandpile.Proofs.Sec7.MainTheoremViscEff
import RandomSandpile.Infra.SupConvolution
import RandomSandpile.Infra.Touching

/-!
# Integer superharmonic matrices and the single-source operator `F̄_0`

Elementary facts used by the identification steps and of Theorem 1.1
(`LimitViscZeroStmt`, `LimitMinimalStmt`; `paper/random_piles-corrected.tex`).

* `IsIntSuperharmonicMatrix N` is Pegden-Smart's set `Γ`: some `u : ℤ^d → ℤ` has
  `Δ_{ℤ^d} u ≤ 2d - 1` and `u ≥ q_N` on `ℤ^d`, so that `F̄_0(M) = inf {s : M - sI ∈ Γ}`
  (`effOp0`). `Γ` is closed downward (`IsIntSuperharmonicMatrix.mono`) and lies in
  `{tr N ≤ 2d - 1}` (`IsIntSuperharmonicMatrix.trace_le`: otherwise `u - q_N ≥ 0` would have
  `Δ_{ℤ^d}(u - q_N) ≤ -c < 0`, and the averages of simple random walk would drive it below `0`).
* `F̄_0(M) ≤ 0` iff `M - εI ∈ Γ` for every `ε > 0` (`effOp0_nonpos_of_forall`,
  `IsIntSuperharmonicMatrix.of_effOp0_nonpos`). The junk value of `sInf` plays no role: `M - sI ∈ Γ`
  for every large `s` (with `u = 0`, `effOp0_set_nonempty`).
* Hence the constraint `F̄_0(D²w) ≤ 0` of the obstacle problem gives `Δw ≤ 2d - 1` in the viscosity
  sense (`ViscFromBelowLE.trace_le_of_effOp0`).
* Quadratic test functions (`ViscFromBelowLE.le_of_touch`, `ViscFromBelowGE.le_of_touch`), the
  second-order Taylor bound of a `C²` test function touching from below
  (`touch_below_of_isLocalMin`), and the second-order condition for a `C²` function touching a
  quadratic from above (`qM_le_hessian_of_isLocalMax`).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- **Pegden-Smart's set `Γ` of integer superharmonic matrices**: some
`u : ℤ^d → ℤ` has `Δ_{ℤ^d} u ≤ 2d - 1` and `u(y) ≥ ½ yᵀ N y` for all `y ∈ ℤ^d`. By definition
`F̄_0(M) = inf {s : M - sI ∈ Γ}` (`effOp0`). -/
def IsIntSuperharmonicMatrix (N : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ u : Site d → ℤ, ∀ y : Site d, lap u y ≤ 2 * (d : ℤ) - 1 ∧ qMZ N y ≤ (u y : ℝ)

/-! ### Averages of simple random walk -/

/-- `(P g)(y) = (2d)⁻¹ ∑_{z ∼ y} g(z)`. -/
def walkAvg (g : Site d → ℝ) (y : Site d) : ℝ := nbrSum g y / (2 * d)

theorem walkAvg_mono {g g' : Site d → ℝ} (h : ∀ y, g y ≤ g' y) (y : Site d) :
    walkAvg g y ≤ walkAvg g' y := by
  unfold walkAvg
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact Finset.sum_le_sum fun i _ => add_le_add (h _) (h _)

theorem walkAvg_sub_const (hd : 1 ≤ d) (g : Site d → ℝ) (k : ℝ) (y : Site d) :
    walkAvg (fun z => g z - k) y = walkAvg g y - k := by
  have hd' : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs : nbrSum (fun z => g z - k) y = nbrSum g y - 2 * d * k := by
    simp only [nbrSum, sub_add_sub_comm, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [walkAvg, walkAvg, hs, sub_div, mul_div_cancel_left₀ k (ne_of_gt hd')]

theorem walkAvg_zero (y : Site d) : walkAvg (fun _ : Site d => (0 : ℝ)) y = 0 := by
  simp [walkAvg, nbrSum]

theorem walkAvg_eq_add_lapR (hd : 1 ≤ d) (g : Site d → ℝ) (y : Site d) :
    walkAvg g y = g y + lapR g y / (2 * d) := by
  have hd' : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [walkAvg, lapR, sub_div, mul_div_cancel_left₀ _ (ne_of_gt hd')]
  ring

theorem walkAvg_iterate_mono (t : ℕ) {g g' : Site d → ℝ} (h : ∀ y, g y ≤ g' y) (y : Site d) :
    (walkAvg (d := d))^[t] g y ≤ (walkAvg (d := d))^[t] g' y := by
  induction t generalizing g g' with
  | zero => exact h y
  | succ t ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (walkAvg_mono h)

theorem walkAvg_iterate_sub_const (hd : 1 ≤ d) (t : ℕ) (g : Site d → ℝ) (k : ℝ) :
    (walkAvg (d := d))^[t] (fun z => g z - k) = fun z => (walkAvg (d := d))^[t] g z - k := by
  induction t generalizing g with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have : walkAvg (fun z => g z - k) = fun z => walkAvg g z - k :=
      funext (walkAvg_sub_const hd g k)
    rw [this, ih]

theorem walkAvg_iterate_zero (t : ℕ) :
    (walkAvg (d := d))^[t] (fun _ : Site d => (0 : ℝ)) = fun _ => 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    have : walkAvg (fun _ : Site d => (0 : ℝ)) = fun _ => 0 := funext walkAvg_zero
    rw [this, ih]

/-- A nonnegative function on `ℤ^d` cannot have `Δ_{ℤ^d} f ≤ -c < 0` everywhere. -/
theorem not_lapR_le_neg_of_nonneg (hd : 1 ≤ d) {f : Site d → ℝ} (hf : ∀ y, 0 ≤ f y) {c : ℝ}
    (hc : 0 < c) : ¬ ∀ y, lapR f y ≤ -c := by
  intro hlap
  have hd' : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set e : ℝ := c / (2 * d) with he
  have he0 : 0 < e := div_pos hc hd'
  have hstep : ∀ y, walkAvg f y ≤ f y - e := fun y => by
    rw [walkAvg_eq_add_lapR hd]
    have := div_le_div_of_nonneg_right (hlap y) hd'.le
    rw [neg_div] at this
    linarith
  have hiter : ∀ t : ℕ, ∀ y, (walkAvg (d := d))^[t] f y ≤ f y - t * e := by
    intro t
    induction t with
    | zero => intro y; simp
    | succ t ih =>
      intro y
      rw [Function.iterate_succ_apply]
      have h1 := walkAvg_iterate_mono t hstep y
      rw [walkAvg_iterate_sub_const hd] at h1
      have h2 := ih y
      push_cast
      linarith
  have hpos : ∀ t : ℕ, ∀ y, 0 ≤ (walkAvg (d := d))^[t] f y := fun t y => by
    have := walkAvg_iterate_mono t (g := fun _ => 0) hf y
    rwa [walkAvg_iterate_zero] at this
  obtain ⟨t, ht⟩ := exists_nat_gt (f 0 / e)
  have h1 := hiter t 0
  have h2 := hpos t 0
  rw [div_lt_iff₀ he0] at ht
  linarith

namespace IsIntSuperharmonicMatrix

/-- `Γ` is closed downward in the order of quadratic forms. -/
theorem mono {N N' : Matrix (Fin d) (Fin d) ℝ} (h : IsIntSuperharmonicMatrix N)
    (hle : ∀ x : Rd d, qM N' x ≤ qM N x) : IsIntSuperharmonicMatrix N' := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, fun y => ⟨(hu y).1, (hle (toE y)).trans (hu y).2⟩⟩

/-- `Γ` is closed downward in the Loewner order. -/
theorem mono_psd {N N' : Matrix (Fin d) (Fin d) ℝ} (h : IsIntSuperharmonicMatrix N)
    (hle : (N - N').PosSemidef) : IsIntSuperharmonicMatrix N' :=
  h.mono fun x => by
    have := qM_nonneg_of_posSemidef hle x
    rw [qM_sub_mat] at this
    linarith

/-- **`Γ ⊆ {tr N ≤ 2d - 1}`.** If `u ≥ q_N` and `Δ_{ℤ^d} u ≤ 2d - 1`, then `f = u - q_N ≥ 0` has
`Δ_{ℤ^d} f ≤ 2d - 1 - tr N`, which must not be negative (`not_lapR_le_neg_of_nonneg`). -/
theorem trace_le (hd : 1 ≤ d) {N : Matrix (Fin d) (Fin d) ℝ} (h : IsIntSuperharmonicMatrix N) :
    N.trace ≤ 2 * (d : ℝ) - 1 := by
  obtain ⟨u, hu⟩ := h
  by_contra hlt
  have hc : 0 < N.trace - (2 * (d : ℝ) - 1) := by linarith [not_le.1 hlt]
  refine not_lapR_le_neg_of_nonneg hd (f := fun y => (u y : ℝ) - qMZ N y)
    (fun y => by linarith [(hu y).2]) hc fun y => ?_
  have e := PegdenSmartRegularity.lapR_sub (fun y => (u y : ℝ)) (qMZ N) y
  rw [lapR_intCast, PegdenSmartRegularity.lapR_qMZ] at e
  have h2 : (lap u y : ℝ) ≤ 2 * (d : ℝ) - 1 := by exact_mod_cast (hu y).1
  rw [e]
  linarith

end IsIntSuperharmonicMatrix

/-! ### `F̄_0` and `Γ` -/

/-- The set whose infimum is `F̄_0(M)` is nonempty: `M - sI ∈ Γ` with `u = 0` for `s` large. -/
theorem effOp0_set_nonempty (hd : 1 ≤ d) (M : Matrix (Fin d) (Fin d) ℝ) :
    {s : ℝ | ∃ u : Site d → ℤ, ∀ y : Site d, lap u y ≤ 2 * (d : ℤ) - 1 ∧
      qMZ (M - s • (1 : Matrix (Fin d) (Fin d) ℝ)) y ≤ (u y : ℝ)}.Nonempty := by
  set c : ℝ := ∑ i, ∑ j, |M i j| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hMc : ∀ i j, |M i j| ≤ c := fun i j =>
    (Finset.single_le_sum (f := fun j => |M i j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
        (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))
  refine ⟨2 * (d : ℝ) ^ 2 * c, 0, fun y => ⟨?_, ?_⟩⟩
  · simp only [lap, nbrSumZ, Pi.zero_apply, add_zero, Finset.sum_const_zero, mul_zero,
      sub_zero]
    omega
  · have h1 := abs_le.1 (abs_qM_le M hc0 hMc (toE y))
    show qM _ (toE y) ≤ ((0 : ℤ) : ℝ)
    rw [qM_sub_mat, qM_smul_one, Int.cast_zero]
    nlinarith [h1.2]

/-- If `M - εI ∈ Γ` for every `ε > 0`, then `F̄_0(M) ≤ 0`. -/
theorem effOp0_nonpos_of_forall {M : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ ε : ℝ, 0 < ε → IsIntSuperharmonicMatrix (M - ε • (1 : Matrix (Fin d) (Fin d) ℝ))) :
    effOp0 d M ≤ 0 := by
  unfold effOp0
  by_cases hb : BddBelow {s : ℝ | ∃ u : Site d → ℤ, ∀ y : Site d, lap u y ≤ 2 * (d : ℤ) - 1 ∧
      qMZ (M - s • (1 : Matrix (Fin d) (Fin d) ℝ)) y ≤ (u y : ℝ)}
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    exact csInf_le hb (h ε hε)
  · rw [Real.sInf_of_not_bddBelow hb]

/-- If `F̄_0(M) ≤ 0`, then `M - εI ∈ Γ` for every `ε > 0`. -/
theorem IsIntSuperharmonicMatrix.of_effOp0_nonpos (hd : 1 ≤ d) {M : Matrix (Fin d) (Fin d) ℝ}
    (h : effOp0 d M ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    IsIntSuperharmonicMatrix (M - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  unfold effOp0 at h
  obtain ⟨s, hs, hsε⟩ := exists_lt_of_csInf_lt (effOp0_set_nonempty hd M) (h.trans_lt hε)
  refine IsIntSuperharmonicMatrix.mono hs fun x => ?_
  rw [qM_sub_mat, qM_sub_mat, qM_smul_one, qM_smul_one]
  have := mul_nonneg (sub_nonneg.2 hsε.le) (sq_nonneg ‖x‖)
  linarith

/-- `F̄_0(N) ≤ 0` gives `tr N ≤ 2d - 1`. -/
theorem trace_le_of_effOp0_nonpos (hd : 1 ≤ d) {N : Matrix (Fin d) (Fin d) ℝ}
    (h : effOp0 d N ≤ 0) : N.trace ≤ 2 * (d : ℝ) - 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := (IsIntSuperharmonicMatrix.of_effOp0_nonpos hd h (ε := ε / d)
    (div_pos hε hdpos)).trace_le hd
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    div_mul_cancel₀ ε (ne_of_gt hdpos)] at this
  linarith

/-- **The constraint `F̄_0(D²w) ≤ 0` gives `Δw ≤ 2d - 1`** in the viscosity sense (test functions
touching from below). -/
theorem ViscFromBelowLE.trace_le_of_effOp0 (hd : 1 ≤ d) {U : Set (Rd d)} {w : Rd d → ℝ}
    (hw : ViscFromBelowLE (effOp0 d) U w) :
    ViscFromBelowLE (fun X => X.trace - (2 * (d : ℝ) - 1)) U w := fun x hx φ hφ hmin =>
  sub_nonpos.2 (trace_le_of_effOp0_nonpos hd (hw x hx φ hφ hmin))

/-! ### Quadratic forms and traces -/

theorem qM_toLp_single (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    qM A (WithLp.toLp 2 (Pi.single i 1)) = A i i / 2 := by
  simp [qM, Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

theorem trace_le_trace_of_qM_le {A B : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ x : Rd d, qM A x ≤ qM B x) : A.trace ≤ B.trace := by
  unfold Matrix.trace
  refine Finset.sum_le_sum fun i _ => ?_
  have := h (WithLp.toLp 2 (Pi.single i 1))
  rw [qM_toLp_single, qM_toLp_single] at this
  simp only [Matrix.diag_apply]
  linarith

theorem qM_neg_right (A : Matrix (Fin d) (Fin d) ℝ) (h : Rd d) : qM A (-h) = qM A h := by
  simp [qM, Matrix.mulVec_neg]

/-- The second symmetric difference of a quadratic. -/
theorem quadratic_symmDiff (c : ℝ) (p a : Rd d) (N : Matrix (Fin d) (Fin d) ℝ) (x h : Rd d) :
    (c + inner ℝ p (x + h - a) + qM N (x + h - a)) + (c + inner ℝ p (x - h - a) + qM N (x - h - a))
      - 2 * (c + inner ℝ p (x - a) + qM N (x - a)) = 2 * qM N h := by
  have e1 : x + h - a = (x - a) + h := by abel
  have e2 : x - h - a = (x - a) - h := by abel
  rw [e1, e2]
  simp only [qM, inner_add_right, inner_sub_right, WithLp.ofLp_add, WithLp.ofLp_sub,
    Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, dotProduct_sub, add_dotProduct,
    sub_dotProduct]
  ring

/-! ### Test functions -/

/-- The Hessian of a `C²` function is symmetric. -/
theorem hessian_isSymm_of_contDiffAt {φ : Rd d → ℝ} {x : Rd d} (hφ : ContDiffAt ℝ 2 φ x) :
    (hessian φ x).IsSymm := by
  have hsym := ContDiffAt.isSymmSndFDerivAt hφ (by simp)
  ext i j
  simp only [hessian, Matrix.transpose_apply, Matrix.of_apply]
  exact hsym _ _

/-- The quadratic `y ↦ c + p·(y - b) + q_Y(y - b)` has Hessian `Y` at `b` (`Y` symmetric). -/
theorem hessian_quadratic (c : ℝ) (p b : Rd d) {Y : Matrix (Fin d) (Fin d) ℝ} (hY : Y.IsSymm)
    (y : Rd d) : hessian (fun z => c + innerSL ℝ p (z - b) + qM Y (z - b)) y = Y := by
  rw [hessian_paraboloid, hessian_qM_of_isSymm hY]

theorem isLocalMin_sub_quadratic {w : Rd d → ℝ} {b q : Rd d} {Y : Matrix (Fin d) (Fin d) ℝ}
    (ht : ∀ᶠ y in 𝓝 b, w b + inner ℝ q (y - b) + qM Y (y - b) ≤ w y) :
    IsLocalMin (fun y => w y - (w b + innerSL ℝ q (y - b) + qM Y (y - b))) b := by
  filter_upwards [ht] with y hy
  simp only [innerSL_apply_apply, sub_self, inner_zero_right, qM_zero_right, add_zero]
  linarith

/-- A viscosity inequality `F(D²w) ≤ 0` tested from below, at a quadratic touching from below. -/
theorem ViscFromBelowLE.le_of_touch {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U : Set (Rd d)}
    {w : Rd d → ℝ} (hw : ViscFromBelowLE F U w) {b q : Rd d} {Y : Matrix (Fin d) (Fin d) ℝ}
    (hY : Y.IsSymm) (hb : b ∈ U)
    (ht : ∀ᶠ y in 𝓝 b, w b + inner ℝ q (y - b) + qM Y (y - b) ≤ w y) : F Y ≤ 0 := by
  have h := hw b hb _ ((contDiff_paraboloid (w b) q b Y (n := 2)).contDiffAt)
    (isLocalMin_sub_quadratic ht)
  rwa [hessian_quadratic _ _ _ hY] at h

/-- A viscosity inequality `F(D²w) ≥ 0` tested from below, at a quadratic touching from below. -/
theorem ViscFromBelowGE.le_of_touch {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U : Set (Rd d)}
    {w : Rd d → ℝ} (hw : ViscFromBelowGE F U w) {b q : Rd d} {Y : Matrix (Fin d) (Fin d) ℝ}
    (hY : Y.IsSymm) (hb : b ∈ U)
    (ht : ∀ᶠ y in 𝓝 b, w b + inner ℝ q (y - b) + qM Y (y - b) ≤ w y) : 0 ≤ F Y := by
  have h := hw b hb _ ((contDiff_paraboloid (w b) q b Y (n := 2)).contDiffAt)
    (isLocalMin_sub_quadratic ht)
  rwa [hessian_quadratic _ _ _ hY] at h

/-- A `C²` test function touching `v` from below at `x` gives, for every `κ > 0`, the quadratic
`v(x) + Dφ(x)·(y - x) + ½(y - x)ᵀ(D²φ(x) - κI)(y - x)` touching `v` from below at `x`. -/
theorem touch_below_of_isLocalMin {v φ : Rd d → ℝ} {x : Rd d} (hφ : ContDiffAt ℝ 2 φ x)
    (hmin : IsLocalMin (fun y => v y - φ y) x) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ y in 𝓝 x, v x + inner ℝ ((InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x)) (y - x)
      + qM (hessian φ x - κ • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - x) ≤ v y := by
  obtain ⟨ρ, hρ, hT⟩ := ContDiffAt.taylor_two hφ (κ := κ / 2) (half_pos hκ)
  filter_upwards [hmin, Metric.ball_mem_nhds x hρ] with y hy hyb
  have h1 := abs_le.1 (hT y (by rwa [Metric.mem_ball, dist_eq_norm] at hyb))
  rw [InnerProductSpace.toDual_symm_apply, qM_sub_mat, qM_smul_one]
  have hy' : v x - φ x ≤ v y - φ y := hy
  linarith [h1.1]

/-- **Second-order condition.** If a `C²` function `ψ` touches a quadratic with matrix `N` from
above at `x` (i.e. `P - ψ` has a local maximum at `x`), then `q_N ≤ q_{D²ψ(x)}`. -/
theorem qM_le_hessian_of_isLocalMax {ψ : Rd d → ℝ} {x : Rd d} (hψ : ContDiffAt ℝ 2 ψ x)
    (c : ℝ) (p a : Rd d) (N : Matrix (Fin d) (Fin d) ℝ)
    (hmax : IsLocalMax (fun y => (c + inner ℝ p (y - a) + qM N (y - a)) - ψ y) x) (h : Rd d) :
    qM N h ≤ qM (hessian ψ x) h := by
  set P : Rd d → ℝ := fun y => c + inner ℝ p (y - a) + qM N (y - a) with hP
  set H := hessian ψ x with hH
  -- the bound on small vectors, for every `κ > 0`
  have hsmall : ∀ κ > 0, ∃ ρ > 0, ∀ k : Rd d, ‖k‖ < ρ → qM N k ≤ qM H k + κ * ‖k‖ ^ 2 := by
    intro κ hκ
    obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hψ hκ
    obtain ⟨ρ₂, hρ₂, hm⟩ := Metric.eventually_nhds_iff.1 hmax
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun k hk => ?_⟩
    have hk1 : ‖k‖ < ρ₁ := hk.trans_le (min_le_left _ _)
    have hk2 : ‖k‖ < ρ₂ := hk.trans_le (min_le_right _ _)
    have hp : dist (x + k) x < ρ₂ := by rwa [dist_eq_norm, add_sub_cancel_left]
    have hm' : dist (x - k) x < ρ₂ := by rwa [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    have m1 : P (x + k) - ψ (x + k) ≤ P x - ψ x := hm hp
    have m2 : P (x - k) - ψ (x - k) ≤ P x - ψ x := hm hm'
    have t1 := abs_le.1 (hT (x + k) (by rwa [add_sub_cancel_left]))
    have t2 := abs_le.1 (hT (x - k) (by rwa [sub_sub_cancel_left, norm_neg]))
    rw [add_sub_cancel_left] at t1
    rw [sub_sub_cancel_left, norm_neg, map_neg, qM_neg_right] at t2
    have hsd := quadratic_symmDiff c p a N x k
    simp only [hP] at m1 m2
    linarith [t1.2, t2.2]
  -- homogeneity
  refine (sub_nonpos.1 (nonpos_of_forall_pos_le_mul (sq_nonneg ‖h‖) fun κ hκ => ?_))
  obtain ⟨ρ, hρ, hb⟩ := hsmall κ hκ
  set t : ℝ := ρ / (2 * (‖h‖ + 1)) with ht
  have ht0 : 0 < t := by positivity
  have htk : ‖t • h‖ < ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ht]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg h]
  have := hb (t • h) htk
  rw [qM_smul, qM_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mul_pow] at this
  have ht2 : 0 < t ^ 2 := by positivity
  have : t ^ 2 * (qM N h - qM H h) ≤ t ^ 2 * (κ * ‖h‖ ^ 2) := by nlinarith
  exact le_of_mul_le_mul_left this ht2

end RandomSandpile

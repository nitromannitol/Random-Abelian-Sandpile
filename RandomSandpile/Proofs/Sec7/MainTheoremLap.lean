import RandomSandpile.Proofs.Sec7.MainTheoremSandpile
import RandomSandpile.Proofs.Sec7.MainTheoremViscEff

/-!
# Theorem 1.1, step: summation by parts for the rescaled Laplacian

`rescaledLapWeak : RescaledLapWeakStmt`. For integer functions `v_n` vanishing off the cubes
`{|x|_∞ < R₀ (n + 1)}` with `v̄_n = n⁻² v_n([n ·]) → v̄` uniformly, and a test function
`φ ∈ C_c^∞(ℝ^d)`, `∫ Δ_{ℤ^d} v_n([nx]) φ(x) dx → ∫ v̄ Δφ`.

Route (no lattice sums). Translation invariance of Lebesgue measure gives
`∫ u([nx] + e) φ(x) dx = ∫ u([nx]) φ(x - e/n) dx` for `e ∈ ℤ^d`, so the lattice Laplacian moves onto
`φ` as the second difference `Σ_i (φ(x - e_i/n) + φ(x + e_i/n) - 2φ(x))`
(`integral_lap_latticeRound`); with `u = v_n`, `u([nx]) = n² v̄_n(x)`. By a uniform second-order
Taylor bound (`taylor_two_uniform`, from the uniform continuity of `D²φ`), `n²` times the second
difference converges to `Δφ = tr D²φ` uniformly (`tendsto_secondDiff`), and it vanishes off the
compact `1`-neighbourhood of the support of `φ`. Dominated convergence concludes.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-! ### Translations of the rescaled lattice -/

theorem latticeRound_add_toE (z : Rd d) (e : Site d) :
    latticeRound (z + toE e) = latticeRound z + e := by
  funext i
  simp [latticeRound, toE, Int.floor_add_intCast]

theorem toE_neg' (e : Site d) : toE (-e) = -toE e := by
  ext i
  simp [toE]

theorem measurable_latticeRound_add (u : Site d → ℤ) (n : ℕ) (e : Site d) :
    Measurable fun x : Rd d => (u (latticeRound ((n : ℝ) • x) + e) : ℝ) :=
  (measurable_of_countable fun z : Site d => (u (z + e) : ℝ)).comp
    (measurable_latticeRound.comp (measurable_const_smul _))

/-- `∫ u([nx] + e) φ(x) dx = ∫ u([nx]) φ(x - e/n) dx`. -/
theorem integral_latticeRound_add (u : Site d → ℤ) (φ : Rd d → ℝ) {n : ℕ} (hn : n ≠ 0)
    (e : Site d) :
    ∫ x, (u (latticeRound ((n : ℝ) • x) + e) : ℝ) * φ x =
      ∫ x, (u (latticeRound ((n : ℝ) • x)) : ℝ) * φ (x - (n : ℝ)⁻¹ • toE e) := by
  set c : Rd d := (n : ℝ)⁻¹ • toE e with hc
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have key : ∫ x, (u (latticeRound ((n : ℝ) • (x + c))) : ℝ) * φ (x + c - c) =
      ∫ x, (u (latticeRound ((n : ℝ) • x)) : ℝ) * φ (x - c) :=
    integral_add_right_eq_self (fun x => (u (latticeRound ((n : ℝ) • x)) : ℝ) * φ (x - c)) c
  rw [← key]
  congr 1
  funext x
  rw [add_sub_cancel_right, smul_add, hc, smul_smul, mul_inv_cancel₀ hn', one_smul,
    latticeRound_add_toE]

theorem integral_neg_two_add_add {a b c : Rd d → ℝ} (ha : Integrable a volume)
    (hb : Integrable b volume) (hc : Integrable c volume) :
    ∫ x, (-2 * a x + b x + c x) = -2 * (∫ x, a x) + (∫ x, b x) + ∫ x, c x := by
  have h1 : Integrable (fun x => -2 * a x + b x) volume := (ha.const_mul (-2)).add hb
  have h2 : Integrable (fun x => -2 * a x) volume := ha.const_mul (-2)
  rw [integral_add h1 hc, integral_add h2 hb, integral_const_mul]

/-- The lattice Laplacian moves onto the test function as a second difference at scale `1/n`. -/
theorem integral_lap_latticeRound (u : Site d → ℤ) {C : ℝ} (hu : ∀ y, |(u y : ℝ)| ≤ C)
    {φ : Rd d → ℝ} (hφ : Integrable φ volume) {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (lap u (latticeRound ((n : ℝ) • x)) : ℝ) * φ x =
      ∫ x, (u (latticeRound ((n : ℝ) • x)) : ℝ) * ∑ i : Fin d,
        (-2 * φ x + φ (x - (n : ℝ)⁻¹ • toE (unit i)) + φ (x + (n : ℝ)⁻¹ • toE (unit i))) := by
  have hI : ∀ (e : Site d) (ψ : Rd d → ℝ), Integrable ψ volume →
      Integrable (fun x => (u (latticeRound ((n : ℝ) • x) + e) : ℝ) * ψ x) volume :=
    fun e ψ hψ => hψ.bdd_mul (measurable_latticeRound_add u n e).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hu _)
  have hI0 : ∀ ψ : Rd d → ℝ, Integrable ψ volume →
      Integrable (fun x => (u (latticeRound ((n : ℝ) • x)) : ℝ) * ψ x) volume := fun ψ hψ => by
    simpa using hI 0 ψ hψ
  have hIm : ∀ i : Fin d,
      Integrable (fun x => (u (latticeRound ((n : ℝ) • x) - unit i) : ℝ) * φ x) volume :=
    fun i => by simpa [← sub_eq_add_neg] using hI (-unit i) φ hφ
  calc ∫ x, (lap u (latticeRound ((n : ℝ) • x)) : ℝ) * φ x
      = ∫ x, ∑ i : Fin d, (-2 * ((u (latticeRound ((n : ℝ) • x)) : ℝ) * φ x) +
          (u (latticeRound ((n : ℝ) • x) + unit i) : ℝ) * φ x +
          (u (latticeRound ((n : ℝ) • x) - unit i) : ℝ) * φ x) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [lap_eq_sum_second_diff]
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i : Fin d, ∫ x, (-2 * ((u (latticeRound ((n : ℝ) • x)) : ℝ) * φ x) +
          (u (latticeRound ((n : ℝ) • x) + unit i) : ℝ) * φ x +
          (u (latticeRound ((n : ℝ) • x) - unit i) : ℝ) * φ x) :=
        integral_finsetSum _ fun i _ =>
          (((hI0 φ hφ).const_mul _).add (hI _ φ hφ)).add (hIm i)
    _ = ∑ i : Fin d, ∫ x, (-2 * ((u (latticeRound ((n : ℝ) • x)) : ℝ) * φ x) +
          (u (latticeRound ((n : ℝ) • x)) : ℝ) * φ (x - (n : ℝ)⁻¹ • toE (unit i)) +
          (u (latticeRound ((n : ℝ) • x)) : ℝ) * φ (x + (n : ℝ)⁻¹ • toE (unit i))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hm := integral_latticeRound_add u φ hn (-unit i)
        simp only [toE_neg', smul_neg, sub_neg_eq_add, ← sub_eq_add_neg] at hm
        have e0 := integral_neg_two_add_add (hI0 φ hφ) (hI (unit i) φ hφ) (hIm i)
        have e1 := integral_neg_two_add_add (hI0 φ hφ)
          (hI0 _ (hφ.comp_sub_right ((n : ℝ)⁻¹ • toE (unit i))))
          (hI0 _ (hφ.comp_add_right ((n : ℝ)⁻¹ • toE (unit i))))
        have e2 := integral_latticeRound_add u φ hn (unit i)
        linarith [e0, e1, e2, hm]
    _ = ∫ x, ∑ i : Fin d, (-2 * ((u (latticeRound ((n : ℝ) • x)) : ℝ) * φ x) +
          (u (latticeRound ((n : ℝ) • x)) : ℝ) * φ (x - (n : ℝ)⁻¹ • toE (unit i)) +
          (u (latticeRound ((n : ℝ) • x)) : ℝ) * φ (x + (n : ℝ)⁻¹ • toE (unit i))) :=
        (integral_finsetSum _ fun i _ => (((hI0 φ hφ).const_mul _).add
          (hI0 _ (hφ.comp_sub_right _))).add (hI0 _ (hφ.comp_add_right _))).symm
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Uniform Taylor bound and second differences -/

/-- Uniform second-order Taylor bound for a compactly supported `C²` function. -/
theorem taylor_two_uniform {φ : Rd d → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {κ : ℝ} (hκ : 0 < κ) : ∃ ρ > 0, ∀ x h : Rd d, ‖h‖ < ρ →
      |φ (x + h) - φ x - fderiv ℝ φ x h - qM (hessian φ x) h| ≤ κ * ‖h‖ ^ 2 := by
  set D := fderiv ℝ φ with hD_def
  have hD1 : ContDiff ℝ 1 D := hφ.fderiv_right (m := 1) (by norm_num)
  have hB : Continuous (fderiv ℝ D) := hD1.continuous_fderiv (by norm_num)
  have hBc : HasCompactSupport (fderiv ℝ D) := (hc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
  have hBu : @UniformContinuous (Rd d) (Rd d →L[ℝ] Rd d →L[ℝ] ℝ)
      PseudoMetricSpace.toUniformSpace PseudoMetricSpace.toUniformSpace (fderiv ℝ D) :=
    hBc.uniformContinuous_of_continuous hB
  obtain ⟨ρ, hρ, hball⟩ := Metric.uniformContinuous_iff.1 hBu κ hκ
  refine ⟨ρ, hρ, fun x h hh => ?_⟩
  set B := fderiv ℝ D x with hB_def
  have hDd : ∀ z, HasFDerivAt D (fderiv ℝ D z) z := fun z =>
    (hD1.differentiable (by norm_num) z).hasFDerivAt
  have hφd : ∀ z, HasFDerivAt φ (D z) z := fun z =>
    (hφ.differentiable (by norm_num) z).hasFDerivAt
  have hmvt : ∀ s : Rd d, ‖s‖ ≤ ‖h‖ → ‖D (x + s) - D x - B s‖ ≤ κ * ‖s‖ := by
    intro s hs
    have hmem : x + s ∈ Metric.closedBall x ‖s‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    have := (convex_closedBall x ‖s‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z => D z - B z) (f' := fun z => fderiv ℝ D z - B)
      (fun z _ => ((hDd z).sub B.hasFDerivAt).hasFDerivWithinAt)
      (fun z hz => by
        rw [← dist_eq_norm]
        refine (hball ?_).le
        rw [Metric.mem_closedBall] at hz
        linarith)
      (Metric.mem_closedBall_self (norm_nonneg _)) hmem
    have e1 : (D (x + s) - B (x + s)) - (D x - B x) = D (x + s) - D x - B s := by
      rw [map_add]; abel
    rw [e1, add_sub_cancel_left] at this
    exact this
  let χ : ℝ → ℝ := fun t => φ (x + t • h) - t * D x h - t ^ 2 / 2 * B h h
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt χ (D (x + t • h) h - D x h - t * B h h) (Set.Icc 0 1) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have h2 : HasDerivAt (fun t => φ (x + t • h)) (D (x + t • h) h) t :=
      (hφd _).comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t * D x h) (D x h) t := by
      simpa using (hasDerivAt_id t).mul_const (D x h)
    have h4 : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * B h h) (t * B h h) t := by
      have h5 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      exact ((h5.div_const 2).mul_const (B h h)).congr_deriv (by ring)
    exact ((h2.sub h3).sub h4).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖D (x + t • h) h - D x h - t * B h h‖ ≤ κ * ‖h‖ ^ 2 := by
    intro t ht
    have hth : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
    have heq : D (x + t • h) h - D x h - t * B h h = (D (x + t • h) - D x - B (t • h)) h := by
      simp
    rw [heq]
    calc ‖(D (x + t • h) - D x - B (t • h)) h‖
        ≤ ‖D (x + t • h) - D x - B (t • h)‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ κ * ‖t • h‖ * ‖h‖ := by gcongr; exact hmvt _ hth
      _ ≤ κ * ‖h‖ * ‖h‖ := by gcongr
      _ = κ * ‖h‖ ^ 2 := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 (by simp)
  have hBq : B h h = 2 * qM (hessian φ x) h := fderiv_fderiv_diag_eq_qM φ x h
  simp only [χ, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, one_pow,
    Real.norm_eq_abs, mul_one] at key
  rw [hBq] at key
  convert key using 2
  ring

theorem qM_neg_right (M : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) : qM M (-x) = qM M x := by
  simp [qM, Matrix.mulVec_neg]

theorem qM_smul_right (M : Matrix (Fin d) (Fin d) ℝ) (a : ℝ) (x : Rd d) :
    qM M (a • x) = a ^ 2 * qM M x := by
  simp only [qM, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

theorem two_qM_toE_unit (M : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    2 * qM M (toE (unit i)) = M i i := by
  have h : WithLp.ofLp (toE (unit i : Site d)) = Pi.single i (1 : ℝ) := by
    funext j
    simp [toE, unit, Pi.single_apply]
  simp [qM, h]

theorem norm_toE_unit' (i : Fin d) : ‖toE (unit i : Site d)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [toE, unit, Pi.single_apply, apply_ite]

/-- `n²` times the second difference of `φ` at scale `1/n` converges uniformly to `Δφ`. -/
theorem tendsto_secondDiff {φ : Rd d → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    TendstoUniformly (fun (n : ℕ) x => (n : ℝ) ^ 2 * ∑ i : Fin d,
      (-2 * φ x + φ (x - (n : ℝ)⁻¹ • toE (unit i)) + φ (x + (n : ℝ)⁻¹ • toE (unit i))))
      (fun x => Matrix.trace (hessian φ x)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hd1 : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by positivity
  obtain ⟨ρ, hρ, hT⟩ := taylor_two_uniform hφ hc (κ := ε / (2 * ((d : ℝ) + 1))) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ρ)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn x
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnρ : (n : ℝ)⁻¹ < ρ := by
    have : (1 / ρ : ℝ) < n := hN.trans (by exact_mod_cast (show N < n by omega))
    rw [inv_lt_comm₀ hn0 hρ]
    simpa using this
  set κ := ε / (2 * ((d : ℝ) + 1)) with hκ
  have hper : ∀ i : Fin d, |(n : ℝ) ^ 2 * (-2 * φ x + φ (x - (n : ℝ)⁻¹ • toE (unit i)) +
      φ (x + (n : ℝ)⁻¹ • toE (unit i))) - hessian φ x i i| ≤ 2 * κ := by
    intro i
    set c : Rd d := (n : ℝ)⁻¹ • toE (unit i) with hc_def
    have hcn : ‖c‖ = (n : ℝ)⁻¹ := by
      rw [hc_def, norm_smul, norm_toE_unit', mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 := abs_le.1 (hT x c (by rw [hcn]; exact hnρ))
    have h2 := abs_le.1 (hT x (-c) (by rw [norm_neg, hcn]; exact hnρ))
    rw [map_neg, qM_neg_right, ← sub_eq_add_neg] at h2
    have hq : (n : ℝ) ^ 2 * (2 * qM (hessian φ x) c) = hessian φ x i i := by
      rw [hc_def, qM_smul_right, ← two_qM_toE_unit (hessian φ x) i]
      field_simp
    have hcn2 : (n : ℝ) ^ 2 * ‖c‖ ^ 2 = 1 := by rw [hcn]; field_simp
    simp only [norm_neg] at h2
    have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have e3 : (n : ℝ) ^ 2 * (κ * ‖c‖ ^ 2) = κ := by rw [mul_left_comm, hcn2, mul_one]
    have p1 := mul_le_mul_of_nonneg_left h1.2 hn2
    have p2 := mul_le_mul_of_nonneg_left h2.2 hn2
    have p3 := mul_le_mul_of_nonneg_left h1.1 hn2
    have p4 := mul_le_mul_of_nonneg_left h2.1 hn2
    rw [← hq, abs_le]
    constructor <;> nlinarith [p1, p2, p3, p4, e3]
  rw [dist_comm, dist_eq_norm, Real.norm_eq_abs, Matrix.trace, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc |∑ i : Fin d, ((n : ℝ) ^ 2 * (-2 * φ x + φ (x - (n : ℝ)⁻¹ • toE (unit i)) +
        φ (x + (n : ℝ)⁻¹ • toE (unit i))) - Matrix.diag (hessian φ x) i)|
      ≤ ∑ i : Fin d, |(n : ℝ) ^ 2 * (-2 * φ x + φ (x - (n : ℝ)⁻¹ • toE (unit i)) +
        φ (x + (n : ℝ)⁻¹ • toE (unit i))) - Matrix.diag (hessian φ x) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, 2 * κ := Finset.sum_le_sum fun i _ => hper i
    _ = (d : ℝ) * (2 * κ) := by simp
    _ < ε := by
        rw [hκ]
        field_simp
        nlinarith

/-! ### The step -/

/-- **Step** of Theorem 1.1: summation by parts for the rescaled Laplacian. -/
theorem rescaledLapWeak : RescaledLapWeakStmt := by
  intro d R₀ v vbar hsupp hvc hconv φ hφ hφc
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  set ψ : ℕ → Rd d → ℝ := fun n x => (n : ℝ) ^ 2 * ∑ i : Fin d,
    (-2 * φ x + φ (x - (n : ℝ)⁻¹ • toE (unit i)) + φ (x + (n : ℝ)⁻¹ • toE (unit i))) with hψ_def
  have hψ := tendsto_secondDiff hφ2 hφc
  -- the compact set carrying the second differences
  set K := Metric.cthickening 1 (tsupport φ) with hK_def
  have hK : IsCompact K := hφc.cthickening
  have hψK : ∀ n : ℕ, 1 ≤ n → ∀ x, x ∉ K → ψ n x = 0 := by
    intro n hn x hx
    have hz : ∀ y, dist x y ≤ 1 → φ y = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport fun hy' =>
        hx (Metric.mem_cthickening_of_dist_le x y 1 _ hy' hy)
    have hn1 : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
    have hcn : ∀ i : Fin d, ‖(n : ℝ)⁻¹ • toE (unit i : Site d)‖ ≤ 1 := fun i => by
      rw [norm_smul, norm_toE_unit', mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)⁻¹)]
      exact hn1
    simp only [hψ_def]
    rw [Finset.sum_eq_zero fun i _ => by
      rw [hz x (by simp), hz (x - _) (by rw [dist_eq_norm, sub_sub_cancel]; exact hcn i),
        hz (x + _) (by rw [dist_eq_norm, sub_add_cancel_left, norm_neg]; exact hcn i)]
      ring, mul_zero]
  -- bounds on `K`
  obtain ⟨Cv, hCv⟩ := hK.exists_bound_of_continuousOn hvc.continuousOn
  have hΔc : Continuous fun x => Matrix.trace (hessian φ x) := by
    have hB : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
      (hφ2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
    simp only [Matrix.trace, Matrix.diag, hessian, Matrix.of_apply]
    exact continuous_finsetSum _ fun i _ =>
      (hB.clm_apply continuous_const).clm_apply continuous_const
  obtain ⟨CΔ, hCΔ⟩ := hK.exists_bound_of_continuousOn hΔc.continuousOn
  set bnd : ℝ := (|Cv| + 1) * (|CΔ| + 1) with hbnd
  -- the identity for `n ≥ 1`
  have hident : ∀ n : ℕ, 1 ≤ n → ∫ x, rescaleSandpile (lap (v n)) n x * φ x =
      ∫ x, rescaleOdo (v n) n x * ψ n x := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
    -- `v n` is bounded (finite support)
    set Kn : ℤ := (R₀ : ℤ) * ((n : ℤ) + 1) with hKn
    have hS : (Set.pi Set.univ fun _ : Fin d => Set.Ioo (-Kn) Kn).Finite :=
      Set.Finite.pi fun _ => Set.finite_Ioo _ _
    have hbd : ∀ y, |(v n y : ℝ)| ≤ ∑ z ∈ hS.toFinset, |(v n z : ℝ)| := by
      intro y
      by_cases hy : y ∈ Set.pi Set.univ fun _ : Fin d => Set.Ioo (-Kn) Kn
      · exact Finset.single_le_sum (f := fun z => |(v n z : ℝ)|) (fun z _ => abs_nonneg _)
          (hS.mem_toFinset.2 hy)
      · have : v n y = 0 := by
          refine hsupp n y ?_
          simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, not_forall] at hy
          obtain ⟨i, hi⟩ := hy
          refine ⟨i, ?_⟩
          by_contra hlt
          exact hi (abs_lt.1 (not_le.1 hlt))
        rw [this, Int.cast_zero, abs_zero]
        exact Finset.sum_nonneg fun z _ => abs_nonneg _
    rw [show (fun x => rescaleSandpile (lap (v n)) n x * φ x) =
        fun x => (lap (v n) (latticeRound ((n : ℝ) • x)) : ℝ) * φ x from rfl,
      integral_lap_latticeRound (v n) hbd hφi hn0]
    congr 1
    funext x
    simp only [hψ_def, rescaleOdo]
    field_simp
  -- dominated convergence
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun x => rescaleOdo (v n) n x * ψ n x) volume := by
    intro n
    have h1 : Measurable (rescaleOdo (v n) n) :=
      (measurable_of_countable fun z : Site d => (v n z : ℝ) / (n : ℝ) ^ 2).comp
        (measurable_latticeRound.comp (measurable_const_smul _))
    have h2 : Continuous (ψ n) := by
      simp only [hψ_def]
      fun_prop
    exact h1.aestronglyMeasurable.mul h2.aestronglyMeasurable
  have hlim : Tendsto (fun n => ∫ x, rescaleOdo (v n) n x * ψ n x) atTop
      (𝓝 (∫ x, vbar x * Matrix.trace (hessian φ x))) := by
    refine tendsto_integral_filter_of_dominated_convergence (K.indicator fun _ => bnd)
      (Eventually.of_forall hmeas) ?_
      ((integrable_indicator_iff hK.measurableSet).2
        (integrableOn_const (C := bnd) hK.measure_lt_top.ne))
      (ae_of_all _ fun x => (hconv.tendsto_at x).mul (hψ.tendsto_at x))
    have hv1 := Metric.tendstoUniformly_iff.1 hconv 1 one_pos
    have hψ1 := Metric.tendstoUniformly_iff.1 hψ 1 one_pos
    filter_upwards [hv1, hψ1, eventually_ge_atTop 1] with n hvn hψn hn
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, abs_mul, hbnd]
      have a1 : |rescaleOdo (v n) n x| ≤ |Cv| + 1 := by
        have := hvn x
        rw [dist_eq_norm, Real.norm_eq_abs] at this
        have hc := hCv x hx
        rw [Real.norm_eq_abs] at hc
        have := abs_sub_abs_le_abs_sub (rescaleOdo (v n) n x) (vbar x)
        rw [abs_sub_comm (vbar x)] at *
        linarith [le_abs_self Cv]
      have a2 : |ψ n x| ≤ |CΔ| + 1 := by
        have := hψn x
        rw [dist_eq_norm, Real.norm_eq_abs] at this
        have hc := hCΔ x hx
        rw [Real.norm_eq_abs] at hc
        have := abs_sub_abs_le_abs_sub (ψ n x) (Matrix.trace (hessian φ x))
        rw [abs_sub_comm (Matrix.trace (hessian φ x))] at *
        linarith [le_abs_self CΔ]
      exact mul_le_mul a1 a2 (abs_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hx, hψK n hn x hx, mul_zero, abs_zero]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hident n hn).symm

end RandomSandpile

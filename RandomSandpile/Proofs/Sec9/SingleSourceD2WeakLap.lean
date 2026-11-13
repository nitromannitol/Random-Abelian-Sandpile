import RandomSandpile.Proofs.Sec9.SingleSourceD2Steps
import RandomSandpile.Proofs.Sec9.SingleSourceD2Algebra
import RandomSandpile.Proofs.Sec7.MainTheoremLap
import RandomSandpile.Proofs.Sec7.MainTheoremWeakStar
import RandomSandpile.Proofs.Sec7.PegdenSmartAdapterWeak
import RandomSandpile.Proofs.Sec9.SingleSourceFstarSub
import RandomSandpile.Proofs.Sec9.SingleSourceLimitMinimalSub

/-!
# Theorem 9.2 in dimension two: weak Laplacian of the limits

`ssLimitWeakLaplace : SSLimitWeakLaplaceD2Stmt`. Every subsequential limit `u` of the rescaled
single-source odometers `v̄_n(x) = n⁻¹ v_n([√n x])` has a locally bounded weak Laplacian off the
origin (as in Pegden-Smart's proof of Lemma 3.1).

Route (no lattice sums, as in Theorem 1.1 step, `Proofs/Sec7/MainTheoremLap.lean`, here at the
real scale `t = √n`).
* Translation invariance moves the lattice Laplacian onto the test function as a second difference
  at scale `1/t` (`integral_lap_latticeRound'`); `t²` times it converges uniformly to `Δφ`
  (`tendsto_secondDiff'`); with the local uniform convergence off the origin, dominated convergence
  gives `∫ Δ_{ℤ²} v_n([√n x]) g(x) dx → ∫ u Δg` for test functions `g` supported away from the origin
  (`tendsto_integral_lap_ss`).
* `|Δ_{ℤ²} v_n| ≤ 4 + |η_min|` off the origin (`abs_lap_ssOdometer_le`). Near `a ≠ 0`, the functions
  `f_n = χ · clip(Δ_{ℤ²} v_n([√n ·]))`, `χ` a smooth bump equal to `1` on `B_ρ(a)`, satisfy the
  hypotheses of the weak-* representation in `L^∞` (`weakStarRepresentation`, Theorem 1.1 step);
  the limit `s` is the weak Laplacian of `u` in `B_ρ(a)`, and is bounded a.e. by the same constant.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

variable {d : ℕ}

/-! ### Summation by parts at a real scale -/

theorem measurable_latticeRound_add' (u : Site d → ℤ) (t : ℝ) (e : Site d) :
    Measurable fun x : Rd d => (u (latticeRound (t • x) + e) : ℝ) :=
  (measurable_of_countable fun z : Site d => (u (z + e) : ℝ)).comp
    (measurable_latticeRound.comp (measurable_const_smul _))

/-- `∫ u([tx] + e) φ(x) dx = ∫ u([tx]) φ(x - e/t) dx`. -/
theorem integral_latticeRound_add' (u : Site d → ℤ) (φ : Rd d → ℝ) {t : ℝ} (ht : t ≠ 0)
    (e : Site d) :
    ∫ x, (u (latticeRound (t • x) + e) : ℝ) * φ x =
      ∫ x, (u (latticeRound (t • x)) : ℝ) * φ (x - t⁻¹ • toE e) := by
  set c : Rd d := t⁻¹ • toE e with hc
  have key : ∫ x, (u (latticeRound (t • (x + c))) : ℝ) * φ (x + c - c) =
      ∫ x, (u (latticeRound (t • x)) : ℝ) * φ (x - c) :=
    integral_add_right_eq_self (fun x => (u (latticeRound (t • x)) : ℝ) * φ (x - c)) c
  rw [← key]
  congr 1
  funext x
  rw [add_sub_cancel_right, smul_add, hc, smul_smul, mul_inv_cancel₀ ht, one_smul,
    latticeRound_add_toE]

/-- The lattice Laplacian moves onto the test function as a second difference at scale `1/t`. -/
theorem integral_lap_latticeRound' (u : Site d → ℤ) {C : ℝ} (hu : ∀ y, |(u y : ℝ)| ≤ C)
    {φ : Rd d → ℝ} (hφ : Integrable φ volume) {t : ℝ} (ht : t ≠ 0) :
    ∫ x, (lap u (latticeRound (t • x)) : ℝ) * φ x =
      ∫ x, (u (latticeRound (t • x)) : ℝ) * ∑ i : Fin d,
        (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) + φ (x + t⁻¹ • toE (unit i))) := by
  have hI : ∀ (e : Site d) (ψ : Rd d → ℝ), Integrable ψ volume →
      Integrable (fun x => (u (latticeRound (t • x) + e) : ℝ) * ψ x) volume :=
    fun e ψ hψ => hψ.bdd_mul (measurable_latticeRound_add' u t e).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hu _)
  have hI0 : ∀ ψ : Rd d → ℝ, Integrable ψ volume →
      Integrable (fun x => (u (latticeRound (t • x)) : ℝ) * ψ x) volume := fun ψ hψ => by
    simpa using hI 0 ψ hψ
  have hIm : ∀ i : Fin d,
      Integrable (fun x => (u (latticeRound (t • x) - unit i) : ℝ) * φ x) volume :=
    fun i => by simpa [← sub_eq_add_neg] using hI (-unit i) φ hφ
  calc ∫ x, (lap u (latticeRound (t • x)) : ℝ) * φ x
      = ∫ x, ∑ i : Fin d, (-2 * ((u (latticeRound (t • x)) : ℝ) * φ x) +
          (u (latticeRound (t • x) + unit i) : ℝ) * φ x +
          (u (latticeRound (t • x) - unit i) : ℝ) * φ x) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [lap_eq_sum_second_diff]
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i : Fin d, ∫ x, (-2 * ((u (latticeRound (t • x)) : ℝ) * φ x) +
          (u (latticeRound (t • x) + unit i) : ℝ) * φ x +
          (u (latticeRound (t • x) - unit i) : ℝ) * φ x) :=
        integral_finsetSum _ fun i _ =>
          (((hI0 φ hφ).const_mul _).add (hI _ φ hφ)).add (hIm i)
    _ = ∑ i : Fin d, ∫ x, (-2 * ((u (latticeRound (t • x)) : ℝ) * φ x) +
          (u (latticeRound (t • x)) : ℝ) * φ (x - t⁻¹ • toE (unit i)) +
          (u (latticeRound (t • x)) : ℝ) * φ (x + t⁻¹ • toE (unit i))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hm := integral_latticeRound_add' u φ ht (-unit i)
        simp only [toE_neg', smul_neg, sub_neg_eq_add, ← sub_eq_add_neg] at hm
        have e0 := integral_neg_two_add_add (hI0 φ hφ) (hI (unit i) φ hφ) (hIm i)
        have e1 := integral_neg_two_add_add (hI0 φ hφ)
          (hI0 _ (hφ.comp_sub_right (t⁻¹ • toE (unit i))))
          (hI0 _ (hφ.comp_add_right (t⁻¹ • toE (unit i))))
        have e2 := integral_latticeRound_add' u φ ht (unit i)
        linarith [e0, e1, e2, hm]
    _ = ∫ x, ∑ i : Fin d, (-2 * ((u (latticeRound (t • x)) : ℝ) * φ x) +
          (u (latticeRound (t • x)) : ℝ) * φ (x - t⁻¹ • toE (unit i)) +
          (u (latticeRound (t • x)) : ℝ) * φ (x + t⁻¹ • toE (unit i))) :=
        (integral_finsetSum _ fun i _ => (((hI0 φ hφ).const_mul _).add
          (hI0 _ (hφ.comp_sub_right _))).add (hI0 _ (hφ.comp_add_right _))).symm
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- `t²` times the second difference of `φ` at scale `1/t` converges uniformly to `Δφ` as
`t → ∞`. -/
theorem tendsto_secondDiff' {φ : Rd d → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    TendstoUniformly (fun (t : ℝ) x => t ^ 2 * ∑ i : Fin d,
      (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) + φ (x + t⁻¹ • toE (unit i))))
      (fun x => Matrix.trace (hessian φ x)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hd1 : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by positivity
  obtain ⟨ρ, hρ, hT⟩ := taylor_two_uniform hφ hc (κ := ε / (2 * ((d : ℝ) + 1))) (by positivity)
  filter_upwards [eventually_gt_atTop (1 / ρ)] with t ht x
  have hn0 : (0 : ℝ) < t := lt_trans (one_div_pos.2 hρ) ht
  have hnρ : t⁻¹ < ρ := by
    rw [inv_lt_comm₀ hn0 hρ]
    simpa using ht
  set κ := ε / (2 * ((d : ℝ) + 1)) with hκ
  have hper : ∀ i : Fin d, |t ^ 2 * (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) +
      φ (x + t⁻¹ • toE (unit i))) - hessian φ x i i| ≤ 2 * κ := by
    intro i
    set c : Rd d := t⁻¹ • toE (unit i) with hc_def
    have hcn : ‖c‖ = t⁻¹ := by
      rw [hc_def, norm_smul, norm_toE_unit', mul_one, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hn0)]
    have h1 := abs_le.1 (hT x c (by rw [hcn]; exact hnρ))
    have h2 := abs_le.1 (hT x (-c) (by rw [norm_neg, hcn]; exact hnρ))
    rw [map_neg, qM_neg_right, ← sub_eq_add_neg] at h2
    have hq : t ^ 2 * (2 * qM (hessian φ x) c) = hessian φ x i i := by
      rw [hc_def, qM_smul_right, ← two_qM_toE_unit (hessian φ x) i]
      field_simp
    have hcn2 : t ^ 2 * ‖c‖ ^ 2 = 1 := by rw [hcn]; field_simp
    simp only [norm_neg] at h2
    have hn2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg _
    have e3 : t ^ 2 * (κ * ‖c‖ ^ 2) = κ := by rw [mul_left_comm, hcn2, mul_one]
    have p1 := mul_le_mul_of_nonneg_left h1.2 hn2
    have p2 := mul_le_mul_of_nonneg_left h2.2 hn2
    have p3 := mul_le_mul_of_nonneg_left h1.1 hn2
    have p4 := mul_le_mul_of_nonneg_left h2.1 hn2
    rw [← hq, abs_le]
    constructor <;> nlinarith [p1, p2, p3, p4, e3]
  rw [dist_comm, dist_eq_norm, Real.norm_eq_abs, Matrix.trace, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc |∑ i : Fin d, (t ^ 2 * (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) +
        φ (x + t⁻¹ • toE (unit i))) - Matrix.diag (hessian φ x) i)|
      ≤ ∑ i : Fin d, |t ^ 2 * (-2 * φ x + φ (x - t⁻¹ • toE (unit i)) +
        φ (x + t⁻¹ • toE (unit i))) - Matrix.diag (hessian φ x) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, 2 * κ := Finset.sum_le_sum fun i _ => hper i
    _ = (d : ℝ) * (2 * κ) := by simp
    _ < ε := by
        rw [hκ]
        field_simp
        nlinarith

/-! ### Dominated convergence off the origin -/

/-- If `v̄_k → u` locally uniformly off the origin and `g ∈ C²_c` is supported away from the origin,
then `∫ v̄_k · t_k² (second difference of g at scale 1/t_k) → ∫ u Δg` as `t_k → ∞`. -/
theorem tendsto_integral_secondDiff {ub : ℕ → Rd 2 → ℝ} {u : Rd 2 → ℝ} {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) (hmeas : ∀ k, Measurable (ub k))
    (hbd : ∀ k, ∃ B : ℝ, ∀ x, |ub k x| ≤ B)
    (hconv : TendstoLocallyUniformlyOn ub u atTop {x : Rd 2 | x ≠ 0})
    {g : Rd 2 → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    {K : Set (Rd 2)} (hK : IsCompact K) (hK0 : ∀ x ∈ K, x ≠ 0) (hgK : tsupport g ⊆ K)
    (hδK : ∀ x, x ∉ K → ∀ y, dist x y ≤ δ → g y = 0) :
    Tendsto (fun k => ∫ x, ub k x * (t k ^ 2 * ∑ i : Fin 2, (-2 * g x +
      g (x - (t k)⁻¹ • toE (unit i)) + g (x + (t k)⁻¹ • toE (unit i))))) atTop
      (𝓝 (∫ x, u x * Matrix.trace (hessian g x))) := by
  set ψ : ℕ → Rd 2 → ℝ := fun k x => t k ^ 2 * ∑ i : Fin 2, (-2 * g x +
      g (x - (t k)⁻¹ • toE (unit i)) + g (x + (t k)⁻¹ • toE (unit i))) with hψ_def
  have hKs : K ⊆ {x : Rd 2 | x ≠ 0} := fun x hx => hK0 x hx
  have hψ : TendstoUniformly ψ (fun x => Matrix.trace (hessian g x)) atTop := by
    have h := tendsto_secondDiff' (d := 2) hg hgc
    rw [Metric.tendstoUniformly_iff] at h ⊢
    intro ε hε
    exact ht.eventually (h ε hε)
  have hψK : ∀ᶠ k in atTop, ∀ x, x ∉ K → ψ k x = 0 := by
    filter_upwards [ht.eventually (eventually_ge_atTop (1 / δ))] with k hk x hx
    have htk : 0 < t k := lt_of_lt_of_le (one_div_pos.2 hδ) hk
    have hz : ∀ y, dist x y ≤ δ → g y = 0 := hδK x hx
    have hn1 : (t k)⁻¹ ≤ δ := by
      rw [inv_le_comm₀ htk hδ]
      simpa using hk
    have hcn : ∀ i : Fin 2, ‖(t k)⁻¹ • toE (unit i : Site 2)‖ ≤ δ := fun i => by
      rw [norm_smul, norm_toE_unit', mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.2 htk)]
      exact hn1
    simp only [hψ_def]
    rw [Finset.sum_eq_zero fun i _ => by
      rw [hz x (by simp [hδ.le]), hz (x - _) (by rw [dist_eq_norm, sub_sub_cancel]; exact hcn i),
        hz (x + _) (by rw [dist_eq_norm, sub_add_cancel_left, norm_neg]; exact hcn i)]
      ring, mul_zero]
  -- bounds on `K`
  have hconvK := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_ne : IsOpen {x : Rd 2 | x ≠ 0})).1 hconv K hKs hK
  obtain ⟨k₁, hk₁⟩ := (Metric.tendstoUniformlyOn_iff.1 hconvK 1 one_pos).exists
  obtain ⟨B₁, hB₁⟩ := hbd k₁
  have huK : ∀ x ∈ K, |u x| ≤ B₁ + 1 := fun x hx => by
    have h1 := hk₁ x hx
    rw [dist_eq_norm, Real.norm_eq_abs] at h1
    have h2 := hB₁ x
    have h3 := abs_sub_abs_le_abs_sub (u x) (ub k₁ x)
    linarith
  have hΔc := PegdenSmartAdapter.continuous_trace_hessian hg
  obtain ⟨CΔ, hCΔ⟩ := hK.exists_bound_of_continuousOn hΔc.continuousOn
  set bnd : ℝ := (|B₁| + 2) * (|CΔ| + 1) with hbnd
  have hgcont : Continuous g := hg.continuous
  have hmeasF : ∀ k, AEStronglyMeasurable (fun x => ub k x * ψ k x) volume := by
    intro k
    have h2 : Continuous (ψ k) := by
      simp only [hψ_def]
      fun_prop
    exact (hmeas k).aestronglyMeasurable.mul h2.aestronglyMeasurable
  refine tendsto_integral_filter_of_dominated_convergence (K.indicator fun _ => bnd)
    (Eventually.of_forall hmeasF) ?_
    ((integrable_indicator_iff hK.measurableSet).2
      (integrableOn_const (C := bnd) hK.measure_lt_top.ne)) (ae_of_all _ fun x => ?_)
  · have hv1 := Metric.tendstoUniformlyOn_iff.1 hconvK 1 one_pos
    have hψ1 := Metric.tendstoUniformly_iff.1 hψ 1 one_pos
    filter_upwards [hv1, hψ1, hψK] with k hvk hψk hψ0
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, abs_mul, hbnd]
      have a1 : |ub k x| ≤ |B₁| + 2 := by
        have h1 := hvk x hx
        rw [dist_eq_norm, Real.norm_eq_abs] at h1
        have h2 := huK x hx
        have h3 := abs_sub_abs_le_abs_sub (ub k x) (u x)
        have h4 := abs_sub_comm (ub k x) (u x)
        linarith [le_abs_self B₁]
      have a2 : |ψ k x| ≤ |CΔ| + 1 := by
        have := hψk x
        rw [dist_eq_norm, Real.norm_eq_abs] at this
        have hc := hCΔ x hx
        rw [Real.norm_eq_abs] at hc
        have := abs_sub_abs_le_abs_sub (ψ k x) (Matrix.trace (hessian g x))
        rw [abs_sub_comm (Matrix.trace (hessian g x))] at *
        linarith [le_abs_self CΔ]
      exact mul_le_mul a1 a2 (abs_nonneg _) (by positivity)
    · show |ub k x * ψ k x| ≤ _
      rw [Set.indicator_of_notMem hx, hψ0 x hx, mul_zero, abs_zero]
  · by_cases hx : x ∈ K
    · exact (hconv.tendsto_at (hKs hx)).mul (hψ.tendsto_at x)
    · have hΔ0 : Matrix.trace (hessian g x) = 0 := by
        have : x ∉ tsupport g := fun h => hx (hgK h)
        rw [PegdenSmartAdapter.hessian_eq_zero_of_not_mem_tsupport this, Matrix.trace_zero]
      rw [hΔ0, mul_zero]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hψK] with k hk
      show 0 = ub k x * ψ k x
      rw [hk x hx, mul_zero]

/-! ### The single-source odometers -/

/-- `v̄_n(x) = n⁻¹ v_n([√n x])` in the plane. -/
theorem rescaleSingleSource_two (v : Site 2 → ℤ) (n : ℕ) (x : Rd 2) :
    rescaleSingleSource v n x = (n : ℝ)⁻¹ * (v (latticeRound (Real.sqrt n • x)) : ℝ) := by
  simp only [rescaleSingleSource]
  have h1 : (-(2 / ((2 : ℕ) : ℝ))) = -1 := by norm_num
  have h2 : (1 / ((2 : ℕ) : ℝ)) = 1 / 2 := by norm_num
  rw [h1, h2, Real.rpow_neg_one, ← Real.sqrt_eq_rpow]

/-- The single-source odometer is bounded (it vanishes off a box). -/
theorem exists_bound_ssOdometer {η : Site 2 → ℤ} (hη : ∀ x, η x ≤ 2 * ((2 : ℕ) : ℤ) - 2)
    (n : ℕ) : ∃ B : ℝ, ∀ y, |(singleSourceOdometer η n y : ℝ)| ≤ B := by
  have hS : (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (-((n : ℤ) + 1)) ((n : ℤ) + 1)).Finite :=
    Set.Finite.pi fun _ => Set.finite_Ioo _ _
  refine ⟨∑ z ∈ hS.toFinset, |(singleSourceOdometer η n z : ℝ)|, fun y => ?_⟩
  by_cases hy : y ∈ Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (-((n : ℤ) + 1)) ((n : ℤ) + 1)
  · exact Finset.single_le_sum (f := fun z => |(singleSourceOdometer η n z : ℝ)|)
      (fun z _ => abs_nonneg _) (hS.mem_toFinset.2 hy)
  · have h0 : singleSourceOdometer η n y = 0 := by
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      refine SingleSourceSub.singleSourceOdometer_eq_zero_of_coord hη n (i := i) ?_
      by_contra hlt
      exact hi (abs_lt.1 (not_le.1 hlt))
    rw [h0, Int.cast_zero, abs_zero]
    exact Finset.sum_nonneg fun z _ => abs_nonneg _

/-- A lattice point `[y]` is `0` only for `|y| < 2`. -/
theorem norm_lt_two_of_latticeRound_eq_zero {y : Rd 2} (hy : latticeRound y = 0) : ‖y‖ < 2 := by
  have h0 : ⌊y 0⌋ = 0 := congrFun hy 0
  have h1 : ⌊y 1⌋ = 0 := congrFun hy 1
  rw [Int.floor_eq_zero_iff] at h0 h1
  have hsq := norm_sq_two y
  have hb : ‖y‖ ^ 2 < 4 := by rw [hsq]; nlinarith [h0.1, h0.2, h1.1, h1.2]
  nlinarith [norm_nonneg y]

/-- **Summation by parts for the single-source odometers.** Along a subsequence `n_k` with
`v̄_{n_k} → u` locally uniformly off the origin, `∫ Δ_{ℤ²} v_{n_k}([√n_k x]) g(x) dx → ∫ u Δg` for
`g ∈ C²_c` supported away from the origin. -/
theorem tendsto_integral_lap_ss {η : Site 2 → ℤ} (hη : ∀ x, η x ≤ 2 * ((2 : ℕ) : ℤ) - 2)
    {nk : ℕ → ℕ} (hmono : StrictMono nk) {u : Rd 2 → ℝ}
    (hconv : TendstoLocallyUniformlyOn
      (fun k => rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k)) u atTop
      {x : Rd 2 | x ≠ 0})
    {g : Rd 2 → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    {K : Set (Rd 2)} (hK : IsCompact K) (hK0 : ∀ x ∈ K, x ≠ 0) (hgK : tsupport g ⊆ K)
    (hδK : ∀ x, x ∉ K → ∀ y, dist x y ≤ δ → g y = 0) :
    Tendsto (fun k => ∫ x, (lap (singleSourceOdometer η (nk k))
      (latticeRound (Real.sqrt (nk k) • x)) : ℝ) * g x) atTop
      (𝓝 (∫ x, u x * Matrix.trace (hessian g x))) := by
  have ht : Tendsto (fun k => Real.sqrt (nk k)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop ⌈b ^ 2⌉₊] with k hk
    have h1 : b ^ 2 ≤ (nk k : ℝ) := by
      have := Nat.le_ceil (b ^ 2)
      have h2 : (⌈b ^ 2⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
      have h3 : (k : ℝ) ≤ nk k := by exact_mod_cast hmono.id_le k
      linarith
    calc b ≤ |b| := le_abs_self b
      _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ Real.sqrt (nk k) := Real.sqrt_le_sqrt h1
  have hmeas : ∀ k, Measurable (fun x => rescaleSingleSource (singleSourceOdometer η (nk k))
      (nk k) x) := fun k => by
    simp only [rescaleSingleSource_two]
    exact measurable_const.mul ((measurable_of_countable fun z : Site 2 =>
      (singleSourceOdometer η (nk k) z : ℝ)).comp
        (measurable_latticeRound.comp (measurable_const_smul _)))
  have hbd : ∀ k, ∃ B : ℝ, ∀ x, |rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k) x|
      ≤ B := fun k => by
    obtain ⟨B, hB⟩ := exists_bound_ssOdometer hη (nk k)
    refine ⟨|((nk k : ℝ))⁻¹| * B, fun x => ?_⟩
    rw [rescaleSingleSource_two, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
  have hlim := tendsto_integral_secondDiff ht hmeas hbd hconv hg hgc hδ hK hK0 hgK hδK
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk1 : 1 ≤ nk k := le_trans hk (hmono.id_le k)
  have hn0 : (0 : ℝ) < nk k := by exact_mod_cast (show 0 < nk k by omega)
  have hs0 : Real.sqrt (nk k) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
  obtain ⟨B, hB⟩ := exists_bound_ssOdometer hη (nk k)
  have hgi : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hgc
  rw [integral_lap_latticeRound' (singleSourceOdometer η (nk k)) hB hgi hs0]
  congr 1
  funext x
  rw [rescaleSingleSource_two, Real.sq_sqrt hn0.le, mul_mul_mul_comm, inv_mul_cancel₀ hn0.ne',
    one_mul]

/-! ### The weak Laplacian near a point off the origin -/

/-- The clipped, localized lattice Laplacians `f_k = χ · clip(Δ_{ℤ²} v_{n_k}([√n_k ·]))`. -/
def clipLap (χ : Rd 2 → ℝ) (C : ℝ) (V : Site 2 → ℤ) (t : ℝ) (x : Rd 2) : ℝ :=
  χ x * max (-C) (min C (lap V (latticeRound (t • x)) : ℝ))

theorem measurable_clipLap {χ : Rd 2 → ℝ} (hχ : Continuous χ) (C : ℝ) (V : Site 2 → ℤ) (t : ℝ) :
    Measurable (clipLap χ C V t) :=
  hχ.measurable.mul (measurable_const.max (measurable_const.min
    ((measurable_of_countable fun z : Site 2 => (lap V z : ℝ)).comp
      (measurable_latticeRound.comp (measurable_const_smul _)))))

theorem abs_clipLap_le {χ : Rd 2 → ℝ} (hχ : ∀ x, |χ x| ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (V : Site 2 → ℤ) (t : ℝ) (x : Rd 2) : |clipLap χ C V t x| ≤ C := by
  unfold clipLap
  rw [abs_mul]
  have h1 : |max (-C) (min C (lap V (latticeRound (t • x)) : ℝ))| ≤ C := by
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  calc |χ x| * |max (-C) (min C (lap V (latticeRound (t • x)) : ℝ))| ≤ 1 * C :=
        mul_le_mul (hχ x) h1 (abs_nonneg _) zero_le_one
    _ = C := one_mul C

/-- Off the origin's lattice cell the clipping is inactive. -/
theorem clipLap_eq {χ : Rd 2 → ℝ} {C : ℝ} {V : Site 2 → ℤ} {t : ℝ} {x : Rd 2}
    (hlap : |(lap V (latticeRound (t • x)) : ℝ)| ≤ C) :
    clipLap χ C V t x = χ x * (lap V (latticeRound (t • x)) : ℝ) := by
  unfold clipLap
  have h := abs_le.1 hlap
  rw [min_eq_right h.2, max_eq_right h.1]

/-- The bound `4 + |η_min|` of `|Δ_{ℤ²} v_n|` off the origin. -/
def lapConst (ηmin : ℤ) : ℝ := 2 * ((2 : ℕ) : ℝ) + |(ηmin : ℝ)|

theorem lapConst_nonneg (ηmin : ℤ) : 0 ≤ lapConst ηmin := by
  unfold lapConst; positivity

theorem abs_lap_le_lapConst {η : Site 2 → ℤ} {ηmin : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * ((2 : ℕ) : ℤ) - 2) (n : ℕ) {z : Site 2} (hz : z ≠ 0) :
    |(lap (singleSourceOdometer η n) z : ℝ)| ≤ lapConst ηmin :=
  abs_le.2 (SingleSourceFstar.abs_lap_ssOdometer_le (by norm_num) hη
    (ssNonempty 2 (by norm_num) η (fun x => (hη x).2) n) hz)

/-- Inside `B_{2ρ}(a)`, `|a| = 4ρ`, the lattice point `[t x]` is not the origin once `t ≥ 1/ρ`. -/
theorem latticeRound_ne_zero {a x : Rd 2} {ρ t : ℝ} (hρ : 0 < ρ) (ha : ‖a‖ = 4 * ρ)
    (hx : x ∈ ball a (2 * ρ)) (ht : 1 / ρ ≤ t) : latticeRound (t • x) ≠ 0 := by
  intro h0
  have h1 := norm_lt_two_of_latticeRound_eq_zero h0
  have hxa : 2 * ρ < ‖x‖ := by
    have h2 := mem_ball_iff_norm.1 hx
    have h3 := norm_sub_norm_le a x
    have h4 := norm_sub_rev a x
    linarith
  have ht0 : 0 ≤ t := le_trans (one_div_pos.2 hρ).le ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at h1
  have h4 : 1 / ρ * (2 * ρ) = 2 := by
    rw [one_div, inv_mul_eq_div, mul_div_assoc, div_self hρ.ne', mul_one]
  have h5 : 1 / ρ * (2 * ρ) ≤ t * ‖x‖ := mul_le_mul ht hxa.le (by linarith) ht0
  linarith

theorem le_sqrt_of_ceil_le {nk : ℕ → ℕ} (hmono : StrictMono nk) {c : ℝ} (hc : 0 ≤ c) {k : ℕ}
    (hk : ⌈c ^ 2⌉₊ ≤ k) : c ≤ Real.sqrt (nk k) := by
  have h1 : c ^ 2 ≤ (nk k : ℝ) := by
    have := Nat.le_ceil (c ^ 2)
    have h2 : (⌈c ^ 2⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    have h3 : (k : ℝ) ≤ nk k := by exact_mod_cast hmono.id_le k
    linarith
  calc c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc).symm
    _ ≤ Real.sqrt (nk k) := Real.sqrt_le_sqrt h1

/-- The clipping is eventually inactive. -/
theorem clipLap_eventually_eq {η : Site 2 → ℤ} {ηmin : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * ((2 : ℕ) : ℤ) - 2) {nk : ℕ → ℕ} (hmono : StrictMono nk)
    {a : Rd 2} {ρ : ℝ} (hρ : 0 < ρ) (ha : ‖a‖ = 4 * ρ) {χ : Rd 2 → ℝ}
    (hχ0 : ∀ x, x ∉ ball a (2 * ρ) → χ x = 0) :
    ∀ᶠ k in atTop, ∀ x, clipLap χ (lapConst ηmin) (singleSourceOdometer η (nk k))
      (Real.sqrt (nk k)) x = χ x * (lap (singleSourceOdometer η (nk k))
        (latticeRound (Real.sqrt (nk k) • x)) : ℝ) := by
  filter_upwards [eventually_ge_atTop ⌈(1 / ρ) ^ 2⌉₊] with k hk x
  by_cases hx : x ∈ ball a (2 * ρ)
  · exact clipLap_eq (abs_lap_le_lapConst hη (nk k)
      (latticeRound_ne_zero hρ ha hx (le_sqrt_of_ceil_le hmono (one_div_pos.2 hρ).le hk)))
  · simp only [clipLap, hχ0 x hx, zero_mul]

/-- `B̄_{3ρ}(a)`, `|a| = 4ρ`, avoids the origin. -/
theorem ne_zero_of_mem_closedBall {a : Rd 2} {ρ : ℝ} (hρ : 0 < ρ) (ha : ‖a‖ = 4 * ρ) :
    ∀ x ∈ closedBall a (3 * ρ), x ≠ 0 := by
  intro x hx h0
  rw [h0, mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at hx
  linarith

/-- A function supported in `B̄_{2ρ}(a)` vanishes within `ρ` of any point outside `B̄_{3ρ}(a)`. -/
theorem eq_zero_of_far {a : Rd 2} {ρ : ℝ} {g : Rd 2 → ℝ}
    (hgs : tsupport g ⊆ closedBall a (2 * ρ)) :
    ∀ x, x ∉ closedBall a (3 * ρ) → ∀ y, dist x y ≤ ρ → g y = 0 := by
  intro x hx y hy
  refine image_eq_zero_of_notMem_tsupport fun hy' => hx ?_
  have h1 := hgs hy'
  rw [mem_closedBall] at h1 ⊢
  have := dist_triangle x y a
  linarith

/-- The localized test functions: `∫ f_k φ → ∫ u Δ(χφ)`. -/
theorem tendsto_integral_clipLap {η : Site 2 → ℤ} {ηmin : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * ((2 : ℕ) : ℤ) - 2) {nk : ℕ → ℕ} (hmono : StrictMono nk)
    {u : Rd 2 → ℝ}
    (hconv : TendstoLocallyUniformlyOn
      (fun k => rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k)) u atTop
      {x : Rd 2 | x ≠ 0})
    {a : Rd 2} {ρ : ℝ} (hρ : 0 < ρ) (ha : ‖a‖ = 4 * ρ) {χ : Rd 2 → ℝ}
    (hχc : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχts : tsupport χ ⊆ closedBall a (2 * ρ)) (hχ0 : ∀ x, x ∉ ball a (2 * ρ) → χ x = 0)
    {φ : Rd 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Tendsto (fun k => ∫ x, clipLap χ (lapConst ηmin) (singleSourceOdometer η (nk k))
      (Real.sqrt (nk k)) x * φ x) atTop
      (𝓝 (∫ x, u x * Matrix.trace (hessian (fun y => χ y * φ y) x))) := by
  have hg : ContDiff ℝ 2 (fun y => χ y * φ y) :=
    (hχc.mul hφ).of_le (WithTop.coe_le_coe.2 le_top)
  have hgc : HasCompactSupport (fun y => χ y * φ y) := hχcs.mul_right
  have hgs : tsupport (fun y => χ y * φ y) ⊆ closedBall a (2 * ρ) :=
    (tsupport_mul_subset_left).trans hχts
  refine (tendsto_integral_lap_ss (fun x => (hη x).2) hmono hconv hg hgc hρ
    (isCompact_closedBall a (3 * ρ)) (ne_zero_of_mem_closedBall hρ ha)
    (hgs.trans (closedBall_subset_closedBall (by linarith))) (eq_zero_of_far hgs)).congr' ?_
  filter_upwards [clipLap_eventually_eq hη hmono hρ ha hχ0] with k hk
  congr 1
  funext x
  rw [hk x]
  ring

/-- A bounded measurable representative of an a.e. bounded function. -/
theorem exists_bounded_rep {s : Rd 2 → ℝ} (hs : AEStronglyMeasurable s volume) {C : ℝ}
    (hC : 0 ≤ C) (hle : ∀ᵐ x ∂volume, s x ≤ C) (hge : ∀ᵐ x ∂volume, -s x ≤ C) :
    ∃ s' : Rd 2 → ℝ, Measurable s' ∧ (∀ x, |s' x| ≤ C) ∧ s' =ᵐ[volume] s := by
  refine ⟨fun x => max (-C) (min C (hs.mk s x)),
    measurable_const.max (measurable_const.min hs.stronglyMeasurable_mk.measurable),
    fun x => abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩, ?_⟩
  filter_upwards [hs.ae_eq_mk, hle, hge] with x h1 h2 h3
  show max (-C) (min C (hs.mk s x)) = s x
  rw [← h1, min_eq_right h2, max_eq_right (by linarith)]

/-- ** near one point.** -/
theorem weakLaplace_near {η : Site 2 → ℤ} {ηmin : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * ((2 : ℕ) : ℤ) - 2) {u : Rd 2 → ℝ}
    (hu : IsSSSubseqLimit η u) {a : Rd 2} (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ {x | x ≠ 0} ∧ ∃ (s : Rd 2 → ℝ) (C : ℝ), Measurable s ∧
      (∀ x, |s x| ≤ C) ∧ IsWeakSolutionLaplace (ball a r) u s := by
  obtain ⟨nk, hmono, hconv⟩ := hu
  set ρ := ‖a‖ / 4 with hρ_def
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hρ : 0 < ρ := by rw [hρ_def]; linarith
  have ha4 : ‖a‖ = 4 * ρ := by rw [hρ_def]; ring
  -- the bump
  let χ : ContDiffBump a := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  have hχ1 : ∀ x ∈ closedBall a ρ, χ x = 1 := fun x hx => χ.one_of_mem_closedBall hx
  have hχ0 : ∀ x, x ∉ ball a (2 * ρ) → χ x = 0 := fun x hx =>
    Function.notMem_support.1 (by rw [χ.support_eq]; exact hx)
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [χ.nonneg (x := x)], χ.le_one⟩
  have hχts : tsupport χ ⊆ closedBall a (2 * ρ) := χ.tsupport_eq.le
  set C : ℝ := lapConst ηmin
  have hC : 0 ≤ C := lapConst_nonneg ηmin
  -- the localized test functions
  have hloc := fun (φ : Rd 2 → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) =>
    tendsto_integral_clipLap hη hmono hconv hρ ha4 χ.contDiff χ.hasCompactSupport hχts hχ0 hφ
  -- the weak-* limit
  obtain ⟨s, hsLp, hweak⟩ := weakStarRepresentation 2
    (fun k => clipLap χ C (singleSourceOdometer η (nk k)) (Real.sqrt (nk k))) C (ball a (2 * ρ))
    isBounded_ball (fun k => measurable_clipLap χ.continuous C _ _)
    (fun k x => abs_clipLap_le hχb hC _ _ x)
    (Eventually.of_forall fun k x hx => by simp only [clipLap, hχ0 x hx, zero_mul])
    (fun φ hφ _ => ⟨_, hloc φ hφ⟩)
  -- `|s| ≤ C` a.e.
  have hmeasf : ∀ k, Measurable
      (clipLap χ C (singleSourceOdometer η (nk k)) (Real.sqrt (nk k))) :=
    fun k => measurable_clipLap χ.continuous C _ _
  have hle : ∀ᵐ x ∂volume, s x ≤ C :=
    hweak.ae_le hsLp hmeasf (fun k x => abs_clipLap_le hχb hC _ _ x)
      (Eventually.of_forall fun k x => (abs_le.1 (abs_clipLap_le hχb hC _ _ x)).2)
  have hweak' : WeakStarTendsto
      (fun k x => -clipLap χ C (singleSourceOdometer η (nk k)) (Real.sqrt (nk k)) x)
      (fun x => -s x) := fun g hg => by
    have := (hweak g hg).neg
    simpa only [neg_mul, integral_neg] using this
  have hge : ∀ᵐ x ∂volume, -s x ≤ C :=
    hweak'.ae_le hsLp.neg (fun k => (hmeasf k).neg)
      (fun k x => (abs_neg _).trans_le (abs_clipLap_le hχb hC _ _ x))
      (Eventually.of_forall fun k x => neg_le.2 (abs_le.1 (abs_clipLap_le hχb hC _ _ x)).1)
  -- a bounded measurable representative
  obtain ⟨s', hs'm, hs'b, hs'e⟩ := exists_bounded_rep hsLp.aestronglyMeasurable hC hle hge
  refine ⟨ρ, hρ, fun x hx => ?_, s', C, hs'm, hs'b, fun φ hφ hφc hφs => ?_⟩
  · simp only [Set.mem_ofPred_eq]
    rintro rfl
    rw [mem_ball, dist_eq_norm, zero_sub, norm_neg] at hx
    linarith
  · have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hχφ : (fun y => χ y * φ y) = φ := by
      funext y
      by_cases hy : y ∈ tsupport φ
      · rw [hχ1 y (ball_subset_closedBall (hφs hy)), one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    have h1 := hloc φ hφ
    rw [hχφ] at h1
    have h2 := hweak φ hφi
    rw [tendsto_nhds_unique h1 h2]
    exact integral_congr_ae (hs'e.mono fun x hx => by
      show s x * φ x = s' x * φ x
      rw [hx])

/-- Almost surely every subsequential limit of the rescaled single-source odometers has a
locally bounded weak Laplacian off the origin. -/
theorem ssLimitWeakLaplace : SSLimitWeakLaplaceD2Stmt := by
  intro E hE
  filter_upwards [ae_all_iff.2 E.bounded] with η hη u hu a ha
  exact weakLaplace_near (fun x => ⟨(hη x).1, hE ▸ (hη x).2⟩) hu ha

end SingleSourceD2

end RandomSandpile

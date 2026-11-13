import RandomSandpile.Proofs.Sec7.MainTheoremSandpile
import RandomSandpile.Proofs.Sec7.DivisibleHomogenize
import RandomSandpile.Proofs.Sec7.MainTheoremWeakStar

/-!
# Theorem 1.1, step: the rescaled environment converges weakly-* to `E η(0) 𝟙_W`

Elementary ingredients of `EnvWeakStarStmt`.

* `volume_frontier_of_isLipschitzDomain`: the boundary of a bounded Lipschitz domain is Lebesgue
  null. Near a boundary point the boundary lies in the graph `{⟨y - x₀, e⟩ = γ((y - x₀)')}` of a
  Lipschitz function over `e^⊥`; the translates of a bounded piece of the graph by `s e`,
  `s ∈ (0, 1]`, are pairwise disjoint (each line in direction `e` meets the graph once), have equal
  measure and lie in a fixed ball, so the piece is null; `measure_null_of_locally_null` globalises.
* `volume_latticeRound_eq`, `integral_latticeRound_finsum`: the cells
  `{x : [n x] = y} = ∏_i [y_i / n, (y_i + 1) / n)` have volume `n^{-d}`, so
  `∫ F([n x]) dx = n^{-d} Σ_y F(y)` for finitely supported `F`.
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology
open scoped ENNReal

namespace RandomSandpile

variable {d : ℕ}

/-! ### The boundary of a Lipschitz domain is null -/

/-- The orthogonal projection onto `e^⊥` does not see translations in direction `e`. -/
theorem proj_add_smul {e : Rd d} (he : ‖e‖ = 1) (z : Rd d) (c : ℝ) :
    (z + c • e) - inner ℝ (z + c • e) e • e = z - inner ℝ z e • e := by
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  rw [inner_add_left, inner_smul_left, hee]
  simp only [conj_trivial, mul_one, add_smul]
  abel

/-- A bounded piece of a Lipschitz graph in direction `e` is null. -/
theorem volume_lipschitzGraph_ball_eq_zero {e : Rd d} (he : ‖e‖ = 1) {γ : Rd d → ℝ}
    (hγ : Continuous γ) (x₀ : Rd d) (r : ℝ) :
    volume {y ∈ Metric.ball x₀ r |
      γ ((y - x₀) - inner ℝ (y - x₀) e • e) = inner ℝ (y - x₀) e} = 0 := by
  set G := {y ∈ Metric.ball x₀ r |
    γ ((y - x₀) - inner ℝ (y - x₀) e • e) = inner ℝ (y - x₀) e} with hG
  have hGm : MeasurableSet G := by
    refine Metric.isOpen_ball.measurableSet.inter (isClosed_eq ?_ ?_).measurableSet
    · exact hγ.comp (by fun_prop)
    · fun_prop
  -- the translates `G + s_k e`, `s_k = 1 / (k + 1)`
  set s : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hs
  set T : ℕ → Set (Rd d) := fun k => (fun y => y + -(s k • e)) ⁻¹' G with hT
  have hTm : ∀ k, MeasurableSet (T k) := fun k => hGm.preimage (measurable_add_const _)
  have hTvol : ∀ k, volume (T k) = volume G := fun k => measure_preimage_add_right _ _ _
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro k l hkl
    refine Set.disjoint_left.2 fun y hyk hyl => hkl ?_
    simp only [hT, Set.mem_preimage, hG, Set.mem_ofPred_eq] at hyk hyl
    -- the two points of `G` differ by `(s l - s k) e`
    have hproj : (y + -(s l • e) - x₀) - inner ℝ (y + -(s l • e) - x₀) e • e =
        (y + -(s k • e) - x₀) - inner ℝ (y + -(s k • e) - x₀) e • e := by
      have := proj_add_smul he (y + -(s k • e) - x₀) (s k - s l)
      rw [show y + -(s k • e) - x₀ + (s k - s l) • e = y + -(s l • e) - x₀ by
        rw [sub_smul]; abel] at this
      exact this
    have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
    have h1 := hyk.2
    have h2 := hyl.2
    rw [hproj] at h2
    have : inner ℝ (y + -(s l • e) - x₀) e = inner ℝ (y + -(s k • e) - x₀) e + (s k - s l) := by
      rw [show y + -(s l • e) - x₀ = (y + -(s k • e) - x₀) + (s k - s l) • e by
        rw [sub_smul]; abel, inner_add_left, inner_smul_left, hee]
      simp
    have hsk : s k = s l := by linarith
    simp only [hs] at hsk
    have : (k : ℝ) + 1 = (l : ℝ) + 1 := by
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hl : (0 : ℝ) < (l : ℝ) + 1 := by positivity
      field_simp at hsk
      linarith
    exact_mod_cast (by linarith : (k : ℝ) = l)
  have hsub : (⋃ k, T k) ⊆ Metric.ball x₀ (r + 1) := by
    refine Set.iUnion_subset fun k y hy => ?_
    simp only [hT, Set.mem_preimage, hG, Set.mem_ofPred_eq, Metric.mem_ball] at hy ⊢
    have hsk : |s k| ≤ 1 := by
      rw [hs, abs_of_pos (by positivity)]
      rw [div_le_one (by positivity)]
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    calc dist y x₀ ≤ dist y (y + -(s k • e)) + dist (y + -(s k • e)) x₀ := dist_triangle _ _ _
      _ < 1 + r := by
          have : dist y (y + -(s k • e)) ≤ 1 := by
            rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_neg, norm_smul,
              Real.norm_eq_abs, he, mul_one]
            exact hsk
          linarith [hy.1]
      _ = r + 1 := by ring
  have hfin : volume (⋃ k, T k) < ⊤ :=
    (measure_mono hsub).trans_lt measure_ball_lt_top
  rw [measure_iUnion hdisj hTm] at hfin
  simp only [hTvol] at hfin
  by_contra h0
  rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at hfin
  exact lt_irrefl _ hfin

/-- **The boundary of a bounded Lipschitz domain is Lebesgue null.** -/
theorem volume_frontier_of_isLipschitzDomain {W : Set (Rd d)} (hW : IsLipschitzDomain W) :
    volume (frontier W) = 0 := by
  refine measure_null_of_locally_null _ fun x₀ hx₀ => ?_
  obtain ⟨r, hr, e, he, L, γ, hγ, hloc⟩ := hW.2.2.2 x₀ hx₀
  refine ⟨frontier W ∩ Metric.ball x₀ r, inter_mem_nhdsWithin _ (Metric.ball_mem_nhds x₀ hr),
    measure_mono_null ?_ (volume_lipschitzGraph_ball_eq_zero he hγ.continuous x₀ r)⟩
  rintro y ⟨hyF, hyB⟩
  refine ⟨hyB, le_antisymm ?_ ?_⟩
  · -- `y ∈ closure W`: `⟨y - x₀, e⟩ ≥ γ(...)` by continuity
    by_contra hlt
    have hlt' : inner ℝ (y - x₀) e < γ ((y - x₀) - inner ℝ (y - x₀) e • e) := not_le.1 hlt
    have hcont : Continuous fun w : Rd d =>
        γ ((w - x₀) - inner ℝ (w - x₀) e • e) - inner ℝ (w - x₀) e :=
      (hγ.continuous.comp (by fun_prop)).sub (by fun_prop)
    have hopen : IsOpen ({w | 0 < γ ((w - x₀) - inner ℝ (w - x₀) e • e) -
        inner ℝ (w - x₀) e} ∩ Metric.ball x₀ r) :=
      (isOpen_lt continuous_const hcont).inter Metric.isOpen_ball
    obtain ⟨w, hw, hwW⟩ := mem_closure_iff.1 (frontier_subset_closure hyF) _ hopen
      ⟨by simp only [Set.mem_ofPred_eq]; linarith, hyB⟩
    have := (hloc w hw.2).1 hwW
    have hw1 : 0 < γ ((w - x₀) - inner ℝ (w - x₀) e • e) - inner ℝ (w - x₀) e := hw.1
    linarith
  · -- `y ∉ W` (`W` is open)
    by_contra hlt
    have hyW : y ∈ W := (hloc y hyB).2 (not_le.1 hlt)
    exact (hW.2.1.frontier_eq ▸ hyF).2 hyW

/-! ### Cells of the rescaled lattice -/

theorem latticeRound_eq_iff {n : ℕ} (hn : n ≠ 0) (x : Rd d) (y : Site d) :
    latticeRound ((n : ℝ) • x) = y ↔
      ∀ i, x i ∈ Set.Ico ((y i : ℝ) / n) (((y i : ℝ) + 1) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [latticeRound, funext_iff, Int.floor_eq_iff, Set.mem_Ico, PiLp.smul_apply,
    smul_eq_mul, div_le_iff₀ hn', lt_div_iff₀ hn', mul_comm (x _)]

theorem volume_latticeRound_eq {n : ℕ} (hn : n ≠ 0) (y : Site d) :
    volume {x : Rd d | latticeRound ((n : ℝ) • x) = y} = ENNReal.ofReal (((n : ℝ)⁻¹) ^ d) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hset : {x : Rd d | latticeRound ((n : ℝ) • x) = y} =
      WithLp.ofLp ⁻¹' Set.pi Set.univ fun i => Set.Ico ((y i : ℝ) / n) (((y i : ℝ) + 1) / n) := by
    ext x
    simp only [Set.mem_ofPred_eq, latticeRound_eq_iff hn, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Ico]
  have hlen : ∀ i, ((y i : ℝ) + 1) / n - (y i : ℝ) / n = (n : ℝ)⁻¹ := fun i => by
    rw [← sub_div, add_sub_cancel_left, one_div]
  simp only [hlen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

theorem measurableSet_latticeRound_eq (n : ℕ) (y : Site d) :
    MeasurableSet {x : Rd d | latticeRound ((n : ℝ) • x) = y} :=
  (measurableSet_singleton y).preimage (measurable_latticeRound.comp (measurable_const_smul _))

/-- `∫ F([n x]) dx = n^{-d} Σ_{y ∈ S} F(y)` for `F` supported in a finite set `S`. -/
theorem integral_latticeRound_finsum {n : ℕ} (hn : n ≠ 0) (F : Site d → ℝ) (S : Finset (Site d))
    (hS : ∀ y, y ∉ S → F y = 0) :
    ∫ x : Rd d, F (latticeRound ((n : ℝ) • x)) = ((n : ℝ)⁻¹) ^ d * ∑ y ∈ S, F y := by
  have hpt : ∀ x : Rd d, F (latticeRound ((n : ℝ) • x)) =
      ∑ y ∈ S, {x : Rd d | latticeRound ((n : ℝ) • x) = y}.indicator (fun _ => F y) x := by
    intro x
    by_cases hx : latticeRound ((n : ℝ) • x) ∈ S
    · rw [Finset.sum_eq_single_of_mem _ hx]
      · rw [Set.indicator_of_mem (by rfl)]
      · intro b _ hb
        rw [Set.indicator_of_notMem]
        exact fun h => hb (h.symm)
    · rw [hS _ hx, Finset.sum_eq_zero]
      intro b hb
      rw [Set.indicator_of_notMem]
      intro h
      have h' : latticeRound ((n : ℝ) • x) = b := h
      exact hx (h' ▸ hb)
  have hfin : ∀ y, volume {x : Rd d | latticeRound ((n : ℝ) • x) = y} < ⊤ := fun y => by
    rw [volume_latticeRound_eq hn]; exact ENNReal.ofReal_lt_top
  simp_rw [hpt]
  rw [integral_finsetSum _ fun y _ =>
    (integrable_indicator_iff (measurableSet_latticeRound_eq n y)).2
      (integrableOn_const (hfin y).ne)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_indicator_const _ (measurableSet_latticeRound_eq n y), measureReal_def,
    volume_latticeRound_eq hn, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_comm]

/-! ### Lattice boxes approximate dyadic cells in `L¹` -/

/-- For `t ∉ {a, b}`, eventually `⌈na⌉ ≤ ⌊nt⌋ < ⌈nb⌉` exactly when `a ≤ t < b`. -/
theorem eventually_ceil_le_floor_iff {a b t : ℝ} (ha : t ≠ a) (hb : t ≠ b) :
    ∀ᶠ n : ℕ in atTop, (⌈(n : ℝ) * a⌉ ≤ ⌊(n : ℝ) * t⌋ ∧ ⌊(n : ℝ) * t⌋ < ⌈(n : ℝ) * b⌉) ↔
      (a ≤ t ∧ t < b) := by
  have h1 : ∀ᶠ n : ℕ in atTop, (⌈(n : ℝ) * a⌉ ≤ ⌊(n : ℝ) * t⌋ ↔ a ≤ t) := by
    rcases lt_or_gt_of_ne ha with hta | hat
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      refine ⟨fun h => ?_, fun h => absurd h (not_le.2 hta)⟩
      have h2 := (Int.ceil_le.1 h).trans (Int.floor_le _)
      exact absurd (le_of_mul_le_mul_left h2 hn') (not_le.2 hta)
    · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (t - a))
      filter_upwards [eventually_ge_atTop N] with n hn
      refine ⟨fun _ => hat.le, fun _ => Int.ceil_le.2 ?_⟩
      have hn' : (1 / (t - a) : ℝ) < n := hN.trans_le (by exact_mod_cast hn)
      have hta : 0 < t - a := by linarith
      have : 1 < (n : ℝ) * (t - a) := by
        rw [div_lt_iff₀ hta] at hn'; linarith
      have := Int.sub_one_lt_floor ((n : ℝ) * t)
      linarith
  have h2 : ∀ᶠ n : ℕ in atTop, (⌊(n : ℝ) * t⌋ < ⌈(n : ℝ) * b⌉ ↔ t < b) := by
    rcases lt_or_gt_of_ne hb with htb | hbt
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      refine ⟨fun _ => htb, fun _ => ?_⟩
      have : (⌊(n : ℝ) * t⌋ : ℝ) < ⌈(n : ℝ) * b⌉ :=
        (Int.floor_le _).trans_lt ((mul_lt_mul_of_pos_left htb hn').trans_le (Int.le_ceil _))
      exact_mod_cast this
    · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (t - b))
      filter_upwards [eventually_ge_atTop N] with n hn
      refine ⟨fun h => ?_, fun h => absurd h (not_lt.2 hbt.le)⟩
      exfalso
      have hn' : (1 / (t - b) : ℝ) < n := hN.trans_le (by exact_mod_cast hn)
      have htb : 0 < t - b := by linarith
      have : 1 < (n : ℝ) * (t - b) := by
        rw [div_lt_iff₀ htb] at hn'; linarith
      have h3 := Int.sub_one_lt_floor ((n : ℝ) * t)
      have h4 : (⌈(n : ℝ) * b⌉ : ℝ) < (n : ℝ) * b + 1 := Int.ceil_lt_add_one _
      have h5 : (⌊(n : ℝ) * t⌋ : ℝ) + 1 ≤ ⌈(n : ℝ) * b⌉ := by exact_mod_cast h
      linarith
  filter_upwards [h1, h2] with n hn1 hn2
  rw [hn1, hn2]

theorem volume_coord_eq (i : Fin d) (c : ℝ) : volume {x : Rd d | x i = c} = 0 := by
  have : {x : Rd d | x i = c} = WithLp.ofLp ⁻¹' {f : Fin d → ℝ | f i = c} := rfl
  rw [this, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).nullMeasurableSet, volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i c

/-- The dyadic cell `D_{j,k} = {x : [2^j x] = k} = ∏_i [k_i 2^{-j}, (k_i + 1) 2^{-j})`. -/
def dyadicCell (j : ℕ) (k : Site d) : Set (Rd d) :=
  {x : Rd d | latticeRound (((2 ^ j : ℕ) : ℝ) • x) = k}

theorem mem_dyadicCell {j : ℕ} {k : Site d} {x : Rd d} :
    x ∈ dyadicCell j k ↔ ∀ i, (k i : ℝ) / 2 ^ j ≤ x i ∧ x i < ((k i : ℝ) + 1) / 2 ^ j := by
  rw [dyadicCell, Set.mem_ofPred_eq, latticeRound_eq_iff (by positivity)]
  push_cast
  rfl

theorem mem_dyadicCube_iff {j : ℕ} {k : Site d} {n : ℕ} {y : Site d} :
    y ∈ dyadicCube j k n ↔ ∀ i, ⌈(n : ℝ) * ((k i : ℝ) / 2 ^ j)⌉ ≤ y i ∧
      y i < ⌈(n : ℝ) * (((k i : ℝ) + 1) / 2 ^ j)⌉ := by
  simp only [dyadicCube, mem_rectBox, Finset.mem_Ico]

/-- The lattice boxes `𝟙{[nx] ∈ Q_{j,k}(n)}` converge to `𝟙_{D_{j,k}}` in `L¹`. -/
theorem tendsto_integral_abs_dyadic (j : ℕ) (k : Site d) :
    Tendsto (fun n : ℕ => ∫ x : Rd d,
      |(↑(dyadicCube j k n) : Set (Site d)).indicator (fun _ => (1 : ℝ))
          (latticeRound ((n : ℝ) • x)) - (dyadicCell j k).indicator (fun _ => (1 : ℝ)) x|)
      atTop (𝓝 0) := by
  set D' : Set (Rd d) := WithLp.ofLp ⁻¹' Set.pi Set.univ
    (fun i => Set.Icc ((k i : ℝ) / 2 ^ j - 1) (((k i : ℝ) + 1) / 2 ^ j + 1)) with hD'
  have hD'm : MeasurableSet D' :=
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).preimage
      (PiLp.volume_preserving_ofLp (Fin d)).measurable
  have hD'fin : volume D' < ⊤ := by
    rw [hD', (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet, volume_pi_pi]
    exact ENNReal.prod_lt_top fun i _ => by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hfl : ∀ (n : ℕ) (x : Rd d) (i : Fin d),
      latticeRound ((n : ℝ) • x) i = ⌊(n : ℝ) * x i⌋ := fun n x i => by simp [latticeRound]
  rw [← integral_zero (Rd d) ℝ]
  refine tendsto_integral_filter_of_dominated_convergence (D'.indicator fun _ => (1 : ℝ))
    (Eventually.of_forall fun n => ?_) ?_
    ((integrable_indicator_iff hD'm).2 (integrableOn_const hD'fin.ne)) ?_
  · have hm1 : Measurable fun x : Rd d => (↑(dyadicCube j k n) : Set (Site d)).indicator
        (fun _ => (1 : ℝ)) (latticeRound ((n : ℝ) • x)) :=
      (measurable_of_countable fun y : Site d => (↑(dyadicCube j k n) : Set (Site d)).indicator
        (fun _ => (1 : ℝ)) y).comp (measurable_latticeRound.comp (measurable_const_smul (n : ℝ)))
    have hm2 : Measurable ((dyadicCell j k).indicator fun _ => (1 : ℝ)) :=
      measurable_const.indicator (measurableSet_latticeRound_eq (2 ^ j) k)
    exact (hm1.sub hm2).abs.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with n hn
    refine ae_of_all _ fun x => ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, abs_abs]
    by_cases hx : x ∈ D'
    · rw [Set.indicator_of_mem hx]
      by_cases h1 : latticeRound ((n : ℝ) • x) ∈ (↑(dyadicCube j k n) : Set (Site d)) <;>
        by_cases h2 : x ∈ dyadicCell j k <;> simp [h1, h2]
    · rw [Set.indicator_of_notMem hx]
      have h2 : x ∉ dyadicCell j k := fun h => hx (by
        rw [mem_dyadicCell] at h
        simp only [hD', Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
        intro i
        exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩)
      have h1 : latticeRound ((n : ℝ) • x) ∉ (↑(dyadicCube j k n) : Set (Site d)) :=
        fun h => hx (by
        rw [Finset.mem_coe, mem_dyadicCube_iff] at h
        simp only [hD', Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
        intro i
        obtain ⟨hi1, hi2⟩ := h i
        rw [hfl] at hi1 hi2
        have e1 : (n : ℝ) * ((k i : ℝ) / 2 ^ j) ≤ (n : ℝ) * x i :=
          (Int.ceil_le.1 hi1).trans (Int.floor_le _)
        have e2 : ((⌊(n : ℝ) * x i⌋ : ℤ) : ℝ) + 1 ≤ (⌈(n : ℝ) * (((k i : ℝ) + 1) / 2 ^ j)⌉ : ℝ) := by
          have := Int.add_one_le_iff.2 hi2
          exact_mod_cast this
        have e3 := Int.ceil_lt_add_one ((n : ℝ) * (((k i : ℝ) + 1) / 2 ^ j))
        have e4 := Int.sub_one_lt_floor ((n : ℝ) * x i)
        have ha : (k i : ℝ) / 2 ^ j ≤ x i := le_of_mul_le_mul_left e1 hn'
        refine ⟨by linarith, ?_⟩
        have h5 : (n : ℝ) * x i < (n : ℝ) * (((k i : ℝ) + 1) / 2 ^ j) + 1 := by linarith
        have h6 : (n : ℝ) * (((k i : ℝ) + 1) / 2 ^ j) + 1 ≤
            (n : ℝ) * (((k i : ℝ) + 1) / 2 ^ j + 1) := by nlinarith
        exact (lt_of_mul_lt_mul_left (h5.trans_le h6) hn'.le).le)
      simp [h1, h2]
  · -- a.e. pointwise convergence off the boundary hyperplanes
    have hnull : volume (⋃ i, ({x : Rd d | x i = (k i : ℝ) / 2 ^ j} ∪
        {x : Rd d | x i = ((k i : ℝ) + 1) / 2 ^ j})) = 0 :=
      measure_iUnion_null fun i => measure_union_null (volume_coord_eq i _) (volume_coord_eq i _)
    refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun x hx => ?_
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or] at hx
    have hev : ∀ᶠ n : ℕ in atTop, ∀ i, (⌈(n : ℝ) * ((k i : ℝ) / 2 ^ j)⌉ ≤ ⌊(n : ℝ) * x i⌋ ∧
        ⌊(n : ℝ) * x i⌋ < ⌈(n : ℝ) * (((k i : ℝ) + 1) / 2 ^ j)⌉ ↔
          ((k i : ℝ) / 2 ^ j ≤ x i ∧ x i < ((k i : ℝ) + 1) / 2 ^ j)) :=
      eventually_all.2 fun i => eventually_ceil_le_floor_iff (hx i).1 (hx i).2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    have hiff : latticeRound ((n : ℝ) • x) ∈ (↑(dyadicCube j k n) : Set (Site d)) ↔
        x ∈ dyadicCell j k := by
      rw [Finset.mem_coe, mem_dyadicCube_iff, mem_dyadicCell]
      refine forall_congr' fun i => ?_
      rw [hfl]
      exact hn i
    by_cases h2 : x ∈ dyadicCell j k
    · simp [h2, hiff.2 h2]
    · simp [h2, mt hiff.1 h2]

/-! ### The rescaled environment on dyadic cells -/

theorem finite_norm_toE_le (R : ℝ) : {k : Site d | ‖toE k‖ ≤ R}.Finite := by
  refine (Set.finite_Icc (fun _ : Fin d => -⌈R⌉) fun _ => ⌈R⌉).subset fun k hk => ?_
  have hk' : ‖toE k‖ ≤ R := hk
  have hb : ∀ i, |(k i : ℝ)| ≤ (⌈R⌉ : ℝ) := fun i => by
    have h1 : |(k i : ℝ)| ≤ ‖toE k‖ := by
      simpa [toE, Real.norm_eq_abs] using PiLp.norm_apply_le (toE k) i
    linarith [Int.le_ceil R]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.1 (hb i)).1; exact_mod_cast this
  · have := (abs_le.1 (hb i)).2; exact_mod_cast this

theorem latticeRound_finsum_eq (n : ℕ) (F : Site d → ℝ) (S : Finset (Site d))
    (hS : ∀ y, y ∉ S → F y = 0) (x : Rd d) :
    F (latticeRound ((n : ℝ) • x)) =
      ∑ y ∈ S, F y * {x : Rd d | latticeRound ((n : ℝ) • x) = y}.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : latticeRound ((n : ℝ) • x) ∈ S
  · rw [Finset.sum_eq_single_of_mem _ hx]
    · rw [Set.indicator_of_mem (by rfl), mul_one]
    · intro b _ hb
      rw [Set.indicator_of_notMem, mul_zero]
      exact fun h => hb (h.symm)
  · rw [hS _ hx, Finset.sum_eq_zero]
    intro b hb
    rw [Set.indicator_of_notMem, mul_zero]
    intro h
    have h' : latticeRound ((n : ℝ) • x) = b := h
    exact hx (h' ▸ hb)

theorem integrable_latticeRound_finsum {n : ℕ} (hn : n ≠ 0) (F : Site d → ℝ)
    (S : Finset (Site d)) (hS : ∀ y, y ∉ S → F y = 0) :
    Integrable (fun x : Rd d => F (latticeRound ((n : ℝ) • x))) volume := by
  have hfin : ∀ y, volume {x : Rd d | latticeRound ((n : ℝ) • x) = y} < ⊤ := fun y => by
    rw [volume_latticeRound_eq hn]; exact ENNReal.ofReal_lt_top
  rw [show (fun x : Rd d => F (latticeRound ((n : ℝ) • x))) = fun x => ∑ y ∈ S, F y *
      {x : Rd d | latticeRound ((n : ℝ) • x) = y}.indicator (fun _ => (1 : ℝ)) x from
    funext (latticeRound_finsum_eq n F S hS)]
  exact integrable_finsetSum _ fun y _ =>
    ((integrable_indicator_iff (measurableSet_latticeRound_eq n y)).2
      (integrableOn_const (hfin y).ne)).const_mul _

theorem measurable_latticeRound_comp (n : ℕ) (F : Site d → ℝ) :
    Measurable fun x : Rd d => F (latticeRound ((n : ℝ) • x)) :=
  (measurable_of_countable F).comp (measurable_latticeRound.comp (measurable_const_smul _))

theorem measurableSet_dyadicCell (j : ℕ) (k : Site d) : MeasurableSet (dyadicCell j k) :=
  measurableSet_latticeRound_eq (2 ^ j) k

theorem volume_dyadicCell_lt_top (j : ℕ) (k : Site d) : volume (dyadicCell j k) < ⊤ := by
  rw [dyadicCell, volume_latticeRound_eq (by positivity)]
  exact ENNReal.ofReal_lt_top

/-- Ergodic averages over dyadic cubes give convergence against dyadic cells. -/
theorem tendsto_integral_env_dyadicCell {η : Site d → ℤ} {K m : ℝ}
    (hK : ∀ y, |(η y : ℝ)| ≤ K)
    (hcube : ∀ (j : ℕ) (k : Site d), Tendsto (fun N : ℕ =>
      (∑ y ∈ dyadicCube j k N, ((η y : ℝ) - m)) / (N : ℝ) ^ d) atTop (𝓝 0))
    (j : ℕ) (k : Site d) :
    Tendsto (fun n : ℕ => ∫ x : Rd d, (η (latticeRound ((n : ℝ) • x)) : ℝ) *
      (dyadicCell j k).indicator (fun _ => (1 : ℝ)) x) atTop
      (𝓝 (m * volume.real (dyadicCell j k))) := by
  set D := dyadicCell (d := d) j k with hD
  have hDi : Integrable (D.indicator fun _ => (1 : ℝ)) volume :=
    integrable_indicator_one (measurableSet_dyadicCell j k) (volume_dyadicCell_lt_top j k)
  set Q : ℕ → Set (Site d) := fun n => (↑(dyadicCube j k n) : Set (Site d)) with hQ
  set h : ℕ → Rd d → ℝ := fun n x => (Q n).indicator (fun _ => (1 : ℝ))
    (latticeRound ((n : ℝ) • x)) with hh
  have hL1 : Tendsto (fun n => ∫ x, |h n x - D.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0) :=
    tendsto_integral_abs_dyadic j k
  have hhi : ∀ n, n ≠ 0 → Integrable (h n) volume := fun n hn =>
    integrable_latticeRound_finsum hn _ (dyadicCube j k n) fun y hy => by
      simp [hQ, Set.indicator_of_notMem (show y ∉ (↑(dyadicCube j k n) : Set (Site d)) from hy)]
  have hmeas : ∀ n : ℕ, Measurable fun x : Rd d => (η (latticeRound ((n : ℝ) • x)) : ℝ) :=
    fun n => measurable_latticeRound_comp n fun y => (η y : ℝ)
  have hint : ∀ (n : ℕ) {u : Rd d → ℝ}, Integrable u volume →
      Integrable (fun x => (η (latticeRound ((n : ℝ) • x)) : ℝ) * u x) volume :=
    fun n u hu => integrable_mul_of_abs_le (hmeas n) (fun x => hK _) hu
  -- the box integrals
  have hA : ∀ n : ℕ, n ≠ 0 → ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * h n x =
      (∑ y ∈ dyadicCube j k n, ((η y : ℝ) - m)) / (n : ℝ) ^ d + m * ∫ x, h n x := by
    intro n hn
    have e1 := integral_latticeRound_finsum hn (fun y => (η y : ℝ) * (Q n).indicator
      (fun _ => (1 : ℝ)) y) (dyadicCube j k n) fun y hy => by
        simp [hQ, Set.indicator_of_notMem (show y ∉ (↑(dyadicCube j k n) : Set (Site d)) from hy)]
    have e2 := integral_latticeRound_finsum hn (fun y => (Q n).indicator
      (fun _ => (1 : ℝ)) y) (dyadicCube j k n) fun y hy => by
        simp [hQ, Set.indicator_of_notMem (show y ∉ (↑(dyadicCube j k n) : Set (Site d)) from hy)]
    simp only [hh]
    rw [e1, e2]
    have s1 : ∑ y ∈ dyadicCube j k n, (η y : ℝ) * (Q n).indicator (fun _ => (1 : ℝ)) y =
        ∑ y ∈ dyadicCube j k n, (η y : ℝ) := Finset.sum_congr rfl fun y hy => by
      rw [Set.indicator_of_mem (show y ∈ Q n from Finset.mem_coe.2 hy), mul_one]
    have s2 : ∑ y ∈ dyadicCube j k n, (Q n).indicator (fun _ => (1 : ℝ)) y =
        ∑ _y ∈ dyadicCube j k n, (1 : ℝ) := Finset.sum_congr rfl fun y hy => by
      rw [Set.indicator_of_mem (show y ∈ Q n from Finset.mem_coe.2 hy)]
    rw [s1, s2, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, inv_pow]
    have hn' : (n : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn)
    field_simp
    ring
  -- `∫ h_n → |D|`
  have hB : Tendsto (fun n => ∫ x, h n x) atTop (𝓝 (volume.real D)) := by
    have hDv : volume.real D = ∫ x, D.indicator (fun _ => (1 : ℝ)) x :=
      (integral_indicator_one (measurableSet_dyadicCell j k)).symm
    rw [hDv]
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' ?_ hL1)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [norm_norm, Real.norm_eq_abs, ← integral_sub (hhi n (by omega)) hDi]
    exact abs_integral_le_integral_abs
  -- the error against the cell
  have herr : Tendsto (fun n : ℕ => (∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) *
      D.indicator (fun _ => (1 : ℝ)) x) - ∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) * h n x)
      atTop (𝓝 0) := by
    have hK' : Tendsto (fun n : ℕ => K * ∫ x, |h n x - D.indicator (fun _ => (1 : ℝ)) x|) atTop
        (𝓝 0) := by simpa using hL1.const_mul K
    refine squeeze_zero_norm' ?_ hK'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs, ← integral_sub (hint n hDi) (hint n (hhi n (by omega)))]
    calc |∫ x, ((η (latticeRound ((n : ℝ) • x)) : ℝ) * D.indicator (fun _ => (1 : ℝ)) x -
          (η (latticeRound ((n : ℝ) • x)) : ℝ) * h n x)|
        = |∫ x, (η (latticeRound ((n : ℝ) • x)) : ℝ) *
            (D.indicator (fun _ => (1 : ℝ)) x - h n x)| := by
          congr 1; congr 1; funext x; ring
      _ ≤ K * ∫ x, |D.indicator (fun _ => (1 : ℝ)) x - h n x| :=
          abs_integral_mul_le_of_abs_le (hmeas n) (fun x => hK _) (hDi.sub (hhi n (by omega)))
      _ = K * ∫ x, |h n x - D.indicator (fun _ => (1 : ℝ)) x| := by
          congr 1; congr 1; funext x; rw [abs_sub_comm]
  have hmain := ((hcube j k).add (hB.const_mul m)).add herr
  rw [zero_add, add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← hA n (by omega)]
  ring

end RandomSandpile

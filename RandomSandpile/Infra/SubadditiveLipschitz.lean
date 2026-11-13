import RandomSandpile.Infra.SubadditiveCubes
import RandomSandpile.Draft.Section5
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# The subadditive ergodic theorem on bounded Lipschitz domains

Proposition 5.3 (`SubadditiveErgodicStmt`) from its version on half-open boxes with
rational corners (`SubadditiveRationalBoxesStmt`, `Infra/SubadditiveCubes.lean`), following
Dal Maso-Modica (*Nonlinear stochastic homogenization and ergodic theory*, J. reine angew. Math.
368 (1986), Proposition 1 and Remark 2) as used in Armstrong-Smart.

The reduction is deterministic: fix a configuration `η` in the full-measure event of the box
statement and put `g = f(·, η) ∈ 𝓜_C`.

* `IsLipschitzDomain.volume_frontier`: the frontier of a bounded Lipschitz domain is
  Lebesgue-null. Locally it lies in a level set `{⟨y - x₀, e⟩ = γ(P(y - x₀))}`; the translates
  of such a set by `t e` are pairwise disjoint and have the same measure, so it is null.
* Lattice counting (Mathlib's `ZLattice.covolume.tendsto_card_div_pow'`): for a bounded measurable
  `V` with null frontier, `|nV ∩ ℤ^d| / n^d → |V| / c`.
* Upper bound (`eventually_div_pow_lt`): an open `U ⊆ V` of full measure contains a finite union
  `K` of mesh cubes with `|U \ K| < ε`; subadditivity and `g ≤ C |·|` give
  `g(nV ∩ ℤ^d) ≤ ∑ g(nQ ∩ ℤ^d) + C |n(V \ K) ∩ ℤ^d|`, whence `limsup g(nV ∩ ℤ^d) / n^d ≤ a |V| / c`.
* Lower bound (`tendsto_discretize_of_boxes`): for a rational box `Q ⊇ W`,
  `g(nQ ∩ ℤ^d) ≤ g(nW ∩ ℤ^d) + g(n(Q \ W) ∩ ℤ^d)`, the box limit on `Q` and the upper bound on
  `Q \ W` (with `U = int Q \ cl W`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric Module LatticeProb
open scoped Pointwise ENNReal

namespace RandomSandpile

namespace SubadditiveLipschitz

variable {d : ℕ}

/-! ### Lipschitz domains have null frontier -/

/-- The height `⟨y - x₀, e⟩ - γ(P(y - x₀))` above the graph of `γ`, `P z = z - ⟨z, e⟩ e`. -/
def graphHeight (x₀ e : Rd d) (γ : Rd d → ℝ) (y : Rd d) : ℝ :=
  inner ℝ (y - x₀) e - γ ((y - x₀) - inner ℝ (y - x₀) e • e)

theorem graphHeight_sub_smul {x₀ e : Rd d} (he : ‖e‖ = 1) (γ : Rd d → ℝ) (y : Rd d) (t : ℝ) :
    graphHeight x₀ e γ (y - t • e) = graphHeight x₀ e γ y - t := by
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have h1 : inner ℝ (y - t • e - x₀) e = inner ℝ (y - x₀) e - t := by
    rw [show y - t • e - x₀ = (y - x₀) - t • e by abel, inner_sub_left, real_inner_smul_left, hee,
      mul_one]
  have h2 : (y - t • e - x₀) - inner ℝ (y - t • e - x₀) e • e =
      (y - x₀) - inner ℝ (y - x₀) e • e := by
    rw [h1, sub_smul]
    abel
  unfold graphHeight
  rw [h2, h1]
  ring

theorem continuous_graphHeight {x₀ e : Rd d} {γ : Rd d → ℝ} (hγ : Continuous γ) :
    Continuous (graphHeight x₀ e γ) := by
  unfold graphHeight
  have h1 : Continuous fun y : Rd d => inner ℝ (y - x₀) e :=
    (continuous_id.sub continuous_const).inner continuous_const
  exact h1.sub (hγ.comp ((continuous_id.sub continuous_const).sub (h1.smul continuous_const)))

/-- The zero level set of `graphHeight` (a Lipschitz graph over `e^⊥`) is null: its translates
by `t e`, `t = 1/(k+1)`, are pairwise disjoint and have equal measure, and inside a ball they all
lie in a slightly bigger ball. -/
theorem volume_graphHeight_eq_zero {x₀ e : Rd d} (he : ‖e‖ = 1) {γ : Rd d → ℝ}
    (hγ : Continuous γ) : volume (graphHeight x₀ e γ ⁻¹' {0}) = 0 := by
  set G := graphHeight x₀ e γ ⁻¹' {0}
  have hGm : MeasurableSet G :=
    (isClosed_singleton.preimage (continuous_graphHeight hγ)).measurableSet
  have hcover : G ⊆ ⋃ R : ℕ, G ∩ ball x₀ R := by
    intro y hy
    obtain ⟨R, hR⟩ := exists_nat_gt (dist y x₀)
    exact Set.mem_iUnion.2 ⟨R, hy, hR⟩
  refine measure_mono_null hcover (measure_iUnion_null fun R => ?_)
  set G0 := G ∩ ball x₀ R
  have hG0m : MeasurableSet G0 := hGm.inter measurableSet_ball
  set t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ht0 : ∀ k, 0 ≤ t k := fun k => by positivity
  have ht1 : ∀ k, t k ≤ 1 := fun k => by
    simp only [t]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set A : ℕ → Set (Rd d) := fun k => (fun y => y + -(t k • e)) ⁻¹' G0
  have hAm : ∀ k, MeasurableSet (A k) := fun k => (measurable_add_const _) hG0m
  have hAvol : ∀ k, volume (A k) = volume G0 := fun k => measure_preimage_add_right _ _ _
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro j k hjk
    refine Set.disjoint_left.2 fun y hyj hyk => hjk ?_
    have hj : graphHeight x₀ e γ (y + -(t j • e)) = 0 := hyj.1
    have hk : graphHeight x₀ e γ (y + -(t k • e)) = 0 := hyk.1
    rw [← sub_eq_add_neg, graphHeight_sub_smul he] at hj hk
    have htt : t j = t k := by linarith
    simp only [t] at htt
    rw [div_eq_div_iff (by positivity) (by positivity)] at htt
    have : (j : ℝ) = k := by linarith
    exact_mod_cast this
  have hsub : (⋃ k, A k) ⊆ ball x₀ (R + 1) := by
    refine Set.iUnion_subset fun k y hy => ?_
    have hy' : dist (y + -(t k • e)) x₀ < R := hy.2
    have hn : dist y (y + -(t k • e)) ≤ 1 := by
      rw [dist_self_add_right, norm_neg, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (ht0 k)]
      exact ht1 k
    rw [mem_ball]
    linarith [dist_triangle y (y + -(t k • e)) x₀]
  have hfin : volume (⋃ k, A k) ≠ ∞ := ((measure_mono hsub).trans_lt measure_ball_lt_top).ne
  rw [measure_iUnion hdisj hAm] at hfin
  simp only [hAvol] at hfin
  by_contra h0
  exact hfin (ENNReal.tsum_const_eq_top_of_ne_zero h0)

/-- **The frontier of a bounded Lipschitz domain is Lebesgue-null.** Near each frontier point it
lies in the graph of the Lipschitz function of the definition. -/
theorem _root_.RandomSandpile.IsLipschitzDomain.volume_frontier {W : Set (Rd d)} (hW : IsLipschitzDomain W) :
    volume (frontier W) = 0 := by
  obtain ⟨-, hWo, -, hloc⟩ := hW
  refine measure_null_of_locally_null _ fun x₀ hx₀ => ?_
  obtain ⟨r, hr, e, he, L, γ, hγ, hiff⟩ := hloc x₀ hx₀
  refine ⟨frontier W ∩ ball x₀ r, inter_mem_nhdsWithin _ (ball_mem_nhds x₀ hr), ?_⟩
  refine measure_mono_null ?_ (volume_graphHeight_eq_zero (x₀ := x₀) he hγ.continuous)
  rintro y ⟨hyf, hyb⟩
  show graphHeight x₀ e γ y = 0
  have hyW : y ∉ W := fun h => (hWo.frontier_eq ▸ hyf).2 h
  have h1 : graphHeight x₀ e γ y ≤ 0 := by
    have := not_lt.1 (mt (hiff y hyb).2 hyW)
    unfold graphHeight
    linarith
  have h2 : 0 ≤ graphHeight x₀ e γ y := by
    have hcl : y ∈ closure (ball x₀ r ∩ W) :=
      isOpen_ball.inter_closure ⟨hyb, frontier_subset_closure hyf⟩
    have hsub : ball x₀ r ∩ W ⊆ {z | 0 ≤ graphHeight x₀ e γ z} := by
      rintro z ⟨hzb, hzW⟩
      have := (hiff z hzb).1 hzW
      show 0 ≤ graphHeight x₀ e γ z
      unfold graphHeight
      linarith
    exact closure_minimal hsub
      (isClosed_le continuous_const (continuous_graphHeight hγ.continuous)) hcl
  linarith

/-! ### Boxes -/

theorem ratBox_subset_Icc (p q : Fin d → ℚ) :
    ratBox p q ⊆ (WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹'
      Set.Icc (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) :=
  fun _ hy => ⟨fun i => (hy i).1, fun i => (hy i).2.le⟩

theorem measurableSet_ratBox (p q : Fin d → ℚ) : MeasurableSet (ratBox p q) := by
  have : ratBox p q = (WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹'
      Set.univ.pi fun i => Set.Ico (p i : ℝ) (q i) := by
    ext y
    simp [ratBox, Set.mem_pi]
  rw [this]
  exact (PiLp.continuous_ofLp 2 _).measurable (MeasurableSet.univ_pi fun i => measurableSet_Ico)

theorem isBounded_ratBox (p q : Fin d → ℚ) : Bornology.IsBounded (ratBox p q) := by
  have hc : IsCompact ((WithLp.toLp 2 : (Fin d → ℝ) → Rd d) ''
      Set.Icc (fun i => (p i : ℝ)) (fun i => (q i : ℝ))) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  refine hc.isBounded.subset fun y hy => ⟨WithLp.ofLp y, ratBox_subset_Icc p q hy, ?_⟩
  simp

theorem volume_frontier_ratBox (p q : Fin d → ℚ) : volume (frontier (ratBox p q)) = 0 := by
  set Sc : Set (Fin d → ℝ) := Set.Icc (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
  set So : Set (Fin d → ℝ) := Set.univ.pi fun i => Set.Ioo (p i : ℝ) (q i)
  have hc : IsClosed ((WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹' Sc) :=
    isClosed_Icc.preimage (PiLp.continuous_ofLp 2 _)
  have ho : IsOpen ((WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹' So) :=
    (isOpen_set_pi Set.finite_univ fun i _ => isOpen_Ioo).preimage (PiLp.continuous_ofLp 2 _)
  have h1 : closure (ratBox p q) ⊆ (WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹' Sc :=
    closure_minimal (ratBox_subset_Icc p q) hc
  have h2 : (WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹' So ⊆ interior (ratBox p q) :=
    interior_maximal (fun y hy i => ⟨(hy i trivial).1.le, (hy i trivial).2⟩) ho
  have hpres := PiLp.volume_preserving_ofLp (ι := Fin d)
  have hSo : MeasurableSet So := MeasurableSet.univ_pi fun i => measurableSet_Ioo
  have hvc : volume ((WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹' Sc) = ∏ i, ENNReal.ofReal (q i - p i) := by
    rw [hpres.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  have hvo : volume ((WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹' So) = ∏ i, ENNReal.ofReal (q i - p i) := by
    rw [hpres.measure_preimage hSo.nullMeasurableSet, Real.volume_pi_Ioo]
  have hsub : (WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹' So ⊆ (WithLp.ofLp : Rd d → Fin d → ℝ) ⁻¹' Sc :=
    fun _ hy => ⟨fun i => (hy i trivial).1.le, fun i => (hy i trivial).2.le⟩
  refine measure_mono_null (Set.sdiff_subset_sdiff h1 h2) ?_
  rw [measure_sdiff hsub ((PiLp.continuous_ofLp 2 _).measurable hSo).nullMeasurableSet
    (by rw [hvo]; exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top), hvc, hvo, tsub_self]

/-! ### Mesh cubes -/

/-- The mesh cube `∏ [zᵢ/(m+1), (zᵢ+1)/(m+1))` of side `1/(m+1)`. -/
abbrev meshCube (m : ℕ) (z : Site d) : Set (Rd d) :=
  ratBox (fun i => (z i : ℚ) / (m + 1)) (fun i => ((z i : ℚ) + 1) / (m + 1))

theorem meshCube_lt (m : ℕ) (z : Site d) (i : Fin d) :
    (z i : ℚ) / (m + 1) < ((z i : ℚ) + 1) / (m + 1) :=
  div_lt_div_of_pos_right (lt_add_one _) (by positivity)

theorem mem_meshCube {m : ℕ} {z : Site d} {y : Rd d} :
    y ∈ meshCube m z ↔ ∀ i, ⌊((m : ℝ) + 1) * y i⌋ = z i := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  simp only [meshCube, ratBox, Set.mem_ofPred_eq, Int.floor_eq_iff]
  refine forall_congr' fun i => ?_
  push_cast
  rw [div_le_iff₀ hm, lt_div_iff₀ hm]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem meshCube_disjoint {m : ℕ} {z z' : Site d} (h : z ≠ z') :
    Disjoint (meshCube m z) (meshCube m z') := by
  refine Set.disjoint_left.2 fun y hy hy' => h ?_
  funext i
  rw [mem_meshCube] at hy hy'
  rw [← hy i, hy' i]

/-- `nV ∩ ℤ^d` is finite for bounded `V` (the proof of `discretizeFinite`,
`Proofs/Sec5/MuConvergenceBall.lean`). -/
theorem discretize_finite {V : Set (Rd d)} (hV : Bornology.IsBounded V) (n : ℕ) :
    (discretize V n).Finite := by
  obtain ⟨R, hR⟩ := (hV.smul₀ (n : ℝ)).exists_norm_le
  refine (Set.finite_Icc (fun _ : Fin d => -⌈R⌉) (fun _ => ⌈R⌉)).subset ?_
  intro x hx
  have hx' : ‖toE x‖ ≤ R := hR _ hx
  have hi : ∀ i, |(x i : ℝ)| ≤ R := fun i => by
    have := PiLp.norm_apply_le (toE x) i
    simpa using this.trans hx'
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.mp (hi i)).1
    have h2 : (-(⌈R⌉ : ℤ) : ℝ) ≤ x i := by
      linarith [Int.le_ceil R]
    exact_mod_cast h2
  · have := (abs_le.mp (hi i)).2
    have h2 : (x i : ℝ) ≤ (⌈R⌉ : ℤ) := by linarith [Int.le_ceil R]
    exact_mod_cast h2

theorem mem_discretize {V : Set (Rd d)} {n : ℕ} (hn : 1 ≤ n) {x : Site d} :
    x ∈ discretize V n ↔ (n : ℝ)⁻¹ • toE x ∈ V :=
  Set.mem_smul_set_iff_inv_smul_mem₀ (by positivity) _ _

theorem finite_meshCube_subset {U : Set (Rd d)} (hU : Bornology.IsBounded U) (m : ℕ) :
    {z : Site d | meshCube m z ⊆ U}.Finite := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine (discretize_finite hU (m + 1)).subset fun z hz => ?_
  rw [mem_discretize (by omega)]
  apply hz
  rw [mem_meshCube]
  intro i
  rw [PiLp.smul_apply, smul_eq_mul, toE_apply]
  push_cast
  rw [mul_inv_cancel_left₀ hm.ne', Int.floor_intCast]

/-- The union of the mesh cubes of side `1/(m+1)` inside `U`. -/
def innerUnion (U : Set (Rd d)) (m : ℕ) : Set (Rd d) :=
  ⋃ z ∈ {z : Site d | meshCube m z ⊆ U}, meshCube m z

/-- The inner mesh approximations of a bounded open set exhaust its measure. -/
theorem tendsto_volume_innerUnion {U : Set (Rd d)} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    Tendsto (fun m => volume (innerUnion U m)) atTop (𝓝 (volume U)) := by
  refine tendsto_measure_of_tendsto_indicator atTop (fun m => ?_) hUo.measurableSet
    hUb.measure_lt_top.ne (Eventually.of_forall fun m => ?_) fun x => ?_
  · exact (finite_meshCube_subset hUb m).measurableSet_biUnion fun z _ => measurableSet_ratBox _ _
  · exact Set.iUnion₂_subset fun z hz => hz
  · by_cases hx : x ∈ U
    · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hUo x hx
      filter_upwards [eventually_gt_atTop ⌈(d : ℝ) / δ ^ 2⌉₊] with m hm
      simp only [hx, iff_true]
      have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hxz : x ∈ meshCube m (fun i => ⌊((m : ℝ) + 1) * x i⌋) := mem_meshCube.2 fun i => rfl
      refine Set.mem_biUnion (x := fun i => ⌊((m : ℝ) + 1) * x i⌋) ?_ hxz
      intro y hy
      apply hball
      have hmd : (d : ℝ) / δ ^ 2 < (m : ℝ) + 1 := by
        have h1 := Nat.le_ceil ((d : ℝ) / δ ^ 2)
        have h2 : ((⌈(d : ℝ) / δ ^ 2⌉₊ : ℕ) : ℝ) < m := by exact_mod_cast hm
        linarith
      have hterm : ∀ i, dist (y i) (x i) ^ 2 ≤ 1 / ((m : ℝ) + 1) := by
        intro i
        have h1 := Int.abs_sub_lt_one_of_floor_eq_floor
          ((mem_meshCube.1 hy i).trans (mem_meshCube.1 hxz i).symm)
        rw [← mul_sub, abs_mul, abs_of_pos hm0] at h1
        have h2 : |y i - x i| < 1 / ((m : ℝ) + 1) := by
          rw [lt_div_iff₀ hm0]; linarith
        have h3 : 1 / ((m : ℝ) + 1) ≤ 1 := by
          rw [div_le_one hm0]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        rw [Real.dist_eq, sq]
        have h4 := abs_nonneg (y i - x i)
        nlinarith
      rw [mem_ball, EuclideanSpace.dist_eq, Real.sqrt_lt' hδ]
      calc ∑ i, dist (y i) (x i) ^ 2 ≤ ∑ _i : Fin d, 1 / ((m : ℝ) + 1) :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = (d : ℝ) / ((m : ℝ) + 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ < δ ^ 2 := by
            rw [div_lt_iff₀ hm0]
            rw [div_lt_iff₀ (by positivity)] at hmd
            linarith
    · refine Eventually.of_forall fun m => ?_
      simp only [hx, iff_false]
      intro h
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 h
      exact hx (hz hxz)

/-- A bounded open set contains a finite disjoint union of mesh cubes of almost full measure. -/
theorem exists_meshCubes {U : Set (Rd d)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (F : Finset (Site d)), (∀ z ∈ F, meshCube m z ⊆ U) ∧
      ∑ z ∈ F, volume.real (meshCube m z) ≤ volume.real U ∧
      volume.real U - ∑ z ∈ F, volume.real (meshCube m z) < ε := by
  have h := (ENNReal.tendsto_toReal hUb.measure_lt_top.ne).comp (tendsto_volume_innerUnion hUo hUb)
  obtain ⟨m, hm⟩ := ((tendsto_order.1 h).1 (volume.real U - ε) (by rw [measureReal_def]; linarith)).exists
  refine ⟨m, (finite_meshCube_subset hUb m).toFinset, fun z hz => ?_, ?_, ?_⟩
  · exact (Set.Finite.mem_toFinset _).1 hz
  all_goals
    have hunion : innerUnion U m = ⋃ z ∈ (finite_meshCube_subset hUb m).toFinset, meshCube m z := by
      simp [innerUnion]
    have hsum : volume.real (innerUnion U m) =
        ∑ z ∈ (finite_meshCube_subset hUb m).toFinset, volume.real (meshCube m z) := by
      rw [hunion]
      exact measureReal_biUnion_finset (fun z _ z' _ hzz => meshCube_disjoint hzz)
        (fun z _ => measurableSet_ratBox _ _)
        (fun z _ => (isBounded_ratBox _ _).measure_lt_top.ne)
    rw [← hsum]
  · exact measureReal_mono (Set.iUnion₂_subset fun z hz => hz) hUb.measure_lt_top.ne
  · have : volume.real U - ε < volume.real (innerUnion U m) := hm
    linarith

/-! ### Counting lattice points

`intLattice`, `mem_intLattice`, `toE_injective'` are copied from `Proofs/Sec6/StrictConcavity.lean`
and `card_inter_eq_discretize` from `Proofs/Sec6/MuLipschitzShell.lean` (both downstream of this
file), made private here. -/

private abbrev intLattice (d : ℕ) : Submodule ℤ (Rd d) :=
  Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin d)))

private theorem mem_intLattice {v : Rd d} : v ∈ intLattice d ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = v i := by
  rw [Basis.mem_span_iff_repr_mem]
  simp [PiLp.basisFun_repr]

private theorem toE_injective' : Function.Injective (toE (d := d)) := fun x y h => by
  funext i
  have := congrArg (fun v : Rd d => v i) h
  simpa [toE_apply] using this

private theorem card_inter_eq_discretize (W : Set (Rd d)) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card ↥(W ∩ (n : ℝ)⁻¹ • (intLattice d : Set (Rd d))) = (discretize W n).ncard := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.card_coe_set_eq]
  have hset : W ∩ (n : ℝ)⁻¹ • (intLattice d : Set (Rd d)) =
      (fun z : Site d => (n : ℝ)⁻¹ • toE z) '' discretize W n := by
    ext v
    rw [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hn0.ne'), inv_inv,
      SetLike.mem_coe, mem_intLattice]
    constructor
    · rintro ⟨hv, hL⟩
      choose k hk using hL
      have hz : toE k = (n : ℝ) • v := by
        ext i
        simp [toE_apply, hk i]
      refine ⟨k, ?_, ?_⟩
      · show toE k ∈ (n : ℝ) • W
        rw [hz]
        exact Set.smul_mem_smul_set hv
      · simp only [hz, smul_smul, inv_mul_cancel₀ hn0.ne', one_smul]
    · rintro ⟨z, hz, rfl⟩
      have hz' : toE z ∈ (n : ℝ) • W := hz
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hn0.ne'] at hz'
      refine ⟨hz', fun i => ⟨z i, ?_⟩⟩
      simp [smul_smul, mul_inv_cancel₀ hn0.ne', toE_apply]
  rw [hset]
  exact Set.ncard_image_of_injective _
    ((smul_right_injective _ (inv_ne_zero hn0.ne')).comp toE_injective')

/-- **Lattice counting.** There is `c > 0` (the covolume of `ℤ^d`) such that
`|nV ∩ ℤ^d| / n^d → |V| / c` for every bounded measurable `V` with null frontier. -/
theorem exists_tendsto_ncard_discretize : ∃ c : ℝ, 0 < c ∧ ∀ V : Set (Rd d),
    Bornology.IsBounded V → MeasurableSet V → volume (frontier V) = 0 →
    Tendsto (fun n : ℕ => ((discretize V n).ncard : ℝ) / (n : ℝ) ^ d) atTop
      (𝓝 (volume.real V / c)) := by
  refine ⟨ZLattice.covolume (intLattice d), ZLattice.covolume_pos (intLattice d), fun V hb hm hf => ?_⟩
  have h := ZLattice.covolume.tendsto_card_div_pow' (intLattice d) hb hm hf
  rw [finrank_euclideanSpace_fin] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [card_inter_eq_discretize V hn]

/-! ### Subadditivity over finite families -/

theorem subadditive_union_set {g : Set (Site d) → ℝ} (hg : IsSubadditive g) {A B : Set (Site d)}
    (hA : A.Finite) (hB : B.Finite) (hAB : Disjoint A B) : g (A ∪ B) ≤ g A + g B := by
  have h := subadditive_union hg (A := hA.toFinset) (B := hB.toFinset) (by simpa using hAB)
  simpa using h

/-- `g(A) ≤ ∑_{i ∈ F} g(Bᵢ) + C (|A| - ∑ |Bᵢ|)` for pairwise disjoint `Bᵢ ⊆ A`, `g ∈ 𝓜_C`. -/
theorem le_sum_add_card {C : ℝ} {g : Set (Site d) → ℝ} (hg : g ∈ subadditiveClass d C)
    {A : Set (Site d)} (hA : A.Finite) {ι : Type*} (F : Finset ι) (B : ι → Set (Site d))
    (hBA : ∀ i ∈ F, B i ⊆ A) (hdisj : (F : Set ι).PairwiseDisjoint B) :
    g A ≤ ∑ i ∈ F, g (B i) + C * ((A.ncard : ℝ) - ∑ i ∈ F, ((B i).ncard : ℝ)) := by
  classical
  suffices H : ∀ F : Finset ι, (∀ i ∈ F, B i ⊆ A) → (F : Set ι).PairwiseDisjoint B →
      g A ≤ ∑ i ∈ F, g (B i) + g (A \ ⋃ i ∈ F, B i) ∧
      ((A \ ⋃ i ∈ F, B i).ncard : ℝ) = A.ncard - ∑ i ∈ F, ((B i).ncard : ℝ) by
    obtain ⟨h1, h2⟩ := H F hBA hdisj
    have h3 := (hg.2 (A \ ⋃ i ∈ F, B i) (hA.subset Set.sdiff_subset)).2
    rw [h2] at h3
    linarith
  intro F
  induction F using Finset.induction_on with
  | empty => intro _ _; simp
  | insert w F hw ih =>
    intro hBA hdisj
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hBA i (Finset.mem_insert_of_mem hi))
      (hdisj.subset (by simp))
    have hsplit : A \ ⋃ i ∈ F, B i = B w ∪ (A \ ⋃ i ∈ insert w F, B i) := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion, Finset.mem_insert, exists_prop,
        not_exists, not_and]
      constructor
      · rintro ⟨hxA, hxF⟩
        by_cases hxw : x ∈ B w
        · exact Or.inl hxw
        · refine Or.inr ⟨hxA, fun i hi hxi => ?_⟩
          rcases hi with rfl | hi
          · exact hxw hxi
          · exact hxF i hi hxi
      · rintro (hxw | ⟨hxA, hx⟩)
        · refine ⟨hBA w (Finset.mem_insert_self w F) hxw, fun i hi hxi => ?_⟩
          have hne : w ≠ i := fun h => hw (h ▸ hi)
          exact Set.disjoint_left.1 (hdisj (Finset.mem_coe.2 (Finset.mem_insert_self w F))
            (Finset.mem_coe.2 (Finset.mem_insert_of_mem hi)) hne) hxw hxi
        · exact ⟨hxA, fun i hi hxi => hx i (Or.inr hi) hxi⟩
    have hdj : Disjoint (B w) (A \ ⋃ i ∈ insert w F, B i) :=
      Set.disjoint_left.2 fun x hx hx' =>
        hx'.2 (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_self w F)) hx)
    have hBwfin : (B w).Finite := hA.subset (hBA w (Finset.mem_insert_self w F))
    have hRfin : (A \ ⋃ i ∈ insert w F, B i).Finite := hA.subset Set.sdiff_subset
    have hsub := subadditive_union_set hg.1 hBwfin hRfin hdj
    have hcard := Set.ncard_union_eq hdj hBwfin hRfin
    rw [← hsplit] at hsub hcard
    rw [Finset.sum_insert hw, Finset.sum_insert hw]
    refine ⟨by linarith, ?_⟩
    have hcard' : ((A \ ⋃ i ∈ F, B i).ncard : ℝ) =
        ((B w).ncard : ℝ) + ((A \ ⋃ i ∈ insert w F, B i).ncard : ℝ) := by
      exact_mod_cast hcard
    linarith

/-- `g(D) / x = (g(D) / |D|) (|D| / x)` for `g ∈ 𝓜_C` and finite `D` (both sides vanish if
`D = ∅`). -/
theorem div_eq_div_mul_div {C : ℝ} {g : Set (Site d) → ℝ} (hg : g ∈ subadditiveClass d C)
    {D : Set (Site d)} (hD : D.Finite) (x : ℝ) :
    g D / x = g D / D.ncard * (D.ncard / x) := by
  by_cases h : D.ncard = 0
  · have h2 := (hg.2 D hD).2
    rw [h, Nat.cast_zero, mul_zero] at h2
    have : g D = 0 := le_antisymm h2 (hg.2 D hD).1
    simp [this]
  · have hD0 : (D.ncard : ℝ) ≠ 0 := by exact_mod_cast h
    rw [div_mul_div_comm, mul_comm (g D), mul_div_mul_left _ _ hD0]

/-! ### The deterministic reduction -/

section Deterministic

variable {C : ℝ} {g : Set (Site d) → ℝ} {a c : ℝ}

/-- The box limit along `n`, normalised by `n^d`. -/
theorem tendsto_box_div_pow (hg : g ∈ subadditiveClass d C)
    (hbox : ∀ p q : Fin d → ℚ, (∀ i, p i < q i) → Tendsto (fun n : ℕ =>
      g (discretize (ratBox p q) n) / ((discretize (ratBox p q) n).ncard : ℝ)) atTop (𝓝 a))
    (hcount : ∀ V : Set (Rd d), Bornology.IsBounded V → MeasurableSet V →
      volume (frontier V) = 0 → Tendsto (fun n : ℕ => ((discretize V n).ncard : ℝ) / (n : ℝ) ^ d)
        atTop (𝓝 (volume.real V / c)))
    {p q : Fin d → ℚ} (hpq : ∀ i, p i < q i) :
    Tendsto (fun n : ℕ => g (discretize (ratBox p q) n) / (n : ℝ) ^ d) atTop
      (𝓝 (a * (volume.real (ratBox p q) / c))) := by
  have := (hbox p q hpq).mul (hcount _ (isBounded_ratBox p q) (measurableSet_ratBox p q)
    (volume_frontier_ratBox p q))
  refine this.congr fun n => ?_
  exact (div_eq_div_mul_div hg (discretize_finite (isBounded_ratBox p q) n) _).symm

/-- **Upper bound.** If `V` is bounded, measurable, with null frontier, and contains an open set
`U` of full measure, then `limsup g(nV ∩ ℤ^d) / n^d ≤ a |V| / c`. -/
theorem eventually_div_pow_lt (hg : g ∈ subadditiveClass d C) (ha : 0 ≤ a) (hc : 0 < c)
    (hbox : ∀ p q : Fin d → ℚ, (∀ i, p i < q i) → Tendsto (fun n : ℕ =>
      g (discretize (ratBox p q) n) / ((discretize (ratBox p q) n).ncard : ℝ)) atTop (𝓝 a))
    (hcount : ∀ V : Set (Rd d), Bornology.IsBounded V → MeasurableSet V →
      volume (frontier V) = 0 → Tendsto (fun n : ℕ => ((discretize V n).ncard : ℝ) / (n : ℝ) ^ d)
        atTop (𝓝 (volume.real V / c)))
    {V U : Set (Rd d)} (hVb : Bornology.IsBounded V) (hVm : MeasurableSet V)
    (hVf : volume (frontier V) = 0) (hUo : IsOpen U) (hUV : U ⊆ V) (hvol : volume V ≤ volume U)
    {b : ℝ} (hb : a * volume.real V / c < b) :
    ∀ᶠ n : ℕ in atTop, g (discretize V n) / (n : ℝ) ^ d < b := by
  have hC : 0 ≤ C := nonneg_of_mem_subadditiveClass hg
  have hUb : Bornology.IsBounded U := hVb.subset hUV
  set v := volume.real V with hv_def
  have hvU : volume.real U = v :=
    le_antisymm (measureReal_mono hUV hVb.measure_lt_top.ne)
      (ENNReal.toReal_mono hUb.measure_lt_top.ne hvol)
  set δ := b - a * v / c with hδ_def
  have hδ : 0 < δ := by linarith
  set ε := δ * c / (2 * (C + 1)) with hε_def
  have hε : 0 < ε := by positivity
  obtain ⟨m, F, hFU, hsv, hFvol⟩ := exists_meshCubes hUo hUb hε
  rw [hvU] at hsv hFvol
  set s := ∑ z ∈ F, volume.real (meshCube m z) with hs_def
  have hlim : Tendsto (fun n : ℕ => ∑ z ∈ F, g (discretize (meshCube m z) n) / (n : ℝ) ^ d +
      C * (((discretize V n).ncard : ℝ) / (n : ℝ) ^ d -
        ∑ z ∈ F, ((discretize (meshCube m z) n).ncard : ℝ) / (n : ℝ) ^ d)) atTop
      (𝓝 (∑ z ∈ F, a * (volume.real (meshCube m z) / c) +
        C * (v / c - ∑ z ∈ F, volume.real (meshCube m z) / c))) := by
    refine (tendsto_finsetSum _ fun z _ => tendsto_box_div_pow hg hbox hcount
      (meshCube_lt m z)).add (tendsto_const_nhds.mul ((hcount V hVb hVm hVf).sub
        (tendsto_finsetSum _ fun z _ => hcount _ (isBounded_ratBox _ _)
          (measurableSet_ratBox _ _) (volume_frontier_ratBox _ _))))
  have hval : ∑ z ∈ F, a * (volume.real (meshCube m z) / c) +
      C * (v / c - ∑ z ∈ F, volume.real (meshCube m z) / c) < b := by
    rw [← Finset.mul_sum, ← Finset.sum_div, ← hs_def]
    have hCε : (C + 1) * ε = δ * c / 2 := by
      rw [hε_def]; field_simp
    have k1 : a * s ≤ a * v := mul_le_mul_of_nonneg_left hsv ha
    have k2 : C * (v - s) ≤ C * ε := mul_le_mul_of_nonneg_left hFvol.le hC
    have k3 : a * s + C * (v - s) ≤ a * v + δ * c / 2 := by nlinarith
    have e1 : a * (s / c) + C * (v / c - s / c) = (a * s + C * (v - s)) / c := by ring
    have e2 : (a * v + δ * c / 2) / c = a * v / c + δ / 2 := by field_simp
    rw [e1]
    have := div_le_div_of_nonneg_right k3 hc.le
    linarith
  filter_upwards [(tendsto_order.1 hlim).2 b hval, eventually_ge_atTop 1] with n hn hn1
  refine lt_of_le_of_lt ?_ hn
  have hnd : (0 : ℝ) < (n : ℝ) ^ d := by positivity
  have key := le_sum_add_card hg (discretize_finite hVb n) F
    (fun z => discretize (meshCube m z) n)
    (fun z hz x hx => (mem_discretize hn1).2 (hUV (hFU z hz ((mem_discretize hn1).1 hx))))
    (fun z _ z' _ hzz => Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1
      (meshCube_disjoint hzz) ((mem_discretize hn1).1 hx) ((mem_discretize hn1).1 hx'))
  calc g (discretize V n) / (n : ℝ) ^ d ≤
      (∑ z ∈ F, g (discretize (meshCube m z) n) + C * (((discretize V n).ncard : ℝ) -
        ∑ z ∈ F, ((discretize (meshCube m z) n).ncard : ℝ))) / (n : ℝ) ^ d :=
        div_le_div_of_nonneg_right key hnd.le
    _ = _ := by rw [add_div, Finset.sum_div, mul_div_assoc, sub_div, Finset.sum_div]

/-- **Deterministic core of Proposition 5.3.** Let `g ∈ 𝓜_C` with `g(nQ ∩ ℤ^d) / |nQ ∩ ℤ^d| → a`
for every box `Q` with rational corners. Then `g(nW ∩ ℤ^d) / |nW ∩ ℤ^d| → a` for every bounded,
open, nonempty `W` with null frontier. -/
theorem tendsto_discretize_of_boxes (hg : g ∈ subadditiveClass d C) (ha : 0 ≤ a) (hc : 0 < c)
    (hbox : ∀ p q : Fin d → ℚ, (∀ i, p i < q i) → Tendsto (fun n : ℕ =>
      g (discretize (ratBox p q) n) / ((discretize (ratBox p q) n).ncard : ℝ)) atTop (𝓝 a))
    (hcount : ∀ V : Set (Rd d), Bornology.IsBounded V → MeasurableSet V →
      volume (frontier V) = 0 → Tendsto (fun n : ℕ => ((discretize V n).ncard : ℝ) / (n : ℝ) ^ d)
        atTop (𝓝 (volume.real V / c)))
    {W : Set (Rd d)} (hWb : Bornology.IsBounded W) (hWo : IsOpen W)
    (hWf : volume (frontier W) = 0) (hWne : W.Nonempty) :
    Tendsto (fun n : ℕ => g (discretize W n) / ((discretize W n).ncard : ℝ)) atTop (𝓝 a) := by
  have hWm := hWo.measurableSet
  obtain ⟨R, hR⟩ := hWb.exists_norm_le
  set K : ℚ := (⌈R⌉ : ℚ) + 1 with hK_def
  have hRK : R < (K : ℝ) := by
    rw [hK_def]; push_cast; linarith [Int.le_ceil R]
  set Q := ratBox (fun _ : Fin d => -K) (fun _ => K) with hQ_def
  have hKpos : ∀ _ : Fin d, -K < K := fun _ => by
    have : (0 : ℝ) < K := lt_of_le_of_lt ((norm_nonneg _).trans (hR _ hWne.some_mem)) hRK
    have : (0 : ℚ) < K := by exact_mod_cast this
    linarith
  have hWQ : W ⊆ Q := by
    intro y hy i
    have h1 := (PiLp.norm_apply_le y i).trans (hR y hy)
    rw [Real.norm_eq_abs] at h1
    constructor
    · push_cast; linarith [neg_abs_le (y i)]
    · push_cast; linarith [le_abs_self (y i)]
  have hQb := isBounded_ratBox (fun _ : Fin d => -K) (fun _ => K)
  have hQm := measurableSet_ratBox (fun _ : Fin d => -K) (fun _ => K)
  have hQf := volume_frontier_ratBox (fun _ : Fin d => -K) (fun _ => K)
  set V2 := Q \ W with hV2_def
  have hV2b : Bornology.IsBounded V2 := hQb.subset Set.sdiff_subset
  have hV2m : MeasurableSet V2 := hQm.diff hWm
  have hV2f : volume (frontier V2) = 0 := by
    refine measure_mono_null ((frontier_inter_subset Q Wᶜ).trans ?_) (measure_union_null hQf hWf)
    rw [frontier_compl]
    exact Set.union_subset_union Set.inter_subset_left Set.inter_subset_right
  have hU2o : IsOpen (interior Q \ closure W) := isOpen_interior.sdiff isClosed_closure
  have hU2V : interior Q \ closure W ⊆ V2 := Set.sdiff_subset_sdiff interior_subset subset_closure
  have hvol2 : volume V2 ≤ volume (interior Q \ closure W) := by
    have hcov : V2 ⊆ (interior Q \ closure W) ∪ (frontier Q ∪ frontier W) := by
      rintro y ⟨hyQ, hyW⟩
      by_cases h1 : y ∈ interior Q
      · by_cases h2 : y ∈ closure W
        · exact Or.inr (Or.inr ⟨h2, by rwa [hWo.interior_eq]⟩)
        · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨subset_closure hyQ, h1⟩)
    calc volume V2 ≤ volume ((interior Q \ closure W) ∪ (frontier Q ∪ frontier W)) :=
          measure_mono hcov
      _ ≤ volume (interior Q \ closure W) + volume (frontier Q ∪ frontier W) :=
          measure_union_le _ _
      _ = volume (interior Q \ closure W) := by rw [measure_union_null hQf hWf, add_zero]
  set vW := volume.real W with hvW_def
  set vQ := volume.real Q with hvQ_def
  have hv2 : volume.real V2 = vQ - vW := measureReal_sdiff hWQ hWm hQb.measure_lt_top.ne
  have hUB_W : ∀ b, a * vW / c < b → ∀ᶠ n : ℕ in atTop, g (discretize W n) / (n : ℝ) ^ d < b :=
    fun b hb => eventually_div_pow_lt hg ha hc hbox hcount hWb hWm hWf hWo subset_rfl le_rfl hb
  have hUB_2 : ∀ b, a * volume.real V2 / c < b →
      ∀ᶠ n : ℕ in atTop, g (discretize V2 n) / (n : ℝ) ^ d < b :=
    fun b hb => eventually_div_pow_lt hg ha hc hbox hcount hV2b hV2m hV2f hU2o hU2V hvol2 hb
  have hQlim := tendsto_box_div_pow hg hbox hcount hKpos
  have hmain : Tendsto (fun n : ℕ => g (discretize W n) / (n : ℝ) ^ d) atTop
      (𝓝 (a * vW / c)) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => hUB_W b hb⟩
    set δ := a * vW / c - b with hδ_def
    have hδ : 0 < δ := by linarith
    have hb2 : a * volume.real V2 / c < a * (vQ - vW) / c + δ / 2 := by
      rw [hv2]; linarith
    filter_upwards [(tendsto_order.1 hQlim).1 (a * (vQ / c) - δ / 2) (by linarith),
      hUB_2 _ hb2, eventually_ge_atTop 1] with n h1 h2 hn
    have hsplit : discretize Q n = discretize W n ∪ discretize V2 n := by
      ext x
      simp only [Set.mem_union, mem_discretize hn, hV2_def, Set.mem_sdiff]
      constructor
      · intro hx
        by_cases hxW : (n : ℝ)⁻¹ • toE x ∈ W
        · exact Or.inl hxW
        · exact Or.inr ⟨hx, hxW⟩
      · rintro (hx | hx)
        · exact hWQ hx
        · exact hx.1
    have hdisj : Disjoint (discretize W n) (discretize V2 n) :=
      Set.disjoint_left.2 fun x hx hx' => ((mem_discretize hn).1 hx').2 ((mem_discretize hn).1 hx)
    have hsub := subadditive_union_set (hg.1) (discretize_finite hWb n)
      (discretize_finite hV2b n) hdisj
    rw [← hsplit] at hsub
    have hnd : (0 : ℝ) < (n : ℝ) ^ d := by positivity
    have h3 : g (discretize Q n) / (n : ℝ) ^ d ≤
        g (discretize W n) / (n : ℝ) ^ d + g (discretize V2 n) / (n : ℝ) ^ d := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hsub hnd.le
    have e1 : a * (vQ / c) - a * (vQ - vW) / c = a * vW / c := by ring
    linarith
  have hvW : 0 < vW :=
    ENNReal.toReal_pos (hWo.measure_pos volume hWne).ne' hWb.measure_lt_top.ne
  have hlim := hmain.div (hcount W hWb hWm hWf) (by positivity)
  rw [show a * vW / c / (vW / c) = a by field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact div_div_div_cancel_right₀ (by positivity) _ _

end Deterministic

/-! ### Proposition 5.3 from the box statement -/

/-- **Proposition 5.3 from its version on rational boxes.** `SubadditiveRationalBoxesStmt`
(Infra/SubadditiveCubes.lean) implies `SubadditiveErgodicStmt`, with the same constant `a` and the
same full-measure event, uniform in the bounded Lipschitz domain `W`. -/
theorem subadditiveErgodic_of_rationalBoxes (h : SubadditiveRationalBoxesStmt) :
    SubadditiveErgodicStmt := by
  intro d hd E C f hf
  obtain ⟨a, ha0, haC, hae⟩ := h d (by omega) E C f hf
  obtain ⟨c, hc, hcount⟩ := exists_tendsto_ncard_discretize (d := d)
  refine ⟨a, ha0, haC, ?_⟩
  filter_upwards [hae] with η hη W hW
  exact tendsto_discretize_of_boxes (hf.mem η) ha0 hc hη hcount hW.1 hW.2.1 (IsLipschitzDomain.volume_frontier hW)
    hW.2.2.1.nonempty

end SubadditiveLipschitz

end RandomSandpile

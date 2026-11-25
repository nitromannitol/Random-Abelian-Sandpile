import RandomSandpile.Proofs.Sec9.SingleSourceD2PerronEnvelope
import RandomSandpile.Proofs.Sec9.SingleSourceD2ObsCompare
import RandomSandpile.Proofs.Sec9.OpenBoundaryComparison
import RandomSandpile.Infra.SupConvolution

/-!
# Theorem 9.2 in dimension two: comparison for the obstacle problem from Alexandrov's theorem

`obsComparison_of_alexandrov`: for the obstacle operator `min{s + g(x), A(X)}` (`obsOp`) on a
bounded open set of `ℝ²`, every upper semicontinuous subsolution of (DP) lies below every lower
semicontinuous supersolution. This is `obsComparison` without the theorem of sums: the
sub- and supersolution are regularized by a sup- and an inf-convolution over `Ω̄`, which are
continuous (semiconvexity, `continuous_supConv_usc`); test functions touching the regularizations
give jets of the original functions at the maximizers (`superJet2_of_supConv`,
`subJet2_of_infConv`). On `O = {x ∈ Ω : u^δ - v_δ > c}` the maximizers lie in `Ω`, the obstacle is
inactive, and the comparison principle for `A(D²u) = 0` (`shiftComparison_of_alexandrov`) gives
`u^δ ≤ v_δ + c` on `Ō`, which fails at a point where `u - v = 2c`.
-/

noncomputable section

open Filter Topology Metric Set
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

open CrandallIshiiLions

/-! ### Sup-convolutions of semicontinuous functions -/

section SupConv

variable {S : Set (Rd 2)} {u : Rd 2 → ℝ}

/-- The sup in `supConv` is attained for an upper semicontinuous function on a compact set. -/
theorem supConv_spec_usc (hS : IsCompact S) (hne : S.Nonempty) (ε : ℝ)
    (hu : UpperSemicontinuousOn u S) (x : Rd 2) :
    (∀ y ∈ S, u y - ‖x - y‖ ^ 2 / (2 * ε) ≤ supConv S ε u x) ∧
      ∃ y ∈ S, supConv S ε u x = u y - ‖x - y‖ ^ 2 / (2 * ε) := by
  have hc : Continuous fun y : Rd 2 => -(‖x - y‖ ^ 2 / (2 * ε)) :=
    (((continuous_const.sub continuous_id).norm.pow 2).div_const _).neg
  have hg : UpperSemicontinuousOn (fun y => u y + -(‖x - y‖ ^ 2 / (2 * ε))) S :=
    hu.add hc.continuousOn.upperSemicontinuousOn
  obtain ⟨y₀, hy₀, hmax⟩ := hg.exists_isMaxOn hne hS
  have hmax' : ∀ y ∈ S, u y - ‖x - y‖ ^ 2 / (2 * ε) ≤ u y₀ - ‖x - y₀‖ ^ 2 / (2 * ε) :=
    fun y hy => by
      have := isMaxOn_iff.1 hmax y hy
      linarith
  have hbdd : BddAbove (Set.range fun y : S => u y - ‖x - y‖ ^ 2 / (2 * ε)) :=
    ⟨u y₀ - ‖x - y₀‖ ^ 2 / (2 * ε), by rintro _ ⟨y, rfl⟩; exact hmax' y y.2⟩
  have hle : ∀ y ∈ S, u y - ‖x - y‖ ^ 2 / (2 * ε) ≤ supConv S ε u x := fun y hy =>
    le_ciSup hbdd (⟨y, hy⟩ : S)
  refine ⟨hle, y₀, hy₀, le_antisymm ?_ (hle y₀ hy₀)⟩
  have : Nonempty S := ⟨⟨y₀, hy₀⟩⟩
  exact ciSup_le fun y => hmax' y y.2

/-- Semiconvexity of the sup-convolution of an upper semicontinuous function. -/
theorem convexOn_supConv_add_usc (hS : IsCompact S) (hne : S.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hu : UpperSemicontinuousOn u S) :
    ConvexOn ℝ Set.univ (fun x => supConv S ε u x + ‖x‖ ^ 2 / (2 * ε)) := by
  have hid : ∀ x w : Rd 2, u w - ‖x - w‖ ^ 2 / (2 * ε) + ‖x‖ ^ 2 / (2 * ε) =
      (u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ x w / ε := by
    intro x w
    rw [norm_sub_sq_real]
    field_simp
    ring
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨hle, w, hw, hzw⟩ := supConv_spec_usc hS hne ε hu (a • x + b • y)
  have hx := (supConv_spec_usc hS hne ε hu x).1 w hw
  have hy := (supConv_spec_usc hS hne ε hu y).1 w hw
  have hx' : (u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ x w / ε ≤
      supConv S ε u x + ‖x‖ ^ 2 / (2 * ε) := by rw [← hid]; linarith
  have hy' : (u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ y w / ε ≤
      supConv S ε u y + ‖y‖ ^ 2 / (2 * ε) := by rw [← hid]; linarith
  have hz : supConv S ε u (a • x + b • y) + ‖a • x + b • y‖ ^ 2 / (2 * ε) =
      (u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ (a • x + b • y) w / ε := by rw [hzw, hid]
  simp only [smul_eq_mul]
  rw [hz, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h1 := mul_le_mul_of_nonneg_left hx' ha
  have h2 := mul_le_mul_of_nonneg_left hy' hb
  have e : (u w - ‖w‖ ^ 2 / (2 * ε)) + (a * inner ℝ x w + b * inner ℝ y w) / ε =
      a * ((u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ x w / ε) +
        b * ((u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ y w / ε) := by
    rw [show a * ((u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ x w / ε) +
        b * ((u w - ‖w‖ ^ 2 / (2 * ε)) + inner ℝ y w / ε) =
        (a + b) * (u w - ‖w‖ ^ 2 / (2 * ε)) + (a * inner ℝ x w + b * inner ℝ y w) / ε by ring,
      hab, one_mul]
  rw [e]
  linarith

/-- The sup-convolution of an upper semicontinuous function is continuous. -/
theorem continuous_supConv_usc (hS : IsCompact S) (hne : S.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hu : UpperSemicontinuousOn u S) : Continuous (supConv S ε u) := by
  have h := (convexOn_supConv_add_usc hS hne hε hu).locallyLipschitz.continuous
  have h2 : Continuous fun x : Rd 2 => ‖x‖ ^ 2 / (2 * ε) := (continuous_norm.pow 2).div_const _
  refine (h.sub h2).congr fun x => ?_
  simp

/-- **Test functions at the sup-convolution give superjets at the maximizer.** -/
theorem superJet2_of_supConv {Ω : Set (Rd 2)} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ S) (hS : IsCompact S)
    (hne : S.Nonempty) {ε : ℝ} (hu : UpperSemicontinuousOn u S) {x y : Rd 2} (hyΩ : y ∈ Ω)
    (hy : supConv S ε u x = u y - ‖x - y‖ ^ 2 / (2 * ε)) {φ : Rd 2 → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (hmax : IsLocalMax (fun z => supConv S ε u z - φ z) x) :
    ((InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x), hessian φ x) ∈
      superJet2 Ω u y := by
  set c := x - y with hc
  have hyc : y + c = x := by rw [hc]; abel
  have hψ : ContDiffAt ℝ 2 (fun z => φ (z + c)) y := ContDiffAt.comp_add_right' (by rwa [hyc])
  have hmax' : IsLocalMax (fun z => u z - φ (z + c)) y := by
    have h1 : (fun z : Rd 2 => z + c) ⁻¹'
        {z' | supConv S ε u z' - φ z' ≤ supConv S ε u x - φ x} ∈ 𝓝 y := by
      have hcont : ContinuousAt (fun z : Rd 2 => z + c) y :=
        (continuous_id.add continuous_const).continuousAt
      refine hcont.preimage_mem_nhds ?_
      rw [hyc]
      exact hmax
    filter_upwards [h1, hΩ.mem_nhds hyΩ] with z hz hzΩ
    have h2 := (supConv_spec_usc hS hne ε hu (z + c)).1 z (hΩS hzΩ)
    have e : z + c - z = c := by abel
    rw [e] at h2
    have hz' : supConv S ε u (z + c) - φ (z + c) ≤ supConv S ε u x - φ x := hz
    rw [hy] at hz'
    show u z - φ (z + c) ≤ u y - φ (y + c)
    rw [hyc]
    linarith
  have hj := mem_superJet2_of_isLocalMax Ω hψ hmax'
  have hd : fderiv ℝ (fun z => φ (z + c)) y = fderiv ℝ φ x := by
    rw [fderiv_comp_add_right (f := φ) c, hyc]
  have hh : hessian (fun z => φ (z + c)) y = hessian φ x := by
    rw [hessian_comp_add_right, hyc]
  rw [hd, hh] at hj
  exact hj

end SupConv

/-! ### Inf-convolutions -/

section InfConv

variable {S : Set (Rd 2)} {v : Rd 2 → ℝ}

/-- The inf-convolution `v_ε(x) = inf_{y ∈ S} (v(y) + |x - y|²/(2ε)) = -(-v)^ε(x)`. -/
def infConv (S : Set (Rd 2)) (ε : ℝ) (v : Rd 2 → ℝ) (x : Rd 2) : ℝ :=
  -supConv S ε (fun y => -v y) x

theorem infConv_spec (hS : IsCompact S) (hne : S.Nonempty) (ε : ℝ)
    (hv : LowerSemicontinuousOn v S) (x : Rd 2) :
    (∀ y ∈ S, infConv S ε v x ≤ v y + ‖x - y‖ ^ 2 / (2 * ε)) ∧
      ∃ y ∈ S, infConv S ε v x = v y + ‖x - y‖ ^ 2 / (2 * ε) := by
  obtain ⟨h1, y, hy, h2⟩ := supConv_spec_usc (u := fun y => -v y) hS hne ε hv.neg x
  refine ⟨fun z hz => ?_, y, hy, ?_⟩
  · have := h1 z hz
    show -supConv S ε (fun y => -v y) x ≤ v z + ‖x - z‖ ^ 2 / (2 * ε)
    linarith
  · show -supConv S ε (fun y => -v y) x = v y + ‖x - y‖ ^ 2 / (2 * ε)
    rw [h2]
    ring

theorem continuous_infConv (hS : IsCompact S) (hne : S.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hv : LowerSemicontinuousOn v S) : Continuous (infConv S ε v) :=
  (continuous_supConv_usc (u := fun y => -v y) hS hne hε hv.neg).neg

/-- **Test functions at the inf-convolution give subjets at the minimizer.** -/
theorem subJet2_of_infConv {Ω : Set (Rd 2)} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ S) (hS : IsCompact S)
    (hne : S.Nonempty) {ε : ℝ} (hv : LowerSemicontinuousOn v S) {x y : Rd 2} (hyΩ : y ∈ Ω)
    (hy : infConv S ε v x = v y + ‖x - y‖ ^ 2 / (2 * ε)) {φ : Rd 2 → ℝ} {a : ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (hmin : IsLocalMin (fun z => infConv S ε v z + a - φ z) x) :
    ((InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x), hessian φ x) ∈
      subJet2 Ω v y := by
  set c := x - y with hc
  have hyc : y + c = x := by rw [hc]; abel
  have hψ : ContDiffAt ℝ 2 (fun z => φ (z + c)) y := ContDiffAt.comp_add_right' (by rwa [hyc])
  have hmin' : IsLocalMin (fun z => v z - φ (z + c)) y := by
    have h1 : (fun z : Rd 2 => z + c) ⁻¹'
        {z' | infConv S ε v x + a - φ x ≤ infConv S ε v z' + a - φ z'} ∈ 𝓝 y := by
      have hcont : ContinuousAt (fun z : Rd 2 => z + c) y :=
        (continuous_id.add continuous_const).continuousAt
      refine hcont.preimage_mem_nhds ?_
      rw [hyc]
      exact hmin
    filter_upwards [h1, hΩ.mem_nhds hyΩ] with z hz hzΩ
    have h2 := (infConv_spec hS hne ε hv (z + c)).1 z (hΩS hzΩ)
    have e : z + c - z = c := by abel
    rw [e] at h2
    have hz' : infConv S ε v x + a - φ x ≤ infConv S ε v (z + c) + a - φ (z + c) := hz
    rw [hy] at hz'
    show v y - φ (y + c) ≤ v z - φ (z + c)
    rw [hyc]
    linarith
  have hj := mem_subJet2_of_isLocalMin Ω hψ hmin'
  have hd : fderiv ℝ (fun z => φ (z + c)) y = fderiv ℝ φ x := by
    rw [fderiv_comp_add_right (f := φ) c, hyc]
  have hh : hessian (fun z => φ (z + c)) y = hessian φ x := by
    rw [hessian_comp_add_right, hyc]
  rw [hd, hh] at hj
  exact hj

/-- At the minimizer of the inf-convolution the paraboloid touches `v` from below, so `v` has a
subjet there. -/
theorem subJet2_nonempty_of_infConv {Ω : Set (Rd 2)} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ S)
    (hS : IsCompact S) (hne : S.Nonempty) {ε : ℝ} (hv : LowerSemicontinuousOn v S)
    {x y : Rd 2} (hyΩ : y ∈ Ω) (hy : infConv S ε v x = v y + ‖x - y‖ ^ 2 / (2 * ε)) :
    ∃ pX, pX ∈ subJet2 Ω v y := by
  set φ : Rd 2 → ℝ := fun z => infConv S ε v x - ‖x - z‖ ^ 2 / (2 * ε) with hφ
  have hφc : ContDiffAt ℝ 2 φ y :=
    (contDiff_const.sub (((contDiff_norm_sq ℝ).comp (contDiff_const.sub contDiff_id)).div_const
      _)).contDiffAt
  have hmin : IsLocalMin (fun z => v z - φ z) y := by
    filter_upwards [hΩ.mem_nhds hyΩ] with z hz
    have h1 := (infConv_spec hS hne ε hv x).1 z (hΩS hz)
    show v y - (infConv S ε v x - ‖x - y‖ ^ 2 / (2 * ε)) ≤
      v z - (infConv S ε v x - ‖x - z‖ ^ 2 / (2 * ε))
    rw [hy]
    linarith
  exact ⟨_, mem_subJet2_of_isLocalMin Ω hφc hmin⟩

end InfConv

/-! ### The boundary margin -/

/-- Near `∂Ω` a subsolution is below `c/2` and a supersolution above `-c/2`. -/
theorem exists_boundary_margin {Ω : Set (Rd 2)} (hK : IsCompact (closure Ω)) {w v : Rd 2 → ℝ}
    (hw : UpperSemicontinuousOn w (closure Ω)) (hv : LowerSemicontinuousOn v (closure Ω))
    (hw0 : ∀ x ∈ frontier Ω, w x ≤ 0) (hv0 : ∀ x ∈ frontier Ω, 0 ≤ v x) {c : ℝ} (hc : 0 < c) :
    ∃ ε₀ > 0, ∀ b ∈ frontier Ω, ∀ y ∈ closure Ω, dist y b < ε₀ → w y < c / 2 ∧ -(c / 2) < v y := by
  have hloc : ∀ b : frontier Ω, ∃ r > 0, ∀ y ∈ ball (b : Rd 2) r ∩ closure Ω,
      w y < c / 2 ∧ -(c / 2) < v y := by
    intro ⟨b, hb⟩
    have hbK : b ∈ closure Ω := frontier_subset_closure hb
    have h1 := hw b hbK (c / 2) (by linarith [hw0 b hb])
    have h2 := hv b hbK (-(c / 2)) (by linarith [hv0 b hb])
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (h1.and h2)
    exact ⟨r, hr, fun y hy => hsub hy⟩
  choose r hr hball using hloc
  have hfK : IsCompact (frontier Ω) := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric hfK
    (c := fun b : frontier Ω => ball (b : Rd 2) (r b)) (fun b => isOpen_ball)
    (fun b hb => mem_iUnion.2 ⟨⟨b, hb⟩, mem_ball_self (hr _)⟩)
  refine ⟨δ, hδ, fun b hb y hy hyb => ?_⟩
  obtain ⟨i, hi⟩ := hcover b hb
  exact hball i y ⟨hi (mem_ball.2 hyb), hy⟩

/-- A ball around a point of an open set, missing the frontier, lies in the set. -/
theorem ball_subset_of_frontier {Ω : Set (Rd 2)} (hΩ : IsOpen Ω) {x : Rd 2} (hx : x ∈ Ω)
    {r : ℝ} (h : ∀ b ∈ frontier Ω, r ≤ dist x b) : ball x r ⊆ Ω := by
  intro y hy
  by_contra hyΩ
  have hnf : ∀ z ∈ ball x r, z ∉ frontier Ω := fun z hz hzf => by
    have := h z hzf
    rw [mem_ball, dist_comm] at hz
    linarith
  have hcov : ball x r ⊆ Ω ∪ (closure Ω)ᶜ := by
    intro z hz
    by_cases hzΩ : z ∈ Ω
    · exact Or.inl hzΩ
    · right
      intro hzc
      exact hnf z hz (by rw [hΩ.frontier_eq]; exact ⟨hzc, hzΩ⟩)
  have hyc : y ∈ (closure Ω)ᶜ := (hcov hy).resolve_left hyΩ
  obtain ⟨z, -, hz1, hz2⟩ := (convex_ball x r).isPreconnected Ω (closure Ω)ᶜ hΩ
    isClosed_closure.isOpen_compl hcov ⟨x, mem_ball_self (lt_of_le_of_lt dist_nonneg hy), hx⟩
    ⟨y, hy, hyc⟩
  exact hz2 (subset_closure hz1)

/-! ### Comparison -/

/-- **Comparison for the obstacle Dirichlet problem** from Alexandrov's theorem. -/
theorem obsComparison_of_alexandrov (hAlex : AlexandrovStmt) {Ω : Set (Rd 2)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {g : Rd 2 → ℝ} (hg : Continuous g)
    {A : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hA : HasTraceShift A) (hAd : DegenerateElliptic A)
    {w v : Rd 2 → ℝ} (hw : IsSubsolutionDP (obsOp g A) Ω w)
    (hv : IsSupersolutionDP (obsOp g A) Ω v) :
    ∀ x ∈ closure Ω, w x ≤ v x := by
  intro x₀ hx₀
  by_contra hlt
  rw [not_le] at hlt
  set K := closure Ω with hKdef
  have hK : IsCompact K := hΩb.isCompact_closure
  have hx₀Ω : x₀ ∈ Ω := by
    by_contra h
    have hfr : x₀ ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hx₀, h⟩
    linarith [hw.2.2 x₀ hfr, hv.2.2 x₀ hfr]
  set c := (w x₀ - v x₀) / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hne : K.Nonempty := ⟨x₀, hx₀⟩
  -- bounds
  obtain ⟨Mw, hMw⟩ := hw.1.bddAbove_of_isCompact hK
  obtain ⟨Mv, hMv⟩ := hv.1.bddBelow_of_isCompact hK
  have hMw' : ∀ y ∈ K, w y ≤ Mw := fun y hy => hMw ⟨y, hy, rfl⟩
  have hMv' : ∀ y ∈ K, Mv ≤ v y := fun y hy => hMv ⟨y, hy, rfl⟩
  have hB : 0 < Mw - Mv + 1 := by linarith [hMw' x₀ hx₀, hMv' x₀ hx₀]
  -- the margins
  obtain ⟨ε₀, hε₀, hmargin⟩ := exists_boundary_margin hK hw.1 hv.1 hw.2.2 hv.2.2 hc
  obtain ⟨η, hη, hgη⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hg.continuousOn) (c / 2) (half_pos hc)
  set R := min (ε₀ / 4) (η / 2) with hRdef
  have hR : 0 < R := lt_min (by linarith) (by linarith)
  have hRε : R ≤ ε₀ / 4 := min_le_left _ _
  have hRη : R ≤ η / 2 := min_le_right _ _
  set δ := R ^ 2 / (4 * (Mw - Mv + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδB : 2 * δ * (Mw - Mv) < R ^ 2 := by
    have h1 : 2 * δ * (Mw - Mv + 1) = R ^ 2 / 2 := by
      rw [hδdef]; field_simp; ring
    have h2 : 2 * δ * (Mw - Mv) < 2 * δ * (Mw - Mv + 1) := by nlinarith
    nlinarith [sq_nonneg R]
  -- the regularizations
  set u' := supConv K δ w with hu'
  set v' := infConv K δ v with hv'
  have hu'c : Continuous u' := continuous_supConv_usc hK hne hδ hw.1
  have hv'c : Continuous v' := continuous_infConv hK hne hδ hv.1
  -- the key properties at a point where `u' - v' ≥ c`
  have hkey : ∀ x ∈ K, c ≤ u' x - v' x → ∃ y₁ ∈ Ω, ∃ y₂ ∈ Ω, x ∈ Ω ∧
      u' x = w y₁ - ‖x - y₁‖ ^ 2 / (2 * δ) ∧ v' x = v y₂ + ‖x - y₂‖ ^ 2 / (2 * δ) ∧
      0 < w y₁ + g y₁ := by
    intro x hx hcx
    obtain ⟨-, y₁, hy₁K, hy₁⟩ := supConv_spec_usc hK hne δ hw.1 x
    obtain ⟨hv'le, y₂, hy₂K, hy₂⟩ := infConv_spec hK hne δ hv.1 x
    have hu'x : u' x ≤ Mw := by
      rw [hu', hy₁]
      have : 0 ≤ ‖x - y₁‖ ^ 2 / (2 * δ) := by positivity
      linarith [hMw' y₁ hy₁K]
    have hv'x : Mv ≤ v' x := by
      rw [hv', hy₂]
      have : 0 ≤ ‖x - y₂‖ ^ 2 / (2 * δ) := by positivity
      linarith [hMv' y₂ hy₂K]
    -- distances
    have hd₁ : ‖x - y₁‖ < R := by
      have h1 : ‖x - y₁‖ ^ 2 = 2 * δ * (w y₁ - u' x) := by
        rw [hu', hy₁]; field_simp; ring
      have h2 : ‖x - y₁‖ ^ 2 < R ^ 2 := by
        rw [h1]
        nlinarith [hMw' y₁ hy₁K]
      exact lt_of_pow_lt_pow_left₀ 2 hR.le h2
    have hd₂ : ‖x - y₂‖ < R := by
      have h1 : ‖x - y₂‖ ^ 2 = 2 * δ * (v' x - v y₂) := by
        rw [hv', hy₂]; field_simp; ring
      have h2 : ‖x - y₂‖ ^ 2 < R ^ 2 := by
        rw [h1]
        nlinarith [hMv' y₂ hy₂K]
      exact lt_of_pow_lt_pow_left₀ 2 hR.le h2
    have hgap : c ≤ w y₁ - v y₂ := by
      have h1 : u' x ≤ w y₁ := by
        rw [hu', hy₁]
        have : 0 ≤ ‖x - y₁‖ ^ 2 / (2 * δ) := by positivity
        linarith
      have h2 : v y₂ ≤ v' x := by
        rw [hv', hy₂]
        have : 0 ≤ ‖x - y₂‖ ^ 2 / (2 * δ) := by positivity
        linarith
      linarith
    -- no frontier point within `ε₀/2`
    have hfar : ∀ b ∈ frontier Ω, ε₀ / 2 ≤ dist x b := by
      intro b hb
      by_contra hcon
      rw [not_le] at hcon
      have h1 : dist y₁ b < ε₀ := by
        calc dist y₁ b ≤ dist y₁ x + dist x b := dist_triangle _ _ _
          _ < R + ε₀ / 2 := by
            rw [dist_comm, dist_eq_norm]; exact add_lt_add hd₁ hcon
          _ ≤ ε₀ := by linarith
      have h2 : dist y₂ b < ε₀ := by
        calc dist y₂ b ≤ dist y₂ x + dist x b := dist_triangle _ _ _
          _ < R + ε₀ / 2 := by
            rw [dist_comm, dist_eq_norm]; exact add_lt_add hd₂ hcon
          _ ≤ ε₀ := by linarith
      have hw1 := (hmargin b hb y₁ hy₁K h1).1
      have hv2 := (hmargin b hb y₂ hy₂K h2).2
      linarith
    have hxΩ : x ∈ Ω := by
      by_contra h
      have hfr : x ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hx, h⟩
      have := hfar x hfr
      rw [dist_self] at this
      linarith
    have hball := ball_subset_of_frontier hΩ hxΩ hfar
    have hy₁Ω : y₁ ∈ Ω := hball (by rw [mem_ball, dist_comm, dist_eq_norm]; linarith)
    have hy₂Ω : y₂ ∈ Ω := hball (by rw [mem_ball, dist_comm, dist_eq_norm]; linarith)
    -- the obstacle at the minimizer
    obtain ⟨pX, hpX⟩ := subJet2_nonempty_of_infConv hΩ subset_closure hK hne hv.1 hy₂Ω hy₂
    have hobs : 0 ≤ v y₂ + g y₂ := (le_min_iff.1 (hv.2.1.2 y₂ hy₂Ω pX hpX)).1
    have hg12 : |g y₁ - g y₂| < c / 2 := by
      have h12 : dist y₁ y₂ < η := by
        calc dist y₁ y₂ ≤ dist y₁ x + dist x y₂ := dist_triangle _ _ _
          _ < R + R := by
            rw [dist_comm, dist_eq_norm, dist_eq_norm]; exact add_lt_add hd₁ hd₂
          _ ≤ η := by linarith
      have := hgη y₁ hy₁K y₂ hy₂K h12
      rwa [Real.dist_eq] at this
    refine ⟨y₁, hy₁Ω, y₂, hy₂Ω, hxΩ, hy₁, hy₂, ?_⟩
    have := (abs_lt.1 hg12).1
    linarith
  -- the domain of comparison
  set O := Ω ∩ {x | c < u' x - v' x} with hOdef
  have hO : IsOpen O := hΩ.inter (isOpen_lt continuous_const (hu'c.sub hv'c))
  have hOb : Bornology.IsBounded O := hΩb.subset inter_subset_left
  have hOK : closure O ⊆ K := closure_mono inter_subset_left
  have hx₀O : x₀ ∈ O := by
    refine ⟨hx₀Ω, ?_⟩
    show c < u' x₀ - v' x₀
    have h1 : w x₀ ≤ u' x₀ := by
      have := (supConv_spec_usc hK hne δ hw.1 x₀).1 x₀ hx₀
      rw [sub_self, norm_zero] at this
      simpa using this
    have h2 : v' x₀ ≤ v x₀ := by
      have := (infConv_spec hK hne δ hv.1 x₀).1 x₀ hx₀
      rw [sub_self, norm_zero] at this
      simpa using this
    rw [hcdef]
    linarith
  -- the viscosity inequalities on `O`
  have hsub : ViscFromAboveLE A O u' := by
    intro x hx φ hφ hmax
    obtain ⟨y₁, hy₁Ω, y₂, hy₂Ω, -, hy₁, -, hpos⟩ := hkey x (subset_closure hx.1) hx.2.le
    have hj := superJet2_of_supConv hΩ subset_closure hK hne hw.1 hy₁Ω hy₁ hφ hmax
    have h := hw.2.1.2 y₁ hy₁Ω _ hj
    rcases min_le_iff.1 h with h1 | h1
    · linarith
    · exact h1
  have hsup : ViscFromBelowGE A O (fun x => v' x + c) := by
    intro x hx φ hφ hmin
    obtain ⟨y₁, -, y₂, hy₂Ω, -, -, hy₂, -⟩ := hkey x (subset_closure hx.1) hx.2.le
    have hj := subJet2_of_infConv hΩ subset_closure hK hne hv.1 hy₂Ω hy₂ (a := c) hφ hmin
    exact (le_min_iff.1 (hv.2.1.2 y₂ hy₂Ω _ hj)).2
  have hbd : ∀ x ∈ frontier O, u' x ≤ v' x + c := by
    intro x hx
    by_contra hcon
    rw [not_le] at hcon
    have hxK : x ∈ K := hOK (frontier_subset_closure hx)
    obtain ⟨-, -, -, -, hxΩ, -⟩ := hkey x hxK (by linarith)
    have hxO : x ∈ O := ⟨hxΩ, show c < u' x - v' x by linarith⟩
    rw [hO.frontier_eq] at hx
    exact hx.2 hxO
  have hshift : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm → ∀ t : ℝ,
      A (M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = A M - ((2 : ℕ) : ℝ) * t := by
    intro M hM t
    rw [hA M hM t]
    norm_num
  have hcomp := shiftComparison_of_alexandrov hAlex 2 (by norm_num) A hAd hshift O hO hOb u'
    (fun x => v' x + c) hu'c.continuousOn (hv'c.add continuous_const).continuousOn hsub hsup hbd
    x₀ (subset_closure hx₀O)
  have := hx₀O.2
  simp only [mem_ofPred_eq] at this
  linarith

end SingleSourceD2

end RandomSandpile

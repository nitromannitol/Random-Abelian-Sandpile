import RandomSandpile.Proofs.Sec9.SingleSourceFlatness
import RandomSandpile.Proofs.Sec7.FlatTiltedZero
import RandomSandpile.Steps.Sec9.OpenBoundary
import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessSteps

/-!
# The operator `F*(M) = sup {l : μ*(l, M) > 0}` and the minimality step

 §5. Continues `Proofs/Sec9/SingleSourceFlatness.lean`.

* `effOpStar E M = sup {l : μ*(l, M) > 0}`; the set is nonempty (`v = 0` is stabilizing and bends
  above `q_l + q_M` for `l ≤ -d(|M|₂ + 1)`, `muStar_lower_neg`) and bounded above
  (`μ*(l, M) = 0` for `l ≥ 2d - 1 - η_min - tr M`, the site bound of Lemma 5.4).
* `effOpStar_nonneg_iff`: `F*(M) ≥ 0` iff `μ*(l, M) > 0` for every `l < 0`, so
  `ViscFromBelowMuStar E U u ↔ ViscFromBelowGE (effOpStar E) U u` (`viscFromBelowMuStar_iff`).
* `degenerateElliptic_effOpStar` and `effOpStar_add_smul_one` (`F*(M + tI) = F*(M) - dt`): `F*`
  satisfies the hypotheses of the Crandall-Ishii-Lions comparison `ShiftComparisonStmt` (proved from
  Alexandrov's theorem, `shiftComparison_of_alexandrov`).
* `ssLimitMinimalStar_of_steps`: the minimality step from
  - (S*) `SSLimitSubStarStmt`: the limits are subsolutions of `F*(D²u) ≤ 0` where they are positive
    (route in its docstring: lattice touching from above, Harnack bound of the touching gap as in the
    proof of Lemma 7.5, a `μ*`-near-maximizer with an inner contact point, leastness of `v_n`);
  - (O*) `SSOriginStarStmt`: minimality at the origin, `v(0) ≤ w(0)`;
  - `SSLimitSupportStmt`: the limits vanish outside a ball (from `SSOuterBoundStmt`);
  - the comparison principle `ShiftComparisonStmt`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric
open scoped ENNReal Matrix

namespace RandomSandpile

open EffectiveOperatorBasic MuLipschitz

variable {d : ℕ}

/-! ### The operator `F*` -/

/-- `F*(M) = sup {l : μ*(l, M) > 0}`. -/
def effOpStar (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup {l : ℝ | 0 < muStarBar E l M}

/-- `μ*(l, M) = 0` for `l ≥ 2d - 1 - η_min - tr M` (site bound of Lemma 5.4). -/
theorem muStarBar_eq_zero_of_ge (hd : 1 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) {l : ℝ}
    (hl : 2 * (d : ℝ) - 1 - (E.ηmin : ℝ) - M.trace ≤ l) : muStarBar E l M = 0 := by
  have hb : ∫⁻ η, limsup (fun n : ℕ => muStar (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P ≤ 0 := by
    calc _ ≤ ∫⁻ _, ENNReal.ofReal
          ((max ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - l - M.trace) 0 / d) ^ d) ∂E.P := by
          refine lintegral_mono_ae ((ae_all_iff.2 E.bounded).mono fun η hη => ?_)
          refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => ?_)
          exact div_ncard_le_ofReal
            (muStar_le_ncard hd (ballZ0_finite _) (fun x _ => (hη x).1) l M)
      _ = 0 := by
          rw [max_eq_right (by linarith), zero_div, zero_pow (by omega), ENNReal.ofReal_zero,
            lintegral_zero]
  unfold muStarBar
  rw [nonpos_iff_eq_zero.1 hb, ENNReal.toReal_zero]

/-- `z · M z ≤ |M|₂ |z|²`. -/
theorem dot_mulVec_le {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (v : Rd d) :
    WithLp.ofLp v ⬝ᵥ (M *ᵥ WithLp.ofLp v) ≤
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M‖ * ‖v‖ ^ 2 := by
  have hneg : (-M).IsSymm := by
    unfold Matrix.IsSymm at hM ⊢; rw [Matrix.transpose_neg, hM]
  have h := dot_mulVec_ge hneg v
  rw [map_neg, norm_neg, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

/-- `v = 0` is stabilizing (`η ≤ 2d - 1`) and `-(q_l + q_M)` is uniformly convex for
`l ≤ -d(|M|₂ + 1)`: its subgradient set at `x` contains a ball of radius `1/2`. -/
theorem muStar_lower_neg (hd : 1 ≤ d) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) {l : ℝ}
    (hl : l ≤ -((d : ℝ) * (‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M‖ + 1)))
    {η : Site d → ℤ} {n : ℕ} (hη : ∀ x ∈ ballZ0 (n : ℝ), η x ≤ 2 * (d : ℤ) - 1) :
    ENNReal.ofReal ((volume (closedBall (0 : Rd d) (1 / 2))).toReal *
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ muStar (ballZ0 (n : ℝ)) η l M := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set t := ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M‖
  have ht : 0 ≤ t := norm_nonneg _
  set V := volume (closedBall (0 : Rd d) (1 / 2))
  have hV : V ≠ ⊤ := measure_closedBall_lt_top.ne
  set B : Set (Site d) := ballZ0 (n : ℝ)
  have h0S : (0 : Site d → ℤ) ∈ stabilizing η B := by
    refine ⟨⟨fun _ => le_rfl, fun _ _ => rfl⟩, fun x hx => ?_⟩
    have : lap (0 : Site d → ℤ) x = 0 := by simp [lap, nbrSumZ]
    rw [this, zero_add]; exact hη x hx
  set w : Site d → ℝ := fun x => ((0 : Site d → ℤ) x : ℝ) - (qlZ l x + qMZ M x) with hw
  have hwS : w ∈ perturbedSuper B η l M := Set.mem_image_of_mem _ h0S
  have hball : ∀ x : Site d, closedBall (-((l / d) • toE x + gradQ M x)) (1 / 2) ⊆
      subGrad w x B := by
    intro x p hp y _
    set g := (l / d) • toE x + gradQ M x
    have he : ‖p + g‖ ≤ 1 / 2 := by
      rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add] at hp; exact hp
    have hcs := abs_real_inner_le_norm (p + g) (toE y - toE x)
    have hz := norm_le_sq_toE_sub x y
    have hql := qlZ_sub_eq_inner hd l x y
    have hqM := qMZ_expand hM x y
    have hdiff : WithLp.ofLp (toE y) - WithLp.ofLp (toE x) = WithLp.ofLp (toE y - toE x) := rfl
    rw [hdiff] at hqM
    have hle := dot_mulVec_le hM (toE y - toE x)
    have hlz : l / (2 * d) * ‖toE y - toE x‖ ^ 2 ≤
        -(t + 1) / 2 * ‖toE y - toE x‖ ^ 2 := by
      have : l / (2 * d) ≤ -(t + 1) / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have h1 : ‖p + g‖ * ‖toE y - toE x‖ ≤ 1 / 2 * ‖toE y - toE x‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg _)
    have hinner : inner ℝ (p + g) (toE y - toE x) =
        inner ℝ p (toE y - toE x) + inner ℝ ((l / d) • toE x) (toE y - toE x) +
          inner ℝ (gradQ M x) (toE y - toE x) := by
      simp only [g, inner_add_left]; ring
    simp only [w, Pi.zero_apply, Int.cast_zero, zero_sub]
    nlinarith [le_abs_self (inner ℝ (p + g) (toE y - toE x)), sq_nonneg ‖toE y - toE x‖]
  have hfin : B.Finite := ballZ0_finite _
  calc ENNReal.ofReal (V.toReal * (B.ncard : ℝ))
      = (B.ncard : ℝ≥0∞) * V := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hV,
          ENNReal.ofReal_natCast, mul_comm]
    _ = ∑' _ : B, V := by
        rw [ENNReal.tsum_set_const, ← hfin.cast_ncard_eq]
        simp
    _ ≤ ∑' x : B, volume (subGrad w x B) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        calc V = volume (closedBall (-((l / d) • toE (x : Site d) + gradQ M x)) (1 / 2)) := by
              simp only [V, Measure.addHaar_closedBall _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          _ ≤ _ := measure_mono (hball x)
    _ = volume (subGradSet w B) := ((supGradSetVolume d w B).2).symm
    _ ≤ muStar B η l M := le_iSup₂_of_le w hwS le_rfl

/-- `μ*(l, M) > 0` for `l ≤ -d(|M|₂ + 1)` when `η_max ≤ 2d - 1`. -/
theorem muStarBar_pos_of_le (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) {l : ℝ}
    (hl : l ≤ -((d : ℝ) * (‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M‖ + 1))) :
    0 < muStarBar E l M := by
  refine (volume_closedBall_toReal_pos (d := d) (by norm_num : (0 : ℝ) < 1 / 2)).trans_le ?_
  refine le_muStarBar_of hd E ?_
  filter_upwards [ae_all_iff.2 E.bounded] with η hη
  exact fun n _ => muStar_lower_neg hd hM hl fun x _ => (hη x).2.trans hE

theorem effOpStar_set_nonempty (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) :
    {l : ℝ | 0 < muStarBar E l M}.Nonempty :=
  ⟨_, muStarBar_pos_of_le hd E hE hM le_rfl⟩

theorem effOpStar_set_bddAbove (hd : 1 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) : BddAbove {l : ℝ | 0 < muStarBar E l M} := by
  refine ⟨2 * (d : ℝ) - 1 - (E.ηmin : ℝ) - M.trace, fun l hl => ?_⟩
  by_contra hlt
  have h := muStarBar_eq_zero_of_ge hd E M (not_le.1 hlt).le
  exact (ne_of_gt hl) h

/-- `F*(M) ≥ 0` iff `μ*(l, M) > 0` for every `l < 0`. -/
theorem effOpStar_nonneg_iff (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) :
    0 ≤ effOpStar E M ↔ ∀ l : ℝ, l < 0 → 0 < muStarBar E l M := by
  have hne := effOpStar_set_nonempty hd E hE hM
  have hbdd := effOpStar_set_bddAbove hd E M
  constructor
  · intro h l hl
    obtain ⟨s, hs, hls⟩ := exists_lt_of_lt_csSup hne (hl.trans_le h)
    exact hs.trans_le (muStarBar_anti muMonotone hd E M hls.le)
  · intro h
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨l, hcl, hl0⟩ := exists_between hc
    exact hcl.trans_le (le_csSup hbdd (h l hl0))

/-- `F*(M) ≤ 0` iff `μ*(l, M) = 0` for every `l > 0`. -/
theorem effOpStar_nonpos_iff (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) :
    effOpStar E M ≤ 0 ↔ ∀ l : ℝ, 0 < l → muStarBar E l M = 0 := by
  have hne := effOpStar_set_nonempty hd E hE hM
  have hbdd := effOpStar_set_bddAbove hd E M
  constructor
  · intro h l hl
    by_contra hne0
    have hpos : 0 < muStarBar E l M := lt_of_le_of_ne (muStarBar_nonneg E l M) (Ne.symm hne0)
    have := le_csSup hbdd hpos
    exact absurd (this.trans h) (not_le.2 hl)
  · intro h
    refine csSup_le hne fun l hl => ?_
    by_contra hlt
    exact (ne_of_gt hl) (h l (not_le.1 hlt))

/-- `F*` is degenerate elliptic (nonincreasing). -/
theorem degenerateElliptic_effOpStar (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) : DegenerateElliptic (effOpStar E) := by
  intro X Y hX hY hXY
  refine csSup_le_csSup (effOpStar_set_bddAbove hd E X) (effOpStar_set_nonempty hd E hE hY)
    fun l hl => ?_
  have h := (muBar_le_add muMatrixMonotone hd E l X (Y - X) hXY).2
  rw [add_sub_cancel] at h
  exact lt_of_lt_of_le hl h

/-- The shift identity `F*(M + tI) = F*(M) - dt`. -/
theorem effOpStar_add_smul_one (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (t : ℝ) :
    effOpStar E (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) = effOpStar E M - d * t := by
  have hset : {l : ℝ | 0 < muStarBar E l (M + t • 1)} =
      (fun l => l - d * t) '' {l : ℝ | 0 < muStarBar E l M} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_image]
    rw [(muBar_shift muShift hd E l t M).2]
    constructor
    · intro h; exact ⟨l + d * t, h, by ring⟩
    · rintro ⟨l', hl', rfl⟩; rwa [sub_add_cancel]
  unfold effOpStar
  rw [hset]
  have hmono : Monotone (fun l : ℝ => l - d * t) := fun a b h => by simp only; linarith
  have hcont : Continuous (fun l : ℝ => l - d * t) := continuous_id.sub continuous_const
  exact (hmono.map_csSup_of_continuousAt hcont.continuousAt
    (effOpStar_set_nonempty hd E hE hM) (effOpStar_set_bddAbove hd E M)).symm

/-- Private copy of `Proofs/Sec7/LimitObstacleGamma.lean`'s `hessian_isSymm_of_contDiffAt` (same
name), so that both modules can be imported together. -/
private theorem hessian_isSymm_of_contDiffAt {φ : Rd d → ℝ} {x : Rd d}
    (hφ : ContDiffAt ℝ 2 φ x) : (hessian φ x).IsSymm := by
  have hsym := ContDiffAt.isSymmSndFDerivAt hφ (by simp)
  ext i j
  simp only [hessian, Matrix.transpose_apply, Matrix.of_apply]
  exact hsym _ _

/-- The `μ*`-constraint of `singleSourceObstacleSetStar` is `F*(D²u) ≥ 0` tested from below. -/
theorem viscFromBelowMuStar_iff (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) (U : Set (Rd d)) (u : Rd d → ℝ) :
    ViscFromBelowMuStar E U u ↔ ViscFromBelowGE (effOpStar E) U u := by
  constructor
  · intro h x hx φ hφ hloc
    exact (effOpStar_nonneg_iff hd E hE (hessian_isSymm_of_contDiffAt hφ)).2 (h x hx φ hφ hloc)
  · intro h x hx φ hφ hloc
    exact (effOpStar_nonneg_iff hd E hE (hessian_isSymm_of_contDiffAt hφ)).1 (h x hx φ hφ hloc)

/-! ### The minimality step -/

/-- **Step**: almost surely, every subsequential limit `u` is a viscosity subsolution of
`F*(D²u) ≤ 0` where it is positive (off the origin): if `φ` touches `u` from above at `a ≠ 0` with
`u(a) > 0`, then `μ*(l, D²φ(a)) = 0` for every `l > 0`. Route: if `μ*(l, H) > 0`,
`l > 0`, `H = D²φ(a)`, take the lattice point `x_n` near `h a` maximizing `v_n - h²φ(·/h)` on a
ball (strict touching); the gap `h²φ(·/h) + c_n - v_n ≥ 0` vanishes at `x_n` and has bounded
Laplacian, so it is `≤ C|x - x_n|²` (Harnack, as in the proof of Lemma 7.5); a `μ*`-near-maximizer
on `B_{θρh}(x_n)` with a contact point in `B_{βθρh}(x_n)` (Lemma 6.2, `C(β)` form), corrected by an
integer affine function, lies below `v_n` at the contact point and above it on the sphere when `β` is
small; its minimum with `v_n` is stabilizing and smaller than `v_n`, contradicting the leastness of
the odometer. No flatness and no recurrence. -/
def SSLimitSubStarStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
      ViscFromAboveLE (effOpStar E) {x : Rd d | x ≠ 0 ∧ 0 < u x} u

/-- **Step (O*)**: minimality at the origin: almost surely, if `v + G` is a
subsequential limit, `v(0) ≤ w(0)` for every member `w` of the `F*`-set. The touching argument
needs a point `a ≠ 0`, and the members are constrained only off the origin. -/
def SSOriginStarStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ᵐ η ∂E.P, ∀ v : Rd d → ℝ, Continuous v →
      IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
        ∀ w ∈ singleSourceObstacleSetStar E, v 0 ≤ w 0

/-- The subsequential limits vanish outside a ball (a consequence of `SSOuterBoundStmt`). -/
def SSLimitSupportStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u → ∃ R : ℝ, ∀ x : Rd d, R < ‖x‖ → u x = 0

/-- **Step** from subsolution, (O*), the support of the limits and the comparison principle. -/
theorem ssLimitMinimalStar_of_steps (hS : SSLimitSubStarStmt) (hO : SSOriginStarStmt)
    (hB : SSLimitSupportStmt) (hCIL : ShiftComparisonStmt) : SSLimitMinimalStarStmt := by
  intro d hd E hmax
  have hd1 : 1 ≤ d := by omega
  have hE : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hmax]; omega
  filter_upwards [hS d hd E hmax, hO d hd E hmax, hB d hd E hmax] with η hSη hOη hBη
  intro v hvc hv w hw x₀
  by_contra hlt
  have hpos : 0 < v x₀ - w x₀ := by linarith [not_le.1 hlt]
  set G := fundamentalSolution d
  set m := (v x₀ - w x₀) / 2 with hm_def
  have hm : 0 < m := by positivity
  have hmx : m < v x₀ - w x₀ := by rw [hm_def]; linarith
  have h0 : v 0 - w 0 ≤ 0 := by linarith [hOη v hvc hv w hw]
  obtain ⟨R, hR⟩ := hBη _ hv
  set R' := max R 0 + 1
  have hwc : Continuous w := hw.1
  set U : Set (Rd d) := {x | m < v x - w x} ∩ ball 0 R' with hU_def
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (hvc.sub hwc)).inter isOpen_ball
  have hUb : Bornology.IsBounded U := isBounded_ball.subset Set.inter_subset_right
  -- the closure of `U` avoids the origin and lies in `{m ≤ v - w}`
  have hcl : closure U ⊆ {x | m ≤ v x - w x} :=
    (closure_mono Set.inter_subset_left).trans
      (closure_minimal (fun x hx => by simp only [Set.mem_setOf_eq] at hx ⊢; exact hx.le)
        (isClosed_le continuous_const (hvc.sub hwc)))
  have hcl0 : ∀ x ∈ closure U, x ≠ 0 := fun x hx h => by
    have h' : m ≤ v 0 - w 0 := by have := hcl hx; rw [h] at this; exact this
    linarith
  have hGc : ContinuousOn G (closure U) :=
    (SingleSourceMin.continuousOn_fundamentalSolution d).mono fun x hx => hcl0 x hx
  -- on `closure U`, `v + G > w + G + m ≥ m > 0`
  have hwG : ∀ x, x ≠ 0 → -G x ≤ w x := hw.2.1
  -- sub- and supersolutions on `U`
  have hsub : ViscFromAboveLE (effOpStar E) U (fun x => v x + G x) := by
    intro x hx φ hφ hloc
    refine hSη _ hv x ⟨hcl0 x (subset_closure hx), ?_⟩ φ hφ hloc
    have h1 : m < v x - w x := hx.1
    have h2 := hwG x (hcl0 x (subset_closure hx))
    show 0 < v x + G x
    linarith
  have hsup : ViscFromBelowGE (effOpStar E) U (fun x => (w x + G x) + m) := by
    have hw3 := (viscFromBelowMuStar_iff hd1 E hE _ _).1 hw.2.2
    intro x hx φ hφ hloc
    have hloc' : IsLocalMin (fun y => (w y + G y) - (φ y - m)) x := by
      refine hloc.congr (Eventually.of_forall fun y => ?_); ring
    have hφ' : ContDiffAt ℝ 2 (fun y => φ y - m) x := hφ.sub contDiffAt_const
    have := hw3 x (hcl0 x (subset_closure hx)) (fun y => φ y - m) hφ' hloc'
    have hH : hessian (fun y => φ y - m) x = hessian φ x := by
      unfold hessian
      congr 1
      ext i j
      have : fderiv ℝ (fun y => φ y - m) = fderiv ℝ φ := by
        funext y; exact fderiv_sub_const _
      rw [this]
    rwa [hH] at this
  -- boundary inequality
  have hbd : ∀ x ∈ frontier U, (fun x => v x + G x) x ≤ (fun x => (w x + G x) + m) x := by
    intro x hx
    have hxcl : x ∈ closure U := frontier_subset_closure hx
    have hxU : x ∉ U := fun h => (hUo.frontier_eq ▸ hx).2 h
    show v x + G x ≤ (w x + G x) + m
    by_cases hxb : x ∈ ball 0 R'
    · have : ¬ m < v x - w x := fun h => hxU ⟨h, hxb⟩
      linarith [not_lt.1 this]
    · -- outside the ball `u = 0 ≤ w + G`
      have hxR : R < ‖x‖ := by
        rw [mem_ball, dist_zero_right, not_lt] at hxb
        have : R ≤ max R 0 := le_max_left _ _
        linarith
      have hu0 := hR x hxR
      have h2 := hwG x (hcl0 x hxcl)
      linarith
  have hcmp := hCIL d hd1 (effOpStar E) (degenerateElliptic_effOpStar hd1 E hE)
    (fun M hM t => effOpStar_add_smul_one hd1 E hE hM t) U hUo hUb
    (fun x => v x + G x) (fun x => (w x + G x) + m)
    ((hvc.continuousOn).add hGc) ((hwc.continuousOn.add hGc).add continuousOn_const)
    hsub hsup hbd
  have hx₀U : x₀ ∈ U := by
    refine ⟨hmx, ?_⟩
    rw [mem_ball, dist_zero_right]
    by_contra hge
    have hxR : R < ‖x₀‖ := by
      have : R ≤ max R 0 := le_max_left _ _
      linarith [not_lt.1 hge]
    have hu0 := hR x₀ hxR
    have h2 := hwG x₀ (fun h => by rw [h] at hpos; linarith)
    linarith
  have key : v x₀ + G x₀ ≤ (w x₀ + G x₀) + m := hcmp x₀ (subset_closure hx₀U)
  linarith

/-- **Theorem 9.2, `F*`-variant** from compactness, (O*), the support of the limits and
Alexandrov's theorem. -/
theorem singleSourceTheoremStar_of_remainingSteps (hComp : SSCompactnessStmt)
    (hS : SSLimitSubStarStmt) (hO : SSOriginStarStmt) (hB : SSLimitSupportStmt)
    (hCIL : ShiftComparisonStmt) : SingleSourceTheoremStarStmt :=
  singleSourceTheoremStar_of_compactness_minimal hComp (ssLimitMinimalStar_of_steps hS hO hB hCIL)

/-! ### The support of the limits from outer bound -/

theorem norm_toE_latticeRound_ge (y : Rd d) : ‖y‖ - Real.sqrt d ≤ ‖toE (latticeRound y)‖ := by
  have h1 : ‖toE (latticeRound y) - y‖ ≤ Real.sqrt d := by
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    have : ∀ i : Fin d, ‖(toE (latticeRound y) - y) i‖ ^ 2 ≤ 1 := fun i => by
      simp only [PiLp.sub_apply, toE_apply, latticeRound, Real.norm_eq_abs, sq_abs]
      have h2 := Int.floor_le (y i)
      have h3 := Int.lt_floor_add_one (y i)
      nlinarith
    calc ∑ i, ‖(toE (latticeRound y) - y) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => this i
      _ = d := by simp
  have h4 := norm_sub_norm_le y (toE (latticeRound y))
  rw [norm_sub_rev] at h1
  linarith [norm_sub_rev y (toE (latticeRound y))]

/-- `SSOuterBoundStmt` (toppled set in `B_{R (n+1)^{1/d}}`) gives the support of the limits. -/
theorem ssLimitSupport_of_outerBound (hOB : SSOuterBoundStmt) : SSLimitSupportStmt := by
  intro d hd E hmax
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨R, hR0, hR⟩ := hOB d hd E.ηmin
  filter_upwards [ae_all_iff.2 E.bounded] with η hη
  have hηb : ∀ x, E.ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2 := fun x => ⟨(hη x).1, hmax ▸ (hη x).2⟩
  intro u hu
  refine ⟨2 * R + Real.sqrt d, fun x hx => ?_⟩
  obtain ⟨nk, hnk, hconv⟩ := hu
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx
    have := Real.sqrt_nonneg (d : ℝ); linarith
  have hlim := hconv.tendsto_at hx0
  have hev : ∀ᶠ k in atTop,
      rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k) x = 0 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hn1 : 1 ≤ nk k := le_trans hk (hnk.id_le k)
    set n := nk k
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    set h : ℝ := (n : ℝ) ^ (1 / (d : ℝ))
    have hh1 : 1 ≤ h := Real.one_le_rpow hnR (by positivity)
    -- `(n + 1)^{1/d} ≤ 2 h`
    have hn2 : ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ 2 * h := by
      have h2n : (n : ℝ) + 1 ≤ 2 * n := by linarith
      calc ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ (2 * (n : ℝ)) ^ (1 / (d : ℝ)) :=
            Real.rpow_le_rpow (by positivity) h2n (by positivity)
        _ = (2 : ℝ) ^ (1 / (d : ℝ)) * h := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * h := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : (2 : ℝ) ^ (1 / (d : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num)
                (by rw [div_le_one hdpos]; exact_mod_cast hd1)
            simpa using this
    have hz := norm_toE_latticeRound_ge (h • x)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)] at hz
    have hzero : singleSourceOdometer η n (latticeRound (h • x)) = 0 := by
      refine hR η hηb n _ ?_
      have hsq : Real.sqrt d ≤ h * Real.sqrt d := le_mul_of_one_le_left (Real.sqrt_nonneg _) hh1
      nlinarith
    simp only [rescaleSingleSource, h] at hzero ⊢
    rw [hzero, Int.cast_zero, mul_zero]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm))

/-- **Theorem 9.2, `F*`-variant** from compactness and outer bound, (O*) and the comparison
principle. -/
theorem singleSourceTheoremStar_of_outerBound (hComp : SSCompactnessStmt)
    (hOB : SSOuterBoundStmt) (hS : SSLimitSubStarStmt) (hO : SSOriginStarStmt)
    (hCIL : ShiftComparisonStmt) : SingleSourceTheoremStarStmt :=
  singleSourceTheoremStar_of_remainingSteps hComp hS hO (ssLimitSupport_of_outerBound hOB) hCIL

end RandomSandpile

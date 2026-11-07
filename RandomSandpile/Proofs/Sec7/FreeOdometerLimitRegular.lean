import RandomSandpile.Proofs.Sec7.MainTheoremUInterior
import RandomSandpile.Proofs.Sec7.LimitObstacleGamma
import RandomSandpile.Proofs.Sec7.MainTheoremViscEff
import RandomSandpile.Proofs.Sec7.MainTheoremUniqueness
import RandomSandpile.Proofs.Sec5.MuBounded
import RandomSandpile.Steps.Sec7.PegdenSmartRegularity

/-! # Regularity of the limits of rescaled free odometers

`freeOdometerLimitRegular : FreeOdometerLimitRegularStmt` (no input). Almost surely (`η` bounded),
every uniform limit `v` of a subsequence of `v̄_n = n⁻² v_n([n ·])` is continuous (Lemma 7.2,
`continuous_of_isOdoSubseqLimit`), vanishes outside a ball (Lemma 7.2's box,
`freeOdometerUpperBound_of_oneDim`), and satisfies `|Δv| ≤ K` in `ℝ^d` in the viscosity sense with
`K = 2d + |η_min| + |η_max|`, the bound of `freeOdometerLapBound`.

The viscosity inequalities are the consistency of the discrete Laplacian
(`viscFromAboveGE_of_lap_ge`, `viscFromBelowLE_of_lap_le`). If `v - φ` has a local maximum at `x`
and `tr D²φ(x) + K < 0`, the quadratic `Q = p·(· - x) + q_{D²φ(x)}(· - x) + q_l(· - x)`, `l > 0`
small, touches `v` strictly from above at `x` (Taylor). The lattice function
`v_n - n² Q(·/n)` has discrete Laplacian `Δ_{ℤ^d} v_n - l - tr D²φ(x) > 0`, so it has no
supergradient at any point of `nB_r(x) ∩ ℤ^d` (`supGrad_eq_empty_of_lapR_pos`), and the rescaled
ABP principle `principle_generic` with mass `0` gives a point `y` of the sphere `∂B_r(x)` with
`v(x) - Q(x) ≤ v(y) - Q(y)`, against the strict touching. The other inequality is symmetric. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

namespace FreeLimitRegular

variable {d : ℕ}

/-- No supergradient at a point where the discrete Laplacian is positive. -/
theorem supGrad_eq_empty_of_lapR_pos {g : Site d → ℝ} {A : Set (Site d)} {z : Site d}
    (hz : z ∈ A) (h : 0 < lapR g z) : supGrad g z A = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  have key : ∀ i, g (z + unit i) + g (z - unit i) ≤ 2 * g z := by
    intro i
    have h1 := hp _ (add_unit_mem_dClosure hz i)
    have h2 := hp _ (sub_unit_mem_dClosure hz i)
    rw [inner_toE_add_unit] at h1
    rw [inner_toE_sub_unit] at h2
    linarith
  have hs : nbrSum g z ≤ 2 * d * g z := by
    simp only [nbrSum]
    calc ∑ i, (g (z + unit i) + g (z - unit i)) ≤ ∑ _i : Fin d, 2 * g z :=
          Finset.sum_le_sum fun i _ => key i
      _ = 2 * d * g z := by simp [Finset.sum_const, Finset.card_univ]; ring
  simp only [lapR] at h
  linarith

/-- The supergradient set is empty where the discrete Laplacian is positive. -/
theorem supGradSet_eq_empty {g : Site d → ℝ} {A : Set (Site d)} (h : ∀ z ∈ A, 0 < lapR g z) :
    supGradSet g A = ∅ := by
  simp only [supGradSet, Set.iUnion_eq_empty]
  exact fun z hz => supGrad_eq_empty_of_lapR_pos hz (h z hz)

theorem lapR_const_mul' (β : ℝ) (g : Site d → ℝ) (x : Site d) :
    lapR (fun y => β * g y) x = β * lapR g x := by
  simp only [lapR, nbrSum, ← mul_add, ← Finset.mul_sum]; ring

theorem toE_zero' : toE (0 : Site d) = 0 := by
  ext i; simp [toE]

/-- Affine functions are discrete harmonic. -/
theorem lapR_affine' (c0 : ℝ) (c : Rd d) (x : Site d) :
    lapR (fun y => c0 + inner ℝ c (toE y - toE 0)) x = 0 := by
  simp only [lapR, nbrSum]
  have h : ∀ i, (c0 + inner ℝ c (toE (x + unit i) - toE 0)) +
      (c0 + inner ℝ c (toE (x - unit i) - toE 0)) = 2 * (c0 + inner ℝ c (toE x - toE 0)) := by
    intro i
    have e1 : toE (x + unit i) - toE 0 = (toE (x + unit i) - toE x) + (toE x - toE 0) := by abel
    have e2 : toE (x - unit i) - toE 0 = (toE (x - unit i) - toE x) + (toE x - toE 0) := by abel
    rw [e1, e2, inner_add_right, inner_add_right, inner_toE_add_unit, inner_toE_sub_unit]
    ring
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp [Finset.sum_const, Finset.card_univ]
  ring

/-- The discrete Laplacian of `σ (u - n² Q(·/n))` for a quadratic `Q`. -/
theorem lapR_rescaled (hd : 1 ≤ d) (σ : ℝ) (u : Site d → ℤ) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.IsSymm) (p a : Rd d) (l : ℝ) {n : ℕ} (hn : n ≠ 0) (z : Site d) :
    lapR (fun z => σ * ((u z : ℝ) - (n : ℝ) ^ 2 *
      (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a)) ((n : ℝ)⁻¹ • toE z))) z =
      σ * ((lap u z : ℝ) - (l + M.trace)) := by
  obtain ⟨c, c0, hcq⟩ := OpenMaxPrinciple.rescaled_quad_affine hM p a l
    (n := (n : ℝ)) (Nat.cast_ne_zero.2 hn)
  have hfun : (fun z => σ * ((u z : ℝ) - (n : ℝ) ^ 2 *
      (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a)) ((n : ℝ)⁻¹ • toE z))) =
      fun z => σ * ((fun y => (u y : ℝ)) z - (fun y => (qlZ l y + qMZ M y) +
        (c0 + inner ℝ c (toE y - toE 0))) z) := by
    funext y
    simp only [hcq, qlZ, qMZ, toE_zero', sub_zero]
    ring
  rw [hfun, lapR_const_mul', PegdenSmartRegularity.lapR_sub, lapR_intCast, lapR_add,
    lapQuadratic d hd, lapR_affine']
  ring

/-- **Consistency, lower bound**: limits of rescaled lattice functions with `Δ_{ℤ^d} ≥ -K`
satisfy `tr D²φ + K ≥ 0` at local maxima of `v - φ`. -/
theorem viscFromAboveGE_of_lap_ge (hd : 1 ≤ d) {nk : ℕ → ℕ} (hnk : StrictMono nk)
    {vk : ℕ → Site d → ℤ} {v : Rd d → ℝ} (hv : Continuous v)
    (hconv : TendstoUniformly (fun k => rescaleOdo (vk k) (nk k)) v atTop) {K : ℝ}
    (hK : ∀ k z, -K ≤ (lap (vk k) z : ℝ)) :
    ViscFromAboveGE (fun X => X.trace + K) Set.univ v := by
  intro x _ φ hφ hmax
  simp only
  by_contra hneg
  push Not at hneg
  set H := hessian φ x with hHdef
  have hH : H.IsSymm := hessian_isSymm_of_contDiffAt hφ
  set δ : ℝ := -(H.trace + K) with hδ
  have hδ0 : 0 < δ := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set κ : ℝ := δ / (8 * d) with hκ
  have hκ0 : 0 < κ := by positivity
  set l : ℝ := δ / 2 with hl
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ hκ0
  obtain ⟨ρ₂, hρ₂, hm⟩ := Metric.eventually_nhds_iff.1 hmax
  set r : ℝ := min ρ₁ ρ₂ / 2 with hr
  have hr0 : 0 < r := by positivity
  set p : Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x) with hp
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (1 : ℝ) *
      ((vk k z : ℝ) - (nk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - x) + qM H (X - x) + ql l (X - x))
          ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball x r) (nk k))) ≤ 0 ∧
      (0 : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards [hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : nk k ≠ 0 := by omega
    refine ⟨?_, ENNReal.zero_ne_top⟩
    rw [supGradSet_eq_empty fun z _ => ?_]
    · simp
    · rw [lapR_rescaled hd 1 (vk k) hH p x l hn0 z]
      linarith [hK k z]
  have hV : Tendsto (fun k => ((0 : ℝ≥0∞)).toReal / (nk k : ℝ) ^ d) atTop (𝓝 0) := by simp
  obtain ⟨y, hy, h⟩ := OpenMaxPrinciple.principle_generic hd (σ := 1) (V := fun _ => 0)
    (OpenMaxPrinciple.continuous_quadratic p x H l) hv hnk hconv hr0 hvol hV (mem_ball_self hr0)
  rw [mem_sphere, dist_eq_norm] at hy
  have hy1 : ‖y - x‖ < ρ₁ := by rw [hy]; linarith [min_le_left ρ₁ ρ₂]
  have hy2 : dist y x < ρ₂ := by rw [dist_eq_norm, hy]; linarith [min_le_right ρ₁ ρ₂]
  have hTy := abs_le.1 (hT y hy1)
  have hmy : v y - φ y ≤ v x - φ x := hm hy2
  simp only [one_mul, sub_self, inner_zero_right, qM_zero_right, ql_zero_right, add_zero,
    sub_zero] at h
  have hql : ql l (y - x) = l * r ^ 2 / (2 * d) := by rw [ql, hy]
  have hfd : inner ℝ p (y - x) = fderiv ℝ φ x (y - x) := by
    rw [hp, InnerProductSpace.toDual_symm_apply]
  rw [hy] at hTy
  have hkey : l * r ^ 2 / (2 * d) = 2 * (κ * r ^ 2) := by
    rw [hl, hκ]; field_simp; ring
  have hr2 : 0 < κ * r ^ 2 := by positivity
  rw [hql, hfd] at h
  linarith [hTy.2]

/-- **Consistency, upper bound**: limits of rescaled lattice functions with `Δ_{ℤ^d} ≤ K`
satisfy `tr D²φ - K ≤ 0` at local minima of `v - φ`. -/
theorem viscFromBelowLE_of_lap_le (hd : 1 ≤ d) {nk : ℕ → ℕ} (hnk : StrictMono nk)
    {vk : ℕ → Site d → ℤ} {v : Rd d → ℝ} (hv : Continuous v)
    (hconv : TendstoUniformly (fun k => rescaleOdo (vk k) (nk k)) v atTop) {K : ℝ}
    (hK : ∀ k z, (lap (vk k) z : ℝ) ≤ K) :
    ViscFromBelowLE (fun X => X.trace - K) Set.univ v := by
  intro x _ φ hφ hmin
  simp only
  by_contra hneg
  push Not at hneg
  set H := hessian φ x with hHdef
  have hH : H.IsSymm := hessian_isSymm_of_contDiffAt hφ
  set δ : ℝ := H.trace - K with hδ
  have hδ0 : 0 < δ := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set κ : ℝ := δ / (8 * d) with hκ
  have hκ0 : 0 < κ := by positivity
  set l : ℝ := δ / 2 with hl
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ hκ0
  obtain ⟨ρ₂, hρ₂, hm⟩ := Metric.eventually_nhds_iff.1 hmin
  set r : ℝ := min ρ₁ ρ₂ / 2 with hr
  have hr0 : 0 < r := by positivity
  set p : Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x) with hp
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (-1 : ℝ) *
      ((vk k z : ℝ) - (nk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - x) + qM H (X - x) + ql (-l) (X - x))
          ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball x r) (nk k))) ≤ 0 ∧
      (0 : ℝ≥0∞) ≠ ⊤ := by
    filter_upwards [hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : nk k ≠ 0 := by omega
    refine ⟨?_, ENNReal.zero_ne_top⟩
    rw [supGradSet_eq_empty fun z _ => ?_]
    · simp
    · rw [lapR_rescaled hd (-1) (vk k) hH p x (-l) hn0 z]
      linarith [hK k z]
  have hV : Tendsto (fun k => ((0 : ℝ≥0∞)).toReal / (nk k : ℝ) ^ d) atTop (𝓝 0) := by simp
  obtain ⟨y, hy, h⟩ := OpenMaxPrinciple.principle_generic hd (σ := -1) (V := fun _ => 0)
    (OpenMaxPrinciple.continuous_quadratic p x H (-l)) hv hnk hconv hr0 hvol hV
    (mem_ball_self hr0)
  rw [mem_sphere, dist_eq_norm] at hy
  have hy1 : ‖y - x‖ < ρ₁ := by rw [hy]; linarith [min_le_left ρ₁ ρ₂]
  have hy2 : dist y x < ρ₂ := by rw [dist_eq_norm, hy]; linarith [min_le_right ρ₁ ρ₂]
  have hTy := abs_le.1 (hT y hy1)
  have hmy : v x - φ x ≤ v y - φ y := hm hy2
  simp only [sub_self, inner_zero_right, qM_zero_right, ql_zero_right, add_zero,
    sub_zero] at h
  have hql : ql (-l) (y - x) = -(l * r ^ 2 / (2 * d)) := by rw [ql, hy]; ring
  have hfd : inner ℝ p (y - x) = fderiv ℝ φ x (y - x) := by
    rw [hp, InnerProductSpace.toDual_symm_apply]
  rw [hy] at hTy
  have hkey : l * r ^ 2 / (2 * d) = 2 * (κ * r ^ 2) := by
    rw [hl, hκ]; field_simp; ring
  have hr2 : 0 < κ * r ^ 2 := by positivity
  rw [hql, hfd] at h
  linarith [hTy.1]

end FreeLimitRegular

open FreeLimitRegular FreeMaxPrinciple in
/-- **Regularity of the limits**, for one bounded `η` (deterministic form): a subsequential limit
`v` of the rescaled free odometers is continuous, vanishes outside a ball and has
`|Δv| ≤ 2d + |η_min| + |η_max|` in `ℝ^d` in the viscosity sense. -/
theorem freeLimitRegular_of_bounded {d : ℕ} (hd : 2 ≤ d) {W : Set (Rd d)}
    (hW : IsLipschitzDomain W) {ηmin ηmax : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) {v : Rd d → ℝ} (hv : IsOdoSubseqLimit η W v) :
    Continuous v ∧ (∃ R : ℝ, ∀ x : Rd d, R ≤ ‖x‖ → v x = 0) ∧
      ViscFromAboveGE (fun X => X.trace + (2 * d + |(ηmin : ℝ)| + |(ηmax : ℝ)|)) Set.univ v ∧
      ViscFromBelowLE (fun X => X.trace - (2 * d + |(ηmin : ℝ)| + |(ηmax : ℝ)|)) Set.univ v := by
  have hd1 : 1 ≤ d := by omega
  have hvc : Continuous v := continuous_of_isOdoSubseqLimit hd hW hη hv
  obtain ⟨nk, hnk, hconv⟩ := hv
  have hlap : ∀ k z, |(lap (freeOdometer η (discretize W (nk k))) z : ℝ)| ≤
      2 * d + |(ηmin : ℝ)| + |(ηmax : ℝ)| := fun k z => by
    have h := freeOdometerLapBound d ηmin ηmax η (discretize W (nk k)) hη
      (PegdenSmartRegularity.freeOdometer_stabilizing_nonempty hd1 η hW.1 (nk k)) z
    have h' : ((|lap (freeOdometer η (discretize W (nk k))) z| : ℤ) : ℝ) ≤
        ((2 * (d : ℤ) + |ηmin| + |ηmax| : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  refine ⟨hvc, ?_, viscFromAboveGE_of_lap_ge hd1 hnk hvc hconv
    (fun k z => (abs_le.1 (hlap k z)).1),
    viscFromBelowLE_of_lap_le hd1 hnk hvc hconv (fun k z => (abs_le.1 (hlap k z)).2)⟩
  obtain ⟨C, R₀, hUB⟩ := freeOdometerUpperBound_of_oneDim oneDimToppling d hd W hW.1 ηmax
  refine ⟨(d : ℝ) * (2 * R₀ + 1) + 1, fun x hx => ?_⟩
  have hxn : (d : ℝ) * (2 * R₀ + 1) < ‖x‖ := by linarith
  have hev : ∀ᶠ k in atTop,
      rescaleOdo (freeOdometer η (discretize W (nk k))) (nk k) x = 0 := by
    filter_upwards [hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    obtain ⟨i, hi⟩ := exists_le_abs_latticeRound hk R₀ hxn
    simp only [rescaleOdo]
    rw [(hUB η (fun y => (hη y).2) (nk k)).2.2 _ ⟨i, hi⟩]
    simp
  exact tendsto_nhds_unique (hconv.tendsto_at x)
    (tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm))

/-- **Regularity of the limits** (`FreeOdometerLimitRegularStmt`), with
`K = 2d + |η_min| + |η_max|`; no input. -/
theorem freeOdometerLimitRegular : FreeOdometerLimitRegularStmt := by
  intro d hd E W hW
  refine ⟨{η | ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax}, ae_iff.1 (ae_all_iff.2 E.bounded),
    2 * d + |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)|, ?_⟩
  intro η hη0 nk hnk v hconv
  exact freeLimitRegular_of_bounded hd hW hη0 ⟨nk, hnk, hconv⟩

end RandomSandpile

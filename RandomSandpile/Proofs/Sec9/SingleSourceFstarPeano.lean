import RandomSandpile.Proofs.Sec9.SingleSourceFstarScale
import RandomSandpile.Proofs.Sec6.MuLipschitzShell
import RandomSandpile.Proofs.Sec6.StrictConcavitySlope
import RandomSandpile.Proofs.Sec7.LimitObstacle

/-!
# Theorem 9.2, `F*`-variant: `F*(D²u) ≤ 0` at Peano points

 §4.3. Almost surely, at every point `b ≠ 0` where a subsequential limit `u`
of the rescaled single-source odometers is positive and has a second-order Peano expansion with
symmetric matrix `N`, `F*(N) ≤ 0` (`ssPeanoStar : SSPeanoStarStmt`), from Lemma 5.5
(`MuConvergenceStmt`) and step (`SSCompactnessStmt`, for the continuity of `u` near `b`).

* `ae_false_peano` (fixed `M'`): on the event of Lemma 5.5 at `(0, M')`, a Peano point with
  `b₋/2 |h|² ≤ q_{M' - N}(h) ≤ b₊/2 |h|²`, `β² b₊ < b₋` and `C (1 - β^d) < μ*(0, M')` (`C` the site
  bound of Lemma 5.4) is impossible: at a large integer scale `m` the hypotheses of
  `false_at_scale` hold (`approx_at_point`: Taylor expansion and uniform convergence of
  `m^{-2} v_n([m·])`; `lower_at_point`; `eventually_scale`: the quadratic gap; Lemma 5.5 and lattice
  point counting in `B_r(b)`, `B_{βr}(b)`: `tendsto_muStar_div_pow`, `tendsto_ncard_diff`).
* `ssPeanoStar`: if `F*(N) > 0`, some `l > 0` has `α = μ*(l, N) > 0`; a rational symmetric `M'`
  (`symQ`) close to `N + (l/2d) I` has `μ*(0, M') ≥ α` (monotonicity and the shift identity) and
  `M' - N ≈ (l/2d) I`, so `ae_false_peano` applies on the countable intersection of events.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceFstar

open EffectiveOperatorBasic

variable {d : ℕ}

/-! ### Lattice point counting in concentric balls -/

/-- `|B_ρ(b)| = ρ^d |B_1|`. -/
theorem volume_real_ball_eq (hd : 1 ≤ d) (b : Rd d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume.real (ball b ρ) = ρ ^ d * volume.real (ball (0 : Rd d) 1) := by
  have : NeZero d := ⟨by omega⟩
  rw [measureReal_def, Measure.addHaar_ball _ _ hρ, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hρ d), measureReal_def]

theorem tendsto_ncard_discretize_ball (hd : 1 ≤ d) (b : Rd d) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun m : ℕ => ((discretize (ball b ρ) m).ncard : ℝ) / (m : ℝ) ^ d) atTop
      (𝓝 (volume.real (ball b ρ))) := by
  have : NeZero d := ⟨by omega⟩
  have h := MuLipschitzShell.tendsto_ncard_discretize (W := ball b ρ) isBounded_ball
    measurableSet_ball (by rw [frontier_ball b hρ.ne']; exact Measure.addHaar_sphere _ _ _)
  rwa [LimitSlopeMass.covolume_intLattice, div_one] at h

/-- `|A_m ∖ I_m| / m^d → (1 - β^d) |B_r|` for `A_m = discretize (B_r(b)) m`,
`I_m = discretize (B_{βr}(b)) m`. -/
theorem tendsto_ncard_diff (hd : 1 ≤ d) (b : Rd d) {r β : ℝ} (hr : 0 < r) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    Tendsto (fun m : ℕ => ((discretize (ball b r) m \ discretize (ball b (β * r)) m).ncard : ℝ) /
      (m : ℝ) ^ d) atTop (𝓝 ((1 - β ^ d) * volume.real (ball b r))) := by
  have h1 := tendsto_ncard_discretize_ball hd b hr
  have h2 := tendsto_ncard_discretize_ball hd b (mul_pos hβ0 hr)
  have hβr : β * r ≤ r := mul_le_of_le_one_left hr.le hβ1
  have hsub : ∀ m : ℕ, discretize (ball b (β * r)) m ⊆ discretize (ball b r) m :=
    fun m x hx => Set.smul_set_mono (ball_subset_ball hβr) hx
  have heq : ∀ m : ℕ,
      ((discretize (ball b r) m \ discretize (ball b (β * r)) m).ncard : ℝ) / (m : ℝ) ^ d =
        ((discretize (ball b r) m).ncard : ℝ) / (m : ℝ) ^ d -
          ((discretize (ball b (β * r)) m).ncard : ℝ) / (m : ℝ) ^ d := by
    intro m
    have h := Set.ncard_sdiff_add_ncard_of_subset (hsub m)
      (SubadditiveLipschitz.discretize_finite isBounded_ball m)
    have h' : ((discretize (ball b r) m \ discretize (ball b (β * r)) m).ncard : ℝ) +
        ((discretize (ball b (β * r)) m).ncard : ℝ) = ((discretize (ball b r) m).ncard : ℝ) := by
      exact_mod_cast h
    rw [← sub_div]
    congr 1
    linarith
  have hlim : (1 - β ^ d) * volume.real (ball b r) =
      volume.real (ball b r) - volume.real (ball b (β * r)) := by
    rw [volume_real_ball_eq hd b hr.le, volume_real_ball_eq hd b (mul_pos hβ0 hr).le, mul_pow]
    ring
  rw [hlim]
  exact (h1.sub h2).congr fun m => (heq m).symm

/-- Lemma 5.5 normalized by `m^d`: `μ*(A_m)/|A_m| → α` gives `μ*(A_m)/m^d → α |B_r|`. -/
theorem tendsto_muStar_div_pow (hd : 1 ≤ d) (b : Rd d) {r : ℝ} (hr : 0 < r) {f : ℕ → ℝ} {α : ℝ}
    (hlim : Tendsto (fun n : ℕ => f n / ((discretize (ball b r) n).ncard : ℝ)) atTop (𝓝 α)) :
    Tendsto (fun m : ℕ => f m / (m : ℝ) ^ d) atTop (𝓝 (α * volume.real (ball b r))) := by
  have hV1 : 0 < volume.real (ball b r) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume b hr).ne' measure_ball_lt_top.ne
  have hcount := tendsto_ncard_discretize_ball hd b hr
  refine (hlim.mul hcount).congr' ?_
  filter_upwards [hcount.eventually (lt_mem_nhds hV1), eventually_ge_atTop 1] with m hm hm1
  have hm' : 0 < ((discretize (ball b r) m).ncard : ℝ) / (m : ℝ) ^ d := hm
  have hm0 : (m : ℝ) ^ d ≠ 0 := (pow_pos (by exact_mod_cast hm1) d).ne'
  have hc0 : ((discretize (ball b r) m).ncard : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_div] at hm'
    exact lt_irrefl 0 hm'
  field_simp

/-! ### The ingredients at one scale -/

/-- The quadratic gap and the positivity margin at all large scales `m`. -/
theorem eventually_scale {ε r β bm bp K ub : ℝ} (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (hbp : 0 ≤ bp) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hbm : bm = 16 * ε + β ^ 2 * bp)
    (hK : K = 4 * (bp + 3 * ε + 1)) (hub : 0 < ub) (hru : r ≤ ub / K) :
    ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧ 1 / (m : ℝ) ≤ r ∧
      bp / 2 * (β * ((m : ℝ) * r)) ^ 2 + 2 * (ε * ((m : ℝ) * r) ^ 2) +
        2 * (((d : ℝ) + 1) * ((m : ℝ) * r + 1) + 1) + 1 ≤ bm / 2 * ((m : ℝ) * r) ^ 2 ∧
      bp / 2 * (β * ((m : ℝ) * r)) ^ 2 + 2 * (ε * ((m : ℝ) * r) ^ 2) +
        2 * (((d : ℝ) + 1) * ((m : ℝ) * r + 1) + 1) + 1 ≤
          (m : ℝ) ^ 2 * (ub / 2 - ε * r ^ 2 / 2) := by
  have h6εr : 0 < 6 * ε * r ^ 2 := mul_pos (mul_pos (by norm_num) hε) (pow_pos hr 2)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop
    (max (1 / r) (max ((2 * ((d : ℝ) + 1) * r + 2 * d + 5) / (6 * ε * r ^ 2))
      (4 * (2 * ((d : ℝ) + 1) * r + 2 * d + 5) / ub)) + 1))] with m hm
  have ha := le_max_left (1 / r) (max ((2 * ((d : ℝ) + 1) * r + 2 * d + 5) / (6 * ε * r ^ 2))
    (4 * (2 * ((d : ℝ) + 1) * r + 2 * d + 5) / ub))
  have hbm1 := le_max_right (1 / r) (max ((2 * ((d : ℝ) + 1) * r + 2 * d + 5) / (6 * ε * r ^ 2))
    (4 * (2 * ((d : ℝ) + 1) * r + 2 * d + 5) / ub))
  have hb2 := le_max_left ((2 * ((d : ℝ) + 1) * r + 2 * d + 5) / (6 * ε * r ^ 2))
    (4 * (2 * ((d : ℝ) + 1) * r + 2 * d + 5) / ub)
  have hc2 := le_max_right ((2 * ((d : ℝ) + 1) * r + 2 * d + 5) / (6 * ε * r ^ 2))
    (4 * (2 * ((d : ℝ) + 1) * r + 2 * d + 5) / ub)
  have hrinv : 0 < 1 / r := one_div_pos.2 hr
  have hm' : max (1 / r) (max ((2 * ((d : ℝ) + 1) * r + 2 * d + 5) / (6 * ε * r ^ 2))
      (4 * (2 * ((d : ℝ) + 1) * r + 2 * d + 5) / ub)) + 1 ≤ (m : ℝ) := hm
  have h1r : 1 / r ≤ (m : ℝ) := by linarith
  have hg1 : (2 * ((d : ℝ) + 1) * r + 2 * d + 5) / (6 * ε * r ^ 2) ≤ (m : ℝ) := by linarith
  have hp1 : 4 * (2 * ((d : ℝ) + 1) * r + 2 * d + 5) / ub ≤ (m : ℝ) := by linarith
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ (m : ℝ) := by linarith
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  refine ⟨by exact_mod_cast hm1R, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by linarith : (0 : ℝ) < m)]
    rw [div_le_iff₀ hr] at h1r
    linarith
  · have h6 : 2 * ((d : ℝ) + 1) * r + 2 * d + 5 ≤ (m : ℝ) * (6 * ε * r ^ 2) :=
      (div_le_iff₀ h6εr).1 hg1
    have h7 := mul_le_mul_of_nonneg_left h6 hx0
    have h8 : (2 * (d : ℝ) + 5) * 1 ≤ (2 * (d : ℝ) + 5) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hm1R (by linarith)
    rw [hbm]
    linarith
  · have hr2 : r ^ 2 ≤ r := by nlinarith
    have hKpos : 0 < K := by rw [hK]; linarith
    have hrK : r * K ≤ ub := (le_div_iff₀ hKpos).1 hru
    have h1 : r ^ 2 * K ≤ ub := le_trans (mul_le_mul_of_nonneg_right hr2 hKpos.le) hrK
    rw [hK] at h1
    have hβ2 : β ^ 2 ≤ 1 := pow_le_one₀ hβ0 hβ1
    have hbpβ : bp * β ^ 2 ≤ bp := mul_le_of_le_one_right hbp hβ2
    have hbpr := mul_le_mul_of_nonneg_right hbpβ (sq_nonneg r)
    have hεr : 0 ≤ ε * r ^ 2 := mul_nonneg hε.le (sq_nonneg r)
    have hbr : 0 ≤ bp * r ^ 2 := mul_nonneg hbp (sq_nonneg r)
    have hr2' := sq_nonneg r
    have hcoef : ε * r ^ 2 / 2 + bp * β ^ 2 * r ^ 2 / 2 + 2 * ε * r ^ 2 ≤ ub / 4 := by linarith
    have h6 : 2 * ((d : ℝ) + 1) * r + 2 * d + 5 ≤ (m : ℝ) * (ub / 4) := by
      have := (div_le_iff₀ hub).1 hp1
      linarith
    have h7 := mul_le_mul_of_nonneg_left h6 hx0
    have h8 : (2 * (d : ℝ) + 5) * 1 ≤ (2 * (d : ℝ) + 5) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hm1R (by linarith)
    have h9 := mul_le_mul_of_nonneg_left hcoef (sq_nonneg (m : ℝ))
    linarith

/-- **The Taylor approximation of the odometer at one scale**: if `|y/m - b| < 2r`, the uniform
error of `m^{-2} v([m·])` at `y/m` is `< εr²/2` and the Taylor remainder of `u` at `b` is
`≤ (ε/8)|·|²` on `B_{2r}(b)`, then `|v(y) - T(y)| ≤ ε (m r)²`. -/
theorem approx_at_point {u : Rd d → ℝ} {b p₀ : Rd d} {N : Matrix (Fin d) (Fin d) ℝ}
    {ε r ρT : ℝ} (hε : 0 < ε) (hrT : 2 * r ≤ ρT)
    (hTb : ∀ y, ‖y - b‖ < ρT →
      |u y - u b - inner ℝ p₀ (y - b) - qM N (y - b)| ≤ ε / 8 * ‖y - b‖ ^ 2)
    {V : Site d → ℤ} {m : ℕ} (hm : m ≠ 0) {y : Site d}
    (hyb : ‖(m : ℝ)⁻¹ • toE y - b‖ < 2 * r)
    (hU : |u ((m : ℝ)⁻¹ • toE y) - rescaleOdo V m ((m : ℝ)⁻¹ • toE y)| < ε * r ^ 2 / 2) :
    |(V y : ℝ) - ((m : ℝ) ^ 2 * u b + (m : ℝ) * inner ℝ p₀ (toE y - (m : ℝ) • b) +
      qM N (toE y - (m : ℝ) • b))| ≤ ε * ((m : ℝ) * r) ^ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have hV : (V y : ℝ) = (m : ℝ) ^ 2 * rescaleOdo V m ((m : ℝ)⁻¹ • toE y) := by
    simp only [rescaleOdo, latticeRound_smul_inv_smul_toE hm]
    field_simp
  have hT := hTb ((m : ℝ)⁻¹ • toE y) (by linarith)
  have hym : toE y - (m : ℝ) • b = (m : ℝ) • ((m : ℝ)⁻¹ • toE y - b) := by
    rw [smul_sub, smul_inv_smul₀ hmne]
  rw [hV, hym, real_inner_smul_right, qM_smul]
  set F := rescaleOdo V m ((m : ℝ)⁻¹ • toE y) with hF
  set w : Rd d := (m : ℝ)⁻¹ • toE y - b with hw
  have hsq : ‖w‖ ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyb.le 2
  have h3 : ε / 8 * ‖w‖ ^ 2 ≤ ε / 8 * (2 * r) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have key : |F - (u b + inner ℝ p₀ w + qM N w)| ≤ ε * r ^ 2 := by
    rw [abs_le]
    have h1 := abs_lt.1 hU
    have h2 := abs_le.1 hT
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have e : (m : ℝ) ^ 2 * F - ((m : ℝ) ^ 2 * u b + (m : ℝ) * ((m : ℝ) * inner ℝ p₀ w) +
      (m : ℝ) ^ 2 * qM N w) = (m : ℝ) ^ 2 * (F - (u b + inner ℝ p₀ w + qM N w)) := by ring
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc (m : ℝ) ^ 2 * |F - (u b + inner ℝ p₀ w + qM N w)| ≤ (m : ℝ) ^ 2 * (ε * r ^ 2) :=
        mul_le_mul_of_nonneg_left key (sq_nonneg _)
    _ = ε * ((m : ℝ) * r) ^ 2 := by ring

/-- **Lower bound of the odometer on `A`**: `v(y) ≥ m² (u(b)/2 - εr²/2)`. -/
theorem lower_at_point {u : Rd d → ℝ} {b : Rd d} {ε r ρc : ℝ}
    (hc : ∀ ⦃y⦄, dist y b < ρc → u b / 2 < u y) (hrc : r ≤ ρc)
    {V : Site d → ℤ} {m : ℕ} (hm : m ≠ 0) {y : Site d}
    (hyb : dist ((m : ℝ)⁻¹ • toE y) b < r)
    (hU : |u ((m : ℝ)⁻¹ • toE y) - rescaleOdo V m ((m : ℝ)⁻¹ • toE y)| < ε * r ^ 2 / 2) :
    (m : ℝ) ^ 2 * (u b / 2 - ε * r ^ 2 / 2) ≤ (V y : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have hV : (V y : ℝ) = (m : ℝ) ^ 2 * rescaleOdo V m ((m : ℝ)⁻¹ • toE y) := by
    simp only [rescaleOdo, latticeRound_smul_inv_smul_toE hm]
    field_simp
  have hcu := hc (show dist ((m : ℝ)⁻¹ • toE y) b < ρc by linarith)
  rw [hV]
  have h1 := (abs_lt.1 hU).2
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  linarith

/-- The `μ*` mass condition of `false_at_scale` from the normalized comparison. -/
theorem mass_at_scale {A I : Set (Site d)} {η : Site d → ℤ} {M' : Matrix (Fin d) (Fin d) ℝ}
    {C : ℝ} {m : ℕ} (hC0 : 0 ≤ C) (hm : 0 < m) (hfin : muStar A η 0 M' ≠ ⊤)
    (h : C * (((A \ I).ncard : ℝ) / (m : ℝ) ^ d) < (muStar A η 0 M').toReal / (m : ℝ) ^ d) :
    ENNReal.ofReal (C * ((A \ I).ncard : ℝ)) < muStar A η 0 M' := by
  have hpow : (0 : ℝ) < (m : ℝ) ^ d := pow_pos (by exact_mod_cast hm) d
  rw [mul_div_assoc', div_lt_div_iff_of_pos_right hpow] at h
  rw [ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg hC0 (Nat.cast_nonneg _)) hfin]
  exact h

/-! ### The contradiction at a Peano point, fixed parameters -/

/-- **(S*) at Peano points, fixed `M'`**. -/
theorem ae_false_peano (hconv : MuConvergenceStmt) (hComp : SSCompactnessStmt) (hd : 2 ≤ d)
    (E : RandomEnvironment d) (hmax : E.ηmax = 2 * (d : ℤ) - 2) {M' : Matrix (Fin d) (Fin d) ℝ}
    (hM' : M'.IsSymm) :
    ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
      ∀ (b p₀ : Rd d) (N : Matrix (Fin d) (Fin d) ℝ), b ≠ 0 → 0 < u b →
        HasSecondOrderTaylorAt u b p₀ N →
        ∀ (β bm bp : ℝ), 0 < β → β ≤ 1 → 0 < bm → 0 ≤ bp → β ^ 2 * bp < bm →
          (max ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - 0 - M'.trace) 0 / d) ^ d * (1 - β ^ d) <
            muStarBar E 0 M' →
          (∀ h : Rd d, bm / 2 * ‖h‖ ^ 2 ≤ qM (M' - N) h ∧ qM (M' - N) h ≤ bp / 2 * ‖h‖ ^ 2) →
          False := by
  have hd1 : 1 ≤ d := by omega
  filter_upwards [(hconv d hd).1 E M' hM' 0, ae_all_iff.2 E.bounded] with η hη hbd
  rintro u ⟨nk, hnk, hconvu⟩ b p₀ N hb0 hub hTay β bm bp hβ0 hβ1 hbm hbp hββ hmass hP
  have hbd' : ∀ z, E.ηmin ≤ η z ∧ η z ≤ 2 * (d : ℤ) - 2 := fun z =>
    ⟨(hbd z).1, (hbd z).2.trans hmax.le⟩
  -- continuity of `u` off the origin (step)
  obtain ⟨φ, hφ, v, hvc, hconvφ⟩ := hComp d hd E.ηmin η hbd' nk hnk
  have hopen : IsOpen {x : Rd d | x ≠ 0} := isOpen_ne
  have huv : Set.EqOn u (fun y => v y + fundamentalSolution d y) {x : Rd d | x ≠ 0} :=
    fun y hy => tendsto_nhds_unique ((hconvu.tendsto_at hy).comp hφ.tendsto_atTop)
      (hconvφ.tendsto_at hy)
  have hucont : ContinuousOn u {x : Rd d | x ≠ 0} :=
    (hvc.continuousOn.add (SingleSourceMin.continuousOn_fundamentalSolution d)).congr huv
  -- constants
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = (max ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - 0 - M'.trace) 0 / d) ^ d := ⟨_, rfl⟩
  rw [← hC] at hmass
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (bm - β ^ 2 * bp) / 16 := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hbm16 : bm = 16 * ε + β ^ 2 * bp := by rw [hε]; ring
  obtain ⟨ρT, hρT, hTb⟩ := hTay.bound (κ := ε / 8) (div_pos hεpos (by norm_num))
  have hb0' : 0 < ‖b‖ := norm_pos_iff.2 hb0
  have hucb : ContinuousAt u b := hucont.continuousAt (hopen.mem_nhds hb0)
  obtain ⟨ρc, hρc, hc⟩ :=
    Metric.eventually_nhds_iff.1 (hucb.eventually (lt_mem_nhds (half_lt_self hub)))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * (bp + 3 * ε + 1) := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; linarith
  obtain ⟨r, hr0, hrb, hrT, hrc, hr1, hru⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ ‖b‖ / 4 ∧ r ≤ ρT / 4 ∧
      r ≤ ρc / 4 ∧ r ≤ 1 ∧ r ≤ u b / K :=
    ⟨min (min (‖b‖ / 4) (ρT / 4)) (min (ρc / 4) (min 1 (u b / K))),
      lt_min (lt_min (by linarith) (by linarith))
        (lt_min (by linarith) (lt_min one_pos (div_pos hub hKpos))),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  -- integer scales `m_k = ⌊n_k^{1/d}⌋` (as in `ssInteriorMinPrinciple_of_compactness`)
  have hdpos : (0 : ℝ) < 1 / (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    positivity
  set hk : ℕ → ℝ := fun k => (nk k : ℝ) ^ (1 / (d : ℝ)) with hhk_def
  set mk : ℕ → ℕ := fun k => ⌊hk k⌋₊ with hmk_def
  have hhk : Tendsto hk atTop atTop :=
    (tendsto_rpow_atTop hdpos).comp (tendsto_natCast_atTop_atTop.comp hnk.tendsto_atTop)
  have hmk : Tendsto mk atTop atTop := tendsto_nat_floor_atTop.comp hhk
  have ht : Tendsto (fun k => (mk k : ℝ) / hk k) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hhk
  have hcs : Tendsto (fun k => (hk k / mk k) ^ 2) atTop (𝓝 1) := by
    have h := (ht.inv₀ one_ne_zero).pow 2
    simp only [inv_one, one_pow] at h
    exact h.congr fun k => by rw [inv_div]
  have hball₃ : closedBall b (3 * r) ⊆ {x : Rd d | x ≠ 0} := by
    intro x hx hx0
    rw [hx0, mem_closedBall, dist_zero_left] at hx
    linarith
  have hFunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).1 hconvu _ hball₃
    (isCompact_closedBall b (3 * r))
  have hG : TendstoUniformlyOn (fun k => rescaleOdo (singleSourceOdometer η (nk k)) (mk k)) u
      atTop (closedBall b (2 * r)) := by
    have h := SingleSourceMin.tendstoUniformlyOn_rescale (by linarith : 2 * r < 3 * r)
      (hucont.mono hball₃) hFunif hcs ht
    refine h.congr ?_
    filter_upwards [hmk.eventually (eventually_ge_atTop 1),
      hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk1 hn1 y _
    exact (SingleSourceMin.rescaleOdo_eq _ (by omega) (by omega) y).symm
  -- Lemma 5.5 on `B_r(b)` and lattice point counting
  obtain ⟨hfinμ, -, hlimμ⟩ := hη (ball b r) (StrictConcavityBall.isLipschitzDomain_ball b hr0)
  have hV1 : 0 < volume.real (ball b r) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume b hr0).ne' measure_ball_lt_top.ne
  have hμlim := tendsto_muStar_div_pow hd1 b hr0 hlimμ
  have hlt : C * ((1 - β ^ d) * volume.real (ball b r)) <
      muStarBar E 0 M' * volume.real (ball b r) := by
    have := mul_lt_mul_of_pos_right hmass hV1
    linarith
  -- choose the scale
  have hev1 := hmk.eventually (eventually_scale (d := d) hεpos hr0 hr1 hbp hβ0.le hβ1 hbm16 hK
    hub hru)
  have hev2 := Metric.tendstoUniformlyOn_iff.1 hG (ε * r ^ 2 / 2)
    (div_pos (mul_pos hεpos (pow_pos hr0 2)) (by norm_num))
  have hev3 := hmk.eventually (((tendsto_ncard_diff hd1 b hr0 hβ0 hβ1).const_mul C).eventually_lt
    hμlim hlt)
  obtain ⟨k, ⟨hm1, hinv, hgapk, hposk⟩, hk2, hk3⟩ := (hev1.and (hev2.and hev3)).exists
  have hm0 : mk k ≠ 0 := by omega
  refine false_at_scale hd1 (fun x => (hbd' x).1)
    (ssNonempty d hd1 η (fun x => (hbd' x).2) (nk k)) hm1 hr0 (by linarith) hM' hbm.le hbp hP
    (u₀ := u b) (p₀ := p₀) ?_ ?_ ?_ hgapk hposk
  · -- the Taylor approximation on the closure
    intro y hy
    have hyb : ‖(mk k : ℝ)⁻¹ • toE y - b‖ < 2 * r := by
      rw [dClosure_eq] at hy
      rcases hy with hy | hy
      · have h := (OpenMaxPrinciple.mem_discretize_iff' hm0).1 hy
        rw [mem_ball, dist_eq_norm] at h
        linarith
      · have h := (OpenMaxPrinciple.bdry_rescaled hm1 hy).2
        linarith
    have hU := hk2 _ (show (mk k : ℝ)⁻¹ • toE y ∈ closedBall b (2 * r) by
      rw [mem_closedBall, dist_eq_norm]; exact hyb.le)
    rw [Real.dist_eq] at hU
    exact approx_at_point hεpos (by linarith) hTb hm0 hyb hU
  · -- the lower bound on `A`
    intro y hy
    have h := (OpenMaxPrinciple.mem_discretize_iff' hm0).1 hy
    rw [mem_ball] at h
    have hU := hk2 _ (show (mk k : ℝ)⁻¹ • toE y ∈ closedBall b (2 * r) by
      rw [mem_closedBall]; linarith)
    rw [Real.dist_eq] at hU
    exact lower_at_point hc (by linarith) hm0 h hU
  · -- the `μ*` mass
    rw [← hC]
    exact mass_at_scale hC0 (by omega) (hfinμ (mk k)).2 hk3

/-! ### Peano points: the rational approximation -/

/-- **(S*) at Peano points**: almost surely, `F*(N) ≤ 0` at every point `b ≠ 0` where a
subsequential limit is positive and has a second-order Peano expansion with symmetric matrix `N`. -/
def SSPeanoStarStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
      ∀ (b p₀ : Rd d) (N : Matrix (Fin d) (Fin d) ℝ), b ≠ 0 → 0 < u b → N.IsSymm →
        HasSecondOrderTaylorAt u b p₀ N → effOpStar E N ≤ 0

theorem ssPeanoStar (hconv : MuConvergenceStmt) (hComp : SSCompactnessStmt) :
    SSPeanoStarStmt := by
  intro d hd E hmax
  have hd1 : 1 ≤ d := by omega
  have hE : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hmax]; omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hrat : ∀ᵐ η ∂E.P, ∀ A : Fin d → Fin d → ℚ, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
      ∀ (b p₀ : Rd d) (N : Matrix (Fin d) (Fin d) ℝ), b ≠ 0 → 0 < u b →
        HasSecondOrderTaylorAt u b p₀ N →
        ∀ (β bm bp : ℝ), 0 < β → β ≤ 1 → 0 < bm → 0 ≤ bp → β ^ 2 * bp < bm →
          (max ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - 0 - (symQ A).trace) 0 / d) ^ d *
            (1 - β ^ d) < muStarBar E 0 (symQ A) →
          (∀ h : Rd d, bm / 2 * ‖h‖ ^ 2 ≤ qM (symQ A - N) h ∧
            qM (symQ A - N) h ≤ bp / 2 * ‖h‖ ^ 2) → False := by
    rw [ae_all_iff]
    intro A
    exact ae_false_peano hconv hComp hd E hmax (symQ_isSymm A)
  filter_upwards [hrat] with η hη
  intro u hu b p₀ N hb0 hub hN hTay
  by_contra hneg
  have hpos : 0 < effOpStar E N := not_le.1 hneg
  obtain ⟨l, hlmem, hl⟩ := exists_lt_of_lt_csSup (effOpStar_set_nonempty hd1 E hE hN) hpos
  have hα : 0 < muStarBar E l N := hlmem
  set L : ℝ := l / (2 * d) with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  -- the site-bound constant near `N + L I`
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ,
      C₀ = (max ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - (N.trace + l / 2) + 1) 0 / d) ^ d :=
    ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  -- `β = 1 - θ` with `C₀ (1 - β^d) < α`
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = min (1 / 2) (muStarBar E l N / (2 * d * (C₀ + 1))) := ⟨_, rfl⟩
  have hθpos : 0 < θ := by
    rw [hθ]
    exact lt_min (by norm_num) (div_pos hα (by positivity))
  have hθ1 : θ ≤ 1 / 2 := by rw [hθ]; exact min_le_left _ _
  have hθ2 : θ ≤ muStarBar E l N / (2 * d * (C₀ + 1)) := by rw [hθ]; exact min_le_right _ _
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 1 - θ := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hβ1 : β ≤ 1 := by rw [hβ]; linarith
  have hβlt : β < 1 := by rw [hβ]; linarith
  have hbern : 1 - (d : ℝ) * θ ≤ β ^ d := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -θ by linarith) d
    rw [← sub_eq_add_neg] at h
    rw [hβ]
    linarith
  have hmass0 : C₀ * (1 - β ^ d) < muStarBar E l N := by
    have h1 : C₀ * (1 - β ^ d) ≤ C₀ * ((d : ℝ) * θ) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀0
    have h2 : θ * (2 * d * (C₀ + 1)) ≤ muStarBar E l N :=
      (le_div_iff₀ (by positivity)).1 hθ2
    have h3 : 0 < (d : ℝ) * θ := mul_pos hdpos hθpos
    have h4 : 0 ≤ C₀ * ((d : ℝ) * θ) := mul_nonneg hC₀0 h3.le
    linarith
  -- the rational matrix `M' = symQ A ≈ N + L I`
  have hβsq : β ^ 2 < 1 := pow_lt_one₀ hβ0.le hβlt (by norm_num)
  have hβ2 : 0 < 1 - β ^ 2 := by linarith
  obtain ⟨η₁, hη₁⟩ : ∃ η₁ : ℝ, η₁ = min ((1 - β ^ 2) * L / 8) (1 / (d : ℝ)) := ⟨_, rfl⟩
  have hη₁pos : 0 < η₁ := by
    rw [hη₁]
    exact lt_min (div_pos (mul_pos hβ2 hLpos) (by norm_num)) (one_div_pos.2 hdpos)
  have hη₁a : η₁ ≤ (1 - β ^ 2) * L / 8 := by rw [hη₁]; exact min_le_left _ _
  have hη₁b : η₁ ≤ 1 / (d : ℝ) := by rw [hη₁]; exact min_le_right _ _
  have hNs : (N + L • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    hN.add (Matrix.isSymm_one.smul _)
  obtain ⟨A, hA⟩ := exists_symQ_near _ hNs (ε := η₁ / (d : ℝ) ^ 2)
    (div_pos hη₁pos (by positivity))
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Matrix (Fin d) (Fin d) ℝ,
      Δ = symQ A - (N + L • (1 : Matrix (Fin d) (Fin d) ℝ)) := ⟨_, rfl⟩
  have hΔe : ∀ i j, |Δ i j| ≤ η₁ / (d : ℝ) ^ 2 := fun i j => by rw [hΔ]; exact hA i j
  have hqΔ : ∀ h : Rd d, |qM Δ h| ≤ η₁ * ‖h‖ ^ 2 := by
    intro h
    have h1 := abs_qM_le Δ (div_nonneg hη₁pos.le (sq_nonneg _)) hΔe h
    have e : (d : ℝ) ^ 2 * (η₁ / (d : ℝ) ^ 2) = η₁ := by field_simp
    rwa [e] at h1
  -- the bounds `b₋ = L - 2η₁`, `b₊ = L + 2η₁`
  have hmat1 : symQ A - N = Δ + L • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [hΔ]; abel
  have hPA : ∀ h : Rd d, (L - 2 * η₁) / 2 * ‖h‖ ^ 2 ≤ qM (symQ A - N) h ∧
      qM (symQ A - N) h ≤ (L + 2 * η₁) / 2 * ‖h‖ ^ 2 := by
    intro h
    rw [hmat1, qM_add_mat, qM_smul_one]
    have h1 := abs_le.1 (hqΔ h)
    constructor <;> linarith [h1.1, h1.2]
  have hβL : 0 ≤ β ^ 2 * L := mul_nonneg (sq_nonneg β) hLpos.le
  have hβη : β ^ 2 * η₁ ≤ η₁ := mul_le_of_le_one_left hη₁pos.le hβsq.le
  have hbm : 0 < L - 2 * η₁ := by linarith
  have hbp : 0 ≤ L + 2 * η₁ := by linarith
  have hββ : β ^ 2 * (L + 2 * η₁) < L - 2 * η₁ := by linarith
  -- monotonicity: `μ*(0, M') ≥ μ*(0, N + 2L I) = μ*(l, N)`
  have hpsd : (N + (2 * L) • (1 : Matrix (Fin d) (Fin d) ℝ) - symQ A).PosSemidef := by
    refine posSemidef_of_qM_nonneg ((hN.add (Matrix.isSymm_one.smul _)).sub (symQ_isSymm A))
      fun h => ?_
    have hmat2 : N + (2 * L) • (1 : Matrix (Fin d) (Fin d) ℝ) - symQ A =
        (2 * L) • (1 : Matrix (Fin d) (Fin d) ℝ) - (symQ A - N) := by abel
    rw [hmat2, qM_sub_mat, qM_smul_one]
    have h1 := (hPA h).2
    have h2 : 2 * η₁ ≤ L := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖h‖)
    linarith
  have hμ : muStarBar E l N ≤ muStarBar E 0 (symQ A) := by
    have h1 := (muBar_le_add muMatrixMonotone hd1 E 0 (symQ A) _ hpsd).2
    rw [add_sub_cancel] at h1
    have h2 := (muBar_shift muShift hd1 E 0 (2 * L) N).2
    have h3 : (0 : ℝ) + d * (2 * L) = l := by
      rw [hL, zero_add, ← mul_assoc, mul_comm (d : ℝ) 2, mul_div_assoc',
        mul_div_cancel_left₀ l (mul_ne_zero two_ne_zero hdpos.ne')]
    rw [h3] at h2
    rw [h2] at h1
    exact h1
  -- the site bound at `M'`
  have htrΔ : |Δ.trace| ≤ 1 := by
    have h1 : |Δ.trace| ≤ (d : ℝ) * (η₁ / (d : ℝ) ^ 2) := by
      unfold Matrix.trace
      calc |∑ i, Matrix.diag Δ i| ≤ ∑ i, |Matrix.diag Δ i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin d, η₁ / (d : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hΔe i i
        _ = (d : ℝ) * (η₁ / (d : ℝ) ^ 2) := by simp
    have h2 : (d : ℝ) * (η₁ / (d : ℝ) ^ 2) ≤ 1 := by
      have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      have e : (d : ℝ) * (η₁ / (d : ℝ) ^ 2) = η₁ / d := by field_simp
      rw [e, div_le_one hdpos]
      have : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one hdpos]; exact hd1R
      linarith
    linarith
  have htrA : (symQ A).trace = Δ.trace + N.trace + l / 2 := by
    have hmat : symQ A = Δ + N + L • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [hΔ]; abel
    rw [hmat, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul, hL, div_mul_eq_mul_div, mul_div_mul_right _ _ hdpos.ne']
  have hCle : (max ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - 0 - (symQ A).trace) 0 / d) ^ d ≤ C₀ := by
    rw [hC₀]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    refine div_le_div_of_nonneg_right (max_le_max_right _ ?_) (Nat.cast_nonneg d)
    have := (abs_le.1 htrΔ).1
    rw [htrA]
    linarith
  have hmassA : (max ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - 0 - (symQ A).trace) 0 / d) ^ d *
      (1 - β ^ d) < muStarBar E 0 (symQ A) := by
    have hβd : 0 ≤ 1 - β ^ d := by
      have := pow_le_one₀ (n := d) hβ0.le hβ1
      linarith
    calc _ ≤ C₀ * (1 - β ^ d) := mul_le_mul_of_nonneg_right hCle hβd
      _ < muStarBar E l N := hmass0
      _ ≤ muStarBar E 0 (symQ A) := hμ
  exact hη A u hu b p₀ N hb0 hub hTay β (L - 2 * η₁) (L + 2 * η₁) hβ0 hβ1
    hbm hbp hββ hmassA hPA

end SingleSourceFstar

end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessGreen
import RandomSandpile.Proofs.Sec9.SingleSourceMinPrinciple

/-! # Theorem 9.2: the rescaled lattice fundamental solution converges to `G`

With `s = n^{1/d}` (`ssScale d n`), `z = [s x]` (`latticeRound`), the error
`E_n(x) = n^{1-2/d} (g(z) - κ) - G(x) - λ_n` (`ssGreenErr`; `g = ssGreen d`, `G = fundamentalSolution d`,
`λ_n = -(1/2π) log s` for `d = 2` and `0` for `d ≥ 3`) tends to `0` uniformly on compact subsets of
`ℝ^d ∖ {0}` (`ssGreenErr_small`). Proof: `n^{1-2/d} = s^{d-2}`, the homogeneity
`s^{d-2} G(s y) - λ_n = G(y)` (`fundamentalSolution_smul`), so with `y = s⁻¹ z`,
`E_n(x) = s^{d-2} (g(z) - G(z) - κ) + (G(y) - G(x))`; the first term is `O(s^{-2})` by
`ssGreen_asymp`, the second is small by uniform continuity of `G` on a compact annulus, since
`|y - x| ≤ √d / s`.
-/

noncomputable section

open Filter Topology LatticeProb

namespace RandomSandpile

variable {d : ℕ}

/-- The single-source scale `s_n = n^{1/d}`. -/
def ssScale (d n : ℕ) : ℝ := (n : ℝ) ^ (1 / (d : ℝ))

/-- The logarithmic shift `λ_n = -(1/2π) log s_n` in `d = 2` (`0` for `d ≥ 3`). -/
def ssShift (d n : ℕ) : ℝ :=
  if d = 2 then -(1 / (2 * Real.pi)) * Real.log (ssScale d n) else 0

/-- The error `E_n(x) = n^{1-2/d} (g([s_n x]) - κ) - G(x) - λ_n`. -/
def ssGreenErr (d : ℕ) (κ : ℝ) (n : ℕ) (x : Rd d) : ℝ :=
  (n : ℝ) ^ (-(2 / (d : ℝ))) * n * (ssGreen d (latticeRound (ssScale d n • x)) - κ)
    - fundamentalSolution d x - ssShift d n

namespace SSComp

theorem ssScale_pos {n : ℕ} (hn : 1 ≤ n) : 0 < ssScale d n :=
  Real.rpow_pos_of_pos (Nat.cast_pos.2 (by omega)) _

theorem one_le_ssScale {n : ℕ} (hn : 1 ≤ n) : 1 ≤ ssScale d n :=
  Real.one_le_rpow (by exact_mod_cast hn) (by positivity)

theorem ssScale_pow (hd : 1 ≤ d) (n : ℕ) : ssScale d n ^ d = n := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [ssScale, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), one_div,
    inv_mul_cancel₀ hd0, Real.rpow_one]

theorem rpow_neg_two_div (n : ℕ) :
    (n : ℝ) ^ (-(2 / (d : ℝ))) = (ssScale d n ^ 2)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg _), ssScale, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 2
  push_cast
  ring

theorem ssScale_tendsto (hd : 1 ≤ d) : Tendsto (fun n : ℕ => ssScale d n) atTop atTop :=
  (tendsto_rpow_atTop (one_div_pos.2 (Nat.cast_pos.2 (by omega)))).comp
    tendsto_natCast_atTop_atTop

/-- `n^{1 - 2/d} = s^{d-2}`. -/
theorem rpow_mul_self_eq (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(2 / (d : ℝ))) * n = ssScale d n ^ (d - 2) := by
  have hs := ssScale_pos (d := d) hn
  have e2 : ssScale d n ^ d = n := ssScale_pow (by omega) n
  have e3 : ssScale d n ^ d = ssScale d n ^ (d - 2) * ssScale d n ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [rpow_neg_two_div, ← e2, e3, mul_comm, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs.ne'),
    mul_one]

/-- **Homogeneity of the fundamental solution**: `s^{d-2} G(s y) - λ(s) = G(y)`. -/
theorem fundamentalSolution_smul (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) {y : Rd d} (hy : y ≠ 0) :
    s ^ (d - 2) * fundamentalSolution d (s • y)
      - (if d = 2 then -(1 / (2 * Real.pi)) * Real.log s else 0) = fundamentalSolution d y := by
  have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hns : ‖s • y‖ = s * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  by_cases h2 : d = 2
  · have h0 : d - 2 = 0 := by omega
    simp only [fundamentalSolution, if_pos h2, hns, h0, pow_zero, one_mul]
    rw [Real.log_mul hs.ne' hy0]
    ring
  · simp only [fundamentalSolution, if_neg h2, hns, sub_zero]
    rw [Real.mul_rpow hs.le (norm_nonneg _)]
    have hsd : s ^ (d - 2) * s ^ (2 - (d : ℝ)) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hs]
      have : ((d - 2 : ℕ) : ℝ) + (2 - (d : ℝ)) = 0 := by
        rw [Nat.cast_sub hd]; push_cast; ring
      rw [this, Real.rpow_zero]
    calc s ^ (d - 2) * (s ^ (2 - (d : ℝ)) * ‖y‖ ^ (2 - (d : ℝ))
          / ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d))
        = (s ^ (d - 2) * s ^ (2 - (d : ℝ))) * (‖y‖ ^ (2 - (d : ℝ))
          / ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d)) := by ring
      _ = _ := by rw [hsd, one_mul]

theorem norm_le_sqrt_mul_of_abs_le (v : Rd d) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, |v i| ≤ B) :
    ‖v‖ ≤ Real.sqrt d * B := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, B ^ 2 := Finset.sum_le_sum fun i _ => by
    rw [Real.norm_eq_abs]
    have := h i
    have := abs_nonneg (v i)
    nlinarith
  calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin d, B ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt d * B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]

/-- The lattice rounding moves a point by at most `√d`. -/
theorem norm_toE_latticeRound_sub_le_sqrt (w : Rd d) : ‖toE (latticeRound w) - w‖ ≤ Real.sqrt d := by
  have := norm_le_sqrt_mul_of_abs_le (toE (latticeRound w) - w) zero_le_one (fun i => by
    simp only [PiLp.sub_apply, toE_apply]
    show |((⌊w i⌋ : ℤ) : ℝ) - w i| ≤ 1
    have h1 := Int.floor_le (w i)
    have h2 := Int.lt_floor_add_one (w i)
    rw [abs_le]; constructor <;> linarith)
  simpa using this

/-- The decomposition `E_n(x) = s^{d-2} (g(z) - G(z) - κ) + (G(s⁻¹ z) - G(x))`, `z = [s x]`. -/
theorem ssGreenErr_eq (hd : 2 ≤ d) (κ : ℝ) {n : ℕ} (hn : 1 ≤ n) (x : Rd d)
    (hz : toE (latticeRound (ssScale d n • x)) ≠ 0) :
    ssGreenErr d κ n x = ssScale d n ^ (d - 2) * (ssGreen d (latticeRound (ssScale d n • x))
        - fundamentalSolution d (toE (latticeRound (ssScale d n • x))) - κ)
      + (fundamentalSolution d ((ssScale d n)⁻¹ • toE (latticeRound (ssScale d n • x)))
        - fundamentalSolution d x) := by
  have hs := ssScale_pos (d := d) hn
  have hy : (ssScale d n)⁻¹ • toE (latticeRound (ssScale d n • x)) ≠ 0 :=
    smul_ne_zero (inv_ne_zero hs.ne') hz
  have hH := fundamentalSolution_smul hd hs hy
  rw [smul_inv_smul₀ hs.ne'] at hH
  simp only [ssGreenErr, ssShift]
  rw [rpow_mul_self_eq hd hn]
  linear_combination hH

end SSComp

open SSComp in
/-- **The Green error tends to zero uniformly on compact subsets of `ℝ^d ∖ {0}`.** -/
theorem ssGreenErr_small (hd : 2 ≤ d) {κ C R : ℝ} (hR : 1 ≤ R)
    (hasymp : ∀ z : Site d, R ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ)))
    {K : Set (Rd d)} (hK : IsCompact K) (hK0 : ∀ x ∈ K, x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ K, |ssGreenErr d κ n x| < ε := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, fun n _ x hx => by simp [hKe] at hx⟩
  obtain ⟨x0, hx0K, hx0min⟩ := hK.exists_isMinOn hKne continuous_norm.continuousOn
  set r : ℝ := ‖x0‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 (hK0 x0 hx0K)
  have hrK : ∀ x ∈ K, r ≤ ‖x‖ := fun x hx => (isMinOn_iff.1 hx0min) x hx
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall (0 : Rd d)
  have hρK : ∀ x ∈ K, ‖x‖ ≤ ρ := fun x hx => mem_closedBall_zero_iff.1 (hρ hx)
  set K' : Set (Rd d) := {y | r / 2 ≤ ‖y‖} ∩ Metric.closedBall 0 (ρ + r) with hK'
  have hK'c : IsCompact K' :=
    (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const continuous_norm)
  have hK'0 : K' ⊆ {x : Rd d | x ≠ 0} := fun y hy => by
    have h1 : r / 2 ≤ ‖y‖ := hy.1
    exact norm_pos_iff.1 (by linarith)
  have hUC := hK'c.uniformContinuousOn_of_continuous
    ((SingleSourceMin.continuousOn_fundamentalSolution d).mono hK'0)
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.1 hUC (ε / 2) (by positivity)
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hrd : 0 < (r / 2) ^ d := by positivity
  set Q : ℝ := 2 * |C| / ((r / 2) ^ d * ε) with hQ
  set s0 : ℝ := max (Real.sqrt d / δ + 1)
    (max (2 * Real.sqrt d / r + 1) (max (2 * R / r + 1) (Real.sqrt Q + 1))) with hs0
  have h1 : Real.sqrt d / δ + 1 ≤ s0 := le_max_left _ _
  have h2 : 2 * Real.sqrt d / r + 1 ≤ s0 := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : 2 * R / r + 1 ≤ s0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h4 : Real.sqrt Q + 1 ≤ s0 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((ssScale_tendsto (d := d) (by omega)).eventually_ge_atTop s0).and (eventually_ge_atTop 1))
  refine ⟨N, fun n hn x hx => ?_⟩
  obtain ⟨hsn, hn1⟩ := hN n hn
  have hs : 0 < ssScale d n := ssScale_pos hn1
  set s : ℝ := ssScale d n with hsdef
  have hsδ : Real.sqrt d / s < δ := by
    rw [div_lt_iff₀ hs]
    have : Real.sqrt d / δ < s := by linarith
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hsr : Real.sqrt d / s < r / 2 := by
    rw [div_lt_iff₀ hs]
    have : 2 * Real.sqrt d / r < s := by linarith
    rw [div_lt_iff₀ hr0] at this
    linarith
  have hsR : R < s * (r / 2) := by
    have : 2 * R / r < s := by linarith
    rw [div_lt_iff₀ hr0] at this
    linarith
  have hsQ : Q < s ^ 2 := by
    have : Real.sqrt Q < s := by linarith
    exact (Real.sqrt_lt' hs).1 this
  set z : Site d := latticeRound (s • x) with hzdef
  have hz : ‖toE z - s • x‖ ≤ Real.sqrt d := SSComp.norm_toE_latticeRound_sub_le_sqrt (s • x)
  set y : Rd d := s⁻¹ • toE z with hydef
  have hsy : s • y = toE z := smul_inv_smul₀ hs.ne' _
  have hyx : ‖y - x‖ ≤ Real.sqrt d / s := by
    have e : y - x = s⁻¹ • (toE z - s • x) := by rw [smul_sub, inv_smul_smul₀ hs.ne']
    rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hz (inv_nonneg.2 hs.le)
  have hxr := hrK x hx
  have hxρ := hρK x hx
  have hy1 : r / 2 ≤ ‖y‖ := by
    have := norm_le_insert' x y
    rw [norm_sub_rev] at this
    linarith
  have hy2 : ‖y‖ ≤ ρ + r := by
    have := norm_le_insert' y x
    linarith
  have hyK' : y ∈ K' := ⟨hy1, mem_closedBall_zero_iff.2 hy2⟩
  have hxK' : x ∈ K' := ⟨show r / 2 ≤ ‖x‖ by linarith, mem_closedBall_zero_iff.2 (by linarith)⟩
  have hGyx : |fundamentalSolution d y - fundamentalSolution d x| < ε / 2 := by
    have := hδG y hyK' x hxK' (by rw [dist_eq_norm]; linarith)
    rwa [Real.dist_eq] at this
  have hzsr : s * (r / 2) ≤ ‖toE z‖ := by
    rw [← hsy, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hy1 hs.le
  have hzpos : 0 < ‖toE z‖ := by linarith
  have hz0 : toE z ≠ 0 := norm_pos_iff.1 hzpos
  have hasy := hasymp z (by linarith)
  rw [Real.rpow_neg hzpos.le, Real.rpow_natCast] at hasy
  have hdec : ssGreenErr d κ n x = s ^ (d - 2) * (ssGreen d z - fundamentalSolution d (toE z) - κ)
      + (fundamentalSolution d y - fundamentalSolution d x) := ssGreenErr_eq hd κ hn1 x hz0
  rw [hdec]
  have hpowle : (s * (r / 2)) ^ d ≤ ‖toE z‖ ^ d := pow_le_pow_left₀ (by positivity) hzsr d
  have hinv : (‖toE z‖ ^ d)⁻¹ ≤ ((s * (r / 2)) ^ d)⁻¹ := inv_anti₀ (by positivity) hpowle
  have hsplit : (s * (r / 2)) ^ d = s ^ (d - 2) * (s ^ 2 * (r / 2) ^ d) := by
    rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hd]
  have hA : |s ^ (d - 2) * (ssGreen d z - fundamentalSolution d (toE z) - κ)| < ε / 2 := by
    rw [abs_mul, abs_of_pos (pow_pos hs _)]
    have hspos : 0 < s ^ (d - 2) := pow_pos hs _
    calc s ^ (d - 2) * |ssGreen d z - fundamentalSolution d (toE z) - κ|
        ≤ s ^ (d - 2) * (|C| * ((s * (r / 2)) ^ d)⁻¹) := by
          refine mul_le_mul_of_nonneg_left (hasy.trans ?_) hspos.le
          calc C * (‖toE z‖ ^ d)⁻¹ ≤ |C| * (‖toE z‖ ^ d)⁻¹ :=
                mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
            _ ≤ |C| * ((s * (r / 2)) ^ d)⁻¹ := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ = |C| / (s ^ 2 * (r / 2) ^ d) := by
          rw [hsplit]
          field_simp
      _ < ε / 2 := by
          rw [div_lt_iff₀ (by positivity)]
          have := (div_lt_iff₀ (by positivity : 0 < (r / 2) ^ d * ε)).1 hsQ
          nlinarith
  calc |s ^ (d - 2) * (ssGreen d z - fundamentalSolution d (toE z) - κ)
        + (fundamentalSolution d y - fundamentalSolution d x)|
      ≤ |s ^ (d - 2) * (ssGreen d z - fundamentalSolution d (toE z) - κ)|
        + |fundamentalSolution d y - fundamentalSolution d x| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hA hGyx
    _ = ε := by ring

end RandomSandpile

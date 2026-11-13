import RandomSandpile.Proofs.Sec7.MainTheoremUExterior

/-! # Theorem 1.1, step: the subsolution property outside `W̄` where `v > 0`

`exteriorSubsolution : ExteriorSubsolutionStmt` (no input; the argument in the proof of
Pegden-Smart's Theorem 4.2, `paper/random_piles-corrected.tex`: leastness of the odometer).

Suppose `Q = v(a) + p·(· - a) + q_N(· - a)` touches a subsequential limit `v` from above at
`a ∉ W̄` with `v(a) > 0`, and some `u : ℤ^d → ℤ` has `Δ_{ℤ^d} u ≤ 2d - 1` and `u ≥ q_{N + εI}`.
For `n = n_k` large and `c₀ = [n a]`, the competitor
`w(z) = u(z - c₀) + ⌊n² Q(c₀/n) - τ n²⌋ + ∑ᵢ ⌊γᵢ⌋ (z - c₀)ᵢ`, where
`n² Q(z/n) - q_N(z - c₀) = n² Q(c₀/n) + γ·(z - c₀)` (`quad_rescale_decomp`), satisfies
`Δ_{ℤ^d} w ≤ 2d - 1`, `w > 0` on `B_{2ρn}(c₀)` (`Q > v(a)/2` near `a`), `w ≥ v_n` on the annulus
`ρn ≤ |z - c₀| < 2ρn` (the quadratic gap `(ε/2)|z - c₀|²`), and `w(c₀) < v_n(c₀)`. The pile
`η 𝟙_{W_n}` vanishes on `B_{2ρn}(c₀)`, so `min(v_n, w)` on that ball, `v_n` elsewhere, is a
stabilizing toppling below `v_n` (`le_of_competitor`), against the leastness of `v_n`. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

namespace ExteriorSub

variable {d : ℕ}

open PegdenSmartRegularity in
/-- **Leastness against a local competitor.** If `w` is nonnegative and stabilizing on
`B_{2R}(c₀)` and `w ≥ v` on the annulus `R ≤ |z - c₀| < 2R`, then `v(c₀) ≤ w(c₀)` for the least
stabilizing toppling `v`. -/
theorem le_of_competitor {σ v w : Site d → ℤ} (hv : IsLeast (stabilizing σ Set.univ) v)
    {c₀ : Site d} {R : ℝ} (hR : 1 ≤ R)
    (hw0 : ∀ z, ‖toE (z - c₀)‖ < 2 * R → 0 ≤ w z)
    (hwlap : ∀ z, ‖toE (z - c₀)‖ < 2 * R → lap w z + σ z ≤ 2 * (d : ℤ) - 1)
    (hgap : ∀ z, R ≤ ‖toE (z - c₀)‖ → ‖toE (z - c₀)‖ < 2 * R → v z ≤ w z) :
    v c₀ ≤ w c₀ := by
  classical
  obtain ⟨hv0, hvlap⟩ := mem_stabilizing_univ.1 hv.1
  set vt : Site d → ℤ := fun z => if ‖toE (z - c₀)‖ < 2 * R then min (v z) (w z) else v z
    with hvt
  have hle : ∀ z, vt z ≤ v z := fun z => by
    simp only [hvt]; split_ifs <;> simp
  have hin : ∀ z, ‖toE (z - c₀)‖ < 2 * R → vt z ≤ w z := fun z hz => by
    simp only [hvt, ite_eq_left hz]; exact min_le_right _ _
  have hS : vt ∈ stabilizing σ Set.univ := by
    refine mem_stabilizing_univ.2 ⟨fun z => ?_, fun z => ?_⟩
    · simp only [hvt]
      split_ifs with h
      · exact le_min (hv0 z) (hw0 z h)
      · exact hv0 z
    · by_cases hz : vt z = v z
      · have := lap_le_lap_of_nbr hz fun i => ⟨hle _, hle _⟩
        linarith [hvlap z]
      · have hzin : ‖toE (z - c₀)‖ < 2 * R := by
          by_contra h
          exact hz (by simp only [hvt, ite_eq_right h])
        have hwz : vt z = w z := by
          simp only [hvt, ite_eq_left hzin] at hz ⊢
          rcases min_choice (v z) (w z) with h | h
          · exact absurd h hz
          · exact h
        have hzR : ‖toE (z - c₀)‖ < R := by
          by_contra h
          push Not at h
          exact hz (by simp only [hvt, ite_eq_left hzin]; exact min_eq_left (hgap z h hzin))
        have hnb : ∀ i, vt (z + unit i) ≤ w (z + unit i) ∧ vt (z - unit i) ≤ w (z - unit i) :=
          fun i => ⟨hin _ (by linarith [norm_toE_add_unit_sub z c₀ i]),
            hin _ (by linarith [norm_toE_sub_unit_sub z c₀ i])⟩
        have := lap_le_lap_of_nbr hwz hnb
        linarith [hwlap z hzin]
  have h0 : ‖toE (c₀ - c₀)‖ < 2 * R := by
    rw [sub_self, OdometerLowerBound.toE_zero, norm_zero]; linarith
  exact (hv.2 hS c₀).trans (hin c₀ h0)

/-- `n² Q(z/n) - q_N(z - c₀)` is affine in `z - c₀` for a quadratic `Q` with matrix `N`. -/
theorem quad_rescale_decomp {N : Matrix (Fin d) (Fin d) ℝ} (hN : N.IsSymm) (p a : Rd d) (c : ℝ)
    {Q : Rd d → ℝ} (hQ : ∀ y, Q y = c + inner ℝ p (y - a) + qM N (y - a)) {n : ℝ} (hn : n ≠ 0)
    (c₀ : Site d) : ∃ γ : Rd d, ∀ z : Site d,
      n ^ 2 * Q (n⁻¹ • toE z) - qMZ N (z - c₀) =
        n ^ 2 * Q (n⁻¹ • toE c₀) + inner ℝ γ (toE (z - c₀)) := by
  obtain ⟨c', c0, hcq⟩ := OpenMaxPrinciple.rescaled_quad_affine hN p a 0 hn
  have hq : ∀ Z : Rd d, n ^ 2 * Q (n⁻¹ • Z) = n ^ 2 * c + qM N Z + inner ℝ c' Z + c0 := by
    intro Z
    have h := hcq Z
    simp only [ql, zero_mul, zero_div, add_zero, zero_add] at h
    rw [hQ]
    linear_combination h
  have hB : inner ℝ (WithLp.toLp 2 (N *ᵥ WithLp.ofLp (toE c₀))) (toE c₀) = 2 * qM N (toE c₀) := by
    have h := OpenMaxPrinciple.qM_sub' hN (toE c₀) (toE c₀)
    simp only [sub_self, qM_zero_right] at h
    linarith
  refine ⟨c' + WithLp.toLp 2 (N *ᵥ WithLp.ofLp (toE c₀)), fun z => ?_⟩
  rw [hq, hq, qMZ, OdometerLowerBound.toE_sub, OpenMaxPrinciple.qM_sub' hN, inner_add_left,
    inner_sub_right, inner_sub_right]
  linarith [hB]

/-- The inner product with `toE h` is the coordinate sum. -/
theorem inner_toE_eq_sum (γ : Rd d) (h : Site d) :
    inner ℝ γ (toE h) = ∑ i, γ i * (h i : ℝ) := by
  simp [toE, PiLp.inner_apply, mul_comm]

/-- Rounding the slopes down costs at most `d |h|`. -/
theorem abs_inner_sub_floor_le (γ : Rd d) (h : Site d) :
    |inner ℝ γ (toE h) - ∑ i, ((⌊γ i⌋ : ℤ) : ℝ) * (h i : ℝ)| ≤ d * ‖toE h‖ := by
  rw [inner_toE_eq_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |γ i * (h i : ℝ) - ((⌊γ i⌋ : ℤ) : ℝ) * (h i : ℝ)|
      ≤ ∑ _i : Fin d, ‖toE h‖ := Finset.sum_le_sum fun i _ => by
        rw [← sub_mul, abs_mul]
        have h1 := Int.floor_le (γ i)
        have h2 := Int.lt_floor_add_one (γ i)
        have h3 : |γ i - ((⌊γ i⌋ : ℤ) : ℝ)| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
        have h4 := PegdenSmartRegularity.abs_coord_le_norm h i
        calc |γ i - ((⌊γ i⌋ : ℤ) : ℝ)| * |(h i : ℝ)| ≤ 1 * ‖toE h‖ :=
              mul_le_mul h3 h4 (abs_nonneg _) zero_le_one
          _ = ‖toE h‖ := one_mul _
    _ = d * ‖toE h‖ := by simp [Finset.sum_const, Finset.card_univ]

end ExteriorSub

set_option maxHeartbeats 400000 in
open ExteriorSub PegdenSmartRegularity FreeMaxPrinciple in
/-- **Step** (`ExteriorSubsolutionStmt`): no input. -/
theorem exteriorSubsolution : ExteriorSubsolutionStmt := by
  intro d hd W hW ηmin ηmax η hbd v hv a p N ha hN hva htouch ε hε
  rintro ⟨u, hu⟩
  have hd1 : 1 ≤ d := by omega
  have hvc : Continuous v := continuous_of_isOdoSubseqLimit hd hW hbd hv
  obtain ⟨nk, hnk, hconv⟩ := hv
  set Q : Rd d → ℝ := fun y => v a + inner ℝ p (y - a) + qM N (y - a) with hQ
  have hQc : Continuous Q := LimitTrace.continuous_quad _ _ _ _
  have hQa : Q a = v a := by simp [hQ, qM_zero_right]
  -- radii
  obtain ⟨ρ₁, hρ₁, hρ₁W⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl a ha
  obtain ⟨ρ₂, hρ₂, ht⟩ := Metric.eventually_nhds_iff.1 htouch
  obtain ⟨ρ₃, hρ₃, hQpos⟩ := Metric.continuous_iff.1 hQc a (v a / 2) (half_pos hva)
  set ρ : ℝ := min (min ρ₁ ρ₂) ρ₃ / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : 3 * ρ < ρ₁ := by
    have := min_le_left (min ρ₁ ρ₂) ρ₃; have := min_le_left ρ₁ ρ₂; linarith
  have hρ2 : 3 * ρ < ρ₂ := by
    have := min_le_left (min ρ₁ ρ₂) ρ₃; have := min_le_right ρ₁ ρ₂; linarith
  have hρ3 : 3 * ρ < ρ₃ := by have := min_le_right (min ρ₁ ρ₂) ρ₃; linarith
  set τ : ℝ := min (ε * ρ ^ 2 / 8) (v a / 8) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ ε * ρ ^ 2 / 8 := min_le_left _ _
  have hτ2 : τ ≤ v a / 8 := min_le_right _ _
  obtain ⟨ρ₄, hρ₄, hQv⟩ := Metric.continuous_iff.1 (hQc.sub hvc) a (τ / 4) (by positivity)
  have hU := Metric.tendstoUniformly_iff.1 hconv (τ / 4) (by positivity)
  -- the scale
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set N₀ : ℝ := 1 + 1 / ρ + Real.sqrt d / ρ + Real.sqrt d / ρ₄ +
    4 * (1 + 2 * d * ρ) / (ε * ρ ^ 2) + 4 * (1 + 2 * d * ρ) / v a + 4 * |(u 0 : ℝ)| / τ with hN₀
  obtain ⟨k, hk1, hk2⟩ :=
    (hU.and (hnk.tendsto_atTop.eventually (eventually_ge_atTop ⌈N₀⌉₊))).exists
  set n : ℕ := nk k with hndef
  have hnN : N₀ ≤ n := Nat.ceil_le.1 hk2
  have t1 : 0 ≤ 1 / ρ := by positivity
  have t2 : 0 ≤ Real.sqrt d / ρ := by positivity
  have t3 : 0 ≤ Real.sqrt d / ρ₄ := by positivity
  have t4 : 0 ≤ 4 * (1 + 2 * d * ρ) / (ε * ρ ^ 2) := by positivity
  have t5 : 0 ≤ 4 * (1 + 2 * d * ρ) / v a := by positivity
  have t6 : 0 ≤ 4 * |(u 0 : ℝ)| / τ := by positivity
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hnρ : 1 ≤ ρ * n := by
    have : 1 / ρ ≤ n := by linarith
    rw [div_le_iff₀ hρ0] at this; linarith
  have hnsd : Real.sqrt d / n < ρ := by
    rw [div_lt_iff₀ hnpos]
    have : Real.sqrt d / ρ < n := by linarith
    rw [div_lt_iff₀ hρ0] at this; linarith
  have hnsd4 : Real.sqrt d / n < ρ₄ := by
    rw [div_lt_iff₀ hnpos]
    have : Real.sqrt d / ρ₄ < n := by linarith
    rw [div_lt_iff₀ hρ₄] at this; linarith
  have hgapn : (1 + 2 * d * ρ) * n ≤ ε * ρ ^ 2 / 4 * n ^ 2 := by
    have : 4 * (1 + 2 * d * ρ) / (ε * ρ ^ 2) ≤ n := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    have := mul_le_mul_of_nonneg_left this hnpos.le
    linarith
  have hposn : (1 + 2 * d * ρ) * n < v a / 4 * n ^ 2 := by
    have : 4 * (1 + 2 * d * ρ) / v a < n := by linarith
    rw [div_lt_iff₀ hva] at this
    have := mul_lt_mul_of_pos_left this hnpos
    linarith
  have hun : |(u 0 : ℝ)| * 4 < τ * n := by
    have : 4 * |(u 0 : ℝ)| / τ < n := by linarith
    rw [div_lt_iff₀ hτ0] at this; linarith
  -- the lattice centre and positions
  set c₀ : Site d := latticeRound ((n : ℝ) • a) with hc₀
  have hround : ‖toE c₀ - (n : ℝ) • a‖ ≤ Real.sqrt d :=
    Real.le_sqrt_of_sq_le (norm_toE_latticeRound_sub_sq_le _)
  have hposz : ∀ z : Site d, ‖(n : ℝ)⁻¹ • toE z - a‖ ≤ (‖toE (z - c₀)‖ + Real.sqrt d) / n := by
    intro z
    have e : (n : ℝ)⁻¹ • toE z - a = (n : ℝ)⁻¹ • (toE (z - c₀) + (toE c₀ - (n : ℝ) • a)) := by
      rw [OdometerLowerBound.toE_sub, smul_add, smul_sub, smul_sub, smul_smul,
        inv_mul_cancel₀ hn0, one_smul]
      abel
    rw [e, norm_smul, norm_inv, Real.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (by positivity)
  have hball : ∀ z : Site d, ‖toE (z - c₀)‖ < 2 * (ρ * n) →
      dist ((n : ℝ)⁻¹ • toE z) a < 3 * ρ := by
    intro z hz
    rw [dist_eq_norm]
    refine (hposz z).trans_lt ?_
    rw [div_lt_iff₀ hnpos]
    have : Real.sqrt d < ρ * n := by rw [div_lt_iff₀ hnpos] at hnsd; linarith
    linarith
  -- values of the free odometer through the rescaling
  set vn : Site d → ℤ := freeOdometer η (discretize W n) with hvn
  have hval : ∀ z, (vn z : ℝ) = (n : ℝ) ^ 2 * rescaleOdo vn n ((n : ℝ)⁻¹ • toE z) := by
    intro z
    simp only [rescaleOdo]
    rw [smul_smul, mul_inv_cancel₀ hn0, one_smul, latticeRound_toE]
    field_simp
  have hclose : ∀ z, |(vn z : ℝ) / (n : ℝ) ^ 2 - v ((n : ℝ)⁻¹ • toE z)| < τ / 4 := by
    intro z
    have h := hk1 ((n : ℝ)⁻¹ • toE z)
    rw [dist_comm, Real.dist_eq] at h
    have hv' : (vn z : ℝ) / (n : ℝ) ^ 2 = rescaleOdo vn n ((n : ℝ)⁻¹ • toE z) := by
      rw [hval z]; field_simp
    rw [hv']; exact h
  -- the competitor
  obtain ⟨γ, hγ⟩ := quad_rescale_decomp hN p a (v a) (Q := Q) (fun y => rfl) hn0 c₀
  set T0 : ℝ := (n : ℝ) ^ 2 * Q ((n : ℝ)⁻¹ • toE c₀) with hT0
  set A₀ : ℝ := T0 - τ * (n : ℝ) ^ 2 with hA₀
  set w : Site d → ℤ := fun z => u (z - c₀) + (⌊A₀⌋ + ∑ i, ⌊γ i⌋ * (z - c₀) i) with hw
  have hwlap : ∀ z, lap w z = lap u (z - c₀) := by
    intro z
    have hI : (fun z : Site d => ⌊A₀⌋ + ∑ i, ⌊γ i⌋ * (z - c₀) i) =
        fun z => (fun z : Site d => ∑ i, ⌊γ i⌋ * z i) z + (⌊A₀⌋ - ∑ i, ⌊γ i⌋ * c₀ i) := by
      funext z
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    have hadd : ∀ x y : Site d, (∑ i, ⌊γ i⌋ * (x + y) i) =
        (∑ i, ⌊γ i⌋ * x i) + ∑ i, ⌊γ i⌋ * y i := fun x y => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    simp only [hw]
    rw [lap_fun_add, lap_comp_sub, hI, lap_add_const,
      lap_of_additive (f := fun z : Site d => ∑ i, ⌊γ i⌋ * z i) hadd, add_zero]
  have hwlow : ∀ z, (n : ℝ) ^ 2 * Q ((n : ℝ)⁻¹ • toE z) + ε / 2 * ‖toE (z - c₀)‖ ^ 2 -
      τ * (n : ℝ) ^ 2 - 1 - d * ‖toE (z - c₀)‖ ≤ (w z : ℝ) := by
    intro z
    have h1 := (hu (z - c₀)).2
    have h2 := Int.floor_le A₀
    have h2' := Int.lt_floor_add_one A₀
    have h3 := abs_inner_sub_floor_le γ (z - c₀)
    have h4 := hγ z
    have hq : qMZ (N + ε • (1 : Matrix (Fin d) (Fin d) ℝ)) (z - c₀) =
        qMZ N (z - c₀) + ε / 2 * ‖toE (z - c₀)‖ ^ 2 := by
      simp only [qMZ]; rw [qM_add_mat, qM_smul_one]; ring
    have hcast : (w z : ℝ) = (u (z - c₀) : ℝ) + ((⌊A₀⌋ : ℤ) : ℝ) +
        ∑ i, ((⌊γ i⌋ : ℤ) : ℝ) * (((z - c₀) i : ℤ) : ℝ) := by
      simp only [hw, Int.cast_add, Int.cast_sum, Int.cast_mul]
      ring
    rw [hcast]
    have h3' := (abs_le.1 h3).2
    linarith
  have hwc : (w c₀ : ℝ) ≤ (u 0 : ℝ) + A₀ := by
    have : (w c₀ : ℝ) = (u 0 : ℝ) + ((⌊A₀⌋ : ℤ) : ℝ) := by
      simp only [hw, sub_self, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
      push_cast; ring
    rw [this]; linarith [Int.floor_le A₀]
  -- the three properties of the competitor
  have hdist2 : ∀ z : Site d, ‖toE (z - c₀)‖ < 2 * (ρ * n) → d * ‖toE (z - c₀)‖ ≤ 2 * d * ρ * n :=
    fun z hz => by
      have := mul_le_mul_of_nonneg_left hz.le hdR
      linarith
  have hc0 : ∀ z, ‖toE (z - c₀)‖ < 2 * (ρ * n) → 0 ≤ w z := by
    intro z hz
    have hy := hball z hz
    have hQy := hQpos _ (by linarith)
    rw [hQa, Real.dist_eq] at hQy
    have hQy' : v a / 2 < Q ((n : ℝ)⁻¹ • toE z) := by linarith [(abs_lt.1 hQy).1]
    have h1 := hwlow z
    have h2 := hdist2 z hz
    have h3 : 0 ≤ ε / 2 * ‖toE (z - c₀)‖ ^ 2 := by positivity
    have h4 : (n : ℝ) ^ 2 * (v a / 2) ≤ (n : ℝ) ^ 2 * Q ((n : ℝ)⁻¹ • toE z) :=
      mul_le_mul_of_nonneg_left hQy'.le (by positivity)
    have h5 : τ * (n : ℝ) ^ 2 ≤ v a / 8 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hτ2 (by positivity)
    have h6 : (1 : ℝ) + 2 * d * ρ * n ≤ (1 + 2 * d * ρ) * n := by linarith
    have hpos' : 0 < v a * (n : ℝ) ^ 2 := by positivity
    have : (0 : ℝ) < w z := by linarith
    exact Int.cast_nonneg_iff.1 this.le
  have hcl : ∀ z, ‖toE (z - c₀)‖ < 2 * (ρ * n) →
      lap w z + (discretize W n).indicator η z ≤ 2 * (d : ℤ) - 1 := by
    intro z hz
    have hy := hball z hz
    have hzW : z ∉ discretize W n := by
      intro hzW
      have hmem : ((n : ℝ))⁻¹ • toE z ∈ W :=
        (Set.mem_smul_set_iff_inv_smul_mem₀ hn0 _ _).1 hzW
      exact hρ₁W (show dist _ a < ρ₁ by linarith) (subset_closure hmem)
    rw [Set.indicator_of_notMem hzW, hwlap]
    linarith [(hu (z - c₀)).1]
  have hcg : ∀ z, ρ * n ≤ ‖toE (z - c₀)‖ → ‖toE (z - c₀)‖ < 2 * (ρ * n) → vn z ≤ w z := by
    intro z hz1 hz2
    have hy := hball z hz2
    have hvQ : v ((n : ℝ)⁻¹ • toE z) ≤ Q ((n : ℝ)⁻¹ • toE z) := ht (by linarith)
    have hcl := (abs_lt.1 (hclose z)).2
    have hvn : (vn z : ℝ) ≤ (n : ℝ) ^ 2 * (Q ((n : ℝ)⁻¹ • toE z) + τ / 4) := by
      have h := hval z
      have : rescaleOdo vn n ((n : ℝ)⁻¹ • toE z) < v ((n : ℝ)⁻¹ • toE z) + τ / 4 := by
        have hv' : (vn z : ℝ) / (n : ℝ) ^ 2 = rescaleOdo vn n ((n : ℝ)⁻¹ • toE z) := by
          rw [hval z]; field_simp
        rw [← hv']; linarith
      rw [h]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h1 := hwlow z
    have h2 := hdist2 z hz2
    have hsq : (ρ * n) ^ 2 ≤ ‖toE (z - c₀)‖ ^ 2 := pow_le_pow_left₀ (by positivity) hz1 2
    have h3 : ε / 2 * (ρ * n) ^ 2 ≤ ε / 2 * ‖toE (z - c₀)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h5 : τ * (n : ℝ) ^ 2 ≤ ε * ρ ^ 2 / 8 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hτ1 (by positivity)
    have h6 : (1 : ℝ) + 2 * d * ρ * n ≤ (1 + 2 * d * ρ) * n := by linarith
    have hpos' : 0 ≤ ε * ρ ^ 2 * (n : ℝ) ^ 2 := by positivity
    have : (vn z : ℝ) ≤ w z := by linarith
    exact Int.cast_le.1 this
  have hle := le_of_competitor (isLeast_freeOdometer
    (freeOdometer_stabilizing_nonempty hd1 η hW.1 n)) hnρ hc0 hcl hcg
  -- the contradiction at the centre
  have hy0 : dist ((n : ℝ)⁻¹ • toE c₀) a < ρ₄ := by
    rw [dist_eq_norm]
    refine (hposz c₀).trans_lt ?_
    rw [sub_self, OdometerLowerBound.toE_zero, norm_zero, zero_add]
    exact hnsd4
  have hQv0 := hQv _ hy0
  simp only [Pi.sub_apply, hQa, sub_self, Real.dist_eq, sub_zero] at hQv0
  have hQv0' : Q ((n : ℝ)⁻¹ • toE c₀) - v ((n : ℝ)⁻¹ • toE c₀) < τ / 4 :=
    (abs_lt.1 hQv0).2
  have hcl0 := (abs_lt.1 (hclose c₀)).1
  have hv0 : (n : ℝ) ^ 2 * (v ((n : ℝ)⁻¹ • toE c₀) - τ / 4) < (vn c₀ : ℝ) := by
    have : v ((n : ℝ)⁻¹ • toE c₀) - τ / 4 < (vn c₀ : ℝ) / (n : ℝ) ^ 2 := by
      linarith only [hcl0]
    rw [lt_div_iff₀ (by positivity)] at this
    linarith only [this]
  have hle' : (vn c₀ : ℝ) ≤ (w c₀ : ℝ) := Int.cast_le.2 hle
  have hT : T0 < (n : ℝ) ^ 2 * (v ((n : ℝ)⁻¹ • toE c₀) + τ / 4) := by
    rw [hT0]
    exact mul_lt_mul_of_pos_left (by linarith only [hQv0']) (by positivity)
  have hu0 : (u 0 : ℝ) ≤ |(u 0 : ℝ)| := le_abs_self _
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hn1 hnpos.le
    linarith only [this]
  have hτn : τ * n ≤ τ * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hnn hτ0.le
  have hτn2 : 0 ≤ τ * (n : ℝ) ^ 2 := by positivity
  linarith only [hle', hwc, hA₀, hT, hv0, hu0, hun, hτn, hτn2]

end RandomSandpile

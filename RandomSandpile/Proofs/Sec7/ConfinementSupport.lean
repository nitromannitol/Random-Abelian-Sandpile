import RandomSandpile.Proofs.Sec7.ConfinementBarrier
import RandomSandpile.Proofs.Sec7.ConfinementHomogenize
import RandomSandpile.Proofs.Sec7.SandpileSupport

/-!
# Theorem 1.1: a support radius depending only on `W` and `E η(0)`

`sandpileSupport : SandpileSupportStmt`. Choose an integer `a ≥ 1` with `W ⊆ (-a, a)^d` and
`K = a (5 d ⌈m⌉ + 4)`, `m = E η(0)`. In the box `D_n = {‖x‖_∞ < 2an}` let
`p_n = G_{D_n}(η 𝟙_{W_n})` and `p_n^m = G_{D_n}(m 𝟙_{W_n})`. Almost surely
`|p_n - p_n^m| ≤ a² n²` for large `n` (`greenBoxHomogenize`, from the cube ergodic theorem), while
`0 ≤ p_n^m ≤ m (2a√d n + 1)² / (2d)` by the exit time of `D_n`. These bounds are the hypotheses
of the barrier `freeOdometer_eq_zero_of_barrier`, so the free odometer vanishes on
`{‖x‖_∞ ≥ Kn}` and the rescaled sandpile vanishes off `B_R(W)` with `R` depending on `d`, `W` and
`m` only. Initial heights may have either sign; the printed proof of Lemma 7.2 gives a box
depending on `η_max`, which correction C12 records.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric Set

namespace RandomSandpile

open DivisibleHomogenizeDomain

variable {d : ℕ}

theorem mem_discretize_openCube_iff {r n : ℕ} (hn : 1 ≤ n) {y : Site d} :
    y ∈ discretize (openCube (r : ℝ)) n ↔ y ∈ boxZ ((r : ℤ) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro hy i
    have h := abs_lt_of_mem_discretize_openCube hn hy i
    have : ((|y i| : ℤ) : ℝ) < (((r : ℤ) * n : ℤ) : ℝ) := by push_cast; exact h
    exact_mod_cast this
  · intro hy
    refine ⟨(n : ℝ)⁻¹ • toE y, fun i => ?_, ?_⟩
    · have h : |(y i : ℝ)| < r * n := by
        have := hy i
        have : ((|y i| : ℤ) : ℝ) < (((r : ℤ) * n : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at this
        exact this
      have e : ((n : ℝ)⁻¹ • toE y) i = (n : ℝ)⁻¹ * y i := by simp [toE]
      rw [e, abs_mul, abs_inv, Nat.abs_cast, inv_mul_lt_iff₀ hn0]
      linarith
    · show (n : ℝ) • ((n : ℝ)⁻¹ • toE y) = toE y
      rw [smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]

theorem abs_coord_le_norm (z : Rd d) (i : Fin d) : |z i| ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq]
  refine Real.abs_le_sqrt ?_
  have := Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using this

/-! ### Numeric inequalities for the barrier -/

theorem confinement_numeric_upper {m A N D c : ℝ} (hm0 : 0 ≤ m) (hA : 1 ≤ A) (hN : 1 ≤ N)
    (hD : 1 ≤ D) (hc : m ≤ c) (hc0 : 0 ≤ c) :
    m * ((Real.sqrt D * (2 * A) + 1) ^ 2 * N ^ 2) + A ^ 2 * N ^ 2 + 1 ≤
      ((A * (5 * D * c + 4) - A) * N) ^ 2 - ((A * (5 * D * c + 4) - 2 * A) * N) ^ 2 := by
  have hsd : 1 ≤ Real.sqrt D := Real.one_le_sqrt.2 hD
  have hRDa : (Real.sqrt D * (2 * A) + 1) ^ 2 ≤ 9 * A ^ 2 * D := by
    have h1 : Real.sqrt D * (2 * A) + 1 ≤ 3 * A * Real.sqrt D := by nlinarith
    have h2 : (3 * A * Real.sqrt D) ^ 2 = 9 * A ^ 2 * D := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
      ring
    have h0 : 0 ≤ Real.sqrt D * (2 * A) + 1 := by positivity
    calc (Real.sqrt D * (2 * A) + 1) ^ 2 ≤ (3 * A * Real.sqrt D) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 9 * A ^ 2 * D := h2
  have e : ((A * (5 * D * c + 4) - A) * N) ^ 2 - ((A * (5 * D * c + 4) - 2 * A) * N) ^ 2 =
      A ^ 2 * (10 * D * c + 5) * N ^ 2 := by ring
  rw [e]
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hmR : m * (Real.sqrt D * (2 * A) + 1) ^ 2 ≤ 9 * A ^ 2 * D * c := by
    calc m * (Real.sqrt D * (2 * A) + 1) ^ 2 ≤ m * (9 * A ^ 2 * D) :=
          mul_le_mul_of_nonneg_left hRDa hm0
      _ ≤ c * (9 * A ^ 2 * D) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 9 * A ^ 2 * D * c := by ring
  have h1 := mul_le_mul_of_nonneg_right hmR (by positivity : (0 : ℝ) ≤ N ^ 2)
  have h2 : 1 ≤ A ^ 2 * N ^ 2 := one_le_mul_of_one_le_of_one_le hA2 hN2
  have h3 : 0 ≤ A ^ 2 * D * c * N ^ 2 := by positivity
  nlinarith [h1, h2, h3]

theorem confinement_numeric_lower {A N c D : ℝ} (hA : 1 ≤ A) (hN : 0 ≤ N) (hc0 : 0 ≤ c)
    (hD : 0 ≤ D) : A ^ 2 * N ^ 2 ≤ ((A * (5 * D * c + 4) - 2 * A) * N) ^ 2 := by
  have h0 : 0 ≤ A := by linarith
  have hpos : 0 ≤ A * (5 * D * c) := by positivity
  have h : A ≤ A * (5 * D * c + 4) - 2 * A := by nlinarith
  have h1 : 0 ≤ A * N := mul_nonneg h0 hN
  calc A ^ 2 * N ^ 2 = (A * N) ^ 2 := by ring
    _ ≤ ((A * (5 * D * c + 4) - 2 * A) * N) ^ 2 :=
        pow_le_pow_left₀ h1 (mul_le_mul_of_nonneg_right h hN) 2

/-! ### Confinement for one `n` -/

/-- If the Green potential of `(η - m) 𝟙_{W_n}` in `D_n = ℤ^d ∩ n (-2a, 2a)^d` is at most `a² n²`,
then the free odometer of `η 𝟙_{W_n}` vanishes on `{‖x‖_∞ ≥ Kn}`, `K = a (5 d ⌈m⌉ + 4)`. -/
theorem freeOdometer_eq_zero_of_green (hd : 2 ≤ d) {W : Set (Rd d)} (hW : IsLipschitzDomain W)
    {a n : ℕ} (ha : 1 ≤ a) (hn1 : 1 ≤ n) (hWa : W ⊆ openCube (a : ℝ)) {m : ℝ} (hm0 : 0 ≤ m)
    {η : Site d → ℤ}
    (he : ∀ x, |∑ y ∈ (DivisibleHomogenizeDomain.discretize_finite hW.1 n).toFinset,
      greenKilled (discretize (openCube (2 * (a : ℝ))) n) x y * ((η y : ℝ) - m)| ≤
        (a : ℝ) ^ 2 * n ^ 2) :
    ∀ z : Site d, (∃ i, ((a * (5 * d * ⌈m⌉₊ + 4) : ℕ) : ℤ) * n ≤ |z i|) →
      freeOdometer η (discretize W n) z = 0 := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set K : ℕ := a * (5 * d * ⌈m⌉₊ + 4) with hK_def
  have hKR : (K : ℝ) = a * (5 * d * ⌈m⌉₊ + 4) := by simp only [hK_def]; push_cast; ring
  set Dn : Set (Site d) := discretize (openCube (2 * (a : ℝ))) n with hDn
  have hDb : Bornology.IsBounded (openCube (d := d) (2 * (a : ℝ))) :=
    isBounded_openCube (by positivity)
  have hcast : 2 * (a : ℝ) = ((2 * a : ℕ) : ℝ) := by push_cast; ring
  have hDfin : Dn.Finite := DivisibleHomogenizeDomain.discretize_finite hDb n
  have hWfin := DivisibleHomogenizeDomain.discretize_finite hW.1 n
  have hDiff : ∀ y, y ∈ Dn ↔ y ∈ boxZ (2 * (a : ℤ) * n) := fun y => by
    rw [hDn, hcast, mem_discretize_openCube_iff hn1]
    push_cast
    rfl
  have hWD : discretize W n ⊆ Dn := by
    intro y ⟨z, hz, hzy⟩
    refine ⟨z, fun i => ?_, hzy⟩
    have := hWa hz i
    linarith
  have hWn : ∀ x ∈ discretize W n, ∀ i, |x i| < (a : ℤ) * n := by
    intro x hx i
    have hx' : x ∈ discretize (openCube (a : ℝ)) n := by
      obtain ⟨z, hz, hzy⟩ := hx
      exact ⟨z, hWa hz, hzy⟩
    have h := abs_lt_of_mem_discretize_openCube hn1 hx' i
    have : ((|x i| : ℤ) : ℝ) < (((a : ℤ) * n : ℤ) : ℝ) := by push_cast; exact h
    exact_mod_cast this
  set p : Site d → ℝ := greenPotential Dn
    (fun y => (((discretize W n).indicator η y : ℤ) : ℝ)) with hp
  have hpot : ∀ x, p x = ∑ y ∈ hWfin.toFinset, greenKilled Dn x y * m +
      ∑ y ∈ hWfin.toFinset, greenKilled Dn x y * ((η y : ℝ) - m) := by
    intro x
    rw [hp, greenPotential, finsum_mem_eq_finite_toFinset_sum _ hDfin, ← Finset.sum_add_distrib]
    rw [← Finset.sum_subset (Set.Finite.toFinset_subset_toFinset.2 hWD) (fun y _ hy => by
      rw [Set.Finite.mem_toFinset] at hy
      rw [Set.indicator_of_notMem hy]
      simp)]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Set.Finite.mem_toFinset] at hy
    rw [Set.indicator_of_mem hy]
    ring
  have hpm0 : ∀ x, 0 ≤ ∑ y ∈ hWfin.toFinset, greenKilled Dn x y * m := fun x =>
    Finset.sum_nonneg fun y _ => mul_nonneg (greenKilled_nonneg _ _ _) hm0
  set RD : ℝ := Real.sqrt d * (2 * (a : ℝ)) with hRD
  have hRD0 : 0 ≤ RD := by positivity
  have hpm : ∀ x, ∑ y ∈ hWfin.toFinset, greenKilled Dn x y * m ≤
      m * ((RD + 1) ^ 2 * n ^ 2) := by
    intro x
    have hexit := greenDomainExitTime d hd1 _ RD hRD0
      (openCube_subset_closedBall (by positivity)) n x
    have hsumD : greenPotential Dn (fun _ => 1) x = ∑ y ∈ hDfin.toFinset, greenKilled Dn x y := by
      rw [greenPotential, finsum_mem_eq_finite_toFinset_sum _ hDfin]
      simp
    have hW1 : ∑ y ∈ hWfin.toFinset, greenKilled Dn x y ≤ (RD * n + 1) ^ 2 / (2 * d) := by
      refine le_trans ?_ (hsumD ▸ hexit)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.2 hWD)
        fun y _ _ => greenKilled_nonneg _ _ _
    rw [← Finset.sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hW1.trans (arith_exit_dom hRD0 hnR hdR)) hm0
  have hK2 : 2 * a ≤ K := by
    have h4 : a * 4 ≤ a * (5 * d * ⌈m⌉₊ + 4) := Nat.mul_le_mul_left a (by omega)
    simp only [hK_def]
    omega
  have hK2' : 2 * (a : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK2
  have hc0 : (0 : ℝ) ≤ (⌈m⌉₊ : ℝ) := Nat.cast_nonneg _
  have hlow := confinement_numeric_lower (A := a) (N := n) (c := ⌈m⌉₊) (D := d) haR
    (by positivity) hc0 hd0
  have hup := confinement_numeric_upper (m := m) (A := a) (N := n) (D := d) (c := ⌈m⌉₊) hm0 haR
    hnR hdR (Nat.le_ceil m) hc0
  refine freeOdometer_eq_zero_of_barrier hd (a := a) (K := K) (n := n) (p := p) (by positivity)
    (by positivity) hK2' hWn (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · exact greenPotential_eq_zero_of_not_mem _ _ (fun h => hx ((hDiff x).1 h))
  · exact lapR_greenPotential hd1 hDfin _ ((hDiff x).2 hx)
  · have h1 := hpot x
    have h2 := hpm0 x
    have h3 := (abs_le.1 (he x)).1
    have hgoal : -(((K : ℝ) - 2 * a) * n) ^ 2 ≤ p x := by
      rw [hKR]
      linarith
    push_cast
    exact hgoal
  · have h1 := hpot x
    have h2 := hpm x
    have h3 := (abs_le.1 (he x)).2
    have hgoal : p x + 1 ≤ (((K : ℝ) - a) * n) ^ 2 - (((K : ℝ) - 2 * a) * n) ^ 2 := by
      rw [hKR]
      linarith
    push_cast
    exact hgoal

/-! ### From the box to the ball -/

/-- If the free odometer vanishes on `{‖x‖_∞ ≥ Kn}`, the rescaled sandpile vanishes off
`B_R(W)` for `R = ‖w₀‖ + d (2 (K + 1) + 1) + d + 2`, `w₀ ∈ W`. -/
theorem rescaleSandpile_eq_zero_of_box {W : Set (Rd d)} {w₀ : Rd d} (hw₀ : w₀ ∈ W)
    {η : Site d → ℤ} {n K : ℕ} (hn1 : 1 ≤ n)
    (hsupp0 : ∀ z : Site d, (∃ i, (K : ℤ) * n ≤ |z i|) → freeOdometer η (discretize W n) z = 0)
    {x : Rd d}
    (hx : x ∉ Metric.thickening (‖w₀‖ + d * (2 * ((K + 1 : ℕ) : ℝ) + 1) + d + 2) W) :
    rescaleSandpile (freeSandpile η (discretize W n)) n x = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsupp : ∀ z : Site d, (∃ i, (K : ℤ) * ((n : ℤ) + 1) ≤ |z i|) →
      freeOdometer η (discretize W n) z = 0 := by
    intro z ⟨i, hi⟩
    refine hsupp0 z ⟨i, ?_⟩
    have : (K : ℤ) * n ≤ (K : ℤ) * ((n : ℤ) + 1) := by nlinarith
    linarith
  set y := latticeRound ((n : ℝ) • x) with hy
  have hxw : ‖w₀‖ + d * (2 * ((K + 1 : ℕ) : ℝ) + 1) + d + 2 ≤ dist x w₀ := by
    by_contra h
    push Not at h
    exact hx (Metric.mem_thickening_iff.2 ⟨w₀, hw₀, h⟩)
  have hxn : (d : ℝ) * (2 * ((K + 1 : ℕ) : ℝ) + 1) < ‖x‖ := by
    have := dist_le_norm_add_norm x w₀
    linarith
  obtain ⟨i, hi⟩ := exists_le_abs_latticeRound hn1 (K + 1) hxn
  have hyW : y ∉ discretize W n := by
    intro hyW
    have hmem : (n : ℝ)⁻¹ • toE y ∈ W :=
      (Set.mem_smul_set_iff_inv_smul_mem₀ (by exact_mod_cast hn0) _ _).1 hyW
    have h1 := norm_inv_smul_latticeRound_sub_le hn0 x
    have h2 : ((d : ℝ) + 1) / n ≤ d + 1 := div_le_self (by positivity) (by exact_mod_cast hn1)
    have h3 := norm_nonneg w₀
    have h4 : 0 ≤ (d : ℝ) * (2 * ((K + 1 : ℕ) : ℝ) + 1) := by positivity
    exact hx (Metric.mem_thickening_iff.2 ⟨_, hmem, by
      rw [dist_comm, dist_eq_norm]; linarith⟩)
  have hv : ∀ z : Site d, |y i| - 1 ≤ |z i| → freeOdometer η (discretize W n) z = 0 := by
    intro z hz
    refine hsupp z ⟨i, ?_⟩
    push_cast at hi
    nlinarith
  have hunit : ∀ j : Fin d, |(LatticeProb.unit j : Site d) i| ≤ 1 := fun j => by
    simp only [LatticeProb.unit, Pi.single_apply]
    split_ifs <;> simp
  have hnb : nbrSumZ (freeOdometer η (discretize W n)) y = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have hp : |y i| - 1 ≤ |(y + LatticeProb.unit j) i| := by
      have := abs_add_le (y i + (LatticeProb.unit j : Site d) i) (-(LatticeProb.unit j : Site d) i)
      rw [add_neg_cancel_right, abs_neg] at this
      rw [Pi.add_apply]
      linarith [hunit j]
    have hm : |y i| - 1 ≤ |(y - LatticeProb.unit j) i| := by
      have := abs_add_le (y i - (LatticeProb.unit j : Site d) i) ((LatticeProb.unit j : Site d) i)
      rw [sub_add_cancel] at this
      rw [Pi.sub_apply]
      linarith [hunit j]
    rw [hv _ hp, hv _ hm, add_zero]
  simp only [rescaleSandpile, freeSandpile]
  rw [Set.indicator_of_notMem hyW, lap_eq, hv y (by linarith), hnb]
  simp

/-! ### The theorem -/

/-- **Step: the support radius** (`SandpileSupportStmt`), depending only on `W` and `E η(0)`. -/
theorem sandpileSupport : SandpileSupportStmt := by
  intro d hd W hW m
  obtain ⟨R, hR0, hRW⟩ := exists_closedBall_of_isBounded hW.1
  set a : ℕ := ⌈R⌉₊ + 1 with ha_def
  have ha : 1 ≤ a := by omega
  have hWa : W ⊆ openCube (a : ℝ) := by
    intro z hz i
    have h1 : ‖z‖ ≤ R := by simpa using hRW hz
    have h3 : R < a := by
      simp only [ha_def]
      push_cast
      linarith [Nat.le_ceil R]
    linarith [abs_coord_le_norm z i]
  set K : ℕ := a * (5 * d * ⌈m⌉₊ + 4) with hK_def
  obtain ⟨w₀, hw₀⟩ := hW.2.2.1.nonempty
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨‖w₀‖ + d * (2 * ((K + 1 : ℕ) : ℝ) + 1) + d + 2, by positivity, fun E hHD hm => ?_⟩
  have hm0 : 0 ≤ m := by
    have h := hHD
    unfold HighDensity at h
    rw [hm] at h
    have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  filter_upwards [hbdd, cubeErgodic d hd E] with η hη hc
  set Kf : ℝ := |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| + |m| with hKf
  have hfK : ∀ y, |(η y : ℝ) - m| ≤ Kf := by
    intro y
    have h1 : (E.ηmin : ℝ) ≤ η y := by exact_mod_cast (hη y).1
    have h2 : (η y : ℝ) ≤ E.ηmax := by exact_mod_cast (hη y).2
    have h3 : |(η y : ℝ)| ≤ |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| := by
      rw [abs_le]
      constructor <;> cases abs_cases (E.ηmin : ℝ) <;> cases abs_cases (E.ηmax : ℝ) <;> linarith
    calc |(η y : ℝ) - m| ≤ |(η y : ℝ)| + |m| := abs_sub _ _
      _ ≤ Kf := by linarith
  have hcube : ∀ (j : ℕ) (k : Site d),
      Tendsto (fun N : ℕ => (∑ y ∈ dyadicCube j k N, ((η y : ℝ) - m)) / (N : ℝ) ^ d) atTop
        (𝓝 0) := by
    intro j k
    simpa only [hm] using hc j k
  obtain ⟨n₀, hn₀⟩ := greenBoxHomogenize hd hW ha hWa (fun y => (η y : ℝ) - m) hfK hcube
    (ε := (a : ℝ) ^ 2) (by positivity)
  filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn x hx
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  exact rescaleSandpile_eq_zero_of_box hw₀ hn1
    (freeOdometer_eq_zero_of_green hd hW ha hn1 hWa hm0
      (fun x => hn₀ n (le_trans (le_max_left _ _) hn) x)) hx

end RandomSandpile

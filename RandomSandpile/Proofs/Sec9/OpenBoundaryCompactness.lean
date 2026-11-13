import RandomSandpile.Proofs.Sec9.OpenBoundary
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainExit
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeGreen
import RandomSandpile.Proofs.Sec7.CompactnessArzelaAscoli

/-!
# Theorem 9.1: compactness of the rescaled open odometers

`openCompactness_of_steps` derives `OpenCompactnessStmt` from two analytic inputs:
* `LapLipschitzInteriorStmt` (`Steps/Sec9/OpenBoundary.lean`): the interior Lipschitz estimate for
  lattice functions with a bounded Laplacian;
* `GreenDomainBoundaryExitStmt` (`Steps/Sec8/DivisibleHomogenizeDomain.lean`, Lemma 8.1's step):
  the expected exit time from `W_n` is `≤ δ n²` within distance `γ n` of `ℤ^d ∖ W_n`.

Elementary ingredients proved here:
* `neg_le_lap_openOdometer`, `abs_lap_openOdometer_le`: `|Δ v_n| ≤ 2d + |η_min| + |η_max|` in `W_n`
  (`v_n` is least: where `v_n > 0`, removing one toppling would keep it stabilizing);
* `openOdometer_le_greenPotential`: `v_n ≤ M g_{W_n} 1` (maximum principle, `v_n = 0` on `∂W_n`), so
  `v̄_n ≤ M (R + 1)² / (2d)` (`greenDomainExitTime`) and `v̄_n ≤ ε` near `∂W`;
* `arzelaAscoli_of_asymptoticEquicontinuous`: Arzelà-Ascoli for uniformly bounded sequences
  supported in a fixed ball that are asymptotically uniformly equicontinuous (the limits need
  not be Lipschitz at re-entrant corners, so `asymptoticArzelaAscoli` does not apply).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-! ### The Laplacian of the open odometer -/

/-- The open odometer is the least element of its class: where it is positive in `A`, removing one
toppling at `x` breaks the stabilizing inequality at `x`, so `Δ v(x) ≥ -η(x)`. -/
theorem neg_le_lap_openOdometer {η : Site d → ℤ} {A : Set (Site d)}
    (hne : (stabilizingOpen η A).Nonempty) {x : Site d} (hx : x ∈ A) :
    -η x ≤ lap (openOdometer η A) x ∨ openOdometer η A x = 0 := by
  have hleast := isLeast_openOdometer hne
  obtain ⟨⟨hT, hst⟩, hbd⟩ := hleast.1
  set v := openOdometer η A with hv
  by_cases h0 : v x = 0
  · exact Or.inr h0
  left
  have hpos : 1 ≤ v x := by have := hT.1 x; omega
  set w : Site d → ℤ := fun y => if y = x then v x - 1 else v y with hw
  have hwv : ∀ y, w y ≤ v y := by
    intro y; simp only [hw]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  have hnb : ∀ i : Fin d, x + unit i ≠ x ∧ x - unit i ≠ x := by
    intro i
    have hu : unit i ≠ (0 : Site d) := by
      intro h
      have := congrFun h i
      simp [unit] at this
    constructor
    · intro h; exact hu (by simpa using h)
    · intro h; exact hu (by simpa [sub_eq_self] using h)
  by_contra hlt
  push Not at hlt
  have hxd : x ∈ dClosure A := subset_dClosure A hx
  have hxb : x ∉ bdry A := Set.disjoint_left.1 (bdry_disjoint A) hx
  have hwst : w ∈ stabilizingOpen η A := by
    refine ⟨⟨⟨fun y => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩, fun y hy => ?_⟩
    · simp only [hw]; split_ifs
      · omega
      · exact hT.1 y
    · have hyx : y ≠ x := fun h => hy (h ▸ hxd)
      simp only [hw, ite_eq_right hyx]
      exact hT.2 y hy
    · by_cases hyx : y = x
      · subst hyx
        have hnbr : nbrSumZ w y = nbrSumZ v y := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hw, ite_eq_right (hnb i).1, ite_eq_right (hnb i).2]
        have : w y = v y - 1 := by simp [hw]
        simp only [lap_eq, hnbr, this] at hlt ⊢
        have hd : (0 : ℤ) ≤ d := Nat.cast_nonneg d
        nlinarith
      · have hnbr : nbrSumZ w y ≤ nbrSumZ v y := nbrSumZ_mono hwv y
        have hwy : w y = v y := by simp [hw, hyx]
        have := hst y hy
        simp only [lap_eq] at this ⊢
        rw [hwy]
        linarith
    · have hyx : y ≠ x := fun h => hxb (h ▸ hy)
      simp only [hw, ite_eq_right hyx]
      exact hbd y hy
  have := hleast.2 hwst x
  simp [hw] at this

/-- `|Δ v_n| ≤ 2d + |η_min| + |η_max|` in `A`. -/
theorem abs_lap_openOdometer_le {η : Site d → ℤ} {A : Set (Site d)} {ηmin ηmax : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) (hne : (stabilizingOpen η A).Nonempty) {x : Site d}
    (hx : x ∈ A) :
    |(lap (openOdometer η A) x : ℝ)| ≤ 2 * d + |(ηmin : ℝ)| + |(ηmax : ℝ)| := by
  have hleast := isLeast_openOdometer hne
  obtain ⟨⟨hT, hst⟩, -⟩ := hleast.1
  have hup : lap (openOdometer η A) x + η x ≤ 2 * (d : ℤ) - 1 := hst x hx
  have h1 : ((lap (openOdometer η A) x : ℤ) : ℝ) + (η x : ℝ) ≤ 2 * d - 1 := by exact_mod_cast hup
  have hb1 : (ηmin : ℝ) ≤ η x := by exact_mod_cast (hη x).1
  have hb2 : (η x : ℝ) ≤ ηmax := by exact_mod_cast (hη x).2
  have hlow : -(ηmax : ℝ) ≤ lap (openOdometer η A) x ∨ (0 : ℝ) ≤ lap (openOdometer η A) x := by
    rcases neg_le_lap_openOdometer hne hx with h | h
    · left
      have : (-(η x : ℝ)) ≤ lap (openOdometer η A) x := by exact_mod_cast h
      linarith
    · right
      have : 0 ≤ lap (openOdometer η A) x := by
        rw [lap_eq, h]
        have := nbrSumZ_mono (u := fun _ => (0 : ℤ)) (fun y => hT.1 y) x
        simpa [nbrSumZ] using this
      exact_mod_cast this
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have a1 := neg_abs_le (ηmin : ℝ)
  have a2 := le_abs_self (ηmax : ℝ)
  have a3 := abs_nonneg (ηmin : ℝ)
  have a4 := abs_nonneg (ηmax : ℝ)
  rw [abs_le]
  constructor
  · rcases hlow with h | h <;> linarith
  · linarith

theorem lapR_const_mul_sub (K : ℝ) (f g : Site d → ℝ) (x : Site d) :
    lapR (fun z => K * f z - g z) x = K * lapR f x - lapR g x := by
  unfold lapR nbrSum
  have h1 : ∑ i : Fin d, ((K * f (x + unit i) - g (x + unit i)) +
      (K * f (x - unit i) - g (x - unit i))) =
      K * ∑ i : Fin d, (f (x + unit i) + f (x - unit i)) -
        ∑ i : Fin d, (g (x + unit i) + g (x - unit i)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]; ring

/-- The maximum principle bound `v ≤ K g_A 1` in `A` for the open odometer, when `-Δ v ≤ K`. -/
theorem openOdometer_le_greenPotential (hd : 1 ≤ d) {η : Site d → ℤ} {A : Set (Site d)}
    (hA : A.Finite) {K : ℝ} (hK : ∀ x ∈ A, -(lap (openOdometer η A) x : ℝ) ≤ K) (x : Site d) :
    (openOdometer η A x : ℝ) ≤ K * greenPotential A (fun _ => 1) x := by
  by_cases hx : x ∈ A
  · have key := DivisibleHomogenize.greenPotential_le_of_lapR_le hd hA (fun _ => 0)
      (fun z => K * greenPotential A (fun _ => 1) z - (openOdometer η A z : ℝ))
      (fun z hz => by
        rw [lapR_const_mul_sub, lapR_greenPotential hd hA _ hz, lapR_intCast]
        have := hK z hz
        linarith)
      (fun y hy => by
        have hyA : y ∉ A := Set.disjoint_right.1 (bdry_disjoint A) hy
        rw [greenPotential_eq_zero_of_not_mem A _ hyA, openOdometer_eq_zero_of_not_mem hyA]
        simp) x hx
    have h0 : greenPotential A (fun _ => (0 : ℝ)) x = 0 := by
      obtain ⟨B, rfl⟩ := hA.exists_finset_coe
      rw [greenPotential_coe_finset]
      simp
    rw [h0] at key
    linarith
  · rw [openOdometer_eq_zero_of_not_mem hx, greenPotential_eq_zero_of_not_mem A _ hx]
    simp

/-! ### Arzelà-Ascoli with asymptotic equicontinuity -/

/-- **Arzelà-Ascoli for asymptotically uniformly equicontinuous sequences**: a uniformly bounded
sequence `F n` on `ℝ^d`, vanishing outside a fixed ball, such that for every `ε > 0` there are
`δ > 0` and `N` with `|F n x - F n y| < ε` whenever `n ≥ N` and `|x - y| < δ`, has a subsequence
converging uniformly on `ℝ^d` to a continuous function. Same diagonal argument as
`asymptoticArzelaAscoli_core` (Proofs/Sec7/CompactnessArzelaAscoli.lean). -/
theorem arzelaAscoli_of_asymptoticEquicontinuous (F : ℕ → Rd d → ℝ) (K ρ : ℝ)
    (hK : ∀ n x, |F n x| ≤ K) (hρ : ∀ n x, ρ < ‖x‖ → F n x = 0)
    (hE : ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x y, dist x y < δ → |F n x - F n y| < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ vbar : Rd d → ℝ, Continuous vbar ∧
      TendstoUniformly (fun j => F (φ j)) vbar atTop := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rd d)
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_countable D hDc F K hK
  have hcauchy : ∀ q ∈ D, CauchySeq (fun j => F (φ j) q) := fun q hq =>
    (hlim q hq).choose_spec.cauchySeq
  have hunif : ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, ∀ x, |F (φ j) x - F (φ k) x| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, N₀, hN₀⟩ := hE (ε / 3) (by positivity)
    have hcov : Metric.closedBall (0 : Rd d) ρ ⊆ ⋃ q : D, Metric.ball (q : Rd d) δ := by
      intro x _
      obtain ⟨q, hq, hxq⟩ := hDd.exists_dist_lt x hδ
      exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, Metric.mem_ball.2 hxq⟩
    obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : Rd d) ρ).elim_finite_subcover
      (fun q : D => Metric.ball (q : Rd d) δ) (fun _ => Metric.isOpen_ball) hcov
    have hN : ∀ q : D, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (F (φ j) q) (F (φ k) q) < ε / 3 :=
      fun q => Metric.cauchySeq_iff.1 (hcauchy q q.2) _ (by positivity)
    choose Nq hNq using hN
    refine ⟨max N₀ (T.sup Nq), fun j hj k hk x => ?_⟩
    have hjN : φ j ≥ N₀ := le_trans (le_trans (le_max_left _ _) hj) (hφ.id_le j)
    have hkN : φ k ≥ N₀ := le_trans (le_trans (le_max_left _ _) hk) (hφ.id_le k)
    by_cases hx : ρ < ‖x‖
    · rw [hρ _ _ hx, hρ _ _ hx]
      simpa using hε
    · have hxb : x ∈ Metric.closedBall (0 : Rd d) ρ :=
        mem_closedBall_zero_iff.2 (not_lt.1 hx)
      obtain ⟨q, hqT, hxq⟩ := Set.mem_iUnion₂.1 (hT hxb)
      have hxq' : dist x q < δ := Metric.mem_ball.1 hxq
      have hjq : j ≥ Nq q := le_trans (Finset.le_sup hqT) (le_trans (le_max_right _ _) hj)
      have hkq : k ≥ Nq q := le_trans (Finset.le_sup hqT) (le_trans (le_max_right _ _) hk)
      have hA := hN₀ (φ j) hjN x q hxq'
      have hB := hN₀ (φ k) hkN x q hxq'
      have hC := hNq q j hjq k hkq
      rw [Real.dist_eq] at hC
      have htri : |F (φ j) x - F (φ k) x| ≤
          |F (φ j) x - F (φ j) q| + |F (φ j) q - F (φ k) q| + |F (φ k) x - F (φ k) q| := by
        have h1 := abs_sub_le (F (φ j) x) (F (φ j) q) (F (φ k) x)
        have h2 := abs_sub_le (F (φ j) q) (F (φ k) q) (F (φ k) x)
        rw [abs_sub_comm (F (φ k) q) (F (φ k) x)] at h2
        linarith
      linarith
  have hUC : UniformCauchySeqOn (fun j => F (φ j)) atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif ε hε
    exact ⟨N, fun m hm n hn x _ => by rw [Real.dist_eq]; exact hN m hm n hn x⟩
  have hpt : ∀ x, ∃ v, Tendsto (fun j => F (φ j) x) atTop (𝓝 v) := fun x =>
    cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hunif ε hε
      exact ⟨N, fun m hm n hn => by rw [Real.dist_eq]; exact hN m hm n hn x⟩)
  choose vbar hvbar using hpt
  have hTU : TendstoUniformly (fun j => F (φ j)) vbar atTop :=
    tendstoUniformlyOn_univ.1 (hUC.tendstoUniformlyOn_of_tendsto fun x _ => hvbar x)
  have hcont : Continuous vbar := by
    rw [Metric.continuous_iff]
    intro x ε hε
    obtain ⟨δ, hδ, N, hN⟩ := hE (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have h1 : Tendsto (fun j => |F (φ j) y - F (φ j) x|) atTop (𝓝 |vbar y - vbar x|) :=
      ((hvbar y).sub (hvbar x)).abs
    have h2 : |vbar y - vbar x| ≤ ε / 2 :=
      le_of_tendsto h1 (eventually_atTop.2 ⟨N, fun j hj =>
        (hN (φ j) (le_trans hj (hφ.id_le j)) y x hy).le⟩)
    rw [Real.dist_eq]
    linarith
  exact ⟨φ, hφ, vbar, hcont, hTU⟩

/-! ### Asymptotic equicontinuity of the rescaled open odometers -/

private theorem toE_sub_ob (x y : Site d) : toE (x - y) = toE x - toE y := by
  ext i; simp [toE]

/-- Sites of `W_n` lie in the open cube `{|x|_∞ < ⌈ρ⌉₊ n + 1}` when `W ⊆ B̄_ρ(0)`. -/
theorem abs_lt_of_mem_discretize {W : Set (Rd d)} {ρ : ℝ} (hW : W ⊆ Metric.closedBall 0 ρ)
    {n : ℕ} {x : Site d} (hx : x ∈ discretize W n) (i : Fin d) :
    |x i| < ((⌈ρ⌉₊ * n + 1 : ℕ) : ℤ) := by
  have h1 := DivisibleHomogenizeDomain.norm_le_of_mem_discretize hW hx
  have h2 : |(x i : ℝ)| ≤ ‖toE x‖ := by
    simpa [toE, Real.norm_eq_abs] using PiLp.norm_apply_le (toE x) i
  have h3 : ρ * n ≤ (⌈ρ⌉₊ : ℝ) * n :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil ρ) (Nat.cast_nonneg n)
  have h5 : ((|x i| : ℤ) : ℝ) < ((((⌈ρ⌉₊ * n + 1 : ℕ) : ℤ)) : ℝ) := by
    rw [Int.cast_abs]; push_cast; linarith
  exact_mod_cast h5

theorem mem_nearCompl_of_near {A : Set (Site d)} {s t : ℝ} {a b : Site d}
    (ha : a ∈ nearCompl A s) (hab : ‖toE (a - b)‖ ≤ t) : b ∈ nearCompl A (s + t) := by
  obtain ⟨z, hz, hza⟩ := ha
  refine ⟨z, hz, ?_⟩
  have e : toE (z - b) = toE (z - a) + toE (a - b) := by
    rw [toE_sub_ob, toE_sub_ob, toE_sub_ob]; abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add hza hab)

theorem nearCompl_mono {A : Set (Site d)} {s t : ℝ} (hst : s ≤ t) :
    nearCompl A s ⊆ nearCompl A t := fun _ ⟨z, hz, h⟩ => ⟨z, hz, h.trans hst⟩

/-- The rescaled open odometers are asymptotically uniformly equicontinuous, from the interior
Lipschitz estimate (`LapLipschitzInteriorStmt`) away from `∂W` and the exit-time bound
(`GreenDomainBoundaryExitStmt`) near `∂W`. -/
theorem openOdometer_equicontinuous (hLip : LapLipschitzInteriorStmt)
    (hExit : GreenDomainBoundaryExitStmt) (hd : 2 ≤ d) {W : Set (Rd d)} (hW : IsLipschitzDomain W)
    {ηmin ηmax : ℤ} {η : Site d → ℤ} (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) :
    ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x y : Rd d, dist x y < δ →
      |rescaleOdo (openOdometer η (discretize W n)) n x -
        rescaleOdo (openOdometer η (discretize W n)) n y| < ε := by
  intro ε hε
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set M : ℝ := 2 * d + |(ηmin : ℝ)| + |(ηmax : ℝ)| with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨γ, hγ, n₀, hexit⟩ := hExit d hd W hW (ε / (4 * M)) (by positivity)
  obtain ⟨C, hC, hlip⟩ := hLip d hd
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Rd d)).1 hW.1
  set P : ℝ := (⌈ρ⌉₊ : ℝ) + 2 with hP
  have hP0 : 0 < P := by positivity
  set Λ : ℝ := C * M * P * (1 + (2 * P / γ) ^ (d - 1)) with hΛ
  have hΛ0 : 0 < Λ := by positivity
  set δ : ℝ := min (γ / 8) (ε / (4 * Λ)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (16 * ((d : ℝ) + 1) / γ)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (8 * Λ * ((d : ℝ) + 1) / ε)
  refine ⟨δ, hδ0, max n₀ (max 1 (max N₁ N₂)), fun n hn x y hxy => ?_⟩
  have hn₀ : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnN₁ : (N₁ : ℝ) ≤ n := by
    exact_mod_cast le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hnN₂ : (N₂ : ℝ) ≤ n := by
    exact_mod_cast le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hγn : 16 * ((d : ℝ) + 1) < γ * n := by
    have := (div_lt_iff₀ hγ).1 (hN₁.trans_le hnN₁)
    linarith
  have hΛn : 8 * Λ * ((d : ℝ) + 1) < ε * n := by
    have := (div_lt_iff₀ hε).1 (hN₂.trans_le hnN₂)
    linarith
  set A := discretize W n with hA
  have hAfin : A.Finite := DivisibleHomogenizeDomain.discretize_finite hW.1 n
  have hne : (stabilizingOpen η A).Nonempty := stabilizingOpen_nonempty (by omega) η hAfin
  set v := openOdometer η A with hv
  have hlap : ∀ z ∈ A, |(lap v z : ℝ)| ≤ M := fun z hz => abs_lap_openOdometer_le hη hne hz
  have hvG : ∀ z, (v z : ℝ) ≤ M * greenPotential A (fun _ => 1) z :=
    openOdometer_le_greenPotential hd1 hAfin fun z hz => by
      linarith [(abs_le.1 (hlap z hz)).1]
  have hv0 : ∀ z, (0 : ℝ) ≤ v z := fun z => by exact_mod_cast openOdometer_nonneg η A z
  have hnear : ∀ z, z ∈ nearCompl A (γ * n) → (v z : ℝ) ≤ ε / 4 * (n : ℝ) ^ 2 := by
    intro z hz
    by_cases hzA : z ∈ A
    · have h1 := hexit n hn₀ z hz
      calc (v z : ℝ) ≤ M * greenPotential A (fun _ => 1) z := hvG z
        _ ≤ M * (ε / (4 * M) * (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h1 hM0.le
        _ = ε / 4 * (n : ℝ) ^ 2 := by field_simp
    · rw [hv, openOdometer_eq_zero_of_not_mem hzA]
      simp only [Int.cast_zero]
      positivity
  set a := latticeRound ((n : ℝ) • x) with ha
  set b := latticeRound ((n : ℝ) • y) with hb
  have hab : ‖toE (a - b)‖ ≤ 2 * ((d : ℝ) + 1) + n * dist x y := by
    have e : toE (a - b) =
        (toE a - (n : ℝ) • x) + (n : ℝ) • (x - y) - (toE b - (n : ℝ) • y) := by
      rw [toE_sub_ob, smul_sub]; abel
    rw [e]
    have h1 := norm_toE_latticeRound_sub_le ((n : ℝ) • x)
    have h2 := norm_toE_latticeRound_sub_le ((n : ℝ) • y)
    have h3 : ‖(n : ℝ) • (x - y)‖ = n * dist x y := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hnpos, dist_eq_norm]
    calc _ ≤ ‖(toE a - (n : ℝ) • x) + (n : ℝ) • (x - y)‖ + ‖toE b - (n : ℝ) • y‖ :=
          norm_sub_le _ _
      _ ≤ ‖toE a - (n : ℝ) • x‖ + ‖(n : ℝ) • (x - y)‖ + ‖toE b - (n : ℝ) • y‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ _ := by rw [h3]; linarith
  have hxyδ : (n : ℝ) * dist x y ≤ n * δ := mul_le_mul_of_nonneg_left hxy.le hnpos.le
  have hδγ : (n : ℝ) * δ ≤ n * (γ / 8) := mul_le_mul_of_nonneg_left (min_le_left _ _) hnpos.le
  have hab' : ‖toE (a - b)‖ ≤ γ * n / 4 := by linarith
  have hba' : ‖toE (b - a)‖ ≤ γ * n / 4 := by
    rw [show b - a = -(a - b) by abel, show toE (-(a - b)) = -toE (a - b) by ext i; simp [toE],
      norm_neg]
    exact hab'
  -- reduce to `|v a - v b| < ε n²`
  have hgoal : |(v a : ℝ) - v b| < ε * (n : ℝ) ^ 2 →
      |rescaleOdo v n x - rescaleOdo v n y| < ε := by
    intro h
    simp only [rescaleOdo]
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2),
      div_lt_iff₀ (by positivity)]
    exact h
  refine hgoal ?_
  by_cases hcase : a ∈ nearCompl A (γ * n / 2) ∨ b ∈ nearCompl A (γ * n / 2)
  · have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hγ2 : γ * n / 2 + γ * n / 4 ≤ γ * n := by linarith
    have hγ3 : γ * n / 2 ≤ γ * n := by linarith
    have hboth : a ∈ nearCompl A (γ * n) ∧ b ∈ nearCompl A (γ * n) := by
      rcases hcase with h | h
      · exact ⟨nearCompl_mono hγ3 h, nearCompl_mono hγ2 (mem_nearCompl_of_near h hab')⟩
      · exact ⟨nearCompl_mono hγ2 (mem_nearCompl_of_near h hba'), nearCompl_mono hγ3 h⟩
    have h1 := hnear a hboth.1
    have h2 := hnear b hboth.2
    have := abs_sub_le_of_nonneg_of_le (hv0 a) h1 (hv0 b) h2
    have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
    have h5 := mul_pos hε hn2
    linarith
  · push Not at hcase
    obtain ⟨hna, hnb⟩ := hcase
    have hfar : ∀ w, w ∉ nearCompl A (γ * n / 2) → ∀ z, z ∉ A → γ * n / 2 ≤ ‖toE (z - w)‖ :=
      fun w hw z hz => le_of_not_ge fun h => hw ⟨z, hz, h⟩
    set R : ℕ := ⌈ρ⌉₊ * n + 1 with hR
    have hr : 0 < γ * n / 2 := by positivity
    have key := hlip v A M R (γ * n / 2) (fun z => openOdometer_nonneg η A z)
      (fun z hz => openOdometer_eq_zero_of_not_mem hz)
      (fun z hz i => abs_lt_of_mem_discretize hρ hz i) hlap hr a b
      (hfar a hna) (hfar b hnb) (by linarith)
    have hR1 : ((R : ℕ) : ℝ) + 1 ≤ P * n := by
      rw [hR, hP]; push_cast; linarith
    have hRr : (((R : ℕ) : ℝ) + 1) / (γ * n / 2) ≤ 2 * P / γ := by
      rw [div_le_div_iff₀ hr hγ]
      have := mul_le_mul_of_nonneg_right hR1 hγ.le
      linarith
    have hR0 : (0 : ℝ) ≤ ((R : ℕ) : ℝ) + 1 := by positivity
    have hpow : ((((R : ℕ) : ℝ) + 1) / (γ * n / 2)) ^ (d - 1) ≤ (2 * P / γ) ^ (d - 1) :=
      pow_le_pow_left₀ (by positivity) hRr _
    have hbound : C * M * (((R : ℕ) : ℝ) + 1) *
        (1 + ((((R : ℕ) : ℝ) + 1) / (γ * n / 2)) ^ (d - 1)) * ‖toE (a - b)‖ ≤
        Λ * n * ‖toE (a - b)‖ := by
      rw [hΛ]
      have hn0 := norm_nonneg (toE (a - b))
      have e : C * M * P * (1 + (2 * P / γ) ^ (d - 1)) * n * ‖toE (a - b)‖ =
          C * M * (P * n) * (1 + (2 * P / γ) ^ (d - 1)) * ‖toE (a - b)‖ := by ring
      rw [e]
      gcongr
    have hΛab : Λ * n * ‖toE (a - b)‖ ≤ Λ * n * (2 * ((d : ℝ) + 1) + n * δ) :=
      mul_le_mul_of_nonneg_left (hab.trans (by linarith)) (by positivity)
    have hΛδ : Λ * δ ≤ ε / 4 := by
      have : Λ * δ ≤ Λ * (ε / (4 * Λ)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hΛ0.le
      rwa [show Λ * (ε / (4 * Λ)) = ε / 4 by field_simp] at this
    have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
    have e2 : Λ * n * (2 * ((d : ℝ) + 1) + n * δ) =
        2 * Λ * ((d : ℝ) + 1) * n + Λ * δ * (n : ℝ) ^ 2 := by ring
    have h3 : 2 * Λ * ((d : ℝ) + 1) * n ≤ ε / 4 * (n : ℝ) ^ 2 := by
      have := mul_lt_mul_of_pos_right hΛn hnpos
      linarith
    have h4 : Λ * δ * (n : ℝ) ^ 2 ≤ ε / 4 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hΛδ hn2.le
    have hfin := key.trans (hbound.trans hΛab)
    rw [e2] at hfin
    have h5 := mul_pos hε hn2
    linarith

/-! ### The reduction -/

/-- **Step** of Theorem 9.1 from the interior Lipschitz estimate and the exit-time bound near
`∂W`. -/
theorem openCompactness_of_steps (hLip : LapLipschitzInteriorStmt)
    (hExit : GreenDomainBoundaryExitStmt) : OpenCompactnessStmt := by
  intro d hd W hW ηmin ηmax η hη nk hnk
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Rd d)).1 hW.1
  set ρ' := max ρ 0 with hρ'_def
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  have hρ' : W ⊆ Metric.closedBall 0 ρ' :=
    hρ.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  set M : ℝ := 2 * d + |(ηmin : ℝ)| + |(ηmax : ℝ)| with hM
  have hM0 : 0 < M := by positivity
  set F : ℕ → Rd d → ℝ := fun j => rescaleOdo (openOdometer η (discretize W (nk j))) (nk j)
    with hF
  have hbound : ∀ j x, |F j x| ≤ M * (ρ' + 1) ^ 2 / (2 * d) := by
    intro j x
    have hB0 : 0 ≤ M * (ρ' + 1) ^ 2 / (2 * d) := by positivity
    rcases Nat.eq_zero_or_pos (nk j) with hn0 | hnpos
    · simp only [hF, rescaleOdo, hn0, Nat.cast_zero]
      simpa using hB0
    · set n := nk j with hn
      set A := discretize W n with hA
      have hAfin : A.Finite := DivisibleHomogenizeDomain.discretize_finite hW.1 n
      have hne : (stabilizingOpen η A).Nonempty := stabilizingOpen_nonempty (by omega) η hAfin
      set z := latticeRound ((n : ℝ) • x)
      have hvG := openOdometer_le_greenPotential hd1 hAfin (K := M) (fun w hw => by
        linarith [(abs_le.1 (abs_lap_openOdometer_le hη hne hw)).1]) z
      have hG := greenDomainExitTime d hd1 W ρ' hρ'0 hρ' n z
      have hv0 : (0 : ℝ) ≤ openOdometer η A z := by exact_mod_cast openOdometer_nonneg η A z
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      show |(openOdometer η A z : ℝ) / (n : ℝ) ^ 2| ≤ _
      rw [abs_of_nonneg (div_nonneg hv0 (sq_nonneg _)), div_le_iff₀ (by positivity)]
      have hsq : (ρ' * n + 1) ^ 2 ≤ ((ρ' + 1) * n) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      calc (openOdometer η A z : ℝ) ≤ M * greenPotential A (fun _ => 1) z := hvG
        _ ≤ M * ((ρ' * n + 1) ^ 2 / (2 * d)) := mul_le_mul_of_nonneg_left hG hM0.le
        _ ≤ M * (((ρ' + 1) * n) ^ 2 / (2 * d)) := by gcongr
        _ = M * (ρ' + 1) ^ 2 / (2 * d) * (n : ℝ) ^ 2 := by ring
  have hsupp : ∀ j x, ρ' + d + 1 < ‖x‖ → F j x = 0 := by
    intro j x hx
    rcases Nat.eq_zero_or_pos (nk j) with hn0 | hnpos
    · simp [hF, rescaleOdo, hn0]
    · refine rescaleOdo_openOdometer_eq_zero hnpos.ne' fun hW' => ?_
      have h1 := norm_inv_smul_latticeRound_sub_le hnpos.ne' x
      have hnR : (1 : ℝ) ≤ nk j := by exact_mod_cast hnpos
      have h2 : ((d : ℝ) + 1) / (nk j) ≤ d + 1 := div_le_self (by positivity) hnR
      have h3 := mem_closedBall_zero_iff.1 (hρ' hW')
      have h4 := norm_sub_norm_le x ((nk j : ℝ)⁻¹ • toE (latticeRound ((nk j : ℝ) • x)))
      rw [norm_sub_rev] at h4
      linarith
  have hE := openOdometer_equicontinuous hLip hExit hd hW hη
  have hE' : ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x y, dist x y < δ →
      |F j x - F j y| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, N, hN⟩ := hE ε hε
    exact ⟨δ, hδ, N, fun j hj x y hxy => hN (nk j) (le_trans hj (hnk.id_le j)) x y hxy⟩
  exact arzelaAscoli_of_asymptoticEquicontinuous F _ _ hbound hsupp hE'

/-- **Theorem 9.1** with compactness reduced to its analytic inputs. -/
theorem openBoundaryTheorem_of_analyticSteps (h64 : EffectiveOperatorBasicStmt)
    (hLip : LapLipschitzInteriorStmt) (hExit : GreenDomainBoundaryExitStmt) (hVan : MuVanishStmt)
    (hMax : OpenInteriorMaxPrincipleStmt) (hMin : OpenInteriorMinPrincipleStmt)
    (hShift : EffShiftStmt) (hCIL : ShiftComparisonStmt) : OpenBoundaryTheoremStmt :=
  openBoundaryTheorem_of_remainingSteps h64 (openCompactness_of_steps hLip hExit) hVan hMax hMin
    hShift hCIL

end RandomSandpile

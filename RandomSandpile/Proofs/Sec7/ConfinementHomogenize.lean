import RandomSandpile.Proofs.Sec7.ConfinementLayer
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainCubes
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainGradient
import RandomSandpile.Proofs.Sec7.MainTheoremEnv
import RandomSandpile.Inputs.LawlerLimicHarmonicDifference

/-!
# Homogenization of the Green potential of `f 𝟙_{W_n}` in a box

For the confinement radius of Theorem 1.1: if `f` is bounded with vanishing normalized dyadic cube
sums and `W ⊆ (-a, a)^d` is a bounded Lipschitz domain, the Green potential in the box
`D_n = ℤ^d ∩ n (-2a, 2a)^d` of `f 𝟙_{W_n}` is `o(n²)` uniformly (`greenBoxHomogenize`). The proof is
the cube decomposition of Lemma 8.1 (`abs_sum_le_cubes_gen`) with the Green function of `D_n` and
the summation set `W_n`: the interior cubes of `W_n` are handled by the interior difference sum of
`D_n` (`greenDomainGradientSum_of_lawlerLimic`), the boundary layer of `W_n`, which lies inside
`D_n`, by `layerMass`.
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology Metric Set

namespace RandomSandpile

open OdometerLowerBound DivisibleHomogenize DivisibleHomogenizeDomain

variable {d : ℕ}

/-- The cube decomposition with the Green function of `D` and the summation set `W ⊆ D`. -/
theorem abs_sum_greenKilled_le_core (hP : BoxPoincare d) {j N : ℕ} {θ K t s Eg Gg Lg : ℝ}
    {D A : Set (Site d)} (hDfin : D.Finite) (hAfin : A.Finite) (hAD : A ⊆ D) (x : Site d)
    (f : Site d → ℝ) (hf : ∀ y, |f y| ≤ K) (hN : 2 * 2 ^ j ≤ (N : ℝ)) (hθ0 : 0 ≤ θ)
    (hθ : ∀ k ∈ cubeIndexSet d j, |∑ y ∈ dyadicCube j k N, f y| ≤ θ * (N : ℝ) ^ d)
    (hS : ∀ y ∈ A, ‖toE y‖ < N) (ht : 0 ≤ t) (hs : Real.sqrt d * ((N : ℝ) / 2 ^ j) ≤ s)
    (hexit : greenPotential D (fun _ => 1) x ≤ Eg)
    (hgrad : ∑ᶠ y ∈ (nearCompl D t)ᶜ, ∑ i : Fin d,
      |greenKilled D x (y + unit i) - greenKilled D x y| ≤ Gg)
    (hlayer : ∑ y ∈ (hAfin.subset inter_subset_left : (A ∩ nearCompl A (t + s)).Finite).toFinset,
      greenKilled D x y ≤ Lg) :
    |∑ y ∈ hAfin.toFinset, greenKilled D x y * f y| ≤
      θ * (2 * 2 ^ j) ^ d * Eg + K * (2 ^ d * d * (2 * N / 2 ^ j)) * Gg + K * Lg := by
  classical
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf 0)
  have hg0 : ∀ y, 0 ≤ greenKilled D x y := fun y => greenKilled_nonneg _ _ _
  have hIfin : (A ∩ (nearCompl A t)ᶜ).Finite := hAfin.subset inter_subset_left
  have hIS : hIfin.toFinset ⊆ hAfin.toFinset :=
    Set.Finite.toFinset_subset_toFinset.2 inter_subset_left
  have key := abs_sum_le_cubes_gen hP (greenKilled D x) f hg0 hf hN hθ0 hθ hAfin.toFinset
    hIfin.toFinset (fun y hy => hS y ((Set.Finite.mem_toFinset _).1 hy)) hIS
  -- The exit time of `D` bounds the mass on `A`.
  have h1 : ∑ y ∈ hAfin.toFinset, greenKilled D x y ≤ Eg := by
    have hpot : greenPotential D (fun _ => 1) x = ∑ y ∈ hDfin.toFinset, greenKilled D x y := by
      rw [greenPotential, finsum_mem_eq_finite_toFinset_sum _ hDfin]
      simp
    refine le_trans ?_ (hpot ▸ hexit)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Set.Finite.toFinset_subset_toFinset.2 hAD) fun y _ _ => hg0 y
  -- The interior of `A` lies in the interior of `D`.
  have hDIfin : ((nearCompl D t)ᶜ).Finite := hDfin.subset (compl_nearCompl_subset ht)
  have hsubI : hIfin.toFinset ⊆ hDIfin.toFinset := by
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy ⊢
    intro hyD
    obtain ⟨z, hz, hzy⟩ := hyD
    exact hy.2 ⟨z, fun hzA => hz (hAD hzA), hzy⟩
  have h2 : ∑ y ∈ hIfin.toFinset, ∑ i : Fin d,
      |greenKilled D x (y + unit i) - greenKilled D x y| ≤ Gg := by
    refine le_trans ?_ hgrad
    rw [finsum_mem_eq_finite_toFinset_sum _ hDIfin]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubI fun y _ _ =>
      Finset.sum_nonneg fun i _ => abs_nonneg _
  -- The layer.
  have hI : ∀ y, y ∉ hIfin.toFinset → y ∈ nearCompl A t := by
    intro y hy
    rw [Set.Finite.mem_toFinset, mem_inter_iff, not_and_or, mem_compl_iff, not_not] at hy
    rcases hy with hyA | hy
    · exact ⟨y, hyA, by rw [sub_self, toE_zero_conf, norm_zero]; exact ht⟩
    · exact hy
  have hT := layer_subset hs hI
  have h3 : ∑ y ∈ hAfin.toFinset, greenKilled D x y *
      ({y | ∃ y', y' ∉ hIfin.toFinset ∧
        ‖toE y' - toE y‖ ≤ Real.sqrt d * ((N : ℝ) / 2 ^ j)}.indicator (fun _ => 1) y) ≤ Lg := by
    refine le_trans ?_ hlayer
    calc ∑ y ∈ hAfin.toFinset, greenKilled D x y *
          ({y | ∃ y', y' ∉ hIfin.toFinset ∧
            ‖toE y' - toE y‖ ≤ Real.sqrt d * ((N : ℝ) / 2 ^ j)}.indicator (fun _ => 1) y)
        ≤ ∑ y ∈ hAfin.toFinset, greenKilled D x y *
            (nearCompl A (t + s)).indicator (fun _ => 1) y :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
            (Set.indicator_le_indicator_of_subset hT (fun _ => zero_le_one) y) (hg0 y)
      _ = ∑ y ∈ (hAfin.subset inter_subset_left :
            (A ∩ nearCompl A (t + s)).Finite).toFinset, greenKilled D x y := by
          rw [← Finset.sum_filter_add_sum_filter_not hAfin.toFinset (· ∈ nearCompl A (t + s))]
          have hzero : ∑ y ∈ hAfin.toFinset.filter (· ∉ nearCompl A (t + s)),
              greenKilled D x y * (nearCompl A (t + s)).indicator (fun _ => 1) y = 0 :=
            Finset.sum_eq_zero fun y hy => by
              rw [Set.indicator_of_notMem (Finset.mem_filter.1 hy).2, mul_zero]
          rw [hzero, add_zero]
          refine Finset.sum_congr ?_ fun y hy => ?_
          · ext y
            simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_inter_iff]
          · rw [Set.indicator_of_mem ((Set.Finite.mem_toFinset _).1 hy).2, mul_one]
  have hc : 0 ≤ θ * (2 * 2 ^ j) ^ d := by positivity
  have hc' : 0 ≤ K * (2 ^ d * d * (2 * N / 2 ^ j)) := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
    positivity
  exact key.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 hc)
    (mul_le_mul_of_nonneg_left h2 hc')) (mul_le_mul_of_nonneg_left h3 hK))

/-- The open cube `(-r, r)^d`. -/
def openCube (r : ℝ) : Set (Rd d) := {z | ∀ i, |z i| < r}

theorem openCube_subset_closedBall {r : ℝ} (hr : 0 ≤ r) :
    openCube (d := d) r ⊆ Metric.closedBall 0 (Real.sqrt d * r) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, ← Real.sqrt_sq hr,
    ← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [hz i, abs_nonneg (z i), sq_abs (z i)]
    _ = d * r ^ 2 := by simp

theorem isBounded_openCube {r : ℝ} (hr : 0 ≤ r) : Bornology.IsBounded (openCube (d := d) r) :=
  Metric.isBounded_closedBall.subset (openCube_subset_closedBall hr)

theorem abs_lt_of_mem_discretize_openCube {r : ℝ} {n : ℕ} (hn : 1 ≤ n) {y : Site d}
    (hy : y ∈ discretize (openCube r) n) (i : Fin d) : |(y i : ℝ)| < r * n := by
  obtain ⟨z, hz, hzy⟩ := hy
  have h : (y i : ℝ) = n * z i := by
    have := congrArg (fun w : Rd d => w i) hzy
    simpa [toE] using this.symm
  rw [h, abs_mul, Nat.abs_cast, mul_comm]
  exact mul_lt_mul_of_pos_right (hz i) (by exact_mod_cast hn)

/-- **Homogenization of `G_{D_n}(f 𝟙_{W_n})`.** For `d ≥ 2`, a bounded Lipschitz domain
`W ⊆ (-a, a)^d` and a bounded `f` whose normalized dyadic cube sums tend to `0`, for every `ε > 0`,
eventually `|∑_{y ∈ W_n} g_{D_n}(x, y) f(y)| ≤ ε n²` for all `x`, where `D_n = ℤ^d ∩ n (-2a, 2a)^d`. -/
theorem greenBoxHomogenize (hd : 2 ≤ d) {W : Set (Rd d)} (hW : IsLipschitzDomain W) {a : ℕ}
    (ha : 1 ≤ a) (hWa : W ⊆ openCube (a : ℝ)) (f : Site d → ℝ) {K : ℝ} (hf : ∀ y, |f y| ≤ K)
    (hcube : ∀ (j : ℕ) (k : Site d),
      Tendsto (fun N : ℕ => (∑ y ∈ dyadicCube j k N, f y) / (N : ℝ) ^ d) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x : Site d,
      |∑ y ∈ (DivisibleHomogenizeDomain.discretize_finite hW.1 n).toFinset,
        greenKilled (discretize (openCube (2 * a : ℝ)) n) x y * f y| ≤ ε * (n : ℝ) ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf 0)
  have hA : (1 : ℝ) ≤ a := by exact_mod_cast ha
  set Dset : Set (Rd d) := openCube (2 * a : ℝ) with hDset
  have hDb : Bornology.IsBounded Dset := isBounded_openCube (by positivity)
  set RD : ℝ := Real.sqrt d * (2 * a) with hRD
  have hRD0 : 0 ≤ RD := by positivity
  have hDR : Dset ⊆ Metric.closedBall 0 RD := openCube_subset_closedBall (by positivity)
  obtain ⟨R, hR0, hRW⟩ := exists_closedBall_of_isBounded hW.1
  obtain ⟨M, hRM, hM1⟩ : ∃ M : ℕ, R < M ∧ 1 ≤ M :=
    ⟨⌈R⌉₊ + 1, by push_cast; linarith [Nat.le_ceil R], by omega⟩
  obtain ⟨δ, hδ0, hKδ⟩ : ∃ δ : ℝ, 0 < δ ∧ K * δ ≤ ε / 4 := by
    refine ⟨ε / (4 * (K + 1)), by positivity, ?_⟩
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨γ, hγ, n₁, hn₁⟩ := layerMass hd hW.1 (volume_frontier_of_isLipschitzDomain hW) ha hδ0
  obtain ⟨β, hβ0, hβγ⟩ : ∃ β : ℝ, 0 < β ∧ β + β = γ := ⟨γ / 2, by positivity, by ring⟩
  obtain ⟨C, n₂, hC⟩ := greenDomainGradientSum_of_lawlerLimic lawlerLimicHarmonicDifference d hd
    Dset hDb β hβ0
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
    (max (Real.sqrt d * M / β) (8 * K * 2 ^ d * d * M * |C| / ε)) (by norm_num : (1 : ℝ) < 2)
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hj1 : Real.sqrt d * M ≤ β * 2 ^ j := by
    have := (le_max_left _ _).trans_lt hj
    rw [div_lt_iff₀ hβ0] at this
    linarith
  have hj2 : 8 * K * 2 ^ d * d * M * |C| ≤ ε * 2 ^ j := by
    have := (le_max_right _ _).trans_lt hj
    rw [div_lt_iff₀ hε] at this
    linarith
  obtain ⟨θ, hθ0, hθe⟩ : ∃ θ : ℝ, 0 < θ ∧
      θ * (2 * 2 ^ j) ^ d = ε / (4 * ((RD + 1) ^ 2 + 1)) :=
    ⟨ε / (4 * (2 * 2 ^ j) ^ d * ((RD + 1) ^ 2 + 1)), by positivity, by field_simp⟩
  have hev : ∀ᶠ N : ℕ in atTop, ∀ k ∈ cubeIndexSet d j,
      |(∑ y ∈ dyadicCube j k N, f y) / (N : ℝ) ^ d| < θ := by
    rw [Filter.eventually_all_finset]
    intro k _
    have h := (hcube j k).abs
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds hθ0)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max (max N₀ (2 * 2 ^ j)) (max n₁ (max n₂ 1)), fun n hn x => ?_⟩
  have hnN : N₀ ≤ n := le_trans (le_max_left _ _) (le_of_max_le_left hn)
  have hn2 : 2 * 2 ^ j ≤ n := le_trans (le_max_right _ _) (le_of_max_le_left hn)
  have hn₁' : n₁ ≤ n := le_trans (le_max_left _ _) (le_of_max_le_right hn)
  have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_of_max_le_right hn)
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_of_max_le_right hn)
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hNR : ((M * n : ℕ) : ℝ) = M * n := by push_cast; ring
  have hNn : N₀ ≤ M * n := le_trans hnN (Nat.le_mul_of_pos_left n (by omega))
  have hN2 : (2 : ℝ) * 2 ^ j ≤ ((M * n : ℕ) : ℝ) := by
    have : (2 * 2 ^ j : ℕ) ≤ M * n := le_trans hn2 (Nat.le_mul_of_pos_left n (by omega))
    exact_mod_cast this
  have hθ : ∀ k ∈ cubeIndexSet d j,
      |∑ y ∈ dyadicCube j k (M * n), f y| ≤ θ * ((M * n : ℕ) : ℝ) ^ d := by
    intro k hk
    have h := hN₀ (M * n) hNn k hk
    have hNd : (0 : ℝ) < ((M * n : ℕ) : ℝ) ^ d := by positivity
    rw [abs_div, abs_of_pos hNd, div_lt_iff₀ hNd] at h
    exact h.le
  have hS : ∀ y ∈ discretize W n, ‖toE y‖ < ((M * n : ℕ) : ℝ) := by
    intro y hy
    have h1 := norm_le_of_mem_discretize hRW hy
    rw [hNR]
    have : R * n < M * n := mul_lt_mul_of_pos_right hRM (by linarith)
    linarith
  have hβn : 0 ≤ β * n := by positivity
  have hs : Real.sqrt d * (((M * n : ℕ) : ℝ) / 2 ^ j) ≤ β * n := by
    rw [hNR]; exact arith_layer_dom h2j (by linarith) hj1
  have hWD : discretize W n ⊆ discretize Dset n := by
    intro y ⟨z, hz, hzy⟩
    refine ⟨z, fun i => ?_, hzy⟩
    have := hWa hz i
    have h2 : (a : ℝ) ≤ 2 * a := by linarith
    linarith
  have hDfin : (discretize Dset n).Finite := DivisibleHomogenizeDomain.discretize_finite hDb n
  set Lfin := ((DivisibleHomogenizeDomain.discretize_finite hW.1 n).subset
      inter_subset_left : (discretize W n ∩
        nearCompl (discretize W n) (β * n + β * n)).Finite).toFinset with hLfin
  have hDcond : ∀ y ∈ hDfin.toFinset, ∀ i, |y i| < 2 * a * n := by
    intro y hy i
    have := abs_lt_of_mem_discretize_openCube hn1 ((Set.Finite.mem_toFinset _).1 hy) i
    have h' : ((|y i| : ℤ) : ℝ) < ((2 * a * n : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h'
  have hLcond : ∀ y ∈ Lfin, y ∈ discretize W n ∧ y ∈ nearCompl (discretize W n) (γ * n) := by
    intro y hy
    rw [hLfin, Set.Finite.mem_toFinset] at hy
    refine ⟨hy.1, ?_⟩
    have e : β * (n : ℝ) + β * n = γ * n := by rw [← hβγ]; ring
    rw [← e]
    exact hy.2
  have hlay : ∑ y ∈ Lfin, greenKilled (discretize Dset n) x y ≤ δ * (n : ℝ) ^ 2 := by
    have h := hn₁ n hn₁' hDfin.toFinset Lfin hDcond hLcond x
    rwa [Set.Finite.coe_toFinset] at h
  have hcore := abs_sum_greenKilled_le_core (boxPoincare d) hDfin
    (DivisibleHomogenizeDomain.discretize_finite hW.1 n) hWD x f hf hN2 hθ0.le hθ hS hβn hs
    (greenDomainExitTime d hd1 Dset RD hRD0 hDR n x) (hC n hn₂ x) hlay
  have hT1 := arith_T1 hθe (arith_exit_dom hRD0 hnR1 hdR) (by positivity) hε.le
    (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
  have hT2 := arith_T2 (K := K) (Q := 2 ^ d) (D := d) (M := M) (C := C) (C' := |C|)
    (P := 2 ^ j) (ε := ε) (n := n) hK (by positivity) (by positivity) (by positivity) h2j
    (by linarith) (le_abs_self C) hj2
  have hT3 : K * (δ * (n : ℝ) ^ 2) ≤ ε / 4 * (n : ℝ) ^ 2 := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hKδ (by positivity)
  rw [hNR] at hcore
  have hεn : 0 ≤ ε * (n : ℝ) ^ 2 := by positivity
  linarith

end RandomSandpile

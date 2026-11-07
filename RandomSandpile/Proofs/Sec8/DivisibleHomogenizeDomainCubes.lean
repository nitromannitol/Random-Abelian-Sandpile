import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainExit
import RandomSandpile.Proofs.Sec7.DivisibleHomogenize

/-!
# Lemma 8.1: the cube decomposition on `W_n`

`paper/random_piles-corrected.tex` (Lemma 8.1; the argument of Lemma 7.3, on `W_n = ℤ^d ∩ nW`). The dyadic cubes of side `2^{-j} N` (`N = M n`,
`W ⊆ B̄_R(0)`, `M = ⌈R⌉ + 1`, so that `W_n ⊆ B_N`) contained in the interior region
`I = {y : dist(y, ℤ^d ∖ W_n) > β n}` are treated as in Lemma 7.3 (pooling at the cube average
and the discrete Poincaré inequality, `abs_sum_cube_le`); the points of the other cubes lie
within `√d 2^{-j} N` of `ℤ^d ∖ I`, hence in the boundary layer of width `γ n = 2 β n` once
`√d 2^{-j} M ≤ β`.

* `abs_sum_le_cubes_gen`: the cube decomposition for a finite `S ⊆ B_N` and an interior `I ⊆ S`
  (the generalization of `abs_sum_le_cubes`, which is the case `S = B_n`, `I = B_{(1-δ)n}`);
* `greenDomainHomogenize_of_steps : GreenDomainBoundaryLayerStmt → GreenDomainGradientSumStmt →
  GreenDomainHomogenizeStmt`.
-/

noncomputable section

open LatticeProb Filter Topology

namespace RandomSandpile

open OdometerLowerBound DivisibleHomogenize

namespace DivisibleHomogenizeDomain

variable {d : ℕ}

/-- **All cubes, general domain**: for a finite `S ⊆ B_N` and `I ⊆ S`, the sum `∑_S g f` is
bounded by the pooled term, the rearrangement error over the cubes contained in `I`, and the
mass of `g` on the points within `√d 2^{-j} N` of a point outside `I`. -/
theorem abs_sum_le_cubes_gen (hP : BoxPoincare d) {j N : ℕ} {θ K : ℝ}
    (g f : Site d → ℝ) (hg : ∀ y, 0 ≤ g y) (hf : ∀ y, |f y| ≤ K)
    (hN : 2 * 2 ^ j ≤ (N : ℝ)) (hθ0 : 0 ≤ θ)
    (hθ : ∀ k ∈ cubeIndexSet d j, |∑ y ∈ dyadicCube j k N, f y| ≤ θ * (N : ℝ) ^ d)
    (S I : Finset (Site d)) (hS : ∀ y ∈ S, ‖toE y‖ < N) (hIS : I ⊆ S) :
    |∑ y ∈ S, g y * f y| ≤
      θ * (2 * 2 ^ j) ^ d * ∑ y ∈ S, g y +
        K * (2 ^ d * d * (2 * N / 2 ^ j)) * ∑ y ∈ I, ∑ i : Fin d, |g (y + unit i) - g y| +
          K * ∑ y ∈ S, g y * ({y | ∃ y', y' ∉ I ∧
            ‖toE y' - toE y‖ ≤ Real.sqrt d * ((N : ℝ) / 2 ^ j)}.indicator (fun _ => 1) y) := by
  classical
  set T : Set (Site d) := {y | ∃ y', y' ∉ I ∧
    ‖toE y' - toE y‖ ≤ Real.sqrt d * ((N : ℝ) / 2 ^ j)} with hT
  have hnR : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hn0 : 0 < N := by exact_mod_cast hnR
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf 0)
  set κ : Site d → Site d := cubeIndex j N with hκ
  set Gd : Site d → Prop := fun k => dyadicCube j k N ⊆ I with hGd
  have hyκ : ∀ y, y ∈ dyadicCube j (κ y) N := fun y => (mem_dyadicCube_iff_cubeIndex hn0).2 rfl
  have hfib : ∀ F : Site d → ℝ, ∑ y ∈ S.filter (fun y => Gd (κ y)), F y =
      ∑ k ∈ (cubeIndexSet d j).filter Gd, ∑ y ∈ dyadicCube j k N, F y := by
    intro F
    rw [← Finset.sum_fiberwise_of_maps_to (s := S.filter (fun y => Gd (κ y)))
      (t := (cubeIndexSet d j).filter Gd) (g := κ) ?_ F]
    · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr ?_ fun _ _ => rfl
      have hGk : Gd k := (Finset.mem_filter.1 hk).2
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, hyk⟩
        exact (mem_dyadicCube_iff_cubeIndex hn0).2 hyk
      · intro hy
        have hyk : κ y = k := (mem_dyadicCube_iff_cubeIndex hn0).1 hy
        refine ⟨⟨hIS (hGk hy), ?_⟩, hyk⟩
        rw [hyk]
        exact hGk
    · intro y hy
      obtain ⟨hyS, hG⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨cubeIndex_mem hn0 (hS y hyS), hG⟩
  have hsubI : S.filter (fun y => Gd (κ y)) ⊆ I := fun y hy => (Finset.mem_filter.1 hy).2 (hyκ y)
  have hbad : ∀ y ∈ S.filter (fun y => ¬ Gd (κ y)), y ∈ T := by
    intro y hy
    obtain ⟨-, hG⟩ := Finset.mem_filter.1 hy
    obtain ⟨y', hy'Q, hy'I⟩ := Finset.not_subset.1 hG
    exact ⟨y', hy'I, norm_sub_le_of_mem_dyadicCube (hyκ y) hy'Q⟩
  have hc : 0 ≤ θ * (2 * 2 ^ j) ^ d := by positivity
  have hc' : 0 ≤ K * (2 ^ d * d * (2 * N / 2 ^ j)) := by positivity
  have hA : |∑ y ∈ S.filter (fun y => Gd (κ y)), g y * f y| ≤
      θ * (2 * 2 ^ j) ^ d * ∑ y ∈ S, g y +
        K * (2 ^ d * d * (2 * N / 2 ^ j)) * ∑ y ∈ I, ∑ i : Fin d, |g (y + unit i) - g y| := by
    rw [hfib]
    calc _ ≤ ∑ k ∈ (cubeIndexSet d j).filter Gd, |∑ y ∈ dyadicCube j k N, g y * f y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ (cubeIndexSet d j).filter Gd,
            (θ * (2 * 2 ^ j) ^ d * ∑ y ∈ dyadicCube j k N, g y +
              K * (2 ^ d * d * (2 * N / 2 ^ j)) *
                ∑ q ∈ dyadicCube j k N, ∑ i : Fin d, |g (q + unit i) - g q|) :=
          Finset.sum_le_sum fun k hk =>
            abs_sum_cube_le hP hN hθ0 g f hg hf k (hθ k (Finset.mem_filter.1 hk).1)
      _ = θ * (2 * 2 ^ j) ^ d * ∑ y ∈ S.filter (fun y => Gd (κ y)), g y +
            K * (2 ^ d * d * (2 * N / 2 ^ j)) *
              ∑ y ∈ S.filter (fun y => Gd (κ y)), ∑ i : Fin d, |g (y + unit i) - g y| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hfib, hfib]
      _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun y _ _ => hg y) hc)
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsubI
            fun y _ _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hc')
  have hB : |∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), g y * f y| ≤
      K * ∑ y ∈ S, g y * T.indicator (fun _ => 1) y := by
    have h1 : ∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), g y =
        ∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), g y * T.indicator (fun _ => 1) y :=
      Finset.sum_congr rfl fun y hy => by rw [Set.indicator_of_mem (hbad y hy), mul_one]
    have h2 : ∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), g y * T.indicator (fun _ => 1) y ≤
        ∑ y ∈ S, g y * T.indicator (fun _ => 1) y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun y _ _ =>
        mul_nonneg (hg y) (Set.indicator_nonneg (fun _ _ => zero_le_one) y)
    calc _ ≤ ∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), |g y * f y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), K * g y := Finset.sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_nonneg (hg y), mul_comm]
          exact mul_le_mul_of_nonneg_right (hf y) (hg y)
      _ = K * ∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), g y := by rw [Finset.mul_sum]
      _ ≤ _ := by rw [h1]; exact mul_le_mul_of_nonneg_left h2 hK
  rw [← Finset.sum_filter_add_sum_filter_not S (fun y => Gd (κ y))]
  calc _ ≤ |∑ y ∈ S.filter (fun y => Gd (κ y)), g y * f y| +
        |∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), g y * f y| := abs_add_le _ _
    _ ≤ _ := by linarith [hA, hB]

/-- The interior region `(nearCompl A t)ᶜ` lies in `A` for `t ≥ 0`. -/
theorem compl_nearCompl_subset {A : Set (Site d)} {t : ℝ} (ht : 0 ≤ t) :
    (nearCompl A t)ᶜ ⊆ A := by
  intro y hy
  by_contra hyA
  exact hy ⟨y, hyA, by rw [sub_self, toE_zero, norm_zero]; exact ht⟩

/-- Points within `s` of a point outside the interior `A ∩ (nearCompl A t)ᶜ` are within
`t + s` of a point outside `A`. -/
theorem mem_nearCompl_of_near {A : Set (Site d)} {t s : ℝ} (ht : 0 ≤ t) {y y' : Site d}
    (hy' : y' ∉ A ∩ (nearCompl A t)ᶜ) (hyy : ‖toE y' - toE y‖ ≤ s) : y ∈ nearCompl A (t + s) := by
  by_cases hA : y' ∈ A
  · have hn : y' ∈ nearCompl A t := by
      by_contra h
      exact hy' ⟨hA, h⟩
    obtain ⟨z, hz, hzy⟩ := hn
    refine ⟨z, hz, ?_⟩
    have : toE (z - y) = toE (z - y') + (toE y' - toE y) := by rw [toE_sub, toE_sub]; abel
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add hzy hyy)
  · refine ⟨y', hA, ?_⟩
    rw [toE_sub]
    linarith

theorem arith_exit_dom {R n D : ℝ} (hR : 0 ≤ R) (hn : 1 ≤ n) (hD : 1 ≤ D) :
    (R * n + 1) ^ 2 / (2 * D) ≤ (R + 1) ^ 2 * n ^ 2 := by
  have h1 : R * n + 1 ≤ (R + 1) * n := by nlinarith
  have h2 : (R * n + 1) ^ 2 ≤ ((R + 1) * n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (R * n + 1) ^ 2 / (2 * D) ≤ (R * n + 1) ^ 2 :=
    div_le_self (by positivity) (by linarith)
  nlinarith


/-- The points within `s₀ ≤ s` of a point outside the interior `I` lie within `t + s` of
`ℤ^d ∖ A`, if every point outside `I` lies within `t` of `ℤ^d ∖ A`. -/
theorem layer_subset {A : Set (Site d)} {I : Finset (Site d)} {t s₀ s : ℝ} (hs : s₀ ≤ s)
    (hI : ∀ y, y ∉ I → y ∈ nearCompl A t) :
    {y | ∃ y', y' ∉ I ∧ ‖toE y' - toE y‖ ≤ s₀} ⊆ nearCompl A (t + s) := by
  rintro y ⟨y', hy'I, hyy⟩
  obtain ⟨z, hz, hzy⟩ := hI y' hy'I
  refine ⟨z, hz, ?_⟩
  have : toE (z - y) = toE (z - y') + (toE y' - toE y) := by rw [toE_sub, toE_sub]; abel
  rw [this]
  exact (norm_add_le _ _).trans (add_le_add hzy (hyy.trans hs))

/-- **Core estimate on a finite set `A ⊆ B_N`**: the Green potential of `f` is bounded by the
pooled term (with the exit time `E_g`), the rearrangement error (with the interior gradient sum
`G_g` on `(nearCompl A t)ᶜ`) and the occupation `L_g` of the layer of width `t + s`. -/
theorem abs_greenPotential_le_core (hP : BoxPoincare d) {j N : ℕ} {θ K t s Eg Gg Lg : ℝ}
    {A : Set (Site d)} (hAfin : A.Finite) (x : Site d) (f : Site d → ℝ) (hf : ∀ y, |f y| ≤ K)
    (hN : 2 * 2 ^ j ≤ (N : ℝ)) (hθ0 : 0 ≤ θ)
    (hθ : ∀ k ∈ cubeIndexSet d j, |∑ y ∈ dyadicCube j k N, f y| ≤ θ * (N : ℝ) ^ d)
    (hS : ∀ y ∈ A, ‖toE y‖ < N) (ht : 0 ≤ t) (hs : Real.sqrt d * ((N : ℝ) / 2 ^ j) ≤ s)
    (hexit : greenPotential A (fun _ => 1) x ≤ Eg)
    (hgrad : ∑ᶠ y ∈ (nearCompl A t)ᶜ, ∑ i : Fin d,
      |greenKilled A x (y + unit i) - greenKilled A x y| ≤ Gg)
    (hlayer : greenPotential A ((nearCompl A (t + s)).indicator fun _ => 1) x ≤ Lg) :
    |greenPotential A f x| ≤
      θ * (2 * 2 ^ j) ^ d * Eg + K * (2 ^ d * d * (2 * N / 2 ^ j)) * Gg + K * Lg := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf 0)
  have hIfin : ((nearCompl A t)ᶜ).Finite := hAfin.subset (compl_nearCompl_subset ht)
  have hpot : ∀ F : Site d → ℝ,
      greenPotential A F x = ∑ y ∈ hAfin.toFinset, greenKilled A x y * F y :=
    fun F => by rw [greenPotential]; exact finsum_mem_eq_finite_toFinset_sum _ hAfin
  have hIS : hIfin.toFinset ⊆ hAfin.toFinset :=
    Set.Finite.toFinset_subset_toFinset.2 (compl_nearCompl_subset ht)
  have key := abs_sum_le_cubes_gen hP (greenKilled A x) f (fun y => greenKilled_nonneg _ _ _) hf
    hN hθ0 hθ hAfin.toFinset hIfin.toFinset
    (fun y hy => hS y ((Set.Finite.mem_toFinset _).1 hy)) hIS
  have h1 : ∑ y ∈ hAfin.toFinset, greenKilled A x y ≤ Eg := by
    have h := hexit
    rw [hpot] at h
    simpa using h
  have h2 : ∑ y ∈ hIfin.toFinset, ∑ i : Fin d,
      |greenKilled A x (y + unit i) - greenKilled A x y| ≤ Gg := by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hIfin]
    exact hgrad
  have hI : ∀ y, y ∉ hIfin.toFinset → y ∈ nearCompl A t := by
    intro y hy
    rw [Set.Finite.mem_toFinset, Set.mem_compl_iff, not_not] at hy
    exact hy
  have h3 : ∑ y ∈ hAfin.toFinset, greenKilled A x y *
      ({y | ∃ y', y' ∉ hIfin.toFinset ∧
        ‖toE y' - toE y‖ ≤ Real.sqrt d * ((N : ℝ) / 2 ^ j)}.indicator (fun _ => 1) y) ≤ Lg := by
    rw [← hpot]
    exact (greenPotential_mono hAfin (Set.indicator_le_indicator_of_subset
      (layer_subset hs hI) fun _ => zero_le_one) x).trans hlayer
  have hc : 0 ≤ θ * (2 * 2 ^ j) ^ d := by positivity
  have hc' : 0 ≤ K * (2 ^ d * d * (2 * N / 2 ^ j)) := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
    positivity
  rw [hpot]
  exact key.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 hc)
    (mul_le_mul_of_nonneg_left h2 hc')) (mul_le_mul_of_nonneg_left h3 hK))

theorem arith_T1 {θP E₀ X ε n2 : ℝ} (hθP : θP = ε / (4 * (E₀ + 1))) (hX : X ≤ E₀ * n2)
    (hE : 0 ≤ E₀) (hε : 0 ≤ ε) (hn2 : 0 ≤ n2) : θP * X ≤ ε / 4 * n2 := by
  rw [hθP]
  calc ε / (4 * (E₀ + 1)) * X ≤ ε / (4 * (E₀ + 1)) * (E₀ * n2) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ ≤ ε / 4 * n2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have : 0 ≤ ε * n2 := mul_nonneg hε hn2
        nlinarith

theorem arith_T2 {K Q D M C C' P ε n : ℝ} (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hP : 0 < P) (hn : 0 ≤ n) (hCC : C ≤ C') (h : 8 * K * Q * D * M * C' ≤ ε * P) :
    K * (Q * D * (2 * (M * n) / P)) * (C * n) ≤ ε / 4 * n ^ 2 := by
  have h0 : 0 ≤ K * (Q * D * (2 * (M * n) / P)) := by positivity
  have h1 : K * (Q * D * (2 * (M * n) / P)) * (C * n) ≤
      K * (Q * D * (2 * (M * n) / P)) * (C' * n) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCC hn) h0
  have e : K * (Q * D * (2 * (M * n) / P)) * (C' * n) =
      (8 * K * Q * D * M * C') / P * n ^ 2 / 4 := by
    field_simp
    ring
  have h2 : (8 * K * Q * D * M * C') / P ≤ ε := by rw [div_le_iff₀ hP]; exact h
  have h3 : (8 * K * Q * D * M * C') / P * n ^ 2 / 4 ≤ ε / 4 * n ^ 2 := by
    have : (8 * K * Q * D * M * C') / P * n ^ 2 ≤ ε * n ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  linarith

theorem arith_layer_dom {s M β P n : ℝ} (hP : 0 < P) (hn : 0 ≤ n) (h : s * M ≤ β * P) :
    s * (M * n / P) ≤ β * n := by
  rw [mul_div_assoc', div_le_iff₀ hP]
  have := mul_le_mul_of_nonneg_right h hn
  linarith

end DivisibleHomogenizeDomain

open DivisibleHomogenizeDomain

/-- **Deterministic homogenization on `W_n`** from the boundary layer and the interior gradient
sum (with (exit_time) on `W_n`, `greenDomainExitTime`, and the Poincaré inequality on boxes,
`boxPoincare`). Constants: `δ = ε / (4 (K + 1))`, `γ` from the boundary layer, `β = γ / 2`,
`2^j > max(√d M / β, 8 K 2^d d M |C_β| / ε)`, `θ = ε / (4 (2^{j+1})^d ((R + 1)² + 1))`,
`N = M n`. -/
theorem greenDomainHomogenize_of_steps (hLayer : GreenDomainBoundaryLayerStmt)
    (hGrad : GreenDomainGradientSumStmt) : GreenDomainHomogenizeStmt := by
  intro d hd W hW f K hf hcube ε hε
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf 0)
  obtain ⟨R, hR0, hRW⟩ := exists_closedBall_of_isBounded hW.1
  obtain ⟨M, hRM, hM1⟩ : ∃ M : ℕ, R < M ∧ 1 ≤ M :=
    ⟨⌈R⌉₊ + 1, by push_cast; linarith [Nat.le_ceil R], by omega⟩
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  obtain ⟨δ, hδ0, hKδ⟩ : ∃ δ : ℝ, 0 < δ ∧ K * δ ≤ ε / 4 := by
    refine ⟨ε / (4 * (K + 1)), by positivity, ?_⟩
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨γ, hγ, n₁, hn₁⟩ := hLayer d hd W hW δ hδ0
  obtain ⟨β, hβ0, hβγ⟩ : ∃ β : ℝ, 0 < β ∧ β + β = γ := ⟨γ / 2, by positivity, by ring⟩
  obtain ⟨C, n₂, hC⟩ := hGrad d hd W hW.1 β hβ0
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
      θ * (2 * 2 ^ j) ^ d = ε / (4 * ((R + 1) ^ 2 + 1)) :=
    ⟨ε / (4 * (2 * 2 ^ j) ^ d * ((R + 1) ^ 2 + 1)), by positivity, by field_simp⟩
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
  have hNpos : (0 : ℝ) < ((M * n : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hN2
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
  have hlay : greenPotential (discretize W n)
      ((nearCompl (discretize W n) (β * n + β * n)).indicator fun _ => 1) x ≤
        δ * (n : ℝ) ^ 2 := by
    have e : β * (n : ℝ) + β * n = γ * n := by rw [← hβγ]; ring
    rw [e]; exact hn₁ n hn₁' x
  have hcore := abs_greenPotential_le_core (boxPoincare d)
    (DivisibleHomogenizeDomain.discretize_finite hW.1 n) x f hf hN2 hθ0.le hθ hS hβn hs
    (greenDomainExitTime d hd1 W R hR0 hRW n x) (hC n hn₂ x) hlay
  have hT1 := arith_T1 hθe (arith_exit_dom hR0 hnR1 hdR) (by positivity) hε.le
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

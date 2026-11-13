import RandomSandpile.Steps.Sec7.DivisibleHomogenize
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTent

/-!
# Uniform box sums from dyadic cube averages

Deterministic step for the Hessian trace bound of Lemma 7.6(3)
(`FreeOdometerLimitHessianTraceStmt`). If a bounded `f : ℤ^d → ℝ` has normalised sums over every
dyadic cube `Q_{j,k}(N)` (`dyadicCube`) tending to `0` (the conclusion of `CubeErgodicStmt` for
`f = η - E η(0)`), then the sums of `f` over *all* integer boxes inside `[-K N, K N]^d` are
uniformly `o(N^d)` (`uniform_box_sum`). Proof: tile the box by the dyadic cubes of side
`≈ N 2^{-j}`; the cubes inside the box are finitely many (independent of `N`), and the cubes that
meet the boundary lie in slabs of width `⌈N 2^{-j}⌉` along the faces, of total size
`≤ 2d ⌈N 2^{-j}⌉ (3KN)^{d-1}`.
-/

noncomputable section

open LatticeProb Filter Topology

namespace RandomSandpile

namespace PegdenSmartRegularity

variable {d : ℕ}

/-- The integer box `∏ᵢ [lᵢ, uᵢ)`. -/
def intBox (l u : Site d) : Finset (Site d) := Fintype.piFinset fun i => Finset.Ico (l i) (u i)

/-- The index of the dyadic interval `[⌈N m 2^{-j}⌉, ⌈N (m+1) 2^{-j}⌉)` containing `t`. -/
def tileIdx (j N : ℕ) (t : ℤ) : ℤ := ⌊(t : ℝ) * 2 ^ j / N⌋

theorem tile_iff {j N : ℕ} (hN : 0 < N) (t m : ℤ) :
    (⌈(N : ℝ) * ((m : ℝ) / 2 ^ j)⌉ ≤ t ∧ t < ⌈(N : ℝ) * (((m : ℝ) + 1) / 2 ^ j)⌉) ↔
      tileIdx j N t = m := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [Int.ceil_le, Int.lt_ceil, tileIdx, Int.floor_eq_iff]
  have e1 : (N : ℝ) * ((m : ℝ) / 2 ^ j) ≤ t ↔ (m : ℝ) ≤ t * 2 ^ j / N := by
    rw [le_div_iff₀ hN', ← mul_div_assoc, div_le_iff₀ h2]
    constructor <;> intro h <;> linarith
  have e2 : (t : ℝ) < N * (((m : ℝ) + 1) / 2 ^ j) ↔ (t : ℝ) * 2 ^ j / N < m + 1 := by
    rw [div_lt_iff₀ hN', ← mul_div_assoc, lt_div_iff₀ h2]
    constructor <;> intro h <;> linarith
  rw [e1, e2]

theorem mem_dyadicCube_iff {j N : ℕ} (hN : 0 < N) (m z : Site d) :
    z ∈ dyadicCube j m N ↔ ∀ i, tileIdx j N (z i) = m i := by
  simp only [dyadicCube, rectBox, Fintype.mem_piFinset, Finset.mem_Ico]
  exact forall_congr' fun i => tile_iff hN (z i) (m i)

/-- Two points of the same dyadic interval are at distance `< ⌈N 2^{-j}⌉`. -/
theorem tile_close {j N : ℕ} (hN : 0 < N) {t t' : ℤ} (h : tileIdx j N t = tileIdx j N t') :
    t' < t + ⌈(N : ℝ) / 2 ^ j⌉ := by
  set m := tileIdx j N t
  obtain ⟨h1, -⟩ := (tile_iff hN t m).2 rfl
  obtain ⟨-, h2⟩ := (tile_iff hN t' m).2 h.symm
  have h3 : ⌈(N : ℝ) * (((m : ℝ) + 1) / 2 ^ j)⌉ ≤ ⌈(N : ℝ) * ((m : ℝ) / 2 ^ j)⌉ +
      ⌈(N : ℝ) / 2 ^ j⌉ := by
    rw [show (N : ℝ) * (((m : ℝ) + 1) / 2 ^ j) = (N : ℝ) * ((m : ℝ) / 2 ^ j) + (N : ℝ) / 2 ^ j by
      ring]
    exact Int.ceil_add_le _ _
  omega

theorem card_intBox_filter_coord (l u : Site d) (i : Fin d) (P : ℤ → Prop) [DecidablePred P] :
    ((intBox l u).filter fun z => P (z i)).card =
      ((Finset.Ico (l i) (u i)).filter P).card *
        ∏ j ∈ Finset.univ.erase i, (Finset.Ico (l j) (u j)).card := by
  classical
  have hset : (intBox l u).filter (fun z => P (z i)) = Fintype.piFinset
      (Function.update (fun j => Finset.Ico (l j) (u j)) i ((Finset.Ico (l i) (u i)).filter P)) := by
    ext z
    simp only [intBox, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hz, hP⟩ j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self, Finset.mem_filter]; exact ⟨hz j, hP⟩
      · rw [Function.update_of_ne hj]; exact hz j
    · intro hz
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; have := hz j; simp only [Function.update_self, Finset.mem_filter] at this
          exact this.1
        · have := hz j; rwa [Function.update_of_ne hj] at this
      · have := hz i; simp only [Function.update_self, Finset.mem_filter] at this; exact this.2
  rw [hset, Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem card_Ico_filter_ends_le (l u s : ℤ) :
    ((Finset.Ico l u).filter fun t => t < l + s ∨ u < t + s).card ≤ 2 * s.toNat := by
  have hsub : (Finset.Ico l u).filter (fun t => t < l + s ∨ u < t + s) ⊆
      Finset.Ico l (l + s) ∪ Finset.Ioo (u - s) u := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioo]
    omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Int.card_Ico, Int.card_Ioo]
  omega

/-- **Uniform box sums.** -/
theorem uniform_box_sum (f : Site d → ℝ) (M : ℝ) (hf : ∀ z, |f z| ≤ M)
    (hcube : ∀ (j : ℕ) (k : Site d),
      Tendsto (fun N : ℕ => (∑ y ∈ dyadicCube j k N, f y) / (N : ℝ) ^ d) atTop (𝓝 0))
    (hd : 1 ≤ d) {ε K : ℝ} (hε : 0 < ε) (hK : 1 ≤ K) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ l u : Site d, (∀ i, -(K * N) ≤ (l i : ℝ) ∧ (u i : ℝ) ≤ K * N) →
      |∑ z ∈ intBox l u, f z| ≤ ε * (N : ℝ) ^ d := by
  classical
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0)
  -- the dyadic scale
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (8 * d * (M + 1) * (3 * K) ^ (d - 1) / ε)
    (by norm_num : (1 : ℝ) < 2)
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  -- the finitely many relevant cubes
  set A : ℤ := ⌈K * 2 ^ j⌉ with hA
  set Mset : Finset (Site d) := Fintype.piFinset fun _ => Finset.Icc (-A - 1) A with hMset
  set ε' : ℝ := ε / (2 * ((Mset.card : ℝ) + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  have hev : ∀ᶠ N : ℕ in atTop, ∀ m ∈ Mset,
      |∑ y ∈ dyadicCube j m N, f y| / (N : ℝ) ^ d < ε' := by
    rw [eventually_all_finset]
    intro m _
    have := (hcube j m).eventually (Metric.ball_mem_nhds 0 hε'pos)
    filter_upwards [this] with N hN
    simpa [Real.dist_eq, abs_div] using hN
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge ((2 : ℝ) ^ j)
  refine ⟨max (max N₁ N₂) 1, fun N hN l u hlu => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := hN1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN2 : N₂ ≤ N := le_trans (le_max_right N₁ N₂) (le_trans (le_max_left _ 1) hN)
  have hNj : (2 : ℝ) ^ j ≤ N := hN₂.trans (by exact_mod_cast hN2)
  have hcubeN := hN₁ N (le_trans (le_max_left N₁ N₂) (le_trans (le_max_left _ 1) hN))
  set idxV : Site d → Site d := fun z i => tileIdx j N (z i) with hidxV
  -- every point of the box has its tile index in `Mset`
  have hmaps : ∀ z ∈ intBox l u, idxV z ∈ Mset := by
    intro z hz
    simp only [intBox, Fintype.mem_piFinset, Finset.mem_Ico] at hz
    simp only [hMset, Fintype.mem_piFinset, Finset.mem_Icc, hidxV, tileIdx]
    intro i
    have hzl : -(K * N) ≤ (z i : ℝ) := (hlu i).1.trans (by exact_mod_cast (hz i).1)
    have hzu : (z i : ℝ) ≤ K * N := le_trans (by exact_mod_cast (hz i).2.le) (hlu i).2
    have hA1 : K * 2 ^ j ≤ (A : ℝ) := Int.le_ceil _
    have hlo : -(K * 2 ^ j) ≤ (z i : ℝ) * 2 ^ j / N := by
      rw [le_div_iff₀ hN']; nlinarith
    have hhi : (z i : ℝ) * 2 ^ j / N ≤ K * 2 ^ j := by
      rw [div_le_iff₀ hN']; nlinarith
    have e1 : -A ≤ ⌊(z i : ℝ) * 2 ^ j / N⌋ := Int.le_floor.2 (by push_cast; linarith)
    have e2 : ⌊(z i : ℝ) * 2 ^ j / N⌋ ≤ A := Int.floor_le_iff.2 (by linarith)
    constructor <;> omega
  -- full and boundary tiles
  set bad : Finset (Site d) := (intBox l u).filter fun z => ¬ dyadicCube j (idxV z) N ⊆ intBox l u
    with hbad
  set s : ℤ := ⌈(N : ℝ) / 2 ^ j⌉ with hs
  have hbad_sub : bad ⊆ Finset.univ.biUnion fun i =>
      (intBox l u).filter fun z => z i < l i + s ∨ u i < z i + s := by
    intro z hz
    simp only [hbad, Finset.mem_filter] at hz
    obtain ⟨hzB, hz⟩ := hz
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    by_contra hcon
    push Not at hcon
    apply hz
    intro y hy
    rw [mem_dyadicCube_iff hNpos] at hy
    simp only [intBox, Fintype.mem_piFinset, Finset.mem_Ico]
    intro i
    obtain ⟨h1, h2⟩ := hcon i hzB
    have c1 := tile_close (j := j) hNpos (hy i).symm
    have c2 := tile_close (j := j) hNpos (hy i)
    constructor <;> omega
  have hs_le : (s : ℝ) ≤ 2 * N / 2 ^ j := by
    have := Int.ceil_lt_add_one ((N : ℝ) / 2 ^ j)
    have h1 : (1 : ℝ) ≤ N / 2 ^ j := by rw [le_div_iff₀ h2j]; linarith
    rw [← hs] at this
    have : (N : ℝ) / 2 ^ j + 1 ≤ 2 * N / 2 ^ j := by rw [mul_div_assoc]; linarith
    linarith
  have hs0 : 0 ≤ s := Int.ceil_nonneg (by positivity)
  have hside : ∀ i, ((Finset.Ico (l i) (u i)).card : ℝ) ≤ 3 * K * N := by
    intro i
    rw [Int.card_Ico]
    have h1 := (hlu i).1; have h2 := (hlu i).2
    by_cases h : l i ≤ u i
    · rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast
      have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have : (1 : ℝ) ≤ K * N := one_le_mul_of_one_le_of_one_le hK hN1'
      linarith
    · rw [Int.toNat_of_nonpos (by omega)]; push_cast; positivity
  have hbad_card : (bad.card : ℝ) ≤ 4 * d * (3 * K) ^ (d - 1) / 2 ^ j * (N : ℝ) ^ d := by
    have h1 : (bad.card : ℝ) ≤ ∑ i : Fin d,
        (((intBox l u).filter fun z => z i < l i + s ∨ u i < z i + s).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hbad_sub).trans Finset.card_biUnion_le
    refine h1.trans ?_
    have h2 : ∀ i : Fin d, (((intBox l u).filter fun z => z i < l i + s ∨ u i < z i + s).card : ℝ)
        ≤ 2 * s * (3 * K * N) ^ (d - 1) := by
      intro i
      rw [card_intBox_filter_coord l u i (fun t => t < l i + s ∨ u i < t + s)]
      push_cast
      have e1 : (((Finset.Ico (l i) (u i)).filter fun t => t < l i + s ∨ u i < t + s).card : ℝ)
          ≤ 2 * s := by
        have := card_Ico_filter_ends_le (l i) (u i) s
        have h' : ((2 * s.toNat : ℕ) : ℝ) = 2 * s := by
          push_cast; rw [← Int.cast_natCast, Int.toNat_of_nonneg hs0]
        rw [← h']; exact_mod_cast this
      have e2 : ∏ j ∈ Finset.univ.erase i, ((Finset.Ico (l j) (u j)).card : ℝ) ≤
          (3 * K * N) ^ (d - 1) := by
        calc ∏ j ∈ Finset.univ.erase i, ((Finset.Ico (l j) (u j)).card : ℝ)
            ≤ ∏ _j ∈ Finset.univ.erase i, 3 * K * (N : ℝ) :=
              Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => hside j
          _ = (3 * K * N) ^ (d - 1) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
                Finset.card_univ, Fintype.card_fin]
      have hs0' : (0 : ℝ) ≤ 2 * (s : ℝ) := by
        have : (0 : ℝ) ≤ s := by exact_mod_cast hs0
        linarith
      exact mul_le_mul e1 e2 (Finset.prod_nonneg fun j _ => Nat.cast_nonneg _) hs0'
    have hpow : (3 * K * (N : ℝ)) ^ (d - 1) * N = (3 * K) ^ (d - 1) * (N : ℝ) ^ d := by
      rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hd]
    have hsum2 : ∑ i : Fin d, 2 * (s : ℝ) * (3 * K * N) ^ (d - 1) =
        d * (2 * (s : ℝ) * (3 * K * N) ^ (d - 1)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hc : 0 ≤ (d : ℝ) * (3 * K * N) ^ (d - 1) := by positivity
    calc ∑ i : Fin d, (((intBox l u).filter fun z => z i < l i + s ∨ u i < z i + s).card : ℝ)
        ≤ ∑ i : Fin d, 2 * (s : ℝ) * (3 * K * N) ^ (d - 1) := Finset.sum_le_sum fun i _ => h2 i
      _ = d * (2 * (s : ℝ) * (3 * K * N) ^ (d - 1)) := hsum2
      _ ≤ d * (2 * (2 * N / 2 ^ j) * (3 * K * N) ^ (d - 1)) := by nlinarith
      _ = 4 * d * ((3 * K * (N : ℝ)) ^ (d - 1) * N) / 2 ^ j := by ring
      _ = 4 * d * (3 * K) ^ (d - 1) / 2 ^ j * (N : ℝ) ^ d := by rw [hpow]; ring
  -- the decomposition
  have hdecomp : ∑ z ∈ intBox l u, f z =
      ∑ m ∈ Mset, ∑ z ∈ (intBox l u).filter (fun z => idxV z = m), f z :=
    (Finset.sum_fiberwise_of_maps_to hmaps f).symm
  have hterm : ∀ m ∈ Mset, |∑ z ∈ (intBox l u).filter (fun z => idxV z = m), f z| ≤
      ε' * (N : ℝ) ^ d + M * ((intBox l u).filter (fun z => idxV z = m) ∩ bad).card := by
    intro m hm
    by_cases hfull : dyadicCube j m N ⊆ intBox l u
    · have hfib : (intBox l u).filter (fun z => idxV z = m) = dyadicCube j m N := by
        ext z
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨-, hz⟩; rw [mem_dyadicCube_iff hNpos]; intro i; rw [← hz]
        · intro hz
          refine ⟨hfull hz, ?_⟩
          funext i; exact (mem_dyadicCube_iff hNpos m z).1 hz i
      rw [hfib]
      have h1 := hcubeN m hm
      rw [div_lt_iff₀ (by positivity)] at h1
      have : (0 : ℝ) ≤ M * (dyadicCube j m N ∩ bad).card := by positivity
      linarith
    · have hfib : (intBox l u).filter (fun z => idxV z = m) ∩ bad =
          (intBox l u).filter (fun z => idxV z = m) := by
        refine Finset.inter_eq_left.2 fun z hz => ?_
        simp only [Finset.mem_filter] at hz
        simp only [hbad, Finset.mem_filter]
        exact ⟨hz.1, by rw [hz.2]; exact hfull⟩
      rw [hfib]
      have hsum : ∑ z ∈ (intBox l u).filter (fun z => idxV z = m), |f z| ≤
          M * ((intBox l u).filter (fun z => idxV z = m)).card := by
        refine (Finset.sum_le_sum fun z _ => hf z).trans (le_of_eq ?_)
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      have : 0 ≤ ε' * (N : ℝ) ^ d := by positivity
      linarith [Finset.abs_sum_le_sum_abs f ((intBox l u).filter (fun z => idxV z = m))]
  have hbadsum : ∑ m ∈ Mset, (((intBox l u).filter (fun z => idxV z = m) ∩ bad).card : ℝ) =
      bad.card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := idxV) (s := bad) (t := Mset)
      (fun z hz => hmaps z (Finset.mem_filter.1 hz).1)
    rw [h]; push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 2
    ext z; simp only [Finset.mem_inter, Finset.mem_filter, hbad]; tauto
  rw [hdecomp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hbadsum]
  have hj' : 8 * d * (M + 1) * (3 * K) ^ (d - 1) / ε < 2 ^ j := hj
  rw [div_lt_iff₀ hε] at hj'
  have e1 : (Mset.card : ℝ) * (ε' * (N : ℝ) ^ d) ≤ ε / 2 * (N : ℝ) ^ d := by
    rw [hε', ← mul_assoc, mul_div_assoc']
    have : (Mset.card : ℝ) * ε / (2 * ((Mset.card : ℝ) + 1)) ≤ ε / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have e2 : M * (bad.card : ℝ) ≤ ε / 2 * (N : ℝ) ^ d := by
    refine (mul_le_mul_of_nonneg_left hbad_card hM).trans ?_
    have hc : 0 ≤ 4 * (d : ℝ) * (3 * K) ^ (d - 1) := by positivity
    have : M * (4 * d * (3 * K) ^ (d - 1) / 2 ^ j) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_iff₀ h2j]; nlinarith
    nlinarith [pow_pos hN' d]
  linarith

end PegdenSmartRegularity

end RandomSandpile

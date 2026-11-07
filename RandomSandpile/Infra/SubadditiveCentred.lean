import RandomSandpile.Infra.SubadditiveCubes
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodicAllFlip

/-! # The subadditive ergodic theorem along centred cubes

This file proves `SubadditiveCentredCubesStmt`: for a subadditive process `f`
(`IsSubadditiveProcess`) over a stationary ergodic random environment, almost surely
`f(η, [-n, n)^d) / (2n)^d` converges, and the limit is the constant `a` of the cube limit
`f(η, [0, n)^d) / n^d → a` (`exists_ae_tendsto_cube_const`).

The cubes `[-n, n)^d` do not have a corner at the origin, so `LatticeProb.akcoglu_krengel` does not
apply to them directly. We do not redo the Akcoglu–Krengel maximal inequality; instead:

* **Upper bound** (`ae_eventually_le_centredCube`). Tiling `[-n, n)^d` by translates of
  `[0, k)^d` (`subadditive_tiling_le`) bounds `f(η, [-n, n)^d)` by an ergodic average of
  `η ↦ f(η, [0, k)^d)` over `[-n, n)^d`, plus a boundary term. The centred cube is the disjoint
  union of `2^d` reflected copies of `[0, n)^d` (`sum_centredCube_eq`), and the reflected shift
  actions are measure preserving and ergodic (`LatticeProb.reflectActionS_props`), so the
  rectangle ergodic theorem along `[0, n)^d` gives the ergodic theorem along the centred cubes
  (`ae_tendsto_sum_centredCube`).
* **Lower bound** (`ae_eventually_ge_centredCube`). If `f(η, c + [-n, n)^d) < (a - ε)(2n)^d`
  for some radius `n ∈ [r₀, K]` at a positive density of centres `c` of a large cube `[0, N)^d`,
  a Vitali selection (`exists_disjoint_centredCubeAt`) of pairwise disjoint such cubes covers a
  positive fraction of `[0, N)^d`; tiling the rest by cubes of side `k ≪ r₀` and using
  subadditivity contradicts `E f(η, [0, N)^d) / N^d → a`. Taking expectations (stationarity
  only, no maximal inequality) bounds the probability of a bad radius in `[r₀, K]` uniformly in
  `K`, which gives the almost sure lower bound.
-/

noncomputable section

open MeasureTheory Filter Topology LatticeProb
open scoped Pointwise

namespace RandomSandpile

/-! ### Centred cubes and their reflected decomposition -/

section CentredCubes

variable {d : ℕ}

/-- The centred cube `[-n, n)^d ∩ ℤ^d`. -/
def centredCube (n : ℕ) : Finset (Site d) :=
  ibox (fun _ => -(n : ℤ)) (fun _ => (n : ℤ))

/-- The cube `c + [-r, r)^d ∩ ℤ^d` centred at `c`. -/
def centredCubeAt (c : Site d) (r : ℕ) : Finset (Site d) :=
  ibox (fun i => c i - r) (fun i => c i + r)

/-- The indicator vector of a coordinate subset `S`. -/
def flipShift (S : Finset (Fin d)) : Site d := fun i => if i ∈ S then 1 else 0

/-- `[-n, n)^d` is the disjoint union over `S ⊆ {1, …, d}` of the reflected cubes
`flipSubset S ([0, n)^d) - 1_S` (coordinates in `S` run over `[-n, -1]`). -/
theorem sum_centredCube_eq {M : Type*} [AddCommMonoid M] (g : Site d → M) (n : ℕ) :
    ∑ x ∈ centredCube n, g x =
      ∑ S : Finset (Fin d), ∑ y ∈ ibox (fun _ => 0) (fun _ => (n : ℤ)),
        g (flipSubset S y - flipShift S) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun x => (Finset.univ.filter fun i => x i < 0, fun i => if x i < 0 then -x i - 1 else x i))
    (fun p => flipSubset p.1 p.2 - flipShift p.1) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [centredCube, mem_ibox] at hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_ibox]
    intro i
    have := hx i
    split_ifs <;> omega
  · rintro ⟨S, y⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_ibox] at hp
    rw [centredCube, mem_ibox]
    intro i
    have := hp i
    simp only [Pi.sub_apply, flipSubset, flipShift]
    split_ifs <;> omega
  · intro x _
    funext i
    simp only [Pi.sub_apply, flipSubset, flipShift, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> omega
  · rintro ⟨S, y⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_ibox] at hp
    have hS : ∀ i, (flipSubset S y - flipShift S) i < 0 ↔ i ∈ S := by
      intro i
      have := hp i
      by_cases h : i ∈ S <;> simp [flipSubset, flipShift, h] <;> omega
    refine Prod.ext ?_ ?_
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hS i
    · funext i
      have := hp i
      by_cases h : i ∈ S <;> simp [flipSubset, flipShift, h] <;> omega
  · intro x _
    congr 1
    funext i
    simp only [Pi.sub_apply, flipSubset, flipShift, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> omega

theorem card_centredCube (n : ℕ) : ((centredCube (d := d) n).card : ℝ) = ((2 * n : ℕ) : ℝ) ^ d := by
  rw [centredCube, card_ibox]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  push_cast
  rw [max_eq_left (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)]
  ring

theorem rectBox_zero_one (N : ℕ) :
    rectBox (d := d) (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) N =
      ibox (fun _ => 0) (fun _ => (N : ℤ)) := by
  ext x
  simp [mem_rectBox, mem_ibox]

end CentredCubes

/-! ### The ergodic theorem along centred cubes -/

section Ergodic

variable {d : ℕ}

/-- **Ergodic theorem along the centred cubes.** For a bounded measurable `h`, almost surely
`(2n)^{-d} ∑_{x ∈ [-n, n)^d} h(T_x η) → E h`. Each of the `2^d` reflected pieces of
`[-n, n)^d` (`sum_centredCube_eq`) is an ergodic average along `[0, n)^d` for the reflected
action `y ↦ T_{flipSubset S y}`, evaluated at `T_{-1_S} η`. -/
theorem ae_tendsto_sum_centredCube (hd : 1 ≤ d) (E : RandomEnvironment d) (h : Config d → ℝ)
    (hm : Measurable h) (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) :
    ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ => (∑ x ∈ centredCube n, h (shift x η)) /
      ((2 * n : ℕ) : ℝ) ^ d) atTop (𝓝 (∫ η, h η ∂E.P)) := by
  haveI := E.isProb
  have hS : ∀ S : Finset (Fin d), ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ =>
      (∑ y ∈ ibox (fun _ => 0) (fun _ => (n : ℤ)), h (shift (flipSubset S y - flipShift S) η)) /
        (n : ℝ) ^ d) atTop (𝓝 (∫ η, h η ∂E.P)) := by
    intro S
    obtain ⟨h1, h2, h3⟩ :=
      reflectActionS_props E.stationary (fun z w η => shift_add z w η) E.ergodic S
    have hR := rectangleErgodic hd E.P (reflectActionS shift S) h1 h2 h3 h hm hb
      (fun _ => 0) (fun _ => 1) (fun _ => le_rfl) (fun _ => zero_le_one)
    have hT := (E.stationary (-flipShift S)).quasiMeasurePreserving.ae hR
    filter_upwards [hT] with η hη
    simp only [sub_zero, Finset.prod_const_one, one_mul] at hη
    refine hη.congr' (Eventually.of_forall fun N => ?_)
    rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_mul_eq_div, rectBox_zero_one]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [sub_eq_add_neg, shift_add]
    rfl
  rw [← ae_all_iff] at hS
  filter_upwards [hS] with η hη
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Finset (Fin d))) fun S _ => hη S
  have hc : ((Finset.univ : Finset (Finset (Fin d))).card : ℝ) = (2 : ℝ) ^ d := by
    simp [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  rw [Finset.sum_const, nsmul_eq_mul, hc] at hsum
  have h2 := hsum.div_const ((2 : ℝ) ^ d)
  rw [mul_div_cancel_left₀ _ (by positivity)] at h2
  refine h2.congr' (Eventually.of_forall fun n => ?_)
  dsimp only
  rw [sum_centredCube_eq, ← Finset.sum_div, div_div]
  congr 1
  push_cast
  ring

end Ergodic

/-! ### The upper bound -/

section Upper

variable {d : ℕ} {C : ℝ} {f : Config d → Set (Site d) → ℝ}

theorem f_cell_eq (hf : IsSubadditiveProcess C f) (η : Config d) (k : ℕ) (z : Site d) :
    f η ↑(cell (d := d) k z) = f (shift z η) ↑(latticeCube d k) := by
  rw [hf.stationary z _ (Finset.finite_toSet _), cell, coe_map_addRight]

/-- Tiling `[-n, n)^d` by translates of `[0, k)^d`: `k^d f(η, [-n, n)^d)` is at most the sum of
`f(T_z η, [0, k)^d)` over `z ∈ [-n, n)^d` plus `C k^d` times the number of sites within distance
`k` of the upper faces. -/
theorem centredCube_tiling_le (hf : IsSubadditiveProcess C f) (η : Config d) {k : ℕ} (hk : 1 ≤ k)
    (n : ℕ) :
    (k : ℝ) ^ d * f η ↑(centredCube (d := d) n) ≤ ∑ z ∈ centredCube n, f (shift z η) ↑(latticeCube d k) +
      C * (k : ℝ) ^ d * (((centredCube (d := d) n).card : ℝ) -
        (ibox (d := d) (fun _ => -(n : ℤ)) (fun _ => (n : ℤ) + (1 - (k : ℤ)))).card) := by
  have hC : 0 ≤ C := nonneg_of_mem_subadditiveClass (hf.mem η)
  have h := subadditive_tiling_le (hf.mem η) (centredCube n) hk
  have hsub : innerSites k (centredCube (d := d) n) ⊆ centredCube n := Finset.filter_subset _ _
  have hin := ibox_add_subset_innerSites (d := d) hk (fun _ => -(n : ℤ)) (fun _ => (n : ℤ))
  have hcard : ((ibox (d := d) (fun _ => -(n : ℤ)) (fun _ => (n : ℤ) + (1 - (k : ℤ)))).card : ℝ) ≤
      (innerSites k (centredCube (d := d) n)).card := by
    exact_mod_cast Finset.card_le_card hin
  have hsum : ∑ z ∈ innerSites k (centredCube n), f η ↑(cell (d := d) k z) ≤
      ∑ z ∈ centredCube n, f (shift z η) ↑(latticeCube d k) := by
    simp only [f_cell_eq hf]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ =>
      ((hf.mem _).2 _ (Finset.finite_toSet _)).1
  have hCk : 0 ≤ C * (k : ℝ) ^ d := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcard hCk]

theorem tendsto_card_centredBox_div (α β : ℤ) :
    Tendsto (fun n : ℕ => ((ibox (d := d) (fun _ => -(n : ℤ) + α) (fun _ => (n : ℤ) + β)).card : ℝ) /
      ((2 * n : ℕ) : ℝ) ^ d) atTop (𝓝 1) := by
  have h := tendsto_card_ibox_div_pow (d := d) (fun _ => -1) (fun _ => 1) (fun _ => by norm_num) α β
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have h2 := h.div_const ((1 + 1 : ℝ) ^ d)
  rw [div_self (by positivity)] at h2
  refine h2.congr' (Eventually.of_forall fun n => ?_)
  have hbox : ibox (d := d) (fun _ => ⌈(n : ℝ) * -1⌉ + α) (fun _ => ⌈(n : ℝ) * 1⌉ + β) =
      ibox (fun _ => -(n : ℤ) + α) (fun _ => (n : ℤ) + β) := by
    congr 1 <;> funext i
    · rw [mul_neg_one, Int.ceil_neg, Int.floor_natCast]
    · rw [mul_one, Int.ceil_natCast]
  rw [hbox, div_div]
  congr 1
  push_cast
  ring

/-- **Upper bound.** Almost surely `limsup f(η, [-n, n)^d) / (2n)^d ≤ a`. -/
theorem ae_eventually_le_centredCube (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) {a : ℝ}
    (hcube : ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ => f η ↑(latticeCube d n) / (n : ℝ) ^ d) atTop (𝓝 a)) :
    ∀ᵐ η ∂E.P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      f η ↑(centredCube (d := d) n) / ((2 * n : ℕ) : ℝ) ^ d ≤ a + ε := by
  have hk : ∀ k : ℕ, ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ =>
      (∑ z ∈ centredCube n, f (shift z η) ↑(latticeCube d k)) / ((2 * n : ℕ) : ℝ) ^ d) atTop
      (𝓝 (∫ η, f η ↑(latticeCube d k) ∂E.P)) := by
    intro k
    have hbk : ∀ η, 0 ≤ f η ↑(latticeCube d k) ∧
        f η ↑(latticeCube d k) ≤ C * ((latticeCube d k).card : ℝ) :=
      fun η => finsetProcess_bd hf (latticeCube d k) η
    exact ae_tendsto_sum_centredCube hd E (fun η => f η ↑(latticeCube d k))
      (finsetProcess_measurable hf _)
      ⟨C * ((latticeCube d k).card : ℝ), (hbk 0).1.trans (hbk 0).2, fun η => by
        rw [abs_of_nonneg (hbk η).1]; exact (hbk η).2⟩
  rw [← ae_all_iff] at hk
  filter_upwards [hk] with η hη ε hε
  have hint := tendsto_integral_cube_div_pow hd E hf hcube
  obtain ⟨k, hk1, hkle⟩ : ∃ k : ℕ, 1 ≤ k ∧
      (∫ η, f η ↑(latticeCube d k) ∂E.P) / (k : ℝ) ^ d < a + ε / 2 := by
    obtain ⟨k, hk⟩ := (eventually_atTop.1 ((hint.eventually (gt_mem_nhds (by linarith :
      a < a + ε / 2))).and (eventually_ge_atTop 1)))
    exact ⟨k, (hk k le_rfl).2, (hk k le_rfl).1⟩
  have hkpos : (0 : ℝ) < (k : ℝ) ^ d := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    positivity
  set B : ℕ → ℝ := fun n => ((ibox (d := d) (fun _ => -(n : ℤ) + 0)
    (fun _ => (n : ℤ) + (1 - (k : ℤ)))).card : ℝ) / ((2 * n : ℕ) : ℝ) ^ d with hB
  set A : ℕ → ℝ := fun n => ((ibox (d := d) (fun _ => -(n : ℤ) + 0)
    (fun _ => (n : ℤ) + 0)).card : ℝ) / ((2 * n : ℕ) : ℝ) ^ d with hA
  set S : ℕ → ℝ := fun n => ∑ z ∈ centredCube n, f (shift z η) ↑(latticeCube d k) with hS
  have hbd : Tendsto B atTop (𝓝 1) := tendsto_card_centredBox_div (d := d) 0 (1 - (k : ℤ))
  have hcc : Tendsto A atTop (𝓝 1) := tendsto_card_centredBox_div (d := d) 0 0
  have hR : Tendsto (fun n : ℕ => S n / ((2 * n : ℕ) : ℝ) ^ d / (k : ℝ) ^ d + C * (A n - B n))
      atTop (𝓝 ((∫ η, f η ↑(latticeCube d k) ∂E.P) / (k : ℝ) ^ d + C * (1 - 1))) :=
    ((hη k).div_const _).add (tendsto_const_nhds.mul (hcc.sub hbd))
  rw [sub_self, mul_zero, add_zero] at hR
  filter_upwards [hR.eventually (gt_mem_nhds (by linarith : _ < a + ε)), eventually_ge_atTop 1]
    with n hn hn1
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) ^ d := by
    have : (1 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * n)
    positivity
  have ht := centredCube_tiling_le hf η hk1 n
  have hcc' : ((centredCube (d := d) n).card : ℝ) = A n * ((2 * n : ℕ) : ℝ) ^ d := by
    rw [hA, div_mul_cancel₀ _ hNpos.ne']
    simp only [add_zero, centredCube]
  have hB' : ((ibox (d := d) (fun _ => -(n : ℤ)) (fun _ => (n : ℤ) + (1 - (k : ℤ)))).card : ℝ) =
      B n * ((2 * n : ℕ) : ℝ) ^ d := by
    rw [hB, div_mul_cancel₀ _ hNpos.ne']
    simp only [add_zero]
  rw [hcc', hB'] at ht
  refine le_of_lt (lt_of_le_of_lt ?_ hn)
  rw [div_le_iff₀ hNpos]
  refine le_of_mul_le_mul_left (ht.trans (le_of_eq ?_)) hkpos
  field_simp
  ring

end Upper


/-! ### A discrete Vitali covering lemma -/

section Vitali

variable {d : ℕ}

theorem mem_centredCubeAt {c x : Site d} {r : ℕ} :
    x ∈ centredCubeAt c r ↔ ∀ i, c i - r ≤ x i ∧ x i < c i + r := mem_ibox

theorem card_centredCubeAt (c : Site d) (r : ℕ) :
    ((centredCubeAt c r).card : ℝ) = ((2 * r : ℕ) : ℝ) ^ d := by
  rw [centredCubeAt, card_ibox]
  have e : ∀ i, max (((c i + r - (c i - r) : ℤ)) : ℝ) 0 = ((2 * r : ℕ) : ℝ) := fun i => by
    rw [max_eq_left] <;> push_cast <;> [ring; (have := (Nat.cast_nonneg r : (0 : ℝ) ≤ r); linarith)]
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Discrete Vitali covering lemma.** Given radii `r z ≥ 1` at the points of a finite set `Z`,
some subfamily `T ⊆ Z` has pairwise disjoint cubes `t + [-r t, r t)^d`, and the cubes
`t + [-2 r t, 2 r t)^d`, `t ∈ T`, cover `Z`, so `|Z| ≤ 2^d ∑_{t ∈ T} (2 r t)^d`. Greedy
selection by decreasing radius. -/
theorem exists_disjoint_centredCubeAt (r : Site d → ℕ) (Z : Finset (Site d))
    (hr : ∀ z ∈ Z, 1 ≤ r z) :
    ∃ T ⊆ Z, (∀ s ∈ T, ∀ t ∈ T, s ≠ t →
        Disjoint (centredCubeAt s (r s)) (centredCubeAt t (r t))) ∧
      (Z.card : ℝ) ≤ 2 ^ d * ∑ t ∈ T, ((2 * r t : ℕ) : ℝ) ^ d := by
  induction Z using Finset.strongInduction with
  | H Z ih =>
  rcases Z.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image Z r hne
  have htQ : t ∈ centredCubeAt t (r t) := by
    rw [mem_centredCubeAt]
    intro i
    have := hr t ht
    omega
  set Z' := Z.filter fun z => Disjoint (centredCubeAt z (r z)) (centredCubeAt t (r t)) with hZ'
  have htZ' : t ∉ Z' := fun h =>
    Finset.disjoint_left.1 (Finset.mem_filter.1 h).2 htQ htQ
  have hZ'Z : Z' ⊂ Z :=
    Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun h => htZ' (h ▸ ht)⟩
  obtain ⟨T', hT'Z, hT'd, hT'c⟩ := ih Z' hZ'Z fun z hz => hr z (Finset.filter_subset _ _ hz)
  have htT' : t ∉ T' := fun h => htZ' (hT'Z h)
  refine ⟨insert t T', Finset.insert_subset ht (hT'Z.trans (Finset.filter_subset _ _)), ?_, ?_⟩
  · intro s hs u hu hsu
    rw [Finset.mem_insert] at hs hu
    rcases hs with rfl | hs <;> rcases hu with rfl | hu
    · exact absurd rfl hsu
    · exact (Finset.mem_filter.1 (hT'Z hu)).2.symm
    · exact (Finset.mem_filter.1 (hT'Z hs)).2
    · exact hT'd s hs u hu hsu
  · have hsub : Z ⊆ Z' ∪ centredCubeAt t (2 * r t) := by
      intro z hz
      by_cases hzd : Disjoint (centredCubeAt z (r z)) (centredCubeAt t (r t))
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hz, hzd⟩)
      · apply Finset.mem_union_right
        obtain ⟨x, hx1, hx2⟩ := Finset.not_disjoint_iff.1 hzd
        rw [mem_centredCubeAt] at hx1 hx2 ⊢
        have hrz := hmax z hz
        intro i
        have := hx1 i
        have := hx2 i
        push_cast
        omega
    have h1 : (Z.card : ℝ) ≤ Z'.card + (centredCubeAt t (2 * r t)).card := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [card_centredCubeAt] at h1
    rw [Finset.sum_insert htT', mul_add]
    have e : ((2 * (2 * r t) : ℕ) : ℝ) ^ d = 2 ^ d * ((2 * r t : ℕ) : ℝ) ^ d := by
      rw [← mul_pow]; push_cast; ring
    linarith

end Vitali

/-! ### The covering inequality -/

section Covering

variable {d : ℕ}

theorem subadditive_le_sum_biUnion {C : ℝ} {g : Set (Site d) → ℝ}
    (hg : g ∈ subadditiveClass d C) (T : Finset (Site d)) (Q : Site d → Finset (Site d))
    (hT : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → Disjoint (Q s) (Q t)) :
    g ↑(T.biUnion Q) ≤ ∑ t ∈ T, g ↑(Q t) := by
  induction T using Finset.induction_on with
  | empty =>
    have := (hg.2 ↑(∅ : Finset (Site d)) (Finset.finite_toSet _)).2
    simpa using this
  | insert t T ht ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ht]
    have hdisj : Disjoint (Q t) (T.biUnion Q) := by
      rw [Finset.disjoint_biUnion_right]
      intro s hs
      exact hT t (Finset.mem_insert_self _ _) s (Finset.mem_insert_of_mem hs)
        fun h => ht (h ▸ hs)
    have h1 := subadditive_union hg.1 hdisj
    have h2 := ih fun s hs u hu => hT s (Finset.mem_insert_of_mem hs) u (Finset.mem_insert_of_mem hu)
    linarith

theorem card_collarBox_le {t : Site d} {r r0 k : ℕ} (hr0 : 1 ≤ r0) (hr : r0 ≤ r) (hk : 1 ≤ k) :
    ((ibox (fun i => t i - r + (1 - (k : ℤ))) (fun i => t i + r)).card : ℝ) ≤
      (1 + (k : ℝ) / (2 * r0)) ^ d * ((2 * r : ℕ) : ℝ) ^ d := by
  rw [card_ibox, ← mul_pow]
  have hr0' : (1 : ℝ) ≤ r0 := by exact_mod_cast hr0
  have hrr : (r0 : ℝ) ≤ r := by exact_mod_cast hr
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkr : (k : ℝ) ≤ (k : ℝ) / (2 * r0) * (2 * r) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc ∏ i, max (((t i + r - (t i - r + (1 - (k : ℤ))) : ℤ)) : ℝ) 0
      ≤ ∏ _i : Fin d, (1 + (k : ℝ) / (2 * r0)) * ((2 * r : ℕ) : ℝ) :=
        Finset.prod_le_prod (fun i _ => le_max_right _ _) fun i _ =>
          max_le (by push_cast; nlinarith) (by positivity)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The covering inequality** (deterministic). Let `g ∈ 𝓜_C` and let `Z ⊆ [K, N - K)^d` be a
set of centres `z` each carrying a radius `n ∈ [r₀, K]` with `g(z + [-n, n)^d) ≤ b (2n)^d`. Then,
for every `k ≥ 1` and `γ ≥ 0` with `γ - b - C δ ≥ 0`, `δ = (1 + k / (2 r₀))^d - 1`,
`g([0, N)^d) ≤ γ N^d - (γ - b - C δ) |Z| / 2^d + k^{-d} ∑_{z ∈ [0, N)^d} (g(z + [0, k)^d) - γ k^d)⁺
+ C (N^d - (N + 1 - k)^d)`.
The proof selects disjoint bad cubes (`exists_disjoint_centredCubeAt`) and tiles the rest by
translates of `[0, k)^d` (`subadditive_tiling_le`). -/
theorem covering_le {C : ℝ} {g : Set (Site d) → ℝ} (hg : g ∈ subadditiveClass d C)
    {N K r0 k : ℕ} (hk : 1 ≤ k) (hr0 : 1 ≤ r0) {b γ : ℝ} (hγ : 0 ≤ γ)
    (hcoef : 0 ≤ γ - b - C * ((1 + (k : ℝ) / (2 * r0)) ^ d - 1))
    (Z : Finset (Site d)) (hZ : Z ⊆ ibox (fun _ => (K : ℤ)) (fun _ => (N : ℤ) - K))
    (hbad : ∀ z ∈ Z, ∃ n : ℕ, r0 ≤ n ∧ n ≤ K ∧
      g ↑(centredCubeAt z n) ≤ b * ((2 * n : ℕ) : ℝ) ^ d) :
    g ↑(ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ))) ≤
      γ * (N : ℝ) ^ d - (γ - b - C * ((1 + (k : ℝ) / (2 * r0)) ^ d - 1)) * ((Z.card : ℝ) / 2 ^ d) +
      (∑ z ∈ ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ)),
        max (g ↑(cell k z) - γ * (k : ℝ) ^ d) 0) / (k : ℝ) ^ d +
      C * ((N : ℝ) ^ d - (ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ) + (1 - (k : ℤ)))).card) := by
  set δ := (1 + (k : ℝ) / (2 * r0)) ^ d - 1 with hδ
  set box := ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ)) with hbox
  set small := ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ) + (1 - (k : ℤ))) with hsmall
  have hC : 0 ≤ C := nonneg_of_mem_subadditiveClass hg
  have hkpos : (0 : ℝ) < (k : ℝ) ^ d := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have hbad' : ∀ z, ∃ n : ℕ, z ∈ Z → r0 ≤ n ∧ n ≤ K ∧
      g ↑(centredCubeAt z n) ≤ b * ((2 * n : ℕ) : ℝ) ^ d := by
    intro z
    by_cases hz : z ∈ Z
    · obtain ⟨n, hn⟩ := hbad z hz
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose r hr using hbad'
  obtain ⟨T, hTZ, hTd, hTc⟩ :=
    exists_disjoint_centredCubeAt r Z fun z hz => hr0.trans (hr z hz).1
  set U := T.biUnion fun t => centredCubeAt t (r t) with hU
  set rest := box \ U with hrest
  have hUcard : (U.card : ℝ) = ∑ t ∈ T, ((2 * r t : ℕ) : ℝ) ^ d := by
    rw [hU, Finset.card_biUnion fun s hs t ht hst => hTd s hs t ht hst, Nat.cast_sum]
    exact Finset.sum_congr rfl fun t _ => card_centredCubeAt t (r t)
  have hUbox : U ⊆ box := by
    refine Finset.biUnion_subset.2 fun t ht x hx => ?_
    have h1 := mem_ibox.1 (hZ (hTZ ht))
    have h2 := (hr t (hTZ ht)).2.1
    rw [mem_centredCubeAt] at hx
    rw [hbox, mem_ibox]
    intro i
    have := h1 i
    have := hx i
    constructor <;> omega
  have hboxcard : (box.card : ℝ) = (N : ℝ) ^ d := by
    rw [hbox, card_ibox]
    simp only [sub_zero, Int.cast_natCast, max_eq_left (Nat.cast_nonneg _), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hrestcard : (rest.card : ℝ) = (N : ℝ) ^ d - U.card := by
    have := Finset.card_sdiff_add_card_eq_card hUbox
    rw [← hboxcard, ← this]
    push_cast
    ring
  -- step 1: split `box = U ∪ rest`
  have h1 : g ↑box ≤ g ↑U + g ↑rest := by
    have := subadditive_union hg.1 (Finset.disjoint_sdiff : Disjoint U (box \ U))
    rwa [Finset.union_sdiff_of_subset hUbox] at this
  -- step 2: the selected cubes
  have h2 : g ↑U ≤ b * U.card := by
    calc g ↑U ≤ ∑ t ∈ T, g ↑(centredCubeAt t (r t)) :=
          subadditive_le_sum_biUnion hg T _ hTd
      _ ≤ ∑ t ∈ T, b * ((2 * r t : ℕ) : ℝ) ^ d :=
          Finset.sum_le_sum fun t ht => (hr t (hTZ ht)).2.2
      _ = b * U.card := by rw [hUcard, Finset.mul_sum]
  -- step 3: tiling the rest
  set I := innerSites k rest with hI
  have hIrest : I ⊆ rest := Finset.filter_subset _ _
  have hrestbox : rest ⊆ box := Finset.sdiff_subset
  have h3 := subadditive_tiling_le hg rest hk
  have h4 : ∑ z ∈ I, g ↑(cell k z) ≤ γ * (k : ℝ) ^ d * I.card +
      ∑ z ∈ box, max (g ↑(cell k z) - γ * (k : ℝ) ^ d) 0 := by
    have h' : ∑ z ∈ I, g ↑(cell k z) ≤
        ∑ z ∈ I, (γ * (k : ℝ) ^ d + max (g ↑(cell k z) - γ * (k : ℝ) ^ d) 0) :=
      Finset.sum_le_sum fun z _ => by linarith [le_max_left (g ↑(cell k z) - γ * (k : ℝ) ^ d) 0]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h'
    have h'' : ∑ z ∈ I, max (g ↑(cell k z) - γ * (k : ℝ) ^ d) 0 ≤
        ∑ z ∈ box, max (g ↑(cell k z) - γ * (k : ℝ) ^ d) 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (hIrest.trans hrestbox) fun _ _ _ => le_max_right _ _
    nlinarith
  -- step 4: the sites of `rest` whose cell leaves `rest`
  have hcollar : rest \ I ⊆ (box \ small) ∪ T.biUnion fun t =>
      ibox (fun i => t i - r t + (1 - (k : ℤ))) (fun i => t i + r t) \ centredCubeAt t (r t) := by
    intro z hz
    obtain ⟨hzr, hzI⟩ := Finset.mem_sdiff.1 hz
    have hzbox := hrestbox hzr
    by_cases hzin : z ∈ small
    · apply Finset.mem_union_right
      have hnot : ¬ cell k z ⊆ rest := fun h => hzI (Finset.mem_filter.2 ⟨hzr, h⟩)
      rw [Finset.not_subset] at hnot
      obtain ⟨x, hxc, hxr⟩ := hnot
      have hxbox : x ∈ box := by
        rw [hbox, mem_ibox]
        rw [mem_cell] at hxc
        rw [hsmall, mem_ibox] at hzin
        intro i
        have := hxc i
        have := hzin i
        constructor <;> omega
      have hxU : x ∈ U := by
        by_contra hxU
        exact hxr (Finset.mem_sdiff.2 ⟨hxbox, hxU⟩)
      rw [hU, Finset.mem_biUnion] at hxU
      obtain ⟨t, ht, hxt⟩ := hxU
      rw [Finset.mem_biUnion]
      refine ⟨t, ht, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩
      · rw [mem_ibox]
        rw [mem_centredCubeAt] at hxt
        rw [mem_cell] at hxc
        intro i
        have := hxt i
        have := hxc i
        constructor <;> omega
      · intro hzt
        exact (Finset.mem_sdiff.1 hzr).2 (Finset.mem_biUnion.2 ⟨t, ht, hzt⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hzbox, hzin⟩)
  have hsmallbox : small ⊆ box := by
    intro z hz
    rw [hsmall, mem_ibox] at hz
    rw [hbox, mem_ibox]
    intro i
    have := hz i
    constructor <;> omega
  have hcount : (rest.card : ℝ) - I.card ≤ ((N : ℝ) ^ d - small.card) + δ * U.card := by
    have e1 : ((rest \ I).card : ℝ) = rest.card - I.card := by
      have := Finset.card_sdiff_add_card_eq_card hIrest
      rw [← this]
      push_cast
      ring
    have e2 : ((box \ small).card : ℝ) = (N : ℝ) ^ d - small.card := by
      have := Finset.card_sdiff_add_card_eq_card hsmallbox
      rw [← hboxcard, ← this]
      push_cast
      ring
    have e3 : ∀ t ∈ T, ((ibox (fun i => t i - r t + (1 - (k : ℤ))) (fun i => t i + r t) \
        centredCubeAt t (r t)).card : ℝ) ≤ δ * ((2 * r t : ℕ) : ℝ) ^ d := by
      intro t ht
      have hsub : centredCubeAt t (r t) ⊆ ibox (fun i => t i - r t + (1 - (k : ℤ)))
          (fun i => t i + r t) := by
        intro x hx
        rw [mem_centredCubeAt] at hx
        rw [mem_ibox]
        intro i
        have := hx i
        constructor <;> omega
      have := Finset.card_sdiff_add_card_eq_card hsub
      have hc := card_collarBox_le (t := t) (d := d) hr0 (hr t (hTZ ht)).1 hk
      have e : ((ibox (fun i => t i - r t + (1 - (k : ℤ))) (fun i => t i + r t) \
          centredCubeAt t (r t)).card : ℝ) =
          ((ibox (fun i => t i - r t + (1 - (k : ℤ))) (fun i => t i + r t)).card : ℝ) -
            (centredCubeAt t (r t)).card := by
        rw [← this]
        push_cast
        ring
      rw [e, card_centredCubeAt, hδ]
      linarith
    have hc1 := Finset.card_le_card hcollar
    have hc2 := Finset.card_union_le (box \ small) (T.biUnion fun t =>
      ibox (fun i => t i - r t + (1 - (k : ℤ))) (fun i => t i + r t) \ centredCubeAt t (r t))
    have hc3 : (T.biUnion fun t => ibox (fun i => t i - r t + (1 - (k : ℤ))) (fun i => t i + r t) \
        centredCubeAt t (r t)).card ≤ ∑ t ∈ T, (ibox (fun i => t i - r t + (1 - (k : ℤ)))
          (fun i => t i + r t) \ centredCubeAt t (r t)).card := Finset.card_biUnion_le
    have hc : ((rest \ I).card : ℝ) ≤ (box \ small).card + ∑ t ∈ T,
        ((ibox (fun i => t i - r t + (1 - (k : ℤ))) (fun i => t i + r t) \
          centredCubeAt t (r t)).card : ℝ) := by
      exact_mod_cast hc1.trans (hc2.trans (Nat.add_le_add_left hc3 _))
    rw [e1, e2] at hc
    have hs := Finset.sum_le_sum e3
    rw [← Finset.mul_sum, ← hUcard] at hs
    linarith
  -- step 5: assemble
  have hgrest : (k : ℝ) ^ d * g ↑rest ≤ (k : ℝ) ^ d * (γ * rest.card +
      (∑ z ∈ box, max (g ↑(cell k z) - γ * (k : ℝ) ^ d) 0) / (k : ℝ) ^ d +
      C * (((N : ℝ) ^ d - small.card) + δ * U.card)) := by
    have hIr : (I.card : ℝ) ≤ rest.card := by exact_mod_cast Finset.card_le_card hIrest
    rw [mul_add, mul_add, mul_div_cancel₀ _ hkpos.ne']
    nlinarith [mul_le_mul_of_nonneg_left hIr (by positivity : 0 ≤ γ * (k : ℝ) ^ d),
      mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ C * (k : ℝ) ^ d)]
  have hgrest' := le_of_mul_le_mul_left hgrest hkpos
  have hUZ : (Z.card : ℝ) / 2 ^ d ≤ U.card := by
    rw [hUcard, div_le_iff₀ (by positivity)]
    linarith
  have hfin := mul_le_mul_of_nonneg_left hUZ hcoef
  rw [hrestcard] at hgrest'
  nlinarith

end Covering


/-! ### The lower bound -/

section Lower

variable {d : ℕ} {C : ℝ} {f : Config d → Set (Site d) → ℝ}

/-- The event that some radius `n ∈ [r₀, K]` is bad: `f(η, [-n, n)^d) < b (2n)^d`. -/
def badEvent (f : Config d → Set (Site d) → ℝ) (r0 K : ℕ) (b : ℝ) : Set (Config d) :=
  ⋃ n ∈ Finset.Icc r0 K, {η | f η ↑(centredCube (d := d) n) < b * ((2 * n : ℕ) : ℝ) ^ d}

theorem measurableSet_badEvent (hf : IsSubadditiveProcess C f) (r0 K : ℕ) (b : ℝ) :
    MeasurableSet (badEvent f r0 K b) :=
  Finset.measurableSet_biUnion _ fun _ _ =>
    measurableSet_lt (hf.measurable _ (Finset.finite_toSet _)) measurable_const

theorem badEvent_mono (r0 : ℕ) (b : ℝ) : Monotone fun K => badEvent f r0 K b := by
  intro K K' hK η hη
  simp only [badEvent, Set.mem_iUnion, Finset.mem_Icc] at hη ⊢
  obtain ⟨n, ⟨h1, h2⟩, h3⟩ := hη
  exact ⟨n, ⟨h1, h2.trans hK⟩, h3⟩

theorem centredCubeAt_eq_map (z : Site d) (r : ℕ) :
    centredCubeAt z r = (centredCube r).map (Equiv.addRight z).toEmbedding := by
  ext x
  simp only [Finset.mem_map_equiv, Equiv.addRight_symm, Equiv.coe_addRight, mem_centredCubeAt,
    centredCube, mem_ibox, Pi.add_apply, Pi.neg_apply]
  constructor <;> intro h i <;> have := h i <;> omega

theorem f_centredCubeAt_eq (hf : IsSubadditiveProcess C f) (η : Config d) (z : Site d) (r : ℕ) :
    f η ↑(centredCubeAt z r) = f (shift z η) ↑(centredCube (d := d) r) := by
  rw [hf.stationary z _ (Finset.finite_toSet _), centredCubeAt_eq_map, coe_map_addRight]

theorem integral_comp_shift (E : RandomEnvironment d) (y : Site d) {h : Config d → ℝ}
    (hm : Measurable h) : ∫ η, h (shift y η) ∂E.P = ∫ η, h η ∂E.P := by
  have hs := E.stationary y
  rw [← integral_map hs.measurable.aemeasurable hm.aestronglyMeasurable, hs.map_eq]

theorem integrable_of_abs_le (E : RandomEnvironment d) {h : Config d → ℝ} (hm : Measurable h)
    (M : ℝ) (hM : ∀ η, |h η| ≤ M) : Integrable h E.P := by
  haveI := E.isProb
  exact Integrable.of_bound hm.aestronglyMeasurable M
    (Eventually.of_forall fun η => by rw [Real.norm_eq_abs]; exact hM η)

/-- **The covering inequality in expectation.** -/
theorem covering_integral_le (E : RandomEnvironment d) (hf : IsSubadditiveProcess C f)
    {N K r0 k : ℕ} (hk : 1 ≤ k) (hr0 : 1 ≤ r0) {b γ : ℝ} (hγ : 0 ≤ γ)
    (hcoef : 0 ≤ γ - b - C * ((1 + (k : ℝ) / (2 * r0)) ^ d - 1)) :
    (γ - b - C * ((1 + (k : ℝ) / (2 * r0)) ^ d - 1)) *
        (((ibox (d := d) (fun _ => (K : ℤ)) (fun _ => (N : ℤ) - K)).card : ℝ) *
          E.P.real (badEvent f r0 K b) / 2 ^ d) ≤
      γ * (N : ℝ) ^ d - ∫ η, f η ↑(latticeCube d N) ∂E.P +
      (N : ℝ) ^ d * (∫ η, max (f η ↑(latticeCube d k) - γ * (k : ℝ) ^ d) 0 ∂E.P) / (k : ℝ) ^ d +
      C * ((N : ℝ) ^ d - (ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ) + (1 - (k : ℤ)))).card) := by
  classical
  haveI := E.isProb
  set c := γ - b - C * ((1 + (k : ℝ) / (2 * r0)) ^ d - 1) with hc
  set B0 := ibox (d := d) (fun _ => (K : ℤ)) (fun _ => (N : ℤ) - K) with hB0
  set box := ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ)) with hbox
  set Bad := badEvent f r0 K b with hBad
  set D := C * ((N : ℝ) ^ d - (ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ) + (1 - (k : ℤ)))).card)
    with hD
  set φ : Config d → ℝ := fun η => max (f η ↑(latticeCube d k) - γ * (k : ℝ) ^ d) 0 with hφ
  have hBadm : MeasurableSet Bad := measurableSet_badEvent hf r0 K b
  have hφm : Measurable φ :=
    ((finsetProcess_measurable hf (latticeCube d k)).sub measurable_const).max measurable_const
  have hφb : ∀ η, |φ η| ≤ C * ((latticeCube d k).card : ℝ) := by
    intro η
    have hb := finsetProcess_bd hf (latticeCube d k) η
    simp only [finsetProcess] at hb
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le (by nlinarith [hb.1, hb.2, (by positivity : (0 : ℝ) ≤ γ * (k : ℝ) ^ d)]) ?_
    exact hb.1.trans hb.2
  have hIm : Measurable (Bad.indicator (1 : Config d → ℝ)) := measurable_one.indicator hBadm
  have hIb : ∀ η, |Bad.indicator (1 : Config d → ℝ) η| ≤ 1 := by
    intro η
    by_cases h : η ∈ Bad <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hshm : ∀ z : Site d, Measurable (shift (d := d) z) := fun z => (E.stationary z).measurable
  set S1 : Config d → ℝ := fun η => ∑ z ∈ B0, Bad.indicator 1 (shift z η) with hS1
  set S2 : Config d → ℝ := fun η => ∑ z ∈ box, φ (shift z η) with hS2
  have hI1 : ∀ z : Site d, Integrable (fun η => Bad.indicator (1 : Config d → ℝ) (shift z η)) E.P :=
    fun z => integrable_of_abs_le E (hIm.comp (hshm z)) 1 fun η => hIb _
  have hI2 : ∀ z : Site d, Integrable (fun η => φ (shift z η)) E.P :=
    fun z => integrable_of_abs_le E (hφm.comp (hshm z)) _ fun η => hφb _
  have hS1i : Integrable S1 E.P := integrable_finsetSum _ fun z _ => hI1 z
  have hS2i : Integrable S2 E.P := integrable_finsetSum _ fun z _ => hI2 z
  have hS1int : ∫ η, S1 η ∂E.P = B0.card * E.P.real Bad := by
    show ∫ η, ∑ z ∈ B0, Bad.indicator (1 : Config d → ℝ) (shift z η) ∂E.P = _
    rw [integral_finsetSum _ fun z _ => hI1 z]
    rw [Finset.sum_congr rfl fun z _ => integral_comp_shift E z hIm, Finset.sum_const,
      integral_indicator_one hBadm, nsmul_eq_mul]
  have hboxcard : (box.card : ℝ) = (N : ℝ) ^ d := by
    rw [hbox, card_ibox]
    simp only [sub_zero, Int.cast_natCast, max_eq_left (Nat.cast_nonneg _), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hS2int : ∫ η, S2 η ∂E.P = (N : ℝ) ^ d * ∫ η, φ η ∂E.P := by
    show ∫ η, ∑ z ∈ box, φ (shift z η) ∂E.P = _
    rw [integral_finsetSum _ fun z _ => hI2 z]
    rw [Finset.sum_congr rfl fun z _ => integral_comp_shift E z hφm, Finset.sum_const,
      nsmul_eq_mul, hboxcard]
  -- the pathwise inequality
  have hpath : ∀ η, f η ↑(latticeCube d N) ≤
      (γ * (N : ℝ) ^ d + D) + (-(c / 2 ^ d) * S1 η + ((k : ℝ) ^ d)⁻¹ * S2 η) := by
    intro η
    have hZ : B0.filter (fun z => shift z η ∈ Bad) ⊆ ibox (fun _ => (K : ℤ)) (fun _ => (N : ℤ) - K) :=
      Finset.filter_subset _ _
    have hbad : ∀ z ∈ B0.filter (fun z => shift z η ∈ Bad), ∃ n : ℕ, r0 ≤ n ∧ n ≤ K ∧
        f η ↑(centredCubeAt z n) ≤ b * ((2 * n : ℕ) : ℝ) ^ d := by
      intro z hz
      have hz' := (Finset.mem_filter.1 hz).2
      simp only [hBad, badEvent, Set.mem_iUnion, Finset.mem_Icc, Set.mem_setOf_eq] at hz'
      obtain ⟨n, ⟨h1, h2⟩, h3⟩ := hz'
      exact ⟨n, h1, h2, by rw [f_centredCubeAt_eq hf]; exact h3.le⟩
    have h := covering_le (hf.mem η) hk hr0 hγ hcoef _ hZ hbad
    have hcard : ((B0.filter (fun z => shift z η ∈ Bad)).card : ℝ) = S1 η := by
      rw [Finset.natCast_card_filter, hS1]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases h : shift z η ∈ Bad <;> simp [h]
    have hsum : ∑ z ∈ box, max (f η ↑(cell k z) - γ * (k : ℝ) ^ d) 0 = S2 η := by
      rw [hS2]
      exact Finset.sum_congr rfl fun z _ => by rw [f_cell_eq hf]
    rw [hcard, hsum] at h
    rw [ibox_zero_eq_latticeCube, ← hD] at h
    have e1 : c * (S1 η / 2 ^ d) = c / 2 ^ d * S1 η := by ring
    have e2 : S2 η / (k : ℝ) ^ d = ((k : ℝ) ^ d)⁻¹ * S2 η := by ring
    linarith
  clear_value S1 S2 φ D c Bad B0 box
  have hFN : Integrable (fun η => f η ↑(latticeCube d N)) E.P := by
    have hb := finsetProcess_bd hf (latticeCube d N)
    simp only [finsetProcess] at hb
    exact integrable_of_abs_le E (finsetProcess_measurable hf _) _ fun η => by
      rw [abs_of_nonneg (hb η).1]; exact (hb η).2
  have key : ∫ η, f η ↑(latticeCube d N) ∂E.P ≤ ∫ η, ((γ * (N : ℝ) ^ d + D) +
      (-(c / 2 ^ d) * S1 η + ((k : ℝ) ^ d)⁻¹ * S2 η)) ∂E.P :=
    integral_mono hFN ((integrable_const _).add ((hS1i.const_mul _).add (hS2i.const_mul _))) hpath
  rw [integral_add ?_ ?_, integral_const, integral_add ?_ ?_, integral_const_mul,
    integral_const_mul, hS1int, hS2int] at key
  any_goals first
    | exact integrable_const _
    | exact (hS1i.const_mul _).add (hS2i.const_mul _)
    | exact hS1i.const_mul _
    | exact hS2i.const_mul _
  simp only [probReal_univ, one_smul] at key
  have e1 : c * ((B0.card : ℝ) * E.P.real Bad / 2 ^ d) = c / 2 ^ d * (B0.card * E.P.real Bad) := by
    ring
  have e2 : (N : ℝ) ^ d * (∫ η, φ η ∂E.P) / (k : ℝ) ^ d =
      ((k : ℝ) ^ d)⁻¹ * ((N : ℝ) ^ d * ∫ η, φ η ∂E.P) := by ring
  rw [e1, e2]
  linarith

end Lower


/-! ### Limits and the almost sure lower bound -/

section LowerAE

variable {d : ℕ} {C : ℝ} {f : Config d → Set (Site d) → ℝ}

theorem tendsto_card_box_div (α β : ℤ) :
    Tendsto (fun N : ℕ => ((ibox (d := d) (fun _ => α) (fun _ => (N : ℤ) + β)).card : ℝ) /
      (N : ℝ) ^ d) atTop (𝓝 1) := by
  have h := tendsto_card_ibox_div_pow (d := d) (fun _ => 0) (fun _ => 1) (fun _ => zero_le_one) α β
  simp only [sub_zero, Finset.prod_const_one, mul_zero, Int.ceil_zero, zero_add, mul_one,
    Int.ceil_natCast] at h
  exact h

/-- The mean excess `E (f(η, [0, k)^d) / k^d - γ)⁺` tends to `0` when `γ > a` (dominated
convergence). -/
theorem tendsto_integral_excess (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) {a γ : ℝ} (haγ : a < γ) (hγ : 0 ≤ γ)
    (hcube : ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ => f η ↑(latticeCube d n) / (n : ℝ) ^ d) atTop (𝓝 a)) :
    Tendsto (fun k : ℕ => (∫ η, max (f η ↑(latticeCube d k) - γ * (k : ℝ) ^ d) 0 ∂E.P) /
      (k : ℝ) ^ d) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := E.P) (fun _ => C)
    (F := fun (n : ℕ) η => max (f η ↑(latticeCube d n) / (n : ℝ) ^ d - γ) 0) (f := fun _ => 0)
    (fun n => ((((finsetProcess_measurable hf (latticeCube d n)).div_const _).sub
      measurable_const).max measurable_const).aestronglyMeasurable)
    (integrable_const C)
    (fun n => Eventually.of_forall fun η => by
      have hb : 0 ≤ f η ↑(latticeCube d n) / (n : ℝ) ^ d ∧
          f η ↑(latticeCube d n) / (n : ℝ) ^ d ≤ C :=
        cubeRatio_nonneg_le hd (finsetProcess_bd hf) n η
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hb.2]) (hb.1.trans hb.2))
    (by
      filter_upwards [hcube] with η hη
      have := (hη.sub_const γ).max (tendsto_const_nhds (x := (0 : ℝ)))
      rwa [max_eq_right (by linarith)] at this)
  simp only [integral_const, smul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkpos : (0 : ℝ) < (k : ℝ) ^ d := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  rw [← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only
  rw [← max_div_div_right hkpos.le, zero_div, sub_div, mul_div_cancel_right₀ _ hkpos.ne']

/-- **Bad radii are rare.** For `ε, θ > 0` there is `r₀ ≥ 1` such that, for every `K`, the
probability that `f(η, [-n, n)^d) < (a - ε)(2n)^d` for some `n ∈ [r₀, K]` is at most `θ`. -/
theorem exists_measureReal_badEvent_le (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) {a : ℝ} (ha : 0 ≤ a)
    (hcube : ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ => f η ↑(latticeCube d n) / (n : ℝ) ^ d) atTop (𝓝 a))
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ r0 : ℕ, 1 ≤ r0 ∧ ∀ K : ℕ, E.P.real (badEvent f r0 K (a - ε)) ≤ θ := by
  haveI := E.isProb
  have hC : 0 ≤ C := nonneg_of_mem_subadditiveClass (hf.mem 0)
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  set η' := θ * ε / (4 * 2 ^ d) with hη'
  have hη'pos : 0 < η' := by positivity
  set γ := a + η' with hγ
  have hγ0 : 0 ≤ γ := by linarith
  obtain ⟨k, hk1, hkI⟩ : ∃ k : ℕ, 1 ≤ k ∧
      (∫ η, max (f η ↑(latticeCube d k) - γ * (k : ℝ) ^ d) 0 ∂E.P) / (k : ℝ) ^ d < η' := by
    have h := tendsto_integral_excess hd E hf (by linarith : a < γ) hγ0 hcube
    obtain ⟨k, hk⟩ := eventually_atTop.1 ((h.eventually (gt_mem_nhds hη'pos)).and
      (eventually_ge_atTop 1))
    exact ⟨k, (hk k le_rfl).2, (hk k le_rfl).1⟩
  obtain ⟨r0, hr0C, hr01⟩ : ∃ r0 : ℕ, C * ((1 + (k : ℝ) / (2 * r0)) ^ d - 1) ≤ ε / 2 ∧ 1 ≤ r0 := by
    have h0 : Tendsto (fun r0 : ℕ => (k : ℝ) / (2 * r0)) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ) / 2)
      refine this.congr fun r0 => ?_
      rw [div_div, mul_comm]
    have h1 : Tendsto (fun r0 : ℕ => C * ((1 + (k : ℝ) / (2 * r0)) ^ d - 1)) atTop
        (𝓝 (C * ((1 + 0) ^ d - 1))) :=
      (((tendsto_const_nhds.add h0).pow d).sub_const 1).const_mul C
    simp only [add_zero, one_pow, sub_self, mul_zero] at h1
    obtain ⟨r0, hr0⟩ := eventually_atTop.1 ((h1.eventually (ge_mem_nhds (by linarith :
      (0 : ℝ) < ε / 2))).and (eventually_ge_atTop 1))
    exact ⟨r0, (hr0 r0 le_rfl).1, (hr0 r0 le_rfl).2⟩
  refine ⟨r0, hr01, fun K => ?_⟩
  set δ := (1 + (k : ℝ) / (2 * r0)) ^ d - 1 with hδ
  set c := γ - (a - ε) - C * δ with hc
  have hcpos : ε / 2 ≤ c := by rw [hc, hγ]; linarith
  have hcoef : 0 ≤ c := by linarith
  set P := E.P.real (badEvent f r0 K (a - ε)) with hP
  have hP0 : 0 ≤ P := measureReal_nonneg
  set I := (∫ η, max (f η ↑(latticeCube d k) - γ * (k : ℝ) ^ d) 0 ∂E.P) with hI
  -- the inequality at scale `N`, divided by `N^d`
  have hB := tendsto_card_box_div (d := d) (K : ℤ) (-(K : ℤ))
  simp only [← sub_eq_add_neg] at hB
  have hS := tendsto_card_box_div (d := d) 0 (1 - (k : ℤ))
  have hint := tendsto_integral_cube_div_pow hd E hf hcube
  have hL : Tendsto (fun N : ℕ => c * (((ibox (d := d) (fun _ => (K : ℤ))
      (fun _ => (N : ℤ) - K)).card : ℝ) / (N : ℝ) ^ d * P / 2 ^ d)) atTop
      (𝓝 (c * (1 * P / 2 ^ d))) :=
    (((hB.mul_const P).div_const _)).const_mul c
  have hR : Tendsto (fun N : ℕ => γ - (∫ η, f η ↑(latticeCube d N) ∂E.P) / (N : ℝ) ^ d +
      I / (k : ℝ) ^ d + C * (1 - ((ibox (d := d) (fun _ => 0)
        (fun _ => (N : ℤ) + (1 - (k : ℤ)))).card : ℝ) / (N : ℝ) ^ d)) atTop
      (𝓝 (γ - a + I / (k : ℝ) ^ d + C * (1 - 1))) :=
    ((tendsto_const_nhds.sub hint).add tendsto_const_nhds).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hS))
  have hlim := le_of_tendsto_of_tendsto hL hR (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      positivity
    have h := covering_integral_le (N := N) (K := K) E hf hk1 hr01 hγ0 hcoef
    rw [← hδ, ← hc, ← hP, ← hI] at h
    have hN0 : (N : ℝ) ^ d ≠ 0 := hNpos.ne'
    rw [← mul_le_mul_iff_of_pos_right hNpos]
    convert h using 1 <;> first | rfl | (field_simp; try ring))
  rw [sub_self, mul_zero, add_zero, one_mul, hγ] at hlim
  have h1 : ε / 2 * (P / 2 ^ d) ≤ c * (P / 2 ^ d) :=
    mul_le_mul_of_nonneg_right hcpos (div_nonneg hP0 h2d.le)
  have h2 : ε / 2 * (P / 2 ^ d) ≤ 2 * η' := by
    have : a + η' - a + I / (k : ℝ) ^ d ≤ 2 * η' := by linarith
    linarith
  rw [hη'] at h2
  have h3 : ε / 2 * (P / 2 ^ d) = ε * P / (2 * 2 ^ d) := by ring
  have h4 : 2 * (θ * ε / (4 * 2 ^ d)) = ε * θ / (2 * 2 ^ d) := by ring
  rw [h3, h4, div_le_div_iff_of_pos_right (by positivity)] at h2
  exact le_of_mul_le_mul_left h2 hε

/-- **Lower bound.** Almost surely `liminf f(η, [-n, n)^d) / (2n)^d ≥ a`. -/
theorem ae_eventually_ge_centredCube (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) {a : ℝ} (ha : 0 ≤ a)
    (hcube : ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ => f η ↑(latticeCube d n) / (n : ℝ) ^ d) atTop (𝓝 a)) :
    ∀ᵐ η ∂E.P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      a - ε ≤ f η ↑(centredCube (d := d) n) / ((2 * n : ℕ) : ℝ) ^ d := by
  haveI := E.isProb
  have hm : ∀ m : ℕ, ∀ᵐ η ∂E.P, ∀ᶠ n : ℕ in atTop,
      a - 1 / ((m : ℝ) + 1) ≤ f η ↑(centredCube (d := d) n) / ((2 * n : ℕ) : ℝ) ^ d := by
    intro m
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    rw [ae_iff]
    refine le_antisymm ?_ zero_le
    have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop
        (𝓝 (ENNReal.ofReal 0)) := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    rw [ENNReal.ofReal_zero] at hlim
    refine ge_of_tendsto' hlim fun j => ?_
    obtain ⟨r0, hr01, hr0⟩ := exists_measureReal_badEvent_le hd E hf ha hcube hε
      (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))
    have hsub : {η | ¬∀ᶠ n : ℕ in atTop, a - 1 / ((m : ℝ) + 1) ≤
        f η ↑(centredCube (d := d) n) / ((2 * n : ℕ) : ℝ) ^ d} ⊆
        ⋃ K, badEvent f r0 K (a - 1 / ((m : ℝ) + 1)) := by
      intro η hη
      simp only [Set.mem_setOf_eq, not_eventually, not_le, frequently_atTop] at hη
      obtain ⟨n, hn, hlt⟩ := hη r0
      have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) ^ d := by
        have : (1 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * n)
        positivity
      rw [div_lt_iff₀ hNpos] at hlt
      simp only [badEvent, Set.mem_iUnion, Finset.mem_Icc, Set.mem_setOf_eq]
      exact ⟨n, n, ⟨hn, le_rfl⟩, hlt⟩
    refine (measure_mono hsub).trans ?_
    have hmono := tendsto_measure_iUnion_atTop (μ := E.P)
      (badEvent_mono (f := f) r0 (a - 1 / ((m : ℝ) + 1)))
    refine le_of_tendsto' hmono fun K => ?_
    show E.P (badEvent f r0 K (a - 1 / ((m : ℝ) + 1))) ≤ _
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hr0 K)
  rw [← ae_all_iff] at hm
  filter_upwards [hm] with η hη ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  exact (hη m).mono fun n hn => by linarith

end LowerAE

/-! ### The theorem -/

/-- **The subadditive ergodic theorem along the centred cubes** (`SubadditiveCentredCubesStmt`):
almost surely `f(η, [-n, n)^d) / (2n)^d` converges, to the constant `a` of the cube limit. -/
theorem ae_tendsto_centredCube {d : ℕ} (hd : 1 ≤ d) (E : RandomEnvironment d) {C : ℝ}
    {f : Config d → Set (Site d) → ℝ} (hf : IsSubadditiveProcess C f) {a : ℝ} (ha : 0 ≤ a)
    (hcube : ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ => f η ↑(latticeCube d n) / (n : ℝ) ^ d) atTop (𝓝 a)) :
    ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ => f η ↑(centredCube (d := d) n) / ((2 * n : ℕ) : ℝ) ^ d)
      atTop (𝓝 a) := by
  filter_upwards [ae_eventually_le_centredCube hd E hf hcube,
    ae_eventually_ge_centredCube hd E hf ha hcube] with η hU hL
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · filter_upwards [hL ((a - a') / 2) (by linarith)] with n hn
    linarith
  · filter_upwards [hU ((a' - a) / 2) (by linarith)] with n hn
    linarith

/-- `SubadditiveCentredCubesStmt` holds. -/
theorem subadditiveCentredCubes : SubadditiveCentredCubesStmt := by
  intro d hd E C f hf
  obtain ⟨a, ha0, -, hcube⟩ := exists_ae_tendsto_cube_const hd E hf
  filter_upwards [ae_tendsto_centredCube hd E hf ha0 hcube] with η hη
  exact ⟨a, hη⟩

end RandomSandpile

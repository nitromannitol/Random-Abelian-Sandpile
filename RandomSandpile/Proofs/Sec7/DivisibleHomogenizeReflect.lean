import RandomSandpile.Steps.Sec7.DivisibleHomogenize
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodicAllFlip

/-!
# Lemma 7.3: `CubeErgodicStmt` from the rectangle ergodic theorem for `0 ≤ a`

`paper/random_piles-corrected.tex`). Lattice-Probability proves the
rectangle a.e. ergodic theorem `LatticeProb.RectangleErgodic d` only for rectangles with corners
`0 ≤ a ≤ b`, whereas the dyadic cubes `Q_{j,k}(N) = rectBox (2^{-j} k) (2^{-j} (k + 1)) N` of
`CubeErgodicStmt` live in all orthants (`k ∈ ℤ^d`). Here the cubes in the other orthants are
reached by coordinate reflections: for `S = {i | k_i < 0}` the action
`reflectActionS shift S z = shift (flipSubset S z)` is again measure preserving, additive and
ergodic (`LatticeProb.reflectActionS_props`), and the rectangle with corners
`a_i = k_i 2^{-j}, b_i = (k_i + 1) 2^{-j}` (`i ∉ S`), `a_i = -(k_i + 1) 2^{-j}`,
`b_i = -k_i 2^{-j}` (`i ∈ S`) has `0 ≤ a ≤ b`. Its image under `flipSubset S` is the box with
intervals `(⌊N k_i 2^{-j}⌋, ⌊N (k_i + 1) 2^{-j}⌋]` in the coordinates `i ∈ S`, which differs from
the dyadic cube only in the two end hyperplane layers of each coordinate; for a bounded summand
this changes the sum by at most `4 M d (N + 1)^(d - 1) = o(N^d)`.

* `box_sum_diff_le`: the bounded-summand comparison of two boxes with endpoints at distance `≤ 1`.
* `cubeErgodic_of_rectangleErgodic`: `CubeErgodicStmt` from `RectangleErgodic d` for all `d`.
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology

namespace RandomSandpile

namespace DivisibleHomogenize

variable {d : ℕ}

/-! ### The bounded observable -/

/-- The bounded observable `η ↦ clamp_{[η_min, η_max]}(η(0)) - E η(0)`. -/
def reflClampObs (E : RandomEnvironment d) (η : Config d) : ℝ :=
  max (E.ηmin : ℝ) (min ((η 0 : ℤ) : ℝ) E.ηmax) - meanEta E.P

theorem measurable_reflClampObs (E : RandomEnvironment d) : Measurable (reflClampObs E) := by
  have h0 : Measurable (fun η : Config d => ((η 0 : ℤ) : ℝ)) :=
    Measurable.of_discrete.comp (measurable_pi_apply 0)
  unfold reflClampObs
  exact (measurable_const.max (h0.min measurable_const)).sub measurable_const

theorem reflClampObs_bound (E : RandomEnvironment d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η, |reflClampObs E η| ≤ M := by
  refine ⟨|(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| + |meanEta E.P|, by positivity, fun η => ?_⟩
  unfold reflClampObs
  have h1 : (E.ηmin : ℝ) ≤ max (E.ηmin : ℝ) (min ((η 0 : ℤ) : ℝ) E.ηmax) := le_max_left _ _
  have h2 : max (E.ηmin : ℝ) (min ((η 0 : ℤ) : ℝ) E.ηmax) ≤ |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| :=
    max_le (le_add_of_le_of_nonneg (le_abs_self _) (abs_nonneg _))
      (le_add_of_nonneg_of_le (abs_nonneg _) ((min_le_right _ _).trans (le_abs_self _)))
  have h3 := neg_abs_le (E.ηmin : ℝ)
  have h4 := abs_nonneg (E.ηmax : ℝ)
  have h5 := neg_abs_le (meanEta E.P)
  have h6 := le_abs_self (meanEta E.P)
  rw [abs_le]
  constructor <;> linarith

/-- On the event `η_min ≤ η(x) ≤ η_max` the clamp does nothing. -/
theorem reflClampObs_shift (E : RandomEnvironment d) (η : Config d) (x : Site d)
    (hx : E.ηmin ≤ η x ∧ E.ηmax ≥ η x) :
    reflClampObs E (shift x η) = (η x : ℝ) - meanEta E.P := by
  unfold reflClampObs
  have h1 : (E.ηmin : ℝ) ≤ (η x : ℝ) := by exact_mod_cast hx.1
  have h2 : (η x : ℝ) ≤ (E.ηmax : ℝ) := by exact_mod_cast hx.2
  rw [shift_apply, add_zero, min_eq_left h2, max_eq_right h1]

theorem integral_reflClampObs (E : RandomEnvironment d) :
    ∫ η, reflClampObs E η ∂E.P = 0 := by
  have hae : reflClampObs E =ᵐ[E.P] fun η => ((η 0 : ℤ) : ℝ) - meanEta E.P := by
    filter_upwards [E.bounded 0] with η hη
    have := reflClampObs_shift E η 0 hη
    simpa [shift_zero] using this
  have h0 : Measurable (fun η : Config d => ((η 0 : ℤ) : ℝ)) :=
    Measurable.of_discrete.comp (measurable_pi_apply 0)
  have hint : Integrable (fun η : Config d => ((η 0 : ℤ) : ℝ)) E.P := by
    refine Integrable.of_bound h0.aestronglyMeasurable (|(E.ηmin : ℝ)| + |(E.ηmax : ℝ)|) ?_
    filter_upwards [E.bounded 0] with η hη
    have h1 : (E.ηmin : ℝ) ≤ (η 0 : ℝ) := by exact_mod_cast hη.1
    have h2 : (η 0 : ℝ) ≤ (E.ηmax : ℝ) := by exact_mod_cast hη.2
    rw [Real.norm_eq_abs, abs_le]
    have h3 := neg_abs_le (E.ηmin : ℝ)
    have h4 := le_abs_self (E.ηmax : ℝ)
    have h5 := abs_nonneg (E.ηmin : ℝ)
    have h6 := abs_nonneg (E.ηmax : ℝ)
    constructor <;> linarith
  rw [integral_congr_ae hae, integral_sub hint (integrable_const _), integral_const]
  simp [meanEta]

/-! ### Comparing two boxes with nearby endpoints -/

/-- The slab `{x ∈ ∏ U | x_i ∈ T}` has at most `|T| C^(d-1)` points when every `|U_j| ≤ C`. -/
theorem card_slab_le (U : Fin d → Finset ℤ) (T : Finset ℤ) (i : Fin d) (C : ℕ)
    (hU : ∀ j, (U j).card ≤ C) :
    (Fintype.piFinset (Function.update U i T)).card ≤ T.card * C ^ (d - 1) := by
  rw [Fintype.card_piFinset]
  have hc : ∀ j, (Function.update U i T j).card =
      Function.update (fun j => (U j).card) i T.card j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp_rw [hc]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  refine Nat.mul_le_mul_left _ ?_
  calc ∏ j ∈ Finset.univ \ {i}, (U j).card ≤ ∏ j ∈ Finset.univ \ {i}, C :=
        Finset.prod_le_prod fun j _ => hU j
    _ = C ^ (d - 1) := by
        rw [Finset.prod_const]
        congr 1
        rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin,
          Finset.card_singleton]

/-- Two boxes `∏ [p_i, q_i)` and `∏ [p'_i, q'_i)` whose endpoints differ by at most `1` (with
`p_i ≤ p'_i`, `q_i ≤ q'_i`) and whose sides have length `≤ N` have sums of a bounded `g` differing by
at most `M · 4 d (N + 1)^(d - 1)`. -/
theorem box_sum_diff_le (p q p' q' : Fin d → ℤ) (N : ℕ)
    (hp1 : ∀ i, p i ≤ p' i) (hp2 : ∀ i, p' i ≤ p i + 1)
    (hq1 : ∀ i, q i ≤ q' i) (hq2 : ∀ i, q' i ≤ q i + 1)
    (hlen : ∀ i, q i - p i ≤ N) (g : Site d → ℝ) (M : ℝ) (hg : ∀ x, |g x| ≤ M) :
    |∑ x ∈ Fintype.piFinset (fun i => Finset.Ico (p i) (q i)), g x -
        ∑ x ∈ Fintype.piFinset (fun i => Finset.Ico (p' i) (q' i)), g x| ≤
      M * (4 * d * ((N : ℝ) + 1) ^ (d - 1)) := by
  obtain ⟨U, hU⟩ : ∃ U : Fin d → Finset ℤ, ∀ i, U i = Finset.Ico (p i) (q i + 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin d → Finset ℤ, ∀ i, L i = Finset.Ico (p i + 1) (q i) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Bad, hBad⟩ : ∃ Bad : Finset (Site d), Bad = Finset.univ.biUnion fun i =>
      Fintype.piFinset (Function.update U i (U i \ L i)) := ⟨_, rfl⟩
  have hUcard : ∀ j, (U j).card ≤ N + 1 := by
    intro j
    rw [hU, Int.card_Ico]
    have := hlen j
    omega
  have hdiff : ∀ i, (U i \ L i).card ≤ 2 := by
    intro i
    have hsub : U i \ L i ⊆ {p i, q i} := by
      intro x hx
      rw [hU, hL] at hx
      simp only [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_insert,
        Finset.mem_singleton] at hx ⊢
      omega
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hBadcard : Bad.card ≤ 2 * d * (N + 1) ^ (d - 1) := by
    calc Bad.card
        ≤ ∑ i, (Fintype.piFinset (Function.update U i (U i \ L i))).card := by
          rw [hBad]; exact Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin d, 2 * (N + 1) ^ (d - 1) :=
          Finset.sum_le_sum fun i _ =>
            (card_slab_le U (U i \ L i) i (N + 1) hUcard).trans
              (Nat.mul_le_mul_right _ (hdiff i))
      _ = 2 * d * (N + 1) ^ (d - 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  have hsubU : ∀ A : Finset (Site d), A ⊆ Fintype.piFinset U →
      Fintype.piFinset L ⊆ A →
      |∑ x ∈ A, g x - ∑ x ∈ Fintype.piFinset L, g x| ≤ M * Bad.card := by
    intro A hA hLA
    have h1 := Finset.sum_sdiff hLA (f := g)
    have h2 : ∑ x ∈ A, g x - ∑ x ∈ Fintype.piFinset L, g x =
        ∑ x ∈ A \ Fintype.piFinset L, g x := by linarith
    have hsub : A \ Fintype.piFinset L ⊆ Bad := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxA, hxL⟩ := hx
      have hxU := Fintype.mem_piFinset.1 (hA hxA)
      rw [Fintype.mem_piFinset] at hxL
      obtain ⟨i, hi⟩ := not_forall.1 hxL
      rw [hBad]
      refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Fintype.mem_piFinset.2 fun j => ?_⟩
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        exact Finset.mem_sdiff.2 ⟨hxU j, hi⟩
      · rw [Function.update_of_ne hj]
        exact hxU j
    rw [h2]
    calc |∑ x ∈ A \ Fintype.piFinset L, g x|
        ≤ ∑ x ∈ A \ Fintype.piFinset L, |g x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ A \ Fintype.piFinset L, M := Finset.sum_le_sum fun x _ => hg x
      _ = ((A \ Fintype.piFinset L).card : ℝ) * M := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Bad.card : ℝ) * M := by
          gcongr
      _ = M * Bad.card := mul_comm _ _
  have hPU : Fintype.piFinset (fun i => Finset.Ico (p i) (q i)) ⊆ Fintype.piFinset U := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    intro i
    rw [hU]
    have := hx i
    simp only [Finset.mem_Ico] at this ⊢
    omega
  have hP'U : Fintype.piFinset (fun i => Finset.Ico (p' i) (q' i)) ⊆ Fintype.piFinset U := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    intro i
    rw [hU]
    have h1 := hx i
    have h2 := hp1 i
    have h3 := hq2 i
    simp only [Finset.mem_Ico] at h1 ⊢
    omega
  have hLP : Fintype.piFinset L ⊆ Fintype.piFinset (fun i => Finset.Ico (p i) (q i)) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    intro i
    have := hx i
    rw [hL] at this
    simp only [Finset.mem_Ico] at this ⊢
    omega
  have hLP' : Fintype.piFinset L ⊆ Fintype.piFinset (fun i => Finset.Ico (p' i) (q' i)) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    intro i
    have h1 := hx i
    have h2 := hp2 i
    have h3 := hq1 i
    rw [hL] at h1
    simp only [Finset.mem_Ico] at h1 ⊢
    omega
  have e1 := hsubU _ hPU hLP
  have e2 := hsubU _ hP'U hLP'
  have hcard : (Bad.card : ℝ) ≤ 2 * d * ((N : ℝ) + 1) ^ (d - 1) := by exact_mod_cast hBadcard
  calc _ ≤ |∑ x ∈ Fintype.piFinset (fun i => Finset.Ico (p i) (q i)), g x -
          ∑ x ∈ Fintype.piFinset L, g x| +
        |∑ x ∈ Fintype.piFinset L, g x -
          ∑ x ∈ Fintype.piFinset (fun i => Finset.Ico (p' i) (q' i)), g x| :=
        abs_sub_le _ _ _
    _ ≤ M * Bad.card + M * Bad.card := by
        rw [abs_sub_comm (∑ x ∈ Fintype.piFinset L, g x)]
        exact add_le_add e1 e2
    _ ≤ M * (4 * d * ((N : ℝ) + 1) ^ (d - 1)) := by
        have := mul_le_mul_of_nonneg_left hcard hM
        linarith

/-! ### The reflected rectangle and the floor box -/

/-- The lower corner of the reflected rectangle. -/
def reflLo (j : ℕ) (k : Site d) (S : Finset (Fin d)) (i : Fin d) : ℝ :=
  if i ∈ S then -(((k i : ℝ) + 1) / 2 ^ j) else (k i : ℝ) / 2 ^ j

/-- The upper corner of the reflected rectangle. -/
def reflHi (j : ℕ) (k : Site d) (S : Finset (Fin d)) (i : Fin d) : ℝ :=
  if i ∈ S then -((k i : ℝ) / 2 ^ j) else ((k i : ℝ) + 1) / 2 ^ j

/-- The lower endpoint of the `i`-th interval of the floor box. -/
def floorLo (j : ℕ) (k : Site d) (S : Finset (Fin d)) (N : ℕ) (i : Fin d) : ℤ :=
  if i ∈ S then ⌊(N : ℝ) * ((k i : ℝ) / 2 ^ j)⌋ + 1 else ⌈(N : ℝ) * ((k i : ℝ) / 2 ^ j)⌉

/-- The upper endpoint of the `i`-th interval of the floor box. -/
def floorHi (j : ℕ) (k : Site d) (S : Finset (Fin d)) (N : ℕ) (i : Fin d) : ℤ :=
  if i ∈ S then ⌊(N : ℝ) * (((k i : ℝ) + 1) / 2 ^ j)⌋ + 1
  else ⌈(N : ℝ) * (((k i : ℝ) + 1) / 2 ^ j)⌉

/-- The image of the reflected rectangle under `flipSubset S`: the intervals are
`(⌊N k_i 2^{-j}⌋, ⌊N (k_i + 1) 2^{-j}⌋]` for `i ∈ S` and `[⌈N k_i 2^{-j}⌉, ⌈N (k_i + 1) 2^{-j}⌉)`
for `i ∉ S`. -/
def floorBox (j : ℕ) (k : Site d) (S : Finset (Fin d)) (N : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => Finset.Ico (floorLo j k S N i) (floorHi j k S N i)

theorem mem_rectBox_refl_iff (j : ℕ) (k : Site d) (S : Finset (Fin d)) (N : ℕ) (x : Site d) :
    x ∈ rectBox (reflLo j k S) (reflHi j k S) N ↔ flipSubset S x ∈ floorBox j k S N := by
  unfold floorBox
  rw [mem_rectBox, Fintype.mem_piFinset]
  refine forall_congr' fun i => ?_
  by_cases hi : i ∈ S
  · simp only [reflLo, reflHi, floorLo, floorHi, flipSubset, hi, ite_true, Finset.mem_Ico,
      mul_neg, Int.ceil_neg]
    omega
  · simp only [reflLo, reflHi, floorLo, floorHi, flipSubset, hi, ite_false]

theorem sum_rectBox_refl (j : ℕ) (k : Site d) (S : Finset (Fin d)) (N : ℕ) (F : Site d → ℝ) :
    ∑ x ∈ rectBox (reflLo j k S) (reflHi j k S) N, F (flipSubset S x) =
      ∑ y ∈ floorBox j k S N, F y := by
  refine Finset.sum_nbij' (flipSubset S) (flipSubset S) (fun x hx => ?_) (fun y hy => ?_)
    (fun x _ => flipSubset_involutive S x) (fun y _ => flipSubset_involutive S y)
    (fun x _ => rfl)
  · exact (mem_rectBox_refl_iff j k S N x).1 hx
  · rw [mem_rectBox_refl_iff, flipSubset_involutive]
    exact hy

theorem reflLo_nonneg (j : ℕ) (k : Site d) (i : Fin d) :
    0 ≤ reflLo j k (Finset.univ.filter fun i => k i < 0) i := by
  unfold reflLo
  by_cases hi : k i < 0
  · have hk : (k i : ℝ) + 1 ≤ 0 := by
      have : k i + 1 ≤ 0 := by omega
      exact_mod_cast this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi, ite_true]
    have : ((k i : ℝ) + 1) / 2 ^ j ≤ 0 := div_nonpos_of_nonpos_of_nonneg hk (by positivity)
    linarith
  · have hk : (0 : ℝ) ≤ k i := by exact_mod_cast not_lt.1 hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi, ite_false]
    positivity

theorem reflLo_le_reflHi (j : ℕ) (k : Site d) (S : Finset (Fin d)) (i : Fin d) :
    reflLo j k S i ≤ reflHi j k S i := by
  unfold reflLo reflHi
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have h1 : (k i : ℝ) / 2 ^ j ≤ ((k i : ℝ) + 1) / 2 ^ j :=
    div_le_div_of_nonneg_right (by linarith) h2.le
  by_cases hi : i ∈ S
  · simp only [hi, ite_true]
    linarith
  · simp only [hi, ite_false]
    exact h1

/-- The dyadic cube and the floor box differ only in end layers, so bounded sums over them differ
by at most `M · 4 d (N + 1)^(d - 1)`. -/
theorem dyadic_vs_floor (j : ℕ) (k : Site d) (S : Finset (Fin d)) (N : ℕ) (g : Site d → ℝ)
    (M : ℝ) (hg : ∀ x, |g x| ≤ M) :
    |∑ x ∈ dyadicCube j k N, g x - ∑ x ∈ floorBox j k S N, g x| ≤
      M * (4 * d * ((N : ℝ) + 1) ^ (d - 1)) := by
  have hlen : ∀ i, ⌈(N : ℝ) * (((k i : ℝ) + 1) / 2 ^ j)⌉ - ⌈(N : ℝ) * ((k i : ℝ) / 2 ^ j)⌉ ≤ N := by
    intro i
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h3 : 1 / (2 : ℝ) ^ j ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h2
    have h4 : ((k i : ℝ) + 1) / 2 ^ j ≤ (k i : ℝ) / 2 ^ j + 1 := by
      rw [add_div]
      linarith
    have h5 : (N : ℝ) * (((k i : ℝ) + 1) / 2 ^ j) ≤
        (N : ℝ) * ((k i : ℝ) / 2 ^ j) + (N : ℕ) := by
      have := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      linarith
    have h6 := Int.ceil_mono h5
    rw [Int.ceil_add_natCast] at h6
    omega
  have := box_sum_diff_le (d := d) (fun i => ⌈(N : ℝ) * ((k i : ℝ) / 2 ^ j)⌉)
    (fun i => ⌈(N : ℝ) * (((k i : ℝ) + 1) / 2 ^ j)⌉) (floorLo j k S N) (floorHi j k S N) N
    (fun i => ?_) (fun i => ?_) (fun i => ?_) (fun i => ?_) hlen g M hg
  · exact this
  · unfold floorLo
    split_ifs
    · exact Int.ceil_le_floor_add_one _
    · exact le_rfl
  · unfold floorLo
    split_ifs
    · linarith [Int.floor_le_ceil ((N : ℝ) * ((k i : ℝ) / 2 ^ j))]
    · linarith
  · unfold floorHi
    split_ifs
    · exact Int.ceil_le_floor_add_one _
    · exact le_rfl
  · unfold floorHi
    split_ifs
    · linarith [Int.floor_le_ceil ((N : ℝ) * (((k i : ℝ) + 1) / 2 ^ j))]
    · linarith

/-! ### The analytic conclusion -/

theorem tendsto_div_of_close (hd : 1 ≤ d) (D T : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hT : Tendsto (fun N : ℕ => T N / (N : ℝ) ^ d) atTop (𝓝 0))
    (hDT : ∀ N : ℕ, |D N - T N| ≤ C * ((N : ℝ) + 1) ^ (d - 1)) :
    Tendsto (fun N : ℕ => D N / (N : ℝ) ^ d) atTop (𝓝 0) := by
  have hE : Tendsto (fun N : ℕ => (D N - T N) / (N : ℝ) ^ d) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => C * 2 ^ (d - 1) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ d)]
    rw [div_le_div_iff₀ (by positivity) hNpos]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have h1 : ((N : ℝ) + 1) ^ e ≤ (2 * (N : ℝ)) ^ e :=
      pow_le_pow_left₀ (by positivity) (by linarith) e
    calc |D N - T N| * N ≤ C * ((N : ℝ) + 1) ^ e * N := by
          have := hDT N
          simp only [Nat.add_sub_cancel] at this
          gcongr
      _ ≤ C * (2 * (N : ℝ)) ^ e * N := by gcongr
      _ = C * 2 ^ (e + 1 - 1) * (N : ℝ) ^ (e + 1) := by
          rw [mul_pow, Nat.add_sub_cancel, pow_succ]
          ring
  have := hT.add hE
  simp only [add_zero] at this
  refine this.congr fun N => ?_
  ring

end DivisibleHomogenize

open DivisibleHomogenize

/-- **(ergodic)**): `CubeErgodicStmt` follows from the rectangle
a.e. ergodic theorem `LatticeProb.RectangleErgodic` for `0 ≤ a ≤ b`, applied to the shift action
reflected in the coordinates `{i | k_i < 0}` on `Config d`, the bounded observable
`clamp(η(0)) - E η(0)`, and the reflected dyadic rectangle; the reflected box differs from the
dyadic cube only in two hyperplane layers per coordinate. -/
theorem cubeErgodic_of_rectangleErgodic (h : ∀ d : ℕ, 1 ≤ d → LatticeProb.RectangleErgodic d) :
    CubeErgodicStmt := by
  intro d hd E
  have hrect : ∀ (j : ℕ) (k : Site d), ∀ᵐ η ∂E.P,
      Tendsto (fun N : ℕ => (∑ x ∈ floorBox j k (Finset.univ.filter fun i => k i < 0) N,
        reflClampObs E (shift x η)) / (N : ℝ) ^ d) atTop (𝓝 0) := by
    intro j k
    obtain ⟨h1, h2, h3⟩ := reflectActionS_props (τ := shift) E.stationary
      (fun z w ω => shift_add z w ω) E.ergodic (Finset.univ.filter fun i => k i < 0)
    have := h d (by omega) E.P (reflectActionS shift (Finset.univ.filter fun i => k i < 0)) h1 h2 h3
      (reflClampObs E) (measurable_reflClampObs E) (reflClampObs_bound E)
      (reflLo j k (Finset.univ.filter fun i => k i < 0))
      (reflHi j k (Finset.univ.filter fun i => k i < 0)) (reflLo_nonneg j k)
      (reflLo_le_reflHi j k _)
    filter_upwards [this] with η hη
    rw [integral_reflClampObs, mul_zero] at hη
    refine hη.congr fun N => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_mul_eq_div]
    congr 1
    exact sum_rectBox_refl j k _ N (fun y => reflClampObs E (shift y η))
  have hall : ∀ᵐ η ∂E.P, ∀ (j : ℕ) (k : Site d),
      Tendsto (fun N : ℕ => (∑ x ∈ floorBox j k (Finset.univ.filter fun i => k i < 0) N,
        reflClampObs E (shift x η)) / (N : ℝ) ^ d) atTop (𝓝 0) :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun k => hrect j k
  obtain ⟨M, hM0, hM⟩ := reflClampObs_bound E
  filter_upwards [hall, ae_all_iff.2 E.bounded] with η hη hbd j k
  have hsum : ∀ N : ℕ, ∑ y ∈ dyadicCube j k N, ((η y : ℝ) - meanEta E.P) =
      ∑ y ∈ dyadicCube j k N, reflClampObs E (shift y η) := fun N =>
    Finset.sum_congr rfl fun x _ => (reflClampObs_shift E η x (hbd x)).symm
  have hclose := tendsto_div_of_close (by omega : 1 ≤ d)
    (fun N => ∑ y ∈ dyadicCube j k N, reflClampObs E (shift y η))
    (fun N => ∑ x ∈ floorBox j k (Finset.univ.filter fun i => k i < 0) N,
      reflClampObs E (shift x η))
    (M * (4 * d)) (by positivity) (hη j k) (fun N => by
      have := dyadic_vs_floor j k (Finset.univ.filter fun i => k i < 0) N
        (fun y => reflClampObs E (shift y η)) M (fun y => hM _)
      calc _ ≤ _ := this
        _ = _ := by ring)
  refine hclose.congr fun N => ?_
  rw [hsum]

end RandomSandpile

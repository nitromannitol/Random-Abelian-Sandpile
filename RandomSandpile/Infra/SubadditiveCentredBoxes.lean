import RandomSandpile.Infra.SubadditiveCentred
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodicAll

/-! # The subadditive ergodic theorem on every box with rational corners

This file proves `SubadditiveRationalBoxesStmt` (`Infra/SubadditiveCubes.lean`): for a
subadditive process `f` over a stationary ergodic random environment, almost surely,
simultaneously for every half-open box `Q = ∏ [pᵢ, qᵢ)` with rational corners (no sign
condition), `f(η, nQ ∩ ℤ^d) / |nQ ∩ ℤ^d| → a`, with the constant `a` of the cube limit.

* **The rectangle ergodic theorem for every box** (`rectangleErgodicAll`, Lattice-Probability's
  `RectangleErgodicAll`). A box `∏ [lᵢ, uᵢ)` is the disjoint union over `S ⊆ {1, …, d}` of its
  pieces with negative coordinates exactly `S` (`sum_ibox_eq_sum_split`); after the reflection
  `xᵢ ↦ -1 - xᵢ` (`i ∈ S`) each piece is a box in the closed positive orthant, up to a boundary
  layer of width one (floors instead of ceilings, `ibox_split_subset`), and the reflected actions
  are measure preserving and ergodic (`LatticeProb.reflectActionS_props`).
* **Deterministic core** (`tendsto_rectBox_div_pow_centred`): the argument of
  `tendsto_rectBox_div_pow` with the container `[0, NK)^d` replaced by the centred cube
  `[-NK, NK)^d`, whose limit is `ae_tendsto_centredCube` (`Infra/SubadditiveCentred.lean`).
  Upper bound: tiling of the box. Lower bound: subadditivity on the centred cube.
-/

noncomputable section

open MeasureTheory Filter Topology LatticeProb
open scoped Pointwise

namespace RandomSandpile

/-! ### Splitting a box into its reflected orthant pieces -/

section Split

variable {d : ℕ}

/-- The coordinates in which `x` is negative. -/
def negCoords (x : Site d) : Finset (Fin d) := Finset.univ.filter fun i => x i < 0

/-- Lower corner of the piece of `∏ [lᵢ, uᵢ)` with negative coordinates exactly `S`, after the
reflection `xᵢ ↦ -1 - xᵢ` for `i ∈ S`. -/
def splitLo (S : Finset (Fin d)) (l u : Site d) : Site d :=
  fun i => if i ∈ S then -min (u i) 0 else max (l i) 0

/-- Upper corner of the reflected piece (see `splitLo`). -/
def splitHi (S : Finset (Fin d)) (l u : Site d) : Site d :=
  fun i => if i ∈ S then -min (l i) 0 else max (u i) 0

theorem negCoords_eq_iff {x : Site d} {S : Finset (Fin d)} :
    negCoords x = S ↔ ∀ i, (x i < 0 ↔ i ∈ S) := by
  simp only [negCoords, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]

theorem sum_ibox_filter_negCoords {M : Type*} [AddCommMonoid M] (g : Site d → M)
    (l u : Site d) (S : Finset (Fin d)) :
    ∑ x ∈ (ibox l u).filter (fun x => negCoords x = S), g x =
      ∑ y ∈ ibox (splitLo S l u) (splitHi S l u), g (flipSubset S y - flipShift S) := by
  have hli : ∀ x ∈ (ibox l u).filter (fun x => negCoords x = S),
      flipSubset S (fun i => if x i < 0 then -x i - 1 else x i) - flipShift S = x := by
    intro x hx
    rw [Finset.mem_filter, negCoords_eq_iff] at hx
    funext k
    have h2 := hx.2 k
    simp only [Pi.sub_apply, flipSubset, flipShift]
    by_cases hk : k ∈ S
    · have : x k < 0 := h2.2 hk
      simp only [hk, if_true, this]
      omega
    · have : ¬ x k < 0 := fun h => hk (h2.1 h)
      simp only [hk, if_false, this]
      omega
  refine Finset.sum_nbij' (fun x i => if x i < 0 then -x i - 1 else x i)
    (fun y => flipSubset S y - flipShift S) ?_ ?_ hli ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, negCoords_eq_iff, mem_ibox] at hx
    rw [mem_ibox]
    intro i
    have h1 := hx.1 i
    have h2 := hx.2 i
    simp only [splitLo, splitHi, min_def, max_def]
    by_cases hi : i ∈ S
    · have : x i < 0 := h2.2 hi
      simp only [hi, if_true, this]
      split_ifs <;> omega
    · have : ¬ x i < 0 := fun h => hi (h2.1 h)
      simp only [hi, if_false, this]
      split_ifs <;> omega
  · intro y hy
    rw [mem_ibox] at hy
    rw [Finset.mem_filter, negCoords_eq_iff, mem_ibox]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h1 := hy i
      simp only [splitLo, splitHi, min_def, max_def] at h1
      simp only [Pi.sub_apply, flipSubset, flipShift]
      by_cases hi : i ∈ S
      · simp only [hi, if_true] at h1 ⊢
        split_ifs at h1 <;> omega
      · simp only [hi, if_false] at h1 ⊢
        split_ifs at h1 <;> omega
    · have h1 := hy i
      simp only [splitLo, splitHi, min_def, max_def] at h1
      simp only [Pi.sub_apply, flipSubset, flipShift]
      by_cases hi : i ∈ S
      · simp only [hi, if_true, iff_true] at h1 ⊢
        split_ifs at h1 <;> omega
      · simp only [hi, if_false, iff_false] at h1 ⊢
        split_ifs at h1 <;> omega
  · intro y hy
    rw [mem_ibox] at hy
    funext i
    have h1 := hy i
    simp only [splitLo, splitHi, min_def, max_def] at h1
    simp only [Pi.sub_apply, flipSubset, flipShift]
    by_cases hi : i ∈ S
    · simp only [hi, if_true] at h1 ⊢
      split_ifs at h1 ⊢ <;> omega
    · simp only [hi, if_false] at h1 ⊢
      split_ifs at h1 ⊢ <;> omega
  · intro x hx
    rw [hli x hx]

/-- **The reflected decomposition of a box.** `∏ [lᵢ, uᵢ)` is the disjoint union over
`S ⊆ {1, …, d}` of the reflected boxes `flipSubset S (∏ [splitLo, splitHi)) - 1_S`. -/
theorem sum_ibox_eq_sum_split {M : Type*} [AddCommMonoid M] (g : Site d → M) (l u : Site d) :
    ∑ x ∈ ibox l u, g x =
      ∑ S : Finset (Fin d), ∑ y ∈ ibox (splitLo S l u) (splitHi S l u),
        g (flipSubset S y - flipShift S) := by
  rw [← Finset.sum_fiberwise (ibox l u) negCoords g]
  exact Finset.sum_congr rfl fun S _ => sum_ibox_filter_negCoords g l u S

/-- The real corners of the reflected pieces of `∏ [pᵢ, qᵢ)`. -/
def splitA (S : Finset (Fin d)) (p q : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if i ∈ S then max (-q i) 0 else max (p i) 0

/-- See `splitA`. -/
def splitB (S : Finset (Fin d)) (p q : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if i ∈ S then max (-p i) 0 else max (q i) 0

theorem splitA_nonneg (S : Finset (Fin d)) (p q : Fin d → ℝ) (i : Fin d) :
    0 ≤ splitA S p q i := by
  unfold splitA
  split_ifs <;> exact le_max_right _ _

theorem splitA_le_splitB (S : Finset (Fin d)) {p q : Fin d → ℝ} (hpq : ∀ i, p i ≤ q i)
    (i : Fin d) : splitA S p q i ≤ splitB S p q i := by
  unfold splitA splitB
  have := hpq i
  split_ifs
  · exact max_le_max (by linarith) le_rfl
  · exact max_le_max this le_rfl

theorem sum_prod_split (p q : Fin d → ℝ) :
    ∑ S : Finset (Fin d), ∏ i, (splitB S p q i - splitA S p q i) = ∏ i, (q i - p i) := by
  set u : Fin d → ℝ := fun i => max (-p i) 0 - max (-q i) 0 with hu
  set v : Fin d → ℝ := fun i => max (q i) 0 - max (p i) 0 with hv
  have h : ∀ i, q i - p i = u i + v i := by
    intro i
    have h1 := max_zero_sub_max_neg_zero_eq_self (q i)
    have h2 := max_zero_sub_max_neg_zero_eq_self (p i)
    simp only [hu, hv]
    linarith
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.compl_eq_univ_sdiff, ← Finset.prod_mul_prod_compl S]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp only [splitA, splitB, hi, if_true, hu]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_compl] at hi
    simp only [splitA, splitB, hi, if_false, hv]

theorem ceil_mul_max_zero (N : ℕ) (x : ℝ) :
    ⌈(N : ℝ) * max x 0⌉ = max ⌈(N : ℝ) * x⌉ 0 := by
  rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg N), mul_zero, Int.ceil_mono.map_max, Int.ceil_zero]

theorem ceil_mul_max_neg_zero (N : ℕ) (x : ℝ) :
    ⌈(N : ℝ) * max (-x) 0⌉ = max (-⌊(N : ℝ) * x⌋) 0 := by
  rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg N), mul_zero, mul_neg, Int.ceil_mono.map_max,
    Int.ceil_zero, Int.ceil_neg]

theorem ibox_mono {l l' u u' : Site d} (hl : ∀ i, l' i ≤ l i) (hu : ∀ i, u i ≤ u' i) :
    ibox l u ⊆ ibox l' u' := by
  intro x hx
  rw [mem_ibox] at hx ⊢
  exact fun i => ⟨(hl i).trans (hx i).1, (hx i).2.trans_le (hu i)⟩

/-- **Floor-ceiling sandwich.** The reflected piece lies between the boxes
`∏ [⌈N aᵢ⌉, ⌈N bᵢ⌉ - 1)` and `∏ [⌈N aᵢ⌉ - 1, ⌈N bᵢ⌉)`, `a = splitA S p q`, `b = splitB S p q`. -/
theorem ibox_split_subset (S : Finset (Fin d)) (p q : Fin d → ℝ) (N : ℕ) :
    ibox (fun i => ⌈(N : ℝ) * splitA S p q i⌉ + 0) (fun i => ⌈(N : ℝ) * splitB S p q i⌉ + -1) ⊆
      ibox (splitLo S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉))
        (splitHi S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉)) ∧
    ibox (splitLo S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉))
        (splitHi S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉)) ⊆
      ibox (fun i => ⌈(N : ℝ) * splitA S p q i⌉ + -1) (fun i => ⌈(N : ℝ) * splitB S p q i⌉ + 0) := by
  have key : ∀ i, (⌈(N : ℝ) * splitA S p q i⌉ - 1 ≤
        splitLo S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉) i ∧
      splitLo S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉) i ≤
        ⌈(N : ℝ) * splitA S p q i⌉) ∧
      (⌈(N : ℝ) * splitB S p q i⌉ - 1 ≤
        splitHi S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉) i ∧
      splitHi S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉) i ≤
        ⌈(N : ℝ) * splitB S p q i⌉) := by
    intro i
    have fp := Int.floor_le_ceil ((N : ℝ) * p i)
    have cp := Int.ceil_le_floor_add_one ((N : ℝ) * p i)
    have fq := Int.floor_le_ceil ((N : ℝ) * q i)
    have cq := Int.ceil_le_floor_add_one ((N : ℝ) * q i)
    by_cases hi : i ∈ S
    · simp only [splitA, splitB, splitLo, splitHi, hi, if_true, ceil_mul_max_neg_zero]
      simp only [min_def, max_def]
      split_ifs <;> omega
    · simp only [splitA, splitB, splitLo, splitHi, hi, if_false, ceil_mul_max_zero]
      omega
  constructor
  · exact ibox_mono (fun i => by have := (key i).1.2; omega) (fun i => by have := (key i).2.1; omega)
  · exact ibox_mono (fun i => by have := (key i).1.1; omega) (fun i => by have := (key i).2.2; omega)

/-- Sums of a bounded function over two sets squeezed between `I ⊆ O` differ by at most
`2 M (|O| - |I|)`. -/
theorem abs_sum_sub_sum_le {α : Type*} [DecidableEq α] {I Y R O : Finset α} (hIY : I ⊆ Y)
    (hYO : Y ⊆ O) (hIR : I ⊆ R) (hRO : R ⊆ O) {F : α → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ x, |F x| ≤ M) :
    |∑ x ∈ Y, F x - ∑ x ∈ R, F x| ≤ 2 * M * ((O.card : ℝ) - I.card) := by
  have bd : ∀ T : Finset α, T ⊆ O → I ⊆ T →
      |∑ x ∈ T \ I, F x| ≤ M * ((O.card : ℝ) - I.card) := by
    intro T hTO hIT
    have h1 : ((T \ I).card : ℝ) + I.card = T.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hIT
    have h2 : (T.card : ℝ) ≤ O.card := by exact_mod_cast Finset.card_le_card hTO
    calc |∑ x ∈ T \ I, F x| ≤ ∑ x ∈ T \ I, |F x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ T \ I, M := Finset.sum_le_sum fun x _ => hF x
      _ = M * ((T \ I).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ M * ((O.card : ℝ) - I.card) := mul_le_mul_of_nonneg_left (by linarith) hM
  have hY := Finset.sum_sdiff (f := F) hIY
  have hR := Finset.sum_sdiff (f := F) hIR
  obtain ⟨a1, a2⟩ := abs_le.1 (bd Y hYO hIY)
  obtain ⟨b1, b2⟩ := abs_le.1 (bd R hRO hIR)
  exact abs_le.2 ⟨by linarith, by linarith⟩

end Split

/-! ### The rectangle ergodic theorem along every box -/

section Ergodic

variable {d : ℕ}

/-- **The rectangle ergodic theorem along every box** (`LatticeProb.RectangleErgodicAll`): for a
measure preserving ergodic `ℤ^d`-action and a bounded measurable `h`, almost surely
`N^{-d} ∑_{x ∈ ∏ [⌈N pᵢ⌉, ⌈N qᵢ⌉)} h(τ_x ω) → |Q| ∫ h` for every `p ≤ q` (no sign condition).
The box is the union of its `2^d` reflected orthant pieces (`sum_ibox_eq_sum_split`); each is,
up to a boundary layer of width one (`ibox_split_subset`), a box in the closed positive orthant
for the reflected action `reflectActionS τ S`, evaluated at `τ_{-1_S} ω`. -/
theorem rectangleErgodicAll (hd : 1 ≤ d) : RectangleErgodicAll d := by
  intro Ω _ μ _ τ h1 h2 h3 h hm hb p q hpq
  obtain ⟨M, hM0, hM⟩ := hb
  have hS : ∀ S : Finset (Fin d), ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ =>
      (∑ y ∈ ibox (splitLo S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉))
        (splitHi S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉)),
        h (τ (flipSubset S y - flipShift S) ω)) / (N : ℝ) ^ d) atTop
      (𝓝 ((∏ i, (splitB S p q i - splitA S p q i)) * ∫ ω, h ω ∂μ)) := by
    intro S
    obtain ⟨g1, g2, g3⟩ := reflectActionS_props h1 h2 h3 S
    have hR := rectangleErgodic hd μ (reflectActionS τ S) g1 g2 g3 h hm ⟨M, hM0, hM⟩
      (splitA S p q) (splitB S p q) (splitA_nonneg S p q) (splitA_le_splitB S hpq)
    have hT := (h1 (-flipShift S)).quasiMeasurePreserving.ae hR
    filter_upwards [hT] with ω hω
    set F : Site d → ℝ := fun y => h (τ (flipSubset S y - flipShift S) ω) with hF
    have hFb : ∀ y, |F y| ≤ M := fun y => hM _
    have hω' : Tendsto (fun N : ℕ => (∑ y ∈ rectBox (splitA S p q) (splitB S p q) N, F y) /
        (N : ℝ) ^ d) atTop (𝓝 ((∏ i, (splitB S p q i - splitA S p q i)) * ∫ ω, h ω ∂μ)) := by
      refine hω.congr' (Eventually.of_forall fun N => ?_)
      rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_mul_eq_div]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [hF, reflectActionS]
      rw [sub_eq_add_neg, h2]
    have hO := tendsto_card_ibox_div_pow (splitA S p q) (splitB S p q)
      (splitA_le_splitB S hpq) (-1) 0
    have hI := tendsto_card_ibox_div_pow (splitA S p q) (splitB S p q)
      (splitA_le_splitB S hpq) 0 (-1)
    have h0 : Tendsto (fun N : ℕ => 2 * M *
        (((ibox (fun i => ⌈(N : ℝ) * splitA S p q i⌉ + -1)
          (fun i => ⌈(N : ℝ) * splitB S p q i⌉ + 0)).card : ℝ) / (N : ℝ) ^ d -
        ((ibox (fun i => ⌈(N : ℝ) * splitA S p q i⌉ + 0)
          (fun i => ⌈(N : ℝ) * splitB S p q i⌉ + -1)).card : ℝ) / (N : ℝ) ^ d)) atTop (𝓝 0) := by
      have := (hO.sub hI).const_mul (2 * M)
      rwa [sub_self, mul_zero] at this
    have hdiff : Tendsto (fun N : ℕ =>
        (∑ y ∈ ibox (splitLo S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉))
          (splitHi S (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉)), F y) / (N : ℝ) ^ d -
        (∑ y ∈ rectBox (splitA S p q) (splitB S p q) N, F y) / (N : ℝ) ^ d) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
      obtain ⟨hIY, hYO⟩ := ibox_split_subset S p q N
      have hIR : ibox (fun i => ⌈(N : ℝ) * splitA S p q i⌉ + 0)
          (fun i => ⌈(N : ℝ) * splitB S p q i⌉ + -1) ⊆
          rectBox (splitA S p q) (splitB S p q) N := by
        rw [rectBox_eq_ibox]
        exact ibox_mono (fun i => by omega) (fun i => by omega)
      have hRO : rectBox (splitA S p q) (splitB S p q) N ⊆
          ibox (fun i => ⌈(N : ℝ) * splitA S p q i⌉ + -1)
            (fun i => ⌈(N : ℝ) * splitB S p q i⌉ + 0) := by
        rw [rectBox_eq_ibox]
        exact ibox_mono (fun i => by omega) (fun i => by omega)
      have hb := abs_sum_sub_sum_le hIY hYO hIR hRO hM0 hFb
      rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hNpos]
      calc _ ≤ 2 * M * (((ibox (fun i => ⌈(N : ℝ) * splitA S p q i⌉ + -1)
            (fun i => ⌈(N : ℝ) * splitB S p q i⌉ + 0)).card : ℝ) -
            ((ibox (fun i => ⌈(N : ℝ) * splitA S p q i⌉ + 0)
              (fun i => ⌈(N : ℝ) * splitB S p q i⌉ + -1)).card : ℝ)) / (N : ℝ) ^ d :=
            div_le_div_of_nonneg_right hb hNpos.le
        _ = _ := by ring
    have := hω'.add hdiff
    rw [add_zero] at this
    refine this.congr fun N => ?_
    ring
  rw [← ae_all_iff] at hS
  filter_upwards [hS] with ω hω
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Finset (Fin d))) fun S _ => hω S
  rw [← Finset.sum_mul, sum_prod_split] at hsum
  refine hsum.congr' (Eventually.of_forall fun N => ?_)
  simp only
  rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_mul_eq_div, rectBox_eq_ibox,
    sum_ibox_eq_sum_split (fun x => h (τ x ω)), Finset.sum_div]

end Ergodic

/-! ### The deterministic core with a centred container -/

section CentredBoxes

variable {d : ℕ}

theorem ceil_nat_mul_neg (N K : ℕ) : ⌈(N : ℝ) * -(K : ℝ)⌉ = -((N : ℤ) * K) := by
  have : (N : ℝ) * -(K : ℝ) = ((-((N : ℤ) * K) : ℤ) : ℝ) := by push_cast; ring
  rw [this, Int.ceil_intCast]

theorem ceil_nat_mul_nat (N K : ℕ) : ⌈(N : ℝ) * (K : ℝ)⌉ = (N : ℤ) * K := by
  rw [← Nat.cast_mul, Int.ceil_natCast]
  push_cast
  ring

theorem centredCube_mul_eq_ibox (N K : ℕ) :
    centredCube (d := d) (N * K) = ibox (fun _ => -((N : ℤ) * K)) (fun _ => (N : ℤ) * K) := by
  simp only [centredCube, Nat.cast_mul]

theorem rectBox_neg_nat_eq_centredCube (K N : ℕ) :
    rectBox (d := d) (fun _ => -(K : ℝ)) (fun _ => (K : ℝ)) N = centredCube (N * K) := by
  rw [rectBox_eq_ibox, centredCube_mul_eq_ibox]
  simp only [ceil_nat_mul_neg, ceil_nat_mul_nat]

/-- **Deterministic core of the box limit, centred container.** Let `g ∈ 𝓜_C` with
`g([-n, n)^d) / (2n)^d → a`, let `m k / k^d → a`, and let `-K ≤ p ≤ q ≤ K` with `K ≥ 1` an
integer. Suppose that for every `k ≥ 1` the cell sums `N^{-d} ∑_{x ∈ B} g(x + [0, k)^d)` over
`B = ∏ [⌈N pᵢ⌉, ⌈N qᵢ⌉)` and over `[-NK, NK)^d` tend to `|Q| m k` and `(2K)^d m k`. Then
`g(∏ [⌈N pᵢ⌉, ⌈N qᵢ⌉)) / N^d → |Q| a`. The proof is that of `tendsto_rectBox_div_pow`, with the
container `[0, NK)^d` replaced by `[-NK, NK)^d`: upper bound by the tiling inequality on `B`,
lower bound by subadditivity on `[-NK, NK)^d = B ∪ ([-NK, NK)^d \ B)` and the tiling inequality
on the complement. -/
theorem tendsto_rectBox_div_pow_centred {C : ℝ} {g : Set (Site d) → ℝ}
    (hg : g ∈ subadditiveClass d C) {a : ℝ}
    (hcube : Tendsto (fun n : ℕ => g ↑(centredCube (d := d) n) / ((2 * n : ℕ) : ℝ) ^ d) atTop
      (𝓝 a))
    {m : ℕ → ℝ} (hm : Tendsto (fun k : ℕ => m k / (k : ℝ) ^ d) atTop (𝓝 a))
    {p q : Fin d → ℝ} (hpq : ∀ i, p i ≤ q i) {K : ℕ} (hK : 1 ≤ K)
    (hpK : ∀ i, -(K : ℝ) ≤ p i) (hqK : ∀ i, q i ≤ K)
    (hB : ∀ k, 1 ≤ k → Tendsto (fun N : ℕ => (∑ x ∈ rectBox p q N, g ↑(cell k x)) / (N : ℝ) ^ d)
      atTop (𝓝 ((∏ i, (q i - p i)) * m k)))
    (hA : ∀ k, 1 ≤ k → Tendsto (fun N : ℕ =>
      (∑ x ∈ centredCube (d := d) (N * K), g ↑(cell k x)) / (N : ℝ) ^ d)
      atTop (𝓝 ((2 * (K : ℝ)) ^ d * m k))) :
    Tendsto (fun N : ℕ => g ↑(rectBox p q N) / (N : ℝ) ^ d) atTop
      (𝓝 ((∏ i, (q i - p i)) * a)) := by
  set V := ∏ i, (q i - p i) with hV
  have hC0 := nonneg_of_mem_subadditiveClass hg
  have hg0 : ∀ A : Finset (Site d), 0 ≤ g ↑A ∧ g ↑A ≤ C * A.card := fun A => by
    have h := hg.2 ↑A (Finset.finite_toSet A)
    rwa [Set.ncard_coe_finset] at h
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.2 (by omega)
  have hvol : ∀ α β : ℤ, Tendsto (fun N : ℕ => ((ibox (fun i => ⌈(N : ℝ) * p i⌉ + α)
      (fun i => ⌈(N : ℝ) * q i⌉ + β)).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 V) :=
    fun α β => tendsto_card_ibox_div_pow p q hpq α β
  have hvolB : Tendsto (fun N : ℕ => ((rectBox p q N).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 V) := by
    have h := hvol 0 0
    simp only [add_zero] at h
    exact h
  have hvolB1 : ∀ k : ℕ, Tendsto (fun N : ℕ => ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
      (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 V) := by
    intro k
    have h := hvol 0 (1 - (k : ℤ))
    simp only [add_zero] at h
    exact h
  have hvolB2 : ∀ k : ℕ, Tendsto (fun N : ℕ => ((ibox (fun i => ⌈(N : ℝ) * p i⌉ + (1 - (k : ℤ)))
      (fun i => ⌈(N : ℝ) * q i⌉)).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 V) := by
    intro k
    have h := hvol (1 - (k : ℤ)) 0
    simp only [add_zero] at h
    exact h
  have hvolA : ∀ β : ℤ, Tendsto (fun N : ℕ => ((ibox (d := d) (fun _ => -((N : ℤ) * K))
      (fun _ => (N : ℤ) * K + β)).card : ℝ) / (N : ℝ) ^ d) atTop
      (𝓝 ((2 * (K : ℝ)) ^ d)) := by
    intro β
    have h := tendsto_card_ibox_div_pow (d := d) (fun _ => -(K : ℝ)) (fun _ => (K : ℝ))
      (fun _ => by linarith) 0 β
    simp only [ceil_nat_mul_neg, ceil_nat_mul_nat, add_zero, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, sub_neg_eq_add] at h
    rw [two_mul]
    exact h
  have hvolA0 : Tendsto (fun N : ℕ => ((ibox (d := d) (fun _ => -((N : ℤ) * K))
      (fun _ => (N : ℤ) * K)).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 ((2 * (K : ℝ)) ^ d)) := by
    have h := hvolA 0
    simp only [add_zero] at h
    exact h
  refine tendsto_of_upper_lower (fun k => V * (m k / (k : ℝ) ^ d))
    (fun k => (2 * (K : ℝ)) ^ d * a - ((2 * (K : ℝ)) ^ d - V) * (m k / (k : ℝ) ^ d)) ?_ ?_ ?_ ?_
  · exact tendsto_const_nhds.mul hm
  · have h := (tendsto_const_nhds (x := (2 * (K : ℝ)) ^ d * a)).sub
      ((tendsto_const_nhds (x := (2 * (K : ℝ)) ^ d - V)).mul hm)
    convert h using 2
    ring
  · -- upper bound: tiling of `B`
    intro k hk
    have hkpos : (0 : ℝ) < (k : ℝ) ^ d := by positivity
    refine ⟨fun N => (∑ x ∈ rectBox p q N, g ↑(cell k x)) / (N : ℝ) ^ d / (k : ℝ) ^ d +
      C * (((rectBox p q N).card : ℝ) / (N : ℝ) ^ d - ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
        (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ) / (N : ℝ) ^ d), ?_, ?_⟩
    · have h := ((hB k hk).div_const ((k : ℝ) ^ d)).add
        ((tendsto_const_nhds (x := C)).mul (hvolB.sub (hvolB1 k)))
      convert h using 2
      ring
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
      have ht := subadditive_tiling_le hg (rectBox p q N) hk
      have hsum : ∑ z ∈ innerSites k (rectBox p q N), g ↑(cell k z) ≤
          ∑ x ∈ rectBox p q N, g ↑(cell k x) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x _ _ => (hg0 _).1)
      have hsub : ibox (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ))) ⊆
          innerSites k (rectBox p q N) :=
        ibox_add_subset_innerSites hk (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉)
      have hin : ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
          (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ) ≤
          (innerSites k (rectBox p q N)).card := by
        exact_mod_cast Finset.card_le_card hsub
      have hCk := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ C * (k : ℝ) ^ d)
      have key : (k : ℝ) ^ d * g ↑(rectBox p q N) ≤ ∑ x ∈ rectBox p q N, g ↑(cell k x) +
          C * (k : ℝ) ^ d * (((rectBox p q N).card : ℝ) - ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
            (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ)) := by
        linarith
      have key' : g ↑(rectBox p q N) ≤ (∑ x ∈ rectBox p q N, g ↑(cell k x)) / (k : ℝ) ^ d +
          C * (((rectBox p q N).card : ℝ) - ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
            (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ)) := by
        rw [div_add' _ _ _ hkpos.ne', le_div_iff₀ hkpos]
        linarith
      calc g ↑(rectBox p q N) / (N : ℝ) ^ d
          ≤ ((∑ x ∈ rectBox p q N, g ↑(cell k x)) / (k : ℝ) ^ d +
            C * (((rectBox p q N).card : ℝ) - ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
              (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ))) / (N : ℝ) ^ d :=
            div_le_div_of_nonneg_right key' hNpos.le
        _ = _ := by ring
  · -- lower bound: `[-NK, NK)^d = B ∪ ([-NK, NK)^d \ B)`
    intro k hk
    have hkpos : (0 : ℝ) < (k : ℝ) ^ d := by positivity
    have hcubeK : Tendsto (fun N : ℕ => g ↑(centredCube (d := d) (N * K)) / (N : ℝ) ^ d) atTop
        (𝓝 ((2 * (K : ℝ)) ^ d * a)) := by
      have h1 : Tendsto (fun N : ℕ => N * K) atTop atTop :=
        tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_right N hK) tendsto_id
      have h2 := (hcube.comp h1).const_mul ((2 * (K : ℝ)) ^ d)
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
      have hK2 : (0 : ℝ) < (2 * (K : ℝ)) ^ d := by positivity
      simp only [Function.comp_apply]
      push_cast
      rw [show (2 * ((N : ℝ) * K)) = (2 * K) * N by ring, mul_pow]
      field_simp
      ring
    refine ⟨fun N => g ↑(centredCube (d := d) (N * K)) / (N : ℝ) ^ d -
      ((∑ x ∈ centredCube (d := d) (N * K), g ↑(cell k x)) / (N : ℝ) ^ d -
        (∑ x ∈ rectBox p q N, g ↑(cell k x)) / (N : ℝ) ^ d) / (k : ℝ) ^ d -
      C * ((((ibox (d := d) (fun _ => -((N : ℤ) * K)) (fun _ => (N : ℤ) * K)).card : ℝ) /
            (N : ℝ) ^ d -
          ((ibox (d := d) (fun _ => -((N : ℤ) * K))
            (fun _ => (N : ℤ) * K + (1 - (k : ℤ)))).card : ℝ) /
            (N : ℝ) ^ d) +
        (((ibox (fun i => ⌈(N : ℝ) * p i⌉ + (1 - (k : ℤ))) (fun i => ⌈(N : ℝ) * q i⌉)).card
          : ℝ) / (N : ℝ) ^ d - ((rectBox p q N).card : ℝ) / (N : ℝ) ^ d)), ?_, ?_⟩
    · have h := (hcubeK.sub (((hA k hk).sub (hB k hk)).div_const ((k : ℝ) ^ d))).sub
        ((tendsto_const_nhds (x := C)).mul ((hvolA0.sub (hvolA (1 - (k : ℤ)))).add
          ((hvolB2 k).sub hvolB)))
      convert h using 2
      ring
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
      set A := ibox (d := d) (fun _ => -((N : ℤ) * K)) (fun _ => (N : ℤ) * K) with hA_def
      have hAc : A = centredCube (d := d) (N * K) := (centredCube_mul_eq_ibox N K).symm
      have hBA : rectBox p q N ⊆ A := by
        intro x hx
        rw [rectBox_eq_ibox, mem_ibox] at hx
        rw [hA_def, mem_ibox]
        intro i
        have h1 : -((N : ℤ) * K) ≤ ⌈(N : ℝ) * p i⌉ := by
          rw [← ceil_nat_mul_neg N K]
          exact Int.ceil_mono (mul_le_mul_of_nonneg_left (hpK i) (Nat.cast_nonneg N))
        have h2 : ⌈(N : ℝ) * q i⌉ ≤ (N : ℤ) * K := by
          rw [← ceil_nat_mul_nat N K]
          exact Int.ceil_mono (mul_le_mul_of_nonneg_left (hqK i) (Nat.cast_nonneg N))
        have := hx i
        constructor <;> omega
      have hsplit := subadditive_union hg.1
        (Finset.disjoint_sdiff : Disjoint (rectBox p q N) (A \ rectBox p q N))
      rw [Finset.union_sdiff_of_subset hBA] at hsplit
      have ht := subadditive_tiling_le hg (A \ rectBox p q N) hk
      have hsumT : ∑ z ∈ innerSites k (A \ rectBox p q N), g ↑(cell k z) ≤
          ∑ x ∈ A \ rectBox p q N, g ↑(cell k x) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x _ _ => (hg0 _).1)
      have hTsum : ∑ x ∈ A \ rectBox p q N, g ↑(cell k x) =
          ∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x) :=
        Finset.sum_sdiff_eq_sub hBA
      have hbd : ((A \ rectBox p q N).card : ℝ) -
          (innerSites k (A \ rectBox p q N)).card ≤
          (((A.card : ℝ) - (ibox (d := d) (fun _ => -((N : ℤ) * K))
            (fun _ => (N : ℤ) * K + (1 - (k : ℤ)))).card)
            + (((ibox (fun i => ⌈(N : ℝ) * p i⌉ + (1 - (k : ℤ))) (fun i => ⌈(N : ℝ) * q i⌉)).card
              : ℝ) - (rectBox p q N).card)) :=
        card_sdiff_innerSites_sdiff_le hk (fun _ => -((N : ℤ) * K)) (fun _ => (N : ℤ) * K)
          (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉)
      have hCk := mul_le_mul_of_nonneg_left hbd (by positivity : (0 : ℝ) ≤ C * (k : ℝ) ^ d)
      set bd := ((A.card : ℝ) - (ibox (d := d) (fun _ => -((N : ℤ) * K))
        (fun _ => (N : ℤ) * K + (1 - (k : ℤ)))).card) +
        (((ibox (fun i => ⌈(N : ℝ) * p i⌉ + (1 - (k : ℤ))) (fun i => ⌈(N : ℝ) * q i⌉)).card
          : ℝ) - (rectBox p q N).card) with hbd_def
      have key : (k : ℝ) ^ d * g ↑(A \ rectBox p q N) ≤
          (∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x)) +
            C * (k : ℝ) ^ d * bd := by
        rw [← hTsum]
        linarith
      have key' : g ↑(A \ rectBox p q N) ≤
          (∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x)) / (k : ℝ) ^ d +
            C * bd := by
        rw [div_add' _ _ _ hkpos.ne', le_div_iff₀ hkpos]
        linarith
      have hlow : g ↑A - (∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x)) /
          (k : ℝ) ^ d - C * bd ≤ g ↑(rectBox p q N) := by
        linarith
      rw [← hAc]
      calc _ = (g ↑A - (∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x)) /
            (k : ℝ) ^ d - C * bd) / (N : ℝ) ^ d := by
            rw [hbd_def]
            ring
        _ ≤ g ↑(rectBox p q N) / (N : ℝ) ^ d := div_le_div_of_nonneg_right hlow hNpos.le


end CentredBoxes

/-! ### Almost sure limits along every rational box -/

section RationalBoxesAll

variable {d : ℕ} {C : ℝ} {f : Config d → Set (Site d) → ℝ}

/-- The rectangle ergodic theorem along every rational box for the cube values
`η ↦ f(η, [0, k)^d)`, in the form of cell sums `∑_{x ∈ B} f(η, x + [0, k)^d)`. -/
theorem ae_tendsto_sum_cell_all (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) (k : ℕ) (p q : Fin d → ℚ) :
    ∀ᵐ η ∂E.P, (∀ i, p i ≤ q i) →
      Tendsto (fun N : ℕ => (∑ x ∈ rectBox (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) N,
        f η ↑(cell k x)) / (N : ℝ) ^ d) atTop
        (𝓝 ((∏ i, ((q i : ℝ) - p i)) * ∫ η, f η ↑(latticeCube d k) ∂E.P)) := by
  haveI := E.isProb
  by_cases hpq : ∀ i, p i ≤ q i
  · have hbk : ∀ η, 0 ≤ f η ↑(latticeCube d k) ∧
        f η ↑(latticeCube d k) ≤ C * ((latticeCube d k).card : ℝ) :=
      fun η => finsetProcess_bd hf (latticeCube d k) η
    have hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ η, |f η ↑(latticeCube d k)| ≤ M := by
      refine ⟨C * ((latticeCube d k).card : ℝ), (hbk 0).1.trans (hbk 0).2, fun η => ?_⟩
      rw [abs_of_nonneg (hbk η).1]
      exact (hbk η).2
    have h := rectangleErgodicAll hd E.P shift E.stationary (fun z w η => shift_add z w η)
      E.ergodic (fun η => f η ↑(latticeCube d k)) (finsetProcess_measurable hf _) hbdd
      (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) (fun i => by exact_mod_cast hpq i)
    filter_upwards [h] with η hη _
    refine hη.congr' (Eventually.of_forall fun N => ?_)
    rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_mul_eq_div]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hf.stationary x _ (Finset.finite_toSet _), cell, coe_map_addRight]
  · exact Eventually.of_forall fun η h => absurd h hpq

/-- **Almost sure limits along every rational box.** Almost surely, simultaneously for every pair
of rational vectors `p ≤ q` (no sign condition), `f(η, ∏ [⌈N pᵢ⌉, ⌈N qᵢ⌉)) / N^d → ∏ (qᵢ - pᵢ) · a`,
with `a` the constant of `exists_ae_tendsto_cube_const`. The inputs are the centred cube limit
`ae_tendsto_centredCube` and the cell sums `ae_tendsto_sum_cell_all`. -/
theorem ae_tendsto_rectBox_all (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ C ∧ ∀ᵐ η ∂E.P, ∀ p q : Fin d → ℚ, (∀ i, p i ≤ q i) →
      Tendsto (fun N : ℕ => f η ↑(rectBox (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) N) /
        (N : ℝ) ^ d) atTop (𝓝 ((∏ i, ((q i : ℝ) - p i)) * a)) := by
  obtain ⟨a, ha0, haC, hcube⟩ := exists_ae_tendsto_cube_const hd E hf
  refine ⟨a, ha0, haC, ?_⟩
  have hm := tendsto_integral_cube_div_pow hd E hf hcube
  have hcc := ae_tendsto_centredCube hd E hf ha0 hcube
  have hE : ∀ᵐ η ∂E.P, ∀ (k : ℕ) (p q : Fin d → ℚ), (∀ i, p i ≤ q i) →
      Tendsto (fun N : ℕ => (∑ x ∈ rectBox (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) N,
        f η ↑(cell k x)) / (N : ℝ) ^ d) atTop
        (𝓝 ((∏ i, ((q i : ℝ) - p i)) * ∫ η, f η ↑(latticeCube d k) ∂E.P)) := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro p
    rw [ae_all_iff]
    intro q
    exact ae_tendsto_sum_cell_all hd E hf k p q
  filter_upwards [hcc, hE] with η hη hEη p q hpq
  obtain ⟨M, hM⟩ := Finite.exists_le (fun i => |(p i : ℝ)| + |(q i : ℝ)|)
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge M
  have hK1 : 1 ≤ K₀ + 1 := by omega
  have hqK : ∀ i, (q i : ℝ) ≤ ((K₀ + 1 : ℕ) : ℝ) := fun i => by
    have h1 := hM i
    have h2 := le_abs_self (q i : ℝ)
    have h3 := abs_nonneg (p i : ℝ)
    push_cast
    linarith
  have hpK : ∀ i, -((K₀ + 1 : ℕ) : ℝ) ≤ (p i : ℝ) := fun i => by
    have h1 := hM i
    have h2 := neg_abs_le (p i : ℝ)
    have h3 := abs_nonneg (q i : ℝ)
    push_cast
    linarith
  refine tendsto_rectBox_div_pow_centred (hf.mem η) hη hm (fun i => by exact_mod_cast hpq i)
    hK1 hpK hqK (fun k _ => hEη k p q hpq) (fun k _ => ?_)
  have h0 : ∀ _i : Fin d, -((K₀ + 1 : ℕ) : ℚ) ≤ ((K₀ + 1 : ℕ) : ℚ) := fun _ => by
    have : (0 : ℚ) ≤ ((K₀ + 1 : ℕ) : ℚ) := Nat.cast_nonneg _
    linarith
  have h := hEη k (fun _ => -((K₀ + 1 : ℕ) : ℚ)) (fun _ => ((K₀ + 1 : ℕ) : ℚ)) h0
  simp only [Rat.cast_neg, Rat.cast_natCast, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, sub_neg_eq_add, rectBox_neg_nat_eq_centredCube] at h
  rw [two_mul]
  exact h

/-- **The box statement** `SubadditiveRationalBoxesStmt` holds: almost surely, simultaneously for
every half-open box with rational corners, `f(η, nQ ∩ ℤ^d) / |nQ ∩ ℤ^d| → a`. -/
theorem subadditiveRationalBoxes : SubadditiveRationalBoxesStmt := by
  intro d hd E C f hf
  obtain ⟨a, ha0, haC, h⟩ := ae_tendsto_rectBox_all hd E hf
  refine ⟨a, ha0, haC, ?_⟩
  filter_upwards [h] with η hη p q hpq
  have hlim := hη p q (fun i => (hpq i).le)
  have hVpos : 0 < ∏ i, ((q i : ℝ) - p i) :=
    Finset.prod_pos fun i _ => sub_pos.2 (by exact_mod_cast hpq i)
  have hvol := tendsto_card_ibox_div_pow (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
    (fun i => by exact_mod_cast (hpq i).le) 0 0
  simp only [add_zero] at hvol
  have h2 := hlim.div hvol hVpos.ne'
  rw [mul_div_cancel_left₀ _ hVpos.ne'] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  rw [discretize_ratBox p q hN, Set.ncard_coe_finset]
  exact div_div_div_cancel_right₀ hNpos.ne' _ _

end RationalBoxesAll

end RandomSandpile

import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeCore

/-!
# The summed (difference) estimate of Lemma 7.3 from the pointwise one

The summed (difference) estimate of Lemma 7.3 from the pointwise one,
`paper/random_piles-corrected.tex` and 1166-1185, via the lattice sum
`∑_{|z|_∞ ≤ R} (1 + |z|)^{1-d} ≤ 2^d d (R + 1)`.

* `DivisibleHomogenize.sum_box_le'` is the lattice sum, proved by induction on `R`: the shell
  `[-(R+1), R+1]^d \ [-R, R]^d` has at most `2 d (2R+3)^{d-1}` points, each at distance at least
  `R + 1` from the origin.
* `greenBallGradientSum_of_difference` sums the pointwise bound `GreenBallDifferenceStmt` over
  `y ∈ B_{(1-δ)n}`, mapping `y ↦ x - y` into the box `[-2n, 2n]^d`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

variable {d : ℕ}

namespace DivisibleHomogenize

open OdometerLowerBound

/-! ### The lattice sum -/

/-- The cube `[-R, R]^d ∩ ℤ^d`. -/
def box (d R : ℕ) : Finset (Site d) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R

theorem mem_box {R : ℕ} {z : Site d} : z ∈ box d R ↔ ∀ i, |z i| ≤ R := by
  simp [box, Fintype.mem_piFinset, abs_le]

theorem box_subset_box {R S : ℕ} (h : R ≤ S) : box d R ⊆ box d S := by
  intro z hz
  rw [mem_box] at hz ⊢
  exact fun i => (hz i).trans (by exact_mod_cast h)

theorem card_box (d R : ℕ) : (box d R).card = (2 * R + 1) ^ d := by
  simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  omega

/-- `a^(k+1) - b^(k+1) ≤ (k+1) (a - b) a^k` for `0 ≤ b ≤ a`. -/
theorem pow_succ_sub_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (k : ℕ) :
    a ^ (k + 1) - b ^ (k + 1) ≤ (k + 1) * (a - b) * a ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : b ^ (k + 1) ≤ a ^ (k + 1) := pow_le_pow_left₀ hb hab _
    have ha : 0 ≤ a := hb.trans hab
    have h2 := mul_le_mul_of_nonneg_left ih ha
    have h3 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hab)
    have e : a ^ (k + 1 + 1) - b ^ (k + 1 + 1) =
        a * (a ^ (k + 1) - b ^ (k + 1)) + (a - b) * b ^ (k + 1) := by ring
    have e2 : a * ((k + 1) * (a - b) * a ^ k) = (k + 1) * (a - b) * a ^ (k + 1) := by ring
    have e3 : ((k + 1 : ℕ) + 1 : ℝ) * (a - b) * a ^ (k + 1) =
        (k + 1) * (a - b) * a ^ (k + 1) + (a - b) * a ^ (k + 1) := by push_cast; ring
    rw [e, e3]
    linarith

/-- On the shell `[-(R+1), R+1]^d \ [-R, R]^d` the sum of `(1 + |z|)^{-k}` is at most
`2^(k+1) (k+1)`. -/
theorem sum_shell_le (k R : ℕ) :
    ∑ z ∈ box (k + 1) (R + 1) \ box (k + 1) R, ((1 + ‖toE z‖) ^ k)⁻¹ ≤
      2 ^ (k + 1) * (k + 1) := by
  have hR : (0 : ℝ) < (R : ℝ) + 2 := by positivity
  have hterm : ∀ z ∈ box (k + 1) (R + 1) \ box (k + 1) R,
      ((1 + ‖toE z‖) ^ k)⁻¹ ≤ (((R : ℝ) + 2) ^ k)⁻¹ := by
    intro z hz
    rw [Finset.mem_sdiff, mem_box, mem_box] at hz
    obtain ⟨-, hz2⟩ := hz
    rw [not_forall] at hz2
    obtain ⟨i, hi⟩ := hz2
    rw [not_le] at hi
    have h1 : (R : ℤ) + 1 ≤ |z i| := hi
    have h2 : (R : ℝ) + 1 ≤ |(z i : ℝ)| := by
      have : (((R : ℤ) + 1 : ℤ) : ℝ) ≤ ((|z i| : ℤ) : ℝ) := by exact_mod_cast h1
      simpa using this
    have h3 : (R : ℝ) + 2 ≤ 1 + ‖toE z‖ := by linarith [abs_coord_le_norm z i]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h3 k)
  have hsum : ∑ z ∈ box (k + 1) (R + 1) \ box (k + 1) R, ((1 + ‖toE z‖) ^ k)⁻¹ ≤
      ((box (k + 1) (R + 1) \ box (k + 1) R).card : ℝ) * (((R : ℝ) + 2) ^ k)⁻¹ := by
    have := Finset.sum_le_card_nsmul _ _ _ hterm
    simpa [nsmul_eq_mul] using this
  have hcard : (((box (k + 1) (R + 1) \ box (k + 1) R).card : ℕ) : ℝ) +
      (2 * (R : ℝ) + 1) ^ (k + 1) = (2 * (R : ℝ) + 3) ^ (k + 1) := by
    have := Finset.card_sdiff_add_card_eq_card (box_subset_box (d := k + 1) (Nat.le_succ R))
    rw [card_box, card_box] at this
    have h' : (((box (k + 1) (R + 1) \ box (k + 1) R).card + (2 * R + 1) ^ (k + 1) : ℕ) : ℝ) =
        ((2 * (R + 1) + 1) ^ (k + 1) : ℕ) := by rw [this]
    push_cast at h'
    rw [h']
    ring
  have hpow := pow_succ_sub_le (a := 2 * (R : ℝ) + 3) (b := 2 * (R : ℝ) + 1) (by positivity)
    (by linarith) k
  have hcard2 : ((box (k + 1) (R + 1) \ box (k + 1) R).card : ℝ) ≤
      2 ^ (k + 1) * (k + 1) * ((R : ℝ) + 2) ^ k := by
    have h4 : (2 * (R : ℝ) + 3) ^ k ≤ (2 * ((R : ℝ) + 2)) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    rw [mul_pow] at h4
    have h5 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ ((k : ℝ) + 1) * 2 by positivity)
    have e : ((k : ℝ) + 1) * 2 * (2 ^ k * ((R : ℝ) + 2) ^ k) =
        2 ^ (k + 1) * (k + 1) * ((R : ℝ) + 2) ^ k := by ring
    have e2 : ((k : ℝ) + 1) * (2 * (R : ℝ) + 3 - (2 * (R : ℝ) + 1)) * (2 * (R : ℝ) + 3) ^ k =
        ((k : ℝ) + 1) * 2 * (2 * (R : ℝ) + 3) ^ k := by ring
    rw [e2] at hpow
    linarith
  calc _ ≤ _ := hsum
    _ ≤ _ := by
      rw [mul_inv_le_iff₀ (by positivity)]
      exact hcard2

/-- The lattice sum `∑_{|z|_∞ ≤ R} (1 + |z|)^{-k} ≤ 2^(k+1) (k+1) (R+1)` (`d = k + 1`). -/
theorem sum_box_le (k R : ℕ) :
    ∑ z ∈ box (k + 1) R, ((1 + ‖toE z‖) ^ k)⁻¹ ≤ 2 ^ (k + 1) * (k + 1) * (R + 1) := by
  induction R with
  | zero =>
    have h0 : ∀ z ∈ box (k + 1) 0, ((1 + ‖toE z‖) ^ k)⁻¹ ≤ 1 := fun z _ =>
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (toE z)]))
    have h1 := Finset.sum_le_card_nsmul _ _ _ h0
    rw [card_box] at h1
    simp only [nsmul_eq_mul, mul_one, Nat.cast_zero, mul_zero, zero_add, one_pow,
      Nat.cast_one] at h1 ⊢
    refine h1.trans ?_
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  | succ R ih =>
    rw [← Finset.sum_sdiff (box_subset_box (d := k + 1) (Nat.le_succ R))]
    have := sum_shell_le k R
    push_cast
    nlinarith [this, ih]

/-- **The lattice sum**: for `d ≥ 1`,
`∑_{|z|_∞ ≤ R} (1 + |z|)^{-(d-1)} ≤ 2^d d (R + 1)`. -/
theorem sum_box_le' (hd : 1 ≤ d) (R : ℕ) :
    ∑ z ∈ box d R, ((1 + ‖toE z‖) ^ (d - 1))⁻¹ ≤ 2 ^ d * d * (R + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simpa using sum_box_le k R

end DivisibleHomogenize

open DivisibleHomogenize OdometerLowerBound

/-- **The summed (difference) estimate from the pointwise one**:
`GreenBallDifferenceStmt` implies `GreenBallGradientSumStmt`. -/
theorem greenBallGradientSum_of_difference (h : GreenBallDifferenceStmt) :
    GreenBallGradientSumStmt := by
  intro d hd δ hδ0 hδ1
  obtain ⟨C, hC, hCb⟩ := h d hd δ hδ0 hδ1
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  refine ⟨3 * d * C * (2 ^ d * d), by positivity, fun n x hx => ?_⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := mem_ballZ0.1 hx
      rw [Nat.cast_zero, mul_zero] at this
      exact absurd this (not_lt.2 (norm_nonneg _))
    · exact hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [finsum_mem_eq_finite_toFinset_sum _ (ballZ0_finite _)]
  set S := (ballZ0_finite (d := d) ((1 - δ) * n)).toFinset with hS
  have hpt : ∀ y ∈ S, ∑ i : Fin d, |greenKilled (ballZ0 (n : ℝ)) x (y + unit i) -
      greenKilled (ballZ0 (n : ℝ)) x y| ≤
        (d * C) * ((1 + ‖toE (x - y)‖) ^ (d - 1))⁻¹ := by
    intro y hy
    have hy' : y ∈ ballZ0 ((1 - δ) * n) := (Set.Finite.mem_toFinset _).1 hy
    have hP : 0 < (1 + ‖toE (x - y)‖) ^ (d - 1) := by positivity
    calc _ ≤ ∑ _i : Fin d, C * ((1 + ‖toE (x - y)‖) ^ (d - 1))⁻¹ :=
          Finset.sum_le_sum fun i _ => by
            rw [← div_eq_mul_inv, le_div_iff₀ hP]
            exact hCb n x y hx hy' i
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsub : S.image (fun y => x - y) ⊆ box d (2 * n) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    have hy' : y ∈ ballZ0 ((1 - δ) * n) := (Set.Finite.mem_toFinset _).1 hy
    have hxn := mem_ballZ0.1 hx
    have hyn := mem_ballZ0.1 hy'
    rw [mem_box]
    intro i
    have h1 : ‖toE (x - y)‖ ≤ ‖toE x‖ + ‖toE y‖ := by
      rw [toE_sub]
      exact norm_sub_le _ _
    have h2 := abs_coord_le_norm (x - y) i
    have h3 : |((x - y) i : ℝ)| < 2 * n := by nlinarith
    have h4 : |(x - y) i| < ((2 * n : ℕ) : ℤ) := by
      have h5 : ((|(x - y) i| : ℤ) : ℝ) < (((2 * n : ℕ) : ℤ) : ℝ) := by
        rw [Int.cast_abs]
        push_cast
        exact h3
      exact Int.cast_lt.1 h5
    exact h4.le
  have hsum := sum_box_le' hd1 (2 * n)
  have hK : 0 ≤ (d : ℝ) * C := by positivity
  calc _ ≤ ∑ y ∈ S, (d * C) * ((1 + ‖toE (x - y)‖) ^ (d - 1))⁻¹ := Finset.sum_le_sum hpt
    _ = (d * C) * ∑ y ∈ S, ((1 + ‖toE (x - y)‖) ^ (d - 1))⁻¹ := by rw [← Finset.mul_sum]
    _ = (d * C) * ∑ z ∈ S.image (fun y => x - y), ((1 + ‖toE z‖) ^ (d - 1))⁻¹ := by
        rw [Finset.sum_image (fun a _ b _ hab => sub_right_injective hab)]
    _ ≤ (d * C) * ∑ z ∈ box d (2 * n), ((1 + ‖toE z‖) ^ (d - 1))⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => by positivity)) hK
    _ ≤ (d * C) * (2 ^ d * d * (((2 * n : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hsum hK
    _ ≤ _ := by
        push_cast
        have h5 : 2 * (n : ℝ) + 1 ≤ 3 * n := by linarith
        have h6 : 0 ≤ (d : ℝ) * C * (2 ^ d * d) := by positivity
        have := mul_le_mul_of_nonneg_left h5 h6
        linarith

end RandomSandpile

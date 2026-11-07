import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeRadial

/-!
# Discrete subharmonicity of `|z - w|^{-4d}` away from `w`

The barrier function used for the domain version of the homogenization lemma
(Lemma 8.1, `paper/random_piles-corrected.tex`) is `z ↦ |z - w|^{-4d}`; it is discretely
subharmonic at distance at least `2 √d` from `w`:

* `lapR_invPow_nonneg`: for `1 ≤ d` and `4 d ≤ |y - w|²`, `Δ_{ℤ^d} (|· - w|^{-4d}) (y) ≥ 0`.

The proof is elementary and is split into small real-arithmetic lemmas. Write `q = |y - w|²`,
`m = 2d`, `c = q + 1` and `h_i = 2 (y - w)_i`, so that the neighbour values are `(c ± h_i)^{-m}`
and `∑_i h_i² = 4 q`.

* `pow_add_sub_lower`: for `0 ≤ t`, `(1 + t)^m + (1 - t)^m ≥ 2 + m (m - 1) t²` and
  `(1 + t)^m - (1 - t)^m ≥ 2 m t` (simultaneous induction on `m`).
* `inv_pow_add_inv_pow_ge`: for `|t| < 1`, `(1 + t)^{-m} + (1 - t)^{-m} ≥ 2 + m (m + 1) t²`
  (the previous bound, together with `(1 - t²)^m (1 + m t²) ≤ 1`, a Bernoulli inequality).
* `inv_pow_add_inv_pow_ge_scaled`: the same for `(c + h)^{-m} + (c - h)^{-m}`, with `t = h / c`.
* `one_add_pow_le`: Bernoulli in the other direction, `(1 + x)^m ≤ 1 + 2 m x` for `m x ≤ 1/2`.
* `sum_inv_pow_ge`: the pure real statement
  `2 d q^{-m} ≤ ∑_i ((q + 1 + 2 v_i)^{-m} + (q + 1 - 2 v_i)^{-m})` when `∑ v_i² = q ≥ 4 d`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

variable {d : ℕ}

namespace DivisibleHomogenizeDomain

open DivisibleHomogenize

/-- `m (m - 1) ≥ 0` for a natural number `m`, in the reals. -/
theorem nat_mul_pred_nonneg (m : ℕ) : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | h
  · simp
  · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith

/-- Binomial lower bounds, by simultaneous induction on `m`: for `t ≥ 0`,
`(1 + t)^m + (1 - t)^m ≥ 2 + m (m - 1) t²` and `(1 + t)^m - (1 - t)^m ≥ 2 m t`. -/
theorem pow_add_sub_lower {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    2 + (m : ℝ) * ((m : ℝ) - 1) * t ^ 2 ≤ (1 + t) ^ m + (1 - t) ^ m ∧
      2 * (m : ℝ) * t ≤ (1 + t) ^ m - (1 - t) ^ m := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnn := nat_mul_pred_nonneg n
    have h3 : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) * t ^ 2 := mul_nonneg hnn (sq_nonneg t)
    have h4 := mul_le_mul_of_nonneg_left h2 ht
    have h5 := mul_le_mul_of_nonneg_left (show 2 ≤ (1 + t) ^ n + (1 - t) ^ n by linarith) ht
    push_cast
    rw [pow_succ (1 + t) n, pow_succ (1 - t) n]
    constructor
    · nlinarith
    · nlinarith

/-- The sum of the inverse powers `(1 + t)^{-m} + (1 - t)^{-m} ≥ 2 + m (m + 1) t²`, for
`0 ≤ t < 1`. -/
theorem inv_pow_add_inv_pow_ge_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (m : ℕ) :
    2 + (m : ℝ) * ((m : ℝ) + 1) * t ^ 2 ≤ ((1 + t) ^ m)⁻¹ + ((1 - t) ^ m)⁻¹ := by
  obtain ⟨hP, -⟩ := pow_add_sub_lower ht m
  have hA : 0 < (1 + t) ^ m := pow_pos (by linarith) m
  have hB : 0 < (1 - t) ^ m := pow_pos (by linarith) m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hnn := nat_mul_pred_nonneg m
  set A := (1 + t) ^ m with hAdef
  set B := (1 - t) ^ m with hBdef
  set u := t ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg t
  have hu1 : u < 1 := by nlinarith
  -- `A * B = (1 - u)^m` and `(1 - u)^m (1 + m u) ≤ 1`
  have hAB : A * B = (1 - u) ^ m := by
    rw [hAdef, hBdef, ← mul_pow, hu]
    congr 1
    ring
  have hE : A * B * (1 + m * u) ≤ 1 := by
    have hb : 1 + (m : ℝ) * u ≤ (1 + u) ^ m := one_add_mul_le_pow (by linarith) m
    calc A * B * (1 + m * u) ≤ A * B * (1 + u) ^ m :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ((1 - u) * (1 + u)) ^ m := by rw [hAB, mul_pow]
      _ ≤ 1 := by
          apply pow_le_one₀ (by nlinarith) (by nlinarith)
  have hS : (2 + (m : ℝ) * ((m : ℝ) - 1) * u) * (1 + m * u) ≥ 2 + m * (m + 1) * u := by
    have : 0 ≤ (m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1)) * u ^ 2 :=
      mul_nonneg (mul_nonneg hm hnn) (sq_nonneg u)
    nlinarith
  have hE0 : 0 ≤ A * B := by positivity
  have hm1 : 0 ≤ 1 + (m : ℝ) * u := by positivity
  rw [inv_add_inv hA.ne' hB.ne', le_div_iff₀ (by positivity)]
  have h1 : (A + B) * (A * B * (1 + m * u)) ≤ A + B :=
    mul_le_of_le_one_right (by positivity) hE
  have h2 : (2 + (m : ℝ) * ((m : ℝ) - 1) * u) * (A * B * (1 + m * u)) ≤
      (A + B) * (A * B * (1 + m * u)) :=
    mul_le_mul_of_nonneg_right hP (by positivity)
  have h3 : (2 + (m : ℝ) * ((m : ℝ) + 1) * u) * (A * B) ≤
      (2 + (m : ℝ) * ((m : ℝ) - 1) * u) * (1 + m * u) * (A * B) :=
    mul_le_mul_of_nonneg_right (by linarith) hE0
  calc (2 + (m : ℝ) * ((m : ℝ) + 1) * u) * (A * B)
      ≤ (2 + (m : ℝ) * ((m : ℝ) - 1) * u) * (1 + m * u) * (A * B) := h3
    _ = (2 + (m : ℝ) * ((m : ℝ) - 1) * u) * (A * B * (1 + m * u)) := by ring
    _ ≤ A + B := h2.trans h1

/-- `(1 + t)^{-m} + (1 - t)^{-m} ≥ 2 + m (m + 1) t²` for `|t| < 1`. -/
theorem inv_pow_add_inv_pow_ge {t : ℝ} (ht : |t| < 1) (m : ℕ) :
    2 + (m : ℝ) * ((m : ℝ) + 1) * t ^ 2 ≤ ((1 + t) ^ m)⁻¹ + ((1 - t) ^ m)⁻¹ := by
  rcases abs_lt.1 ht with ⟨hl, hr⟩
  rcases le_total 0 t with h | h
  · exact inv_pow_add_inv_pow_ge_nonneg h hr m
  · have := inv_pow_add_inv_pow_ge_nonneg (t := -t) (by linarith) (by linarith) m
    have e1 : 1 + -t = 1 - t := by ring
    have e2 : 1 - -t = 1 + t := by ring
    rw [e1, e2, neg_sq] at this
    linarith

/-- `(c + h)^{-m} + (c - h)^{-m} ≥ c^{-m} (2 + m (m + 1) (h / c)²)` for `|h| < c`. -/
theorem inv_pow_add_inv_pow_ge_scaled {c h : ℝ} (hc : 0 < c) (hh : |h| < c) (m : ℕ) :
    (c ^ m)⁻¹ * (2 + (m : ℝ) * ((m : ℝ) + 1) * (h / c) ^ 2) ≤
      ((c + h) ^ m)⁻¹ + ((c - h) ^ m)⁻¹ := by
  have ht : |h / c| < 1 := by
    rw [abs_div, abs_of_pos hc, div_lt_one hc]
    exact hh
  have key := inv_pow_add_inv_pow_ge ht m
  have e1 : c + h = c * (1 + h / c) := by field_simp
  have e2 : c - h = c * (1 - h / c) := by field_simp
  rw [e1, e2, mul_pow, mul_pow, mul_inv, mul_inv, ← mul_add]
  exact mul_le_mul_of_nonneg_left key (inv_nonneg.2 (pow_nonneg hc.le _))

/-- Bernoulli in the other direction: `(1 + x)^m ≤ 1 + 2 m x` when `0 ≤ x ≤ 1` and
`m x ≤ 1/2`. -/
theorem one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) (hmx : (m : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ m ≤ 1 + 2 * m * x := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hb : 1 + (m : ℝ) * (-x) ≤ (1 + -x) ^ m := one_add_mul_le_pow (by linarith) m
  have hpos : 0 < 1 - (m : ℝ) * x := by linarith
  have h1 : (1 + x) ^ m * (1 - (m : ℝ) * x) ≤ 1 := by
    calc (1 + x) ^ m * (1 - (m : ℝ) * x) ≤ (1 + x) ^ m * (1 + -x) ^ m :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ((1 + x) * (1 + -x)) ^ m := (mul_pow _ _ _).symm
      _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)
  have h2 : (1 : ℝ) ≤ (1 + 2 * m * x) * (1 - (m : ℝ) * x) := by
    nlinarith [mul_nonneg (mul_nonneg hm hx) (show (0 : ℝ) ≤ 1 - 2 * (m * x) by linarith)]
  exact le_of_mul_le_mul_right (h1.trans h2) hpos

/-- The numerical inequality `d (q + 1)² ≤ (2d + 1) q²` for `q ≥ 4`. -/
theorem key_numeric {q e : ℝ} (he : 0 ≤ e) (hq : 4 ≤ q) :
    e * (q + 1) ^ 2 ≤ (2 * e + 1) * q ^ 2 := by
  have h : (q + 1) ^ 2 ≤ 2 * q ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h he, sq_nonneg q]

/-- **Pure real form of the barrier inequality**: if `∑ v_i² = q ≥ 4 d` (`d ≥ 1`) then
`2 d q^{-2d} ≤ ∑_i ((q + 1 + 2 v_i)^{-2d} + (q + 1 - 2 v_i)^{-2d})`. -/
theorem sum_inv_pow_ge (hd : 1 ≤ d) (v : Fin d → ℝ) (q : ℝ) (hv : ∑ i, v i ^ 2 = q)
    (hq : 4 * (d : ℝ) ≤ q) :
    2 * (d : ℝ) * (q ^ (2 * d))⁻¹ ≤
      ∑ i, (((q + 1 + 2 * v i) ^ (2 * d))⁻¹ + ((q + 1 - 2 * v i) ^ (2 * d))⁻¹) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hq4 : 4 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hc : 0 < q + 1 := by linarith
  have hm : ((2 * d : ℕ) : ℝ) = 2 * d := by push_cast; ring
  -- termwise bound
  have hterm : ∀ i, ((q + 1) ^ (2 * d))⁻¹ * (2 + ((2 * d : ℕ) : ℝ) * (((2 * d : ℕ) : ℝ) + 1) *
        (4 / (q + 1) ^ 2) * v i ^ 2) ≤
      ((q + 1 + 2 * v i) ^ (2 * d))⁻¹ + ((q + 1 - 2 * v i) ^ (2 * d))⁻¹ := by
    intro i
    have hvi : v i ^ 2 ≤ q := by
      rw [← hv]
      exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have habs : |2 * v i| < q + 1 := by
      apply abs_lt_of_sq_lt_sq _ hc.le
      nlinarith
    have := inv_pow_add_inv_pow_ge_scaled hc habs (2 * d)
    have e : (2 * v i / (q + 1)) ^ 2 = 4 / (q + 1) ^ 2 * v i ^ 2 := by
      field_simp
      ring
    rw [e] at this
    convert this using 3
    ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  refine le_trans ?_ hsum
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, hv,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm]
  -- `x = 1 / q`, `(1 + x)^m ≤ 1 + 2 m x`
  have hx : 0 ≤ q⁻¹ := inv_nonneg.2 hq0.le
  have hx1 : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hmx : ((2 * d : ℕ) : ℝ) * q⁻¹ ≤ 1 / 2 := by
    rw [hm, ← div_eq_mul_inv, div_le_iff₀ hq0]
    linarith
  have hB := one_add_pow_le hx hx1 (2 * d) hmx
  have hqc : (q ^ (2 * d))⁻¹ = ((q + 1) ^ (2 * d))⁻¹ * (1 + q⁻¹) ^ (2 * d) := by
    have h1 : q + 1 = q * (1 + q⁻¹) := by field_simp
    have h2 : (0 : ℝ) < 1 + q⁻¹ := by positivity
    rw [h1, mul_pow, mul_inv, inv_mul_cancel_right₀ (pow_pos h2 _).ne']
  have hcm : 0 ≤ ((q + 1) ^ (2 * d))⁻¹ := inv_nonneg.2 (pow_nonneg hc.le _)
  have hB' : (1 + q⁻¹) ^ (2 * d) ≤ 1 + 2 * (2 * d) * q⁻¹ := by rw [hm] at hB; exact hB
  have hnum := key_numeric (q := q) (e := d) (by positivity) hq4
  have hfin : 2 * (d : ℝ) * (1 + 2 * (2 * d) * q⁻¹) ≤
      d * 2 + 2 * d * (2 * d + 1) * (4 / (q + 1) ^ 2) * q := by
    rw [← sub_nonneg]
    have e : d * 2 + 2 * (d : ℝ) * (2 * d + 1) * (4 / (q + 1) ^ 2) * q -
        2 * (d : ℝ) * (1 + 2 * (2 * d) * q⁻¹) =
        8 * d * ((2 * d + 1) * q ^ 2 - d * (q + 1) ^ 2) / (q * (q + 1) ^ 2) := by
      field_simp
      ring
    rw [e]
    apply div_nonneg
    · have : 0 ≤ (2 * (d : ℝ) + 1) * q ^ 2 - d * (q + 1) ^ 2 := by linarith
      positivity
    · positivity
  rw [hqc]
  calc 2 * (d : ℝ) * (((q + 1) ^ (2 * d))⁻¹ * (1 + q⁻¹) ^ (2 * d))
      = ((q + 1) ^ (2 * d))⁻¹ * (2 * d * (1 + q⁻¹) ^ (2 * d)) := by ring
    _ ≤ ((q + 1) ^ (2 * d))⁻¹ * (2 * d * (1 + 2 * (2 * d) * q⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB' (by positivity)) hcm
    _ ≤ ((q + 1) ^ (2 * d))⁻¹ * (d * 2 + 2 * d * (2 * d + 1) * (4 / (q + 1) ^ 2) * q) :=
        mul_le_mul_of_nonneg_left hfin hcm

/-- **The barrier is subharmonic away from its pole**: for `d ≥ 1` and `|y - w|² ≥ 4 d`, the
function `z ↦ |z - w|^{-4d}` has nonnegative discrete Laplacian at `y`. -/
theorem lapR_invPow_nonneg (hd : 1 ≤ d) (w y : Site d)
    (hy : 4 * (d : ℝ) ≤ ‖toE (y - w)‖ ^ 2) :
    0 ≤ lapR (fun z : Site d => ((‖toE (z - w)‖ ^ 2) ^ (2 * d))⁻¹) y := by
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = ‖toE (y - w)‖ ^ 2 := ⟨_, rfl⟩
  rw [← hqdef] at hy
  have hv : ∑ i, (((y - w) i : ℤ) : ℝ) ^ 2 = q := by
    rw [hqdef]
    exact (DivisibleHomogenize.norm_toE_sq (y - w)).symm
  have key := sum_inv_pow_ge hd (fun i => (((y - w) i : ℤ) : ℝ)) q hv hy
  have hplus : ∀ i, ‖toE (y + unit i - w)‖ ^ 2 = q + 1 + 2 * (((y - w) i : ℤ) : ℝ) := by
    intro i
    rw [add_sub_right_comm, DivisibleHomogenize.norm_toE_add_unit_sq, hqdef]
    ring
  have hminus : ∀ i, ‖toE (y - unit i - w)‖ ^ 2 = q + 1 - 2 * (((y - w) i : ℤ) : ℝ) := by
    intro i
    rw [sub_right_comm, DivisibleHomogenize.norm_toE_sub_unit_sq, hqdef]
    ring
  simp only [lapR, nbrSum, hplus, hminus, ← hqdef]
  linarith

end DivisibleHomogenizeDomain

end RandomSandpile

import RandomSandpile.Steps.Sec7.OneDimToppling

/-!
# Proof of Lemma 7.1 (one-dimensional toppling)

Proofs of the four steps of `RandomSandpile/Steps/Sec7/OneDimToppling.lean` and of
`RandomSandpile.OneDimTopplingStmt` (Lemma 7.1, `paper/random_piles-corrected.tex`, in
the corrected form [C5]). This is a direct proof: no literature input is used.

Ramp potential `Q_m(x) = ∑_{|y| ≤ m} (y - x)⁺`:
* `rampPotential_secondDiff`: `Δ Q_m = 𝟙_{[-m, m]}` (the second difference of `t ↦ t⁺` is `𝟙_{t = 0}`);
* `rampPotential_eq_zero`: `Q_m(x) = 0` for `x ≥ m`;
* `rampPotential_neg`: the reflection identity `Q_m(-x) = Q_m(x) + (2m + 1) x`;
* `two_mul_rampPotential_of_abs_le`: `2 Q_m(x) = (m - x)(m - x + 1)` for `|x| ≤ m`, by a two-step
  induction downward from `x = m`, using `Δ Q_m = 1` on `[-m, m]`.

The solution `g = Q_{ℓ(r+1)} + Q_{ℓ(r+1)+r} - (2r + 2) Q_ℓ` is then even (`oneDimOdometer_neg`, the
coefficients of the reflection identity cancel: `∑ f = 0`), vanishes for `x ≥ ℓ(r+1) + r`, is
nonnegative for `x ≥ 0` (for `x ≥ ℓ` only the nonnegative terms survive; for `0 ≤ x < ℓ`,
`2g(x) = 2r(ℓ - x)(ℓ + x) + 2g(ℓ)` with `2g(ℓ) = 2ℓ²r² + 2ℓr² + r² + 2ℓr + r`), and satisfies
`g ≤ Q_{ℓ(r+1)} + Q_{ℓ(r+1)+r} ≤ L(L+1)` with `L + 1 = (r + 1)(ℓ + 1)`.
-/

noncomputable section

open Finset

namespace RandomSandpile

/-! ### The ramp potential -/

/-- The second difference of the ramp `t ↦ t⁺`, evaluated at `t = y - x`, is `𝟙_{x = y}`. -/
private theorem ramp_secondDiff (x y : ℤ) :
    max (y - (x + 1)) 0 + max (y - (x - 1)) 0 - 2 * max (y - x) 0 = if x = y then 1 else 0 := by
  simp only [max_def]; split_ifs <;> omega

/-- `Δ Q_m = 𝟙_{[-m, m]}`. -/
theorem rampPotential_secondDiff (m : ℕ) (x : ℤ) :
    rampPotential m (x + 1) + rampPotential m (x - 1) - 2 * rampPotential m x =
      if |x| ≤ m then 1 else 0 := by
  simp only [rampPotential, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ramp_secondDiff, Finset.sum_ite_eq, Finset.mem_Icc, abs_le]

/-- `Q_m(x) = 0` for `x ≥ m`. -/
theorem rampPotential_eq_zero {m : ℕ} {x : ℤ} (hx : (m : ℤ) ≤ x) : rampPotential m x = 0 :=
  Finset.sum_eq_zero fun y hy => by
    rw [Finset.mem_Icc] at hy
    exact max_eq_right (by omega)

/-- `Q_m ≥ 0`. -/
theorem rampPotential_nonneg (m : ℕ) (x : ℤ) : 0 ≤ rampPotential m x :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- Reindexing a sum over `[-m, m]` by `y ↦ -y`. -/
private theorem sum_Icc_comp_neg (m : ℕ) (F : ℤ → ℤ) :
    ∑ y ∈ Icc (-(m : ℤ)) m, F (-y) = ∑ y ∈ Icc (-(m : ℤ)) m, F y :=
  Finset.sum_nbij' (fun y => -y) (fun y => -y)
    (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)
    (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)
    (fun a _ => neg_neg a) (fun a _ => neg_neg a) (fun _ _ => rfl)

/-- `∑_{|y| ≤ m} y = 0`. -/
private theorem sum_Icc_id (m : ℕ) : ∑ y ∈ Icc (-(m : ℤ)) m, y = 0 := by
  have h := sum_Icc_comp_neg m id
  simp only [id] at h
  rw [Finset.sum_neg_distrib] at h
  linarith

/-- The reflection identity `Q_m(-x) = Q_m(x) + (2m + 1) x`, from `(x - y)⁺ = (y - x)⁺ + (x - y)`
and `∑_{|y| ≤ m} y = 0`. -/
theorem rampPotential_neg (m : ℕ) (x : ℤ) :
    rampPotential m (-x) = rampPotential m x + (2 * m + 1) * x := by
  have h1 : rampPotential m (-x) = ∑ y ∈ Icc (-(m : ℤ)) m, (max (y - x) 0 + (x - y)) :=
    calc rampPotential m (-x) = ∑ y ∈ Icc (-(m : ℤ)) m, max (-y - -x) 0 :=
          (sum_Icc_comp_neg m fun y => max (y - -x) 0).symm
      _ = _ := Finset.sum_congr rfl fun y _ => by simp only [max_def]; split_ifs <;> omega
  rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_Icc_id, Finset.sum_const,
    Int.card_Icc, nsmul_eq_mul, ← rampPotential]
  have : (((m : ℤ) + 1 - -(m : ℤ)).toNat : ℤ) = 2 * m + 1 := by omega
  rw [this]
  ring

/-- `2 Q_m(x) = (m - x)(m - x + 1)` for `|x| ≤ m`. -/
theorem two_mul_rampPotential_of_abs_le {m : ℕ} {x : ℤ} (hx : |x| ≤ m) :
    2 * rampPotential m x = (m - x) * (m - x + 1) := by
  have key : ∀ n : ℕ, n ≤ 2 * m + 1 →
      2 * rampPotential m (m - n) = n * (n + 1) ∧
        2 * rampPotential m (m - n + 1) = (n - 1) * n := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_zero, sub_zero, rampPotential_eq_zero le_rfl]; ring
      · rw [Nat.cast_zero, sub_zero, rampPotential_eq_zero (by omega)]; ring
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hd := rampPotential_secondDiff m (m - n)
      rw [ite_eq_left (by rw [abs_le]; omega)] at hd
      have e1 : (m : ℤ) - ((n + 1 : ℕ) : ℤ) = m - n - 1 := by push_cast; ring
      have e2 : (m : ℤ) - ((n + 1 : ℕ) : ℤ) + 1 = m - n := by push_cast; ring
      rw [e2, e1]
      push_cast
      exact ⟨by linear_combination 2 * hd + 2 * h1 - h2, by linear_combination h1⟩
  rw [abs_le] at hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m - x := ⟨(m - x).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h := (key n (by omega)).1
  rw [hn, sub_sub_cancel] at h
  exact h

/-- `2 Q_m(x) ≤ m(m + 1)` for `x ≥ 0`. -/
theorem two_mul_rampPotential_le {m : ℕ} {x : ℤ} (hx : 0 ≤ x) :
    2 * rampPotential m x ≤ m * (m + 1) := by
  rcases le_or_gt (m : ℤ) x with h | h
  · rw [rampPotential_eq_zero h]; positivity
  · rw [two_mul_rampPotential_of_abs_le (by rw [abs_le]; constructor <;> omega)]
    nlinarith [mul_nonneg hx (by omega : (0 : ℤ) ≤ 2 * m - x + 1)]

/-! ### The solution of Lemma 7.1 -/

/-- `g` is even: the coefficients of the reflection identity cancel, `(2ℓ(r+1) + 1) +
(2(ℓ(r+1) + r) + 1) = (2r + 2)(2ℓ + 1)` (equivalently `∑ f = 0`). -/
theorem oneDimOdometer_neg (r ℓ : ℕ) (x : ℤ) : oneDimOdometer r ℓ (-x) = oneDimOdometer r ℓ x := by
  simp only [oneDimOdometer, rampPotential_neg]
  push_cast
  ring

/-- `g(x) = 0` for `x ≥ ℓ(r+1) + r`. -/
theorem oneDimOdometer_eq_zero_of_le {r ℓ : ℕ} {x : ℤ} (hx : (ℓ : ℤ) * (r + 1) + r ≤ x) :
    oneDimOdometer r ℓ x = 0 := by
  have hb : (ℓ : ℤ) ≤ ℓ * (r + 1) := le_mul_of_one_le_right (by positivity) (by linarith)
  unfold oneDimOdometer
  rw [rampPotential_eq_zero (by push_cast; linarith), rampPotential_eq_zero (by push_cast; linarith),
    rampPotential_eq_zero (by linarith)]
  ring

/-- `g(x) ≥ 0` for `x ≥ 0`. -/
private theorem oneDimOdometer_nonneg_of_nonneg (r ℓ : ℕ) {x : ℤ} (hx : 0 ≤ x) :
    0 ≤ oneDimOdometer r ℓ x := by
  have hb : (ℓ : ℤ) ≤ ℓ * (r + 1) := le_mul_of_one_le_right (by positivity) (by linarith)
  rcases le_or_gt (ℓ : ℤ) x with h | h
  · unfold oneDimOdometer
    rw [rampPotential_eq_zero h]
    linarith [rampPotential_nonneg (ℓ * (r + 1)) x, rampPotential_nonneg (ℓ * (r + 1) + r) x]
  · have ha := two_mul_rampPotential_of_abs_le (m := ℓ) (x := x)
      (by rw [abs_le]; constructor <;> omega)
    have hb' := two_mul_rampPotential_of_abs_le (m := ℓ * (r + 1)) (x := x)
      (by rw [abs_le]; push_cast; constructor <;> linarith)
    have hL := two_mul_rampPotential_of_abs_le (m := ℓ * (r + 1) + r) (x := x)
      (by rw [abs_le]; push_cast; constructor <;> linarith [(Nat.cast_nonneg r : (0 : ℤ) ≤ r)])
    push_cast at hb' hL
    have hG : 2 * oneDimOdometer r ℓ x = 2 * r * ((ℓ - x) * (ℓ + x)) +
        (2 * ℓ ^ 2 * r ^ 2 + 2 * ℓ * r ^ 2 + r ^ 2 + 2 * ℓ * r + r) := by
      unfold oneDimOdometer
      linear_combination hb' + hL - (2 * (r : ℤ) + 2) * ha
    have h1 : (0 : ℤ) ≤ 2 * r * ((ℓ - x) * (ℓ + x)) :=
      mul_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
    have h2 : (0 : ℤ) ≤ 2 * ℓ ^ 2 * r ^ 2 + 2 * ℓ * r ^ 2 + r ^ 2 + 2 * ℓ * r + r := by positivity
    linarith

/-- `g(x) ≤ ((r + 1)(ℓ + 1))²` for `x ≥ 0`. -/
private theorem oneDimOdometer_le_of_nonneg (r ℓ : ℕ) {x : ℤ} (hx : 0 ≤ x) :
    oneDimOdometer r ℓ x ≤ (((r : ℤ) + 1) * (ℓ + 1)) ^ 2 := by
  unfold oneDimOdometer
  have ha := mul_nonneg (by positivity : (0 : ℤ) ≤ 2 * r + 2) (rampPotential_nonneg ℓ x)
  have hb := two_mul_rampPotential_le (m := ℓ * (r + 1)) hx
  have hL := two_mul_rampPotential_le (m := ℓ * (r + 1) + r) hx
  push_cast at hb hL
  have e : ((r : ℤ) + 1) * (ℓ + 1) = ℓ * (r + 1) + r + 1 := by ring
  rw [e]
  have hb0 : (0 : ℤ) ≤ ℓ * (r + 1) := by positivity
  have hr : (0 : ℤ) ≤ r := by positivity
  generalize (ℓ : ℤ) * (r + 1) = b at hb hL hb0 ⊢
  nlinarith [mul_nonneg hb0 hr, sq_nonneg (r : ℤ)]

/-! ### The four steps and Lemma 7.1 -/

/-- Step 1 of Lemma 7.1: `Δ g = f`. -/
theorem oneDimSecondDiff : OneDimSecondDiffStmt := by
  intro r ℓ x
  have h1 := rampPotential_secondDiff (ℓ * (r + 1)) x
  have h2 := rampPotential_secondDiff (ℓ * (r + 1) + r) x
  have h3 := rampPotential_secondDiff ℓ x
  push_cast at h1 h2
  have hsplit : oneDimOdometer r ℓ (x + 1) + oneDimOdometer r ℓ (x - 1) - 2 * oneDimOdometer r ℓ x =
      (rampPotential (ℓ * (r + 1)) (x + 1) + rampPotential (ℓ * (r + 1)) (x - 1) -
          2 * rampPotential (ℓ * (r + 1)) x) +
        (rampPotential (ℓ * (r + 1) + r) (x + 1) + rampPotential (ℓ * (r + 1) + r) (x - 1) -
          2 * rampPotential (ℓ * (r + 1) + r) x) -
        (2 * r + 2) * (rampPotential ℓ (x + 1) + rampPotential ℓ (x - 1) -
          2 * rampPotential ℓ x) := by
    unfold oneDimOdometer; ring
  rw [hsplit, h1, h2, h3]
  have hb : (ℓ : ℤ) ≤ ℓ * (r + 1) := le_mul_of_one_le_right (by positivity) (by linarith)
  have hr : (0 : ℤ) ≤ r := by positivity
  generalize |x| = t
  generalize (ℓ : ℤ) * (r + 1) = b at hb ⊢
  split_ifs <;> omega

/-- Step 2 of Lemma 7.1: `g` vanishes off `I = {|x| < ℓ(r+1) + r}`. -/
theorem oneDimSupport : OneDimSupportStmt := by
  intro r ℓ x hx
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    exact oneDimOdometer_eq_zero_of_le hx
  · rw [abs_of_neg h] at hx
    rw [← oneDimOdometer_neg]
    exact oneDimOdometer_eq_zero_of_le hx

/-- Step 3 of Lemma 7.1: `g ≥ 0`. -/
theorem oneDimNonneg : OneDimNonnegStmt := by
  intro r ℓ x
  rcases le_or_gt 0 x with h | h
  · exact oneDimOdometer_nonneg_of_nonneg r ℓ h
  · rw [← oneDimOdometer_neg]
    exact oneDimOdometer_nonneg_of_nonneg r ℓ (by linarith)

/-- Step 4 of Lemma 7.1: `g ≤ ((r + 1)(ℓ + 1))²`. -/
theorem oneDimBound : OneDimBoundStmt := by
  intro r ℓ x
  rcases le_or_gt 0 x with h | h
  · exact oneDimOdometer_le_of_nonneg r ℓ h
  · rw [← oneDimOdometer_neg]
    exact oneDimOdometer_le_of_nonneg r ℓ (by linarith)

/-- **Lemma 7.1** (`lemma:one_dim`, corrected form [C5]). -/
theorem oneDimToppling : OneDimTopplingStmt :=
  oneDimToppling_of_steps oneDimSecondDiff oneDimSupport oneDimNonneg oneDimBound

end RandomSandpile

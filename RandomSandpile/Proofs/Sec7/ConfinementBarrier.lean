import RandomSandpile.Defs.Odometer
import RandomSandpile.Defs.Green

/-!
# A quadratic barrier confining the free odometer to a box

The barrier of the confinement argument for Theorem 1.1 with a radius depending only on `W` and
`E η(0)`. For integers `a, K, n` with `K ≥ 2a`, let `D = {x : ‖x‖_∞ < 2an}` and
`b(x) = (Kn - ‖x‖_∞)₊²`. Its lattice Laplacian is at most `2` (`lap_boxBarrier_le`), since `b` is
the minimum over the coordinates of `((Kn - |x_i|)₊)²`, each of whose second differences is at
most `2`. If the initial sandpile `f = η 𝟙_{W_n}` is supported in `{‖x‖_∞ < an}` and `p` solves
`Δ p = -f` in `D` with `p = 0` off `D`, `p ≥ -((K - 2a) n)²` on `D` and
`p + 1 ≤ ((K - a) n)² - ((K - 2a) n)²` on `W_n`, then
`v = min(b, ((K - 2a) n)² + ⌈p⌉)` on `D` and `v = b` off `D` is a nonnegative integer stabilizing
function, so the free odometer satisfies `v_n ≤ v ≤ b` by least action and vanishes on
`{‖x‖_∞ ≥ Kn}` (`freeOdometer_eq_zero_of_barrier`).
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- The sup norm `max_i |x_i|` of a site, as a natural number. -/
def supNat (x : Site d) : ℕ := Finset.univ.sup fun i => (x i).natAbs

theorem natAbs_le_supNat (x : Site d) (i : Fin d) : (x i).natAbs ≤ supNat x :=
  Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)

theorem abs_le_supNat (x : Site d) (i : Fin d) : |x i| ≤ (supNat x : ℤ) := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast natAbs_le_supNat x i

theorem exists_abs_eq_supNat (hd : 0 < d) (x : Site d) : ∃ i, |x i| = (supNat x : ℤ) := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ hne fun i => (x i).natAbs
  exact ⟨i, by rw [← Int.natCast_natAbs, ← hi]; rfl⟩

/-- The one-dimensional profile `(L - |t|)₊²`. -/
def barrierProfile (L t : ℤ) : ℤ := (max (L - |t|) 0) ^ 2

/-- The second differences of `(L - |t|)₊²` are at most `2`. -/
theorem barrierProfile_secondDiff_le (L t : ℤ) :
    barrierProfile L (t + 1) + barrierProfile L (t - 1) - 2 * barrierProfile L t ≤ 2 := by
  simp only [barrierProfile]
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h1 : |t + 1| = -t - 1 := by rw [abs_of_nonpos (by omega)]; ring
    have h2 : |t - 1| = -t + 1 := by rw [abs_of_neg (by omega)]; ring
    rw [h1, h2, abs_of_neg ht]
    rcases le_or_gt 1 (L + t) with hu | hu
    · rw [max_eq_left (by omega), max_eq_left (by omega), max_eq_left (by omega)]
      nlinarith
    · rcases eq_or_lt_of_le (show L + t ≤ 0 by omega) with hu0 | hu0
      · rw [max_eq_left (by omega), max_eq_right (by omega), max_eq_left (by omega)]
        nlinarith
      · rw [max_eq_right (by omega), max_eq_right (by omega), max_eq_right (by omega)]
        norm_num
  · simp only [zero_add, zero_sub, abs_neg, abs_one, abs_zero, sub_zero]
    rcases le_or_gt 1 L with hL | hL
    · rw [max_eq_left (by omega), max_eq_left (by omega)]
      nlinarith
    · rw [max_eq_right (by omega)]
      rcases le_or_gt 0 L with hL0 | hL0
      · rw [max_eq_left hL0]
        nlinarith
      · rw [max_eq_right hL0.le]
        norm_num
  · have h1 : |t + 1| = t + 1 := abs_of_pos (by omega)
    have h2 : |t - 1| = t - 1 := abs_of_nonneg (by omega)
    rw [h1, h2, abs_of_pos ht]
    rcases le_or_gt 1 (L - t) with hu | hu
    · rw [max_eq_left (by omega), max_eq_left (by omega), max_eq_left (by omega)]
      nlinarith
    · rcases eq_or_lt_of_le (show L - t ≤ 0 by omega) with hu0 | hu0
      · rw [max_eq_right (by omega), max_eq_left (by omega), max_eq_left (by omega)]
        nlinarith
      · rw [max_eq_right (by omega), max_eq_right (by omega), max_eq_right (by omega)]
        norm_num

/-- The barrier `b(x) = (L - ‖x‖_∞)₊²`. -/
def boxBarrier (L : ℤ) (x : Site d) : ℤ := (max (L - supNat x) 0) ^ 2

theorem boxBarrier_nonneg (L : ℤ) (x : Site d) : 0 ≤ boxBarrier L x := sq_nonneg _

theorem boxBarrier_le_profile (L : ℤ) (x : Site d) (i : Fin d) :
    boxBarrier L x ≤ barrierProfile L (x i) := by
  unfold boxBarrier barrierProfile
  have h := abs_le_supNat x i
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max (by omega) le_rfl) 2

theorem unit_apply_self (i : Fin d) : (unit i : Site d) i = 1 := by
  simp [unit]

theorem unit_apply_ne {i j : Fin d} (h : j ≠ i) : (unit j : Site d) i = 0 := by
  simp [unit, Ne.symm h]

/-- The lattice Laplacian of the barrier is at most `2`. -/
theorem lap_boxBarrier_le (hd : 0 < d) (L : ℤ) (x : Site d) : lap (boxBarrier L) x ≤ 2 := by
  obtain ⟨i, hi⟩ := exists_abs_eq_supNat hd x
  set c : Site d → ℤ := fun y => barrierProfile L (y i) with hc
  have hbx : boxBarrier L x = c x := by simp only [hc, boxBarrier, barrierProfile, hi]
  have hle : lap (boxBarrier L) x ≤ lap c x := by
    rw [lap_eq, lap_eq, hbx]
    have := nbrSumZ_mono (fun y => boxBarrier_le_profile L y i) x
    linarith
  refine hle.trans ?_
  rw [lap_eq_sum_second_diff, Finset.sum_eq_single i]
  · simp only [hc, Pi.add_apply, Pi.sub_apply, unit_apply_self]
    linarith [barrierProfile_secondDiff_le L (x i)]
  · intro j _ hji
    simp only [hc, Pi.add_apply, Pi.sub_apply, unit_apply_ne hji, add_zero, sub_zero]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The barrier vanishes where `‖x‖_∞ ≥ L`. -/
theorem boxBarrier_eq_zero {L : ℤ} {x : Site d} {i : Fin d} (h : L ≤ |x i|) :
    boxBarrier L x = 0 := by
  unfold boxBarrier
  have := abs_le_supNat x i
  rw [max_eq_right (by omega)]
  norm_num

/-- The cube `{x : ‖x‖_∞ < r}`. -/
def boxZ (r : ℤ) : Set (Site d) := {x | ∀ i, |x i| < r}

/-- The Laplacian of the integer ceiling: `Δ ⌈p⌉ < Δ p + 2d` in positive dimension. -/
theorem lap_ceil_lt (hd : 0 < d) (p : Site d → ℝ) (x : Site d) :
    (lap (fun y => ⌈p y⌉) x : ℝ) < lapR p x + 2 * d := by
  rw [lap_eq, lapR]
  simp only [nbrSumZ, nbrSum]
  push_cast
  have h1 : ∀ i : Fin d, ((⌈p (x + unit i)⌉ : ℤ) : ℝ) + ((⌈p (x - unit i)⌉ : ℤ) : ℝ) <
      p (x + unit i) + p (x - unit i) + 2 := fun i => by
    linarith [Int.ceil_lt_add_one (p (x + unit i)), Int.ceil_lt_add_one (p (x - unit i))]
  have h2 : (p x : ℝ) ≤ ((⌈p x⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have h3 := Finset.sum_lt_sum_of_nonempty hne fun i _ => h1 i
  have h4 : ∑ i : Fin d, (p (x + unit i) + p (x - unit i) + 2) =
      ∑ i : Fin d, (p (x + unit i) + p (x - unit i)) + 2 * d := by
    rw [Finset.sum_add_distrib]
    simp
    ring
  have h5 : 2 * (d : ℝ) * p x ≤ 2 * d * ((⌈p x⌉ : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- **Confinement by the barrier.** Let `K ≥ 2a`, let `W_n ⊆ {‖x‖_∞ < an}` and let `p` solve
`Δ p = -η 𝟙_{W_n}` in `D = {‖x‖_∞ < 2an}` with `p = 0` off `D`, `p ≥ -((K - 2a) n)²` on `D` and
`p + 1 ≤ ((K - a) n)² - ((K - 2a) n)²` on `W_n`. Then the free odometer of `η 𝟙_{W_n}` vanishes
on `{‖x‖_∞ ≥ Kn}`. -/
theorem freeOdometer_eq_zero_of_barrier (hd : 2 ≤ d) {η : Site d → ℤ} {Wn : Set (Site d)}
    {a K n : ℤ} (ha : 0 ≤ a) (hn : 0 ≤ n) (hK : 2 * a ≤ K)
    (hWn : ∀ x ∈ Wn, ∀ i, |x i| < a * n) {p : Site d → ℝ}
    (hp0 : ∀ x, x ∉ boxZ (2 * a * n) → p x = 0)
    (hp1 : ∀ x ∈ boxZ (2 * a * n), lapR p x = -((Wn.indicator η x : ℤ) : ℝ))
    (hp2 : ∀ x ∈ boxZ (2 * a * n), -((((K - 2 * a) * n : ℤ) : ℝ)) ^ 2 ≤ p x)
    (hp3 : ∀ x ∈ Wn, p x + 1 ≤ (((K - a) * n : ℤ) : ℝ) ^ 2 - (((K - 2 * a) * n : ℤ) : ℝ) ^ 2) :
    ∀ x : Site d, (∃ i, K * n ≤ |x i|) → freeOdometer η Wn x = 0 := by
  classical
  have hd0 : 0 < d := by omega
  set L : ℤ := K * n with hL
  set bd : ℤ := ((K - 2 * a) * n) ^ 2 with hbd
  set D : Set (Site d) := boxZ (2 * a * n) with hD
  set v : Site d → ℤ := fun y => if y ∈ D then min (boxBarrier L y) (bd + ⌈p y⌉)
    else boxBarrier L y with hv
  have hWD : ∀ x ∈ Wn, x ∈ D := fun x hx i => by
    have := hWn x hx i
    nlinarith
  have hvb : ∀ y, v y ≤ boxBarrier L y := fun y => by
    simp only [hv]
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  -- Off `D` the barrier is at most `bd`.
  have hbout : ∀ y, y ∉ D → boxBarrier L y ≤ bd := by
    intro y hy
    simp only [hD, boxZ, Set.mem_ofPred_eq, not_forall, not_lt] at hy
    obtain ⟨i, hi⟩ := hy
    have hs := abs_le_supNat y i
    unfold boxBarrier
    rw [hbd]
    have hnn : 0 ≤ (K - 2 * a) * n := mul_nonneg (by omega) hn
    refine pow_le_pow_left₀ (le_max_right _ _) (max_le (by nlinarith) hnn) 2
  have hvsec : ∀ y, v y ≤ bd + ⌈p y⌉ := by
    intro y
    by_cases hy : y ∈ D
    · simp only [hv, ite_eq_left hy]
      exact min_le_right _ _
    · simp only [hv, ite_eq_right hy, hp0 y hy, Int.ceil_zero, add_zero]
      exact hbout y hy
  -- On `W_n` the second branch is active.
  have hWsec : ∀ x ∈ Wn, v x = bd + ⌈p x⌉ := by
    intro x hx
    simp only [hv, ite_eq_left (hWD x hx)]
    refine min_eq_right ?_
    have hs : (supNat x : ℤ) < a * n := by
      obtain ⟨i, hi⟩ := exists_abs_eq_supNat hd0 x
      rw [← hi]
      exact hWn x hx i
    have hb : ((K - a) * n) ^ 2 ≤ boxBarrier L x := by
      unfold boxBarrier
      have hnn : 0 ≤ (K - a) * n := mul_nonneg (by omega) hn
      exact pow_le_pow_left₀ hnn (le_max_of_le_left (by nlinarith)) 2
    have hc := Int.ceil_lt_add_one (p x)
    have h3 := hp3 x hx
    have h4 : ((bd + ⌈p x⌉ : ℤ) : ℝ) ≤ ((((K - a) * n) ^ 2 : ℤ) : ℝ) := by
      push_cast [hbd]
      push_cast at h3
      linarith
    have h5 : bd + ⌈p x⌉ ≤ ((K - a) * n) ^ 2 := by exact_mod_cast h4
    exact h5.trans hb
  -- The stabilizing inequality.
  have hstab : v ∈ stabilizing (Wn.indicator η) Set.univ := by
    rw [mem_stabilizing_univ]
    refine ⟨fun y => ?_, fun x => ?_⟩
    · simp only [hv]
      split_ifs with hy
      · refine le_min (boxBarrier_nonneg L y) ?_
        have h2 := hp2 y hy
        have hc := Int.le_ceil (p y)
        have : (0 : ℝ) ≤ ((bd + ⌈p y⌉ : ℤ) : ℝ) := by
          push_cast [hbd]
          push_cast at h2
          linarith
        exact_mod_cast this
      · exact boxBarrier_nonneg L y
    · -- Second-branch estimate.
      have hsecond : v x = bd + ⌈p x⌉ → x ∈ D →
          lap v x + Wn.indicator η x ≤ 2 * (d : ℤ) - 1 := by
        intro hvx hxD
        have hle : lap v x ≤ lap (fun y => ⌈p y⌉) x := by
          rw [lap_eq, lap_eq, hvx]
          have := nbrSumZ_mono hvsec x
          have hconst := nbrSumZ_add_const (fun y => ⌈p y⌉) bd x
          linarith
        have hlt := lap_ceil_lt hd0 p x
        rw [hp1 x hxD] at hlt
        have : ((lap (fun y => ⌈p y⌉) x + Wn.indicator η x : ℤ) : ℝ) < 2 * d := by
          push_cast
          linarith
        have : lap (fun y => ⌈p y⌉) x + Wn.indicator η x < 2 * (d : ℤ) := by exact_mod_cast this
        omega
      -- First-branch estimate (`x ∉ W_n`).
      have hfirst : v x = boxBarrier L x → x ∉ Wn →
          lap v x + Wn.indicator η x ≤ 2 * (d : ℤ) - 1 := by
        intro hvx hxW
        have hle : lap v x ≤ lap (boxBarrier L) x := by
          rw [lap_eq, lap_eq, hvx]
          have := nbrSumZ_mono hvb x
          linarith
        rw [Set.indicator_of_notMem hxW, add_zero]
        have := lap_boxBarrier_le hd0 L x
        omega
      by_cases hxW : x ∈ Wn
      · exact hsecond (hWsec x hxW) (hWD x hxW)
      · by_cases hxD : x ∈ D
        · rcases min_choice (boxBarrier L x) (bd + ⌈p x⌉) with h | h
          · exact hfirst (by simp only [hv, ite_eq_left hxD]; exact h) hxW
          · exact hsecond (by simp only [hv, ite_eq_left hxD]; exact h) hxD
        · exact hfirst (by simp only [hv, ite_eq_right hxD]) hxW
  intro x ⟨i, hi⟩
  have h1 := freeOdometer_le hstab x
  have h2 := hvb x
  have h3 := boxBarrier_eq_zero (L := L) hi
  have h4 := freeOdometer_nonneg η Wn x
  exact le_antisymm (h1.trans (h2.trans h3.le)) h4

end RandomSandpile

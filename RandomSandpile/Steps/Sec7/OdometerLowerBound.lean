import RandomSandpile.Draft.Section7
import RandomSandpile.Steps.Sec3.LeastAction

/-!
# Steps of Lemma 7.4 (a lower bound on the odometer)

Carving of `RandomSandpile.OdometerLowerBoundStmt` (Lemma 7.4, `lowerbound`,
`paper/random_piles-corrected.tex`) into steps and the reduction
`odometerLowerBound_of_steps`, which takes Lemma 7.3 (`DivisibleHomogenizeStmt`) as an explicit
hypothesis.

The printed proof compares the open-boundary odometer `w_n` of `η` in `B_n` with the Green
potentials `r_n(x) = ∑_{y ∈ B_n} g_n(x, y) η(y)` (`greenPotentialBall`) and
`d_n(x) = ∑_{y ∈ B_n} g_n(x, y) E(η(0))` (`greenPotentialBallMean`), which solve
`Δ_{ℤ^d} r_n = -η`, `Δ_{ℤ^d} d_n = -E(η(0))` in `B_n` and vanish on `∂B_n`.
Here `q_l(x) = l |x|² / (2d)` (`qlZ`), so that `Δ_{ℤ^d} q_l = l`.

* **Discrete minimum principle** (1243-1247). A function superharmonic in a finite
  `A ⊂ ℤ^d` is bounded below in `A` by its values on `∂A`. Step `SuperharmonicMinPrincipleStmt`.
* **Comparison with `r_n`**. `w_n - r_n - q_{2d-1}` is superharmonic in `B_n`
  because `w_n` is stabilizing, and `w_n = r_n = 0` on `∂B_n`; with `|y| < n + 1` on `∂B_n` this
  gives `w_n(x) ≥ r_n(x) - (2d - 1)((n + 1)² - |x|²) / (2d)`. Step
  `StabilizingGreenComparisonStmt`. (The paper writes the boundary term as
  `(2d-1)(n² - |x|²)/2`, dropping the `O(n)` error `max_{∂B_n} |y|² - n²` and the
  normalisation `1/(2d)` of `q_l`;
* **Lemma 7.3**. `r_n ≥ d_n - ε' C n²` on `B_n` for `n ≥ n_0(ε')`. Hypothesis.
* **Lower bound on `d_n`**. `d_n + q_m` is harmonic in `B_n` for `m = E(η(0))`
  and `d_n = 0` on `∂B_n`, where `|y| ≥ n`; so `d_n(x) ≥ m (n² - |x|²) / (2d)` for `m ≥ 0`.
  Step `MeanGreenPotentialLowerStmt`.
* **Choice of constants**, done in the reduction. With
  `δ := E(η(0)) - (2d - 1) > 0` (a parenthesization slip) the
  three bounds give `w_n(x) ≥ δ (n² - |x|²)/(2d) - (2d - 1)(2n + 1)/(2d) - ε' C n²`. On
  `B_{(1-ε)n}`, `n² - |x|² ≥ ε n²` (for `ε < 1`; for `ε ≥ 1` the ball is empty), and
  `ε' := δ ε / (4 d C)` gives `w_n(x) ≥ δ ε n² / (4d) - (2d - 1)(2n + 1)/(2d) ≥ 1` for `n` large.

The existence part of the statement (some `w ∈ 𝓛(η, B_n) ∩ 𝓢(η, B_n)` vanishes on `∂B_n`) is
Step 2 of Proposition 3.1, `ExistsLegalStabilizingStmt` (a legal stabilizing toppling function,
which vanishes off `B_n`), proved as `RandomSandpile.existsLegalStabilizing`; the connectedness of
`B_n` required by `LeastActionStmt` is not needed. The reduction also uses the elementary facts
proved below in the namespace `OdometerLowerBound`: `B_r` is finite (`ballZ0_finite`), and
`n ≤ |y| < n + 1` on `∂B_n` (`le_norm_of_mem_bdry_ballZ0`, `norm_lt_of_mem_bdry_ballZ0`).

Only the high-density hypothesis `E(η(0)) > 2d - 1` and Lemma 7.3 are used; `w_n` only needs to
be stabilizing and to vanish on `∂B_n` for the lower bound, legality is not used.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter

namespace RandomSandpile

/-- **Discrete minimum principle** (1243-1247): for `d ≥ 1`, a finite `A ⊂ ℤ^d`
and `f : ℤ^d → ℝ` superharmonic in `A` (`Δ_{ℤ^d} f ≤ 0` in `A`), every value of `f` in `A` is
bounded below by a value of `f` on `∂A`: `f(x) ≥ min_{∂A} f`. -/
def SuperharmonicMinPrincipleStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (A : Set (Site d)), A.Finite → ∀ f : Site d → ℝ,
    (∀ x ∈ A, lapR f x ≤ 0) → ∀ x ∈ A, ∃ y ∈ bdry A, f y ≤ f x

/-- **Comparison of the odometer with `r_n`**: for `d ≥ 1`, `n ∈ ℕ`, a
configuration `η` and a toppling function `w` stabilizing for `η` in `B_n`
(`Δ_{ℤ^d} w + η ≤ 2d - 1` in `B_n`) with `w = 0` on `∂B_n`,
`w(x) ≥ r_n(x) - (2d - 1)((n + 1)² - |x|²) / (2d)` for `x ∈ B_n`. -/
def StabilizingGreenComparisonStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (n : ℕ) (η : Config d) (w : Site d → ℤ),
    w ∈ stabilizing η (ballZ0 (n : ℝ)) → (∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)), w y = 0) →
      ∀ x ∈ ballZ0 (d := d) (n : ℝ),
        greenPotentialBall n η x - (2 * d - 1) * (((n : ℝ) + 1) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) ≤
          (w x : ℝ)

/-- **Lower bound on `d_n`**: for `d ≥ 1`, `n ∈ ℕ` and a density `m ≥ 0`,
`d_n(x) = ∑_{y ∈ B_n} g_n(x, y) m ≥ m (n² - |x|²) / (2d)` for `x ∈ B_n`. -/
def MeanGreenPotentialLowerStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (n : ℕ) (m : ℝ), 0 ≤ m → ∀ x ∈ ballZ0 (d := d) (n : ℝ),
    m * ((n : ℝ) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) ≤ greenPotentialBallMean n m x

variable {d : ℕ}

/-! ### Elementary facts on lattice balls (namespaced to avoid clashes with other files) -/

namespace OdometerLowerBound

/-- `toE 0 = 0`. -/
theorem toE_zero : toE (0 : Site d) = 0 := by
  ext i; simp

theorem mem_ballZ0 {r : ℝ} {x : Site d} : x ∈ ballZ0 r ↔ ‖toE x‖ < r := by
  simp [ballZ0, ballZ, toE_zero]

/-- The lattice ball `B_r` is finite. -/
theorem ballZ0_finite (r : ℝ) : (ballZ0 (d := d) r).Finite := by
  refine (Set.finite_Icc (fun _ : Fin d => -⌈r⌉) fun _ => ⌈r⌉).subset fun x hx => ?_
  have hx' := mem_ballZ0.1 hx
  have hi : ∀ i, |(x i : ℝ)| < r := fun i => by
    have := PiLp.norm_apply_le (toE x) i
    simp only [toE_apply, Real.norm_eq_abs] at this
    linarith
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := (abs_lt.1 (hi i)).1
    have h2 : (-⌈r⌉ : ℝ) ≤ x i := by linarith [Int.le_ceil r]
    exact_mod_cast h2
  · have h1 := (abs_lt.1 (hi i)).2
    have h2 : (x i : ℝ) ≤ ⌈r⌉ := by linarith [Int.le_ceil r]
    exact_mod_cast h2

theorem toE_add (x y : Site d) : toE (x + y) = toE x + toE y := by
  ext i; simp

theorem toE_sub (x y : Site d) : toE (x - y) = toE x - toE y := by
  ext i; simp

theorem norm_toE_unit (i : Fin d) : ‖toE (unit i)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [unit, Pi.single_apply, apply_ite]

/-- On `∂B_r`, `|y| ≥ r`. -/
theorem le_norm_of_mem_bdry_ballZ0 {r : ℝ} {y : Site d} (hy : y ∈ bdry (ballZ0 r)) :
    r ≤ ‖toE y‖ :=
  not_lt.1 fun h => (mem_bdry.1 hy).1 (mem_ballZ0.2 h)

/-- On `∂B_r`, `|y| < r + 1`. -/
theorem norm_lt_of_mem_bdry_ballZ0 {r : ℝ} {y : Site d} (hy : y ∈ bdry (ballZ0 r)) :
    ‖toE y‖ < r + 1 := by
  obtain ⟨-, x, hx, i, hi | hi⟩ := mem_bdry.1 hy
  · have hy' : y = x - unit i := by rw [hi]; abel
    rw [hy', toE_sub]
    calc ‖toE x - toE (unit i)‖ ≤ ‖toE x‖ + ‖toE (unit i)‖ := norm_sub_le _ _
      _ < r + 1 := by rw [norm_toE_unit]; linarith [mem_ballZ0.1 hx]
  · rw [hi, toE_add]
    calc ‖toE x + toE (unit i)‖ ≤ ‖toE x‖ + ‖toE (unit i)‖ := norm_add_le _ _
      _ < r + 1 := by rw [norm_toE_unit]; linarith [mem_ballZ0.1 hx]

/-- The elementary inequality of the choice of constants: if `a n ≥ 16 d` and
`n ≥ 1`, then `a n² / (4d) - (2d - 1)(2n + 1) / (2d) ≥ 1`. -/
theorem one_le_of_large {a n : ℝ} (hd : 1 ≤ (d : ℝ)) (hn : 1 ≤ n) (han : 16 * d ≤ a * n) :
    1 ≤ a * n ^ 2 / (4 * d) - (2 * d - 1) * (2 * n + 1) / (2 * d) := by
  have hd0 : 0 < (d : ℝ) := by linarith
  have h1 : 16 * d * n ≤ a * n * n := mul_le_mul_of_nonneg_right han (by linarith)
  have hnum : 0 ≤ (a * n ^ 2 - 2 * (2 * d - 1) * (2 * n + 1) - 4 * d) / (4 * d) :=
    div_nonneg (by nlinarith) (by positivity)
  have e : a * n ^ 2 / (4 * d) - (2 * d - 1) * (2 * n + 1) / (2 * d) =
      1 + (a * n ^ 2 - 2 * (2 * d - 1) * (2 * n + 1) - 4 * d) / (4 * d) := by
    field_simp; ring
  linarith

end OdometerLowerBound

open OdometerLowerBound

/-- **Reduction for Lemma 7.4**: Lemma 7.3 (`DivisibleHomogenizeStmt`), the
existence of a legal stabilizing toppling function (Step 2 of Proposition 3.1), the comparison of
`w_n` with `r_n` and the lower bound on `d_n` give `OdometerLowerBoundStmt`. -/
theorem odometerLowerBound_of_steps (h73 : DivisibleHomogenizeStmt)
    (hex : ExistsLegalStabilizingStmt) (hcomp : StabilizingGreenComparisonStmt)
    (hmean : MeanGreenPotentialLowerStmt) : OdometerLowerBoundStmt := by
  intro d hd E hE
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hd0 : (0 : ℝ) < d := by linarith
  set m := meanEta E.P with hm_def
  have hδ : 0 < m - (2 * d - 1) := by unfold HighDensity at hE; linarith
  have hm0 : 0 ≤ m := by linarith
  filter_upwards [h73 d hd E] with η ⟨C, hC, hη⟩ ε hε
  set δ := m - (2 * d - 1) with hδ_def
  set ε₁ := min ε 1 with hε₁_def
  have hε₁ : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  set a := δ * ε₁ with ha_def
  have ha : 0 < a := mul_pos hδ hε₁
  obtain ⟨n₀', hn₀'⟩ := hη (a / (4 * d * C)) (by positivity)
  refine ⟨max n₀' (⌈16 * d / a⌉₊ + 1), fun n hn => ⟨?_, ?_⟩⟩
  · obtain ⟨v, hvL, hvS⟩ := hex d (by omega) (ballZ0 (n : ℝ)) (ballZ0_finite _) η
    exact ⟨v, ⟨mem_locLegal_of_isLegal hvL, hvS⟩, fun y hy =>
      hvL.eq_zero_of_notMem (Set.disjoint_right.1 (bdry_disjoint _) hy)⟩
  · rintro w ⟨-, hwS⟩ hw0 x hx
    have hn1 : n₀' ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : ⌈16 * d / a⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have han : 16 * d ≤ a * n := by
      have h1 : 16 * d / a ≤ (n : ℝ) := by
        refine (Nat.le_ceil _).trans ?_
        exact_mod_cast (show ⌈16 * (d : ℝ) / a⌉₊ ≤ n by omega)
      rw [div_le_iff₀ ha] at h1; linarith
    have hxn : ‖toE x‖ < (1 - ε) * n := mem_ballZ0.1 hx
    -- `ε < 1` (otherwise `B_{(1-ε)n}` is empty), so `|x| < (1 - ε₁) n`
    have hxn₁ : ‖toE x‖ < (1 - ε₁) * n := by
      rcases le_total ε 1 with h | h
      · rwa [hε₁_def, min_eq_left h]
      · exfalso
        have : (1 - ε) * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith [norm_nonneg (toE x)]
    have hxB : x ∈ ballZ0 (d := d) (n : ℝ) := by
      refine mem_ballZ0.2 (hxn₁.trans_le ?_)
      nlinarith
    have hgap : ε₁ * n ^ 2 ≤ (n : ℝ) ^ 2 - ‖toE x‖ ^ 2 := by
      have h0 := norm_nonneg (toE x)
      have hsq : ‖toE x‖ ^ 2 ≤ ((1 - ε₁) * n) ^ 2 := pow_le_pow_left₀ h0 hxn₁.le 2
      nlinarith
    have h1 := hcomp d hd1 n η w hwS hw0 x hxB
    have h2 := (abs_le.1 (hn₀' n hn1 x hxB)).1
    have h3 := hmean d hd1 n m hm0 x hxB
    have hCε : a / (4 * d * C) * C * (n : ℝ) ^ 2 = a * n ^ 2 / (4 * d) := by
      field_simp
    rw [hCε] at h2
    have hfin := one_le_of_large hdR hnR han
    have key : a * n ^ 2 / (4 * d) - (2 * d - 1) * (2 * n + 1) / (2 * d) ≤ (w x : ℝ) := by
      have e1 : m * ((n : ℝ) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) -
          (2 * d - 1) * (((n : ℝ) + 1) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) =
          δ * ((n : ℝ) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) - (2 * d - 1) * (2 * n + 1) / (2 * d) := by
        rw [hδ_def]; field_simp; ring
      have e2 : a * n ^ 2 / (2 * d) ≤ δ * ((n : ℝ) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) := by
        rw [ha_def, mul_assoc]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hδ.le) (by positivity)
      have e3 : a * n ^ 2 / (4 * d) = a * n ^ 2 / (2 * d) - a * n ^ 2 / (4 * d) := by
        field_simp; ring
      linarith
    exact_mod_cast hfin.trans key

end RandomSandpile

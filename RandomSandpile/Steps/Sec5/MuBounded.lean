import RandomSandpile.Draft.Section5

/-! # Lemma 5.4 (bounds on `μ` and `μ*`): proof steps

The printed proof of Lemma 5.4 (`MuBoundedStmt`, `paper/random_piles-corrected.tex`, with
the proposed correction of the vanishing range of `μ` drafted in `MuBoundedStmt`) decomposed into step
statements, the support lemmas `mu_le_of_steps`, `muStar_le_of_steps` (the bound on every finite
`A ⊂ ℤ^d`, which is the form used in Lemma 5.5), and the reduction
`muBounded_of_steps` concluding exactly `MuBoundedStmt`.

* `LocLegalLapLowerStmt` (683): a locally legal toppling `u ∈ 𝓛(η, A)` satisfies
  `Δ_{ℤ^d} u + η ≥ min(0, η)` in `A`; hence `Δ_{ℤ^d} u ≥ -max(η_max, 0)` in `A`;
* `LapQuadraticStmt`: `Δ_{ℤ^d}(q_l + q_M) = l + Tr(M)` on the lattice;
* `SupGradVolumeLeStmt` (the discrete Monge-Ampère bound): at `x ∈ A`, a supergradient
  `p ∈ ∂⁺(w, x, A)` satisfies `w(x + e_i) - w(x) ≤ p_i ≤ w(x) - w(x - e_i)`, so `∂⁺(w, x, A)` lies
  in a box with side lengths `-Δ_i w(x) ≥ 0`, and the arithmetic-geometric mean inequality gives
  `|∂⁺(w, x, A)| ≤ d^{-d} (-Δ_{ℤ^d} w(x))^d`; dually `|∂⁻(w, x, A)| ≤ d^{-d} (Δ_{ℤ^d} w(x))^d`.
  The positive parts take care of an empty supergradient set, and they give the vanishing ranges:
  when `-Δ_{ℤ^d} w(x) ≤ 0` the box is degenerate.

The printed proof concludes "by Lemma 5.3"; only the subadditivity
`|∂⁺(w, A)| ≤ ∑_{x ∈ A} |∂⁺(w, x, A)|` of Lebesgue measure is needed, so Lemma 5.3 is not a step.
For `μ` the printed bound `-Δ_{ℤ^d} w ≤ η_max + Tr(M) + l` uses `min(-η_max, 0) ≥ -η_max`, which
needs `η_max ≥ 0`; the steps use `-max(η_max, 0)`, as in the drafted correction. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal

namespace RandomSandpile

/-- Step 1 (683). A locally legal toppling `u ∈ 𝓛(η, A)` satisfies
`Δ_{ℤ^d} u(x) + η(x) ≥ min(0, η(x))` at every `x ∈ A`. -/
def LocLegalLapLowerStmt : Prop :=
  ∀ (d : ℕ) (η : Site d → ℤ) (A : Set (Site d)) (u : Site d → ℤ), u ∈ locLegal η A →
    ∀ x ∈ A, min 0 (η x) ≤ lap u x + η x

/-- Step 2. The discrete Laplacian of the parabola `q_l + q_M` restricted to the lattice
is constant, `Δ_{ℤ^d}(q_l + q_M) = l + Tr(M)`. The dimension is positive: `q_l = l |x|² / (2d)`
 has a junk value for `d = 0`. -/
def LapQuadraticStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (x : Site d),
    lapR (fun y => qlZ l y + qMZ M y) x = l + M.trace

/-- Step 3 (the discrete Monge-Ampère bound at one site). For `x ∈ A`,
`|∂⁺(w, x, A)| ≤ d^{-d} ((-Δ_{ℤ^d} w(x))⁺)^d` and `|∂⁻(w, x, A)| ≤ d^{-d} ((Δ_{ℤ^d} w(x))⁺)^d`. -/
def SupGradVolumeLeStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)) (w : Site d → ℝ) (x : Site d), x ∈ A →
    volume (supGrad w x A) ≤ ENNReal.ofReal ((max (-lapR w x) 0 / d) ^ d) ∧
      volume (subGrad w x A) ≤ ENNReal.ofReal ((max (lapR w x) 0 / d) ^ d)

/-! ### Support lemmas: the bounds on every finite set -/

/-- The discrete Laplacian of a difference. -/
theorem lapR_sub' {d : ℕ} (f g : Site d → ℝ) (x : Site d) :
    lapR (fun y => f y - g y) x = lapR f x - lapR g x := by
  have h : ∀ i : Fin d, (f (x + unit i) - g (x + unit i)) + (f (x - unit i) - g (x - unit i)) =
      (f (x + unit i) + f (x - unit i)) - (g (x + unit i) + g (x - unit i)) := fun i => by ring
  simp only [lapR, nbrSum, h, Finset.sum_sub_distrib]
  ring

/-- Summing a per-site bound over a finite set: if each `|∂(x)|` is at most `ofReal c`, then the
measure of `⋃_{x ∈ A} ∂(x)` is at most `c |A|`. -/
theorem volume_biUnion_le_ncard {d : ℕ} {A : Set (Site d)} (hA : A.Finite)
    (S : Site d → Set (Rd d)) {c : ℝ} (hc : 0 ≤ c)
    (hS : ∀ x ∈ A, volume (S x) ≤ ENNReal.ofReal c) :
    volume (⋃ x ∈ A, S x) ≤ ENNReal.ofReal (c * (A.ncard : ℝ)) := by
  have hU : (⋃ x ∈ A, S x) = ⋃ x ∈ hA.toFinset, S x := by simp
  rw [hU]
  refine (measure_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum fun x hx => hS x (hA.mem_toFinset.1 hx)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card A hA, mul_comm,
    ENNReal.ofReal_mul hc, ENNReal.ofReal_natCast]

/-- **Support lemma for `μ`**. If
`η ≤ η_max` in a finite `A`, then
`μ(A, η, l, M) ≤ d^{-d} ((max(η_max, 0) + l + Tr(M))⁺)^d |A|`. -/
theorem mu_le_of_steps (hlegal : LocLegalLapLowerStmt) (hquad : LapQuadraticStmt)
    (hvol : SupGradVolumeLeStmt) {d : ℕ} (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite)
    {η : Site d → ℤ} {ηmax : ℤ} (hη : ∀ x ∈ A, η x ≤ ηmax) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    mu A η l M ≤ ENNReal.ofReal
      ((max (((max ηmax 0 : ℤ) : ℝ) + l + M.trace) 0 / d) ^ d * (A.ncard : ℝ)) := by
  refine iSup₂_le fun w hw => ?_
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.1 hw
  refine volume_biUnion_le_ncard hA _ (by positivity) fun x hx => (hvol d A _ x hx).1.trans ?_
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ d)
  refine div_le_div_of_nonneg_right (max_le_max_right _ ?_) (Nat.cast_nonneg d)
  rw [lapR_sub', lapR_intCast, hquad d hd]
  have h1 := hlegal d η A u hu x hx
  have h2 : (min 0 (η x) - η x : ℤ) ≥ -max ηmax 0 := by
    have := hη x hx
    rcases le_total 0 (η x) with h | h
    · rw [min_eq_left h]; have := le_max_left ηmax 0; omega
    · rw [min_eq_right h]; have := le_max_right ηmax 0; omega
  have h3 : ((-max ηmax 0 : ℤ) : ℝ) ≤ (lap u x : ℝ) := by exact_mod_cast h2.le.trans (by omega)
  push_cast at h3 ⊢
  linarith

/-- **Support lemma for `μ*`** ("the other direction is similar", on an arbitrary finite
set). If `η ≥ η_min` in a finite `A`, then
`μ*(A, η, l, M) ≤ d^{-d} (((2d - 1) - η_min - l - Tr(M))⁺)^d |A|`, for `d ≥ 1`. -/
theorem muStar_le_of_steps (hquad : LapQuadraticStmt) (hvol : SupGradVolumeLeStmt) {d : ℕ}
    (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) {η : Site d → ℤ} {ηmin : ℤ} (hη : ∀ x ∈ A, ηmin ≤ η x)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStar A η l M ≤ ENNReal.ofReal
      ((max ((2 * (d : ℝ) - 1) - (ηmin : ℝ) - l - M.trace) 0 / d) ^ d * (A.ncard : ℝ)) := by
  refine iSup₂_le fun w hw => ?_
  obtain ⟨v, hv, rfl⟩ := mem_perturbedSuper.1 hw
  refine volume_biUnion_le_ncard hA _ (by positivity) fun x hx => (hvol d A _ x hx).2.trans ?_
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ d)
  refine div_le_div_of_nonneg_right (max_le_max_right _ ?_) (Nat.cast_nonneg d)
  rw [lapR_sub', lapR_intCast, hquad d hd]
  have h1 := hv.2 x hx
  have h2 := hη x hx
  have h3 : (lap v x : ℝ) ≤ 2 * (d : ℝ) - 1 - (ηmin : ℝ) := by
    have : lap v x ≤ 2 * (d : ℤ) - 1 - ηmin := by omega
    exact_mod_cast this
  linarith

/-! ### The reduction -/

/-- The lattice cube `Q_r` is finite. -/
theorem cubeZ0_finite' {d : ℕ} (r : ℝ) : (cubeZ0 r : Set (Site d)).Finite := by
  refine (Set.finite_Icc (fun _ : Fin d => -⌈r⌉) (fun _ => ⌈r⌉)).subset fun y hy => ?_
  have hy' : ∀ i, |((y i - 0 : ℤ) : ℝ)| < r := hy
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_lt.1 (hy' i)).1
    have : -(⌈r⌉ : ℝ) ≤ (y i : ℝ) := by
      push_cast at this; linarith [Int.le_ceil r]
    exact_mod_cast this
  · have := (abs_lt.1 (hy' i)).2
    have : (y i : ℝ) ≤ ⌈r⌉ := by
      push_cast at this; linarith [Int.le_ceil r]
    exact_mod_cast this

/-- For `n ≥ 1` the lattice cube `Q_n` contains the origin, so `|Q_n| ≥ 1`. -/
theorem one_le_ncard_cubeZ0 {d : ℕ} {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ ((cubeZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
  have h0 : (0 : Site d) ∈ cubeZ0 (n : ℝ) := fun i => by
    simp only [Pi.zero_apply, sub_zero, Int.cast_zero, abs_zero, Nat.cast_pos]; omega
  exact_mod_cast (Set.ncard_pos (cubeZ0_finite' _)).2 ⟨0, h0⟩

/-- From `μ ≤ c |Q_n|` with `c ≥ 0` and `n ≥ 1`, the strict bound `μ < (c + 1) |Q_n|`. -/
theorem lt_ofReal_succ_mul {d : ℕ} {m : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n)
    (h : m ≤ ENNReal.ofReal (c * ((cubeZ0 (d := d) (n : ℝ)).ncard : ℝ))) :
    m < ENNReal.ofReal ((c + 1) * ((cubeZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  have hN := one_le_ncard_cubeZ0 (d := d) hn
  refine h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
  nlinarith

/-- **Reduction for Lemma 5.4**: the steps imply `MuBoundedStmt` exactly. -/
theorem muBounded_of_steps (hlegal : LocLegalLapLowerStmt) (hquad : LapQuadraticStmt)
    (hvol : SupGradVolumeLeStmt) : MuBoundedStmt := by
  intro d hd
  refine ⟨fun ηmax l M _ => ⟨_, fun n hn η hη => lt_ofReal_succ_mul (by positivity) hn
      (mu_le_of_steps hlegal hquad hvol (by omega) (cubeZ0_finite' _) (fun x _ => hη x) l M)⟩,
    fun ηmin l M _ => ⟨_, fun n hn η hη => lt_ofReal_succ_mul (by positivity) hn
      (muStar_le_of_steps hquad hvol (by omega) (cubeZ0_finite' _) (fun x _ => hη x) l M)⟩,
    fun ηmax l M _ hl n η hη => ?_, fun ηmin l M _ hl n η hη => ?_⟩
  · have hd0 : d ≠ 0 := by omega
    refine le_antisymm ((mu_le_of_steps hlegal hquad hvol (by omega) (cubeZ0_finite' _)
      (fun x _ => hη x) l M).trans (le_of_eq ?_)) bot_le
    rw [max_eq_right (by linarith), zero_div, zero_pow hd0, zero_mul, ENNReal.ofReal_zero]
  · have hd0 : d ≠ 0 := by omega
    refine le_antisymm ((muStar_le_of_steps hquad hvol (by omega) (cubeZ0_finite' _)
      (fun x _ => hη x) l M).trans (le_of_eq ?_)) bot_le
    rw [max_eq_right (by linarith), zero_div, zero_pow hd0, zero_mul, ENNReal.ofReal_zero]

end RandomSandpile

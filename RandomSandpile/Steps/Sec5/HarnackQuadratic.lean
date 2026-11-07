import RandomSandpile.Draft.Section5

/-! # Proposition 5.2 (quadratic growth from the discrete Harnack inequality): proof steps

Proposition 5.2 (`HarnackQuadraticStmt`, `paper/random_piles-corrected.tex`) is cited from
Levine-Peres (2010), Lemma 2.17, without proof. We prove it from the discrete Harnack inequality
for nonnegative harmonic functions of Lattice-Probability (`LatticeProb.harnack`,
`LatticeProb/Walk/Harnack/SmallR.lean`). The proof is decomposed into three steps; the reduction
`harnackQuadratic_of_steps` concludes exactly `HarnackQuadraticStmt`. Boxes are the sup-norm boxes
`LatticeProb.box d r = [-r, r]^d ∩ ℤ^d`.

* `BoxHarnackBddLapStmt`: the Harnack inequality for nonnegative functions with bounded
  Laplacian. If `f ≥ 0` on `box d (2r)` and `|Δ f| ≤ λ` on `box d (2r - 1)`, then
  `f(y) ≤ A f(z) + A λ r²` for `y, z ∈ box d r`, with `A` depending only on `d`. Write `f = h + w`
  with `h` the harmonic function on `box d (2r - 1)` with boundary values `f` (nonnegative, so
  `LatticeProb.harnack` applies) and `w` vanishing on the boundary, `|w| ≤ λ E[τ] ≤ 2λr²`;
* `ExpGrowthBddLapStmt`: the crude bound `f(z) ≤ λ (2d + 1)^{|z|_1}` on `B_R` for `f ≥ 0`,
  `f(0) = 0`, `Δ f ≤ λ` on `B_R`, from `f(z + e) ≤ ∑_{y ∼ z} f(y) = Δ f(z) + 2d f(z)`; it handles
  the points `x` with `|x|` below a scale depending on `β`, where the boxes of the Harnack chain do
  not fit;
* `LatticeSegmentStmt`: the discrete segment `c_k = ⌊k x / N⌋` from `0` to `x`, whose points
  satisfy `|c_k,i| ≤ |x_i|` and whose steps are at most `|x_i| / N + 1` in each coordinate.

The reduction (the standard Harnack chain): for `x ∈ B_{βR}` with `s = |x|` large, set
`a = (1 - β) / (2βd)` and `r = ⌊s a⌋`. The boxes `c_k + box d (2r)` lie in `B_R` since
`|c_k| + 2dr ≤ s + s (1 - β) / β = s / β < R`, consecutive points of the segment lie in a common
box of radius `r` when `N ≥ 2 / a`, and iterating `f(c_{k+1}) ≤ A f(c_k) + A λ r²` from
`f(c_0) = f(0) = 0` gives `f(x) ≤ N A^N λ r² ≤ N A^N a² λ s²`. -/

open LatticeProb

namespace RandomSandpile

/-- Step (Harnack inequality for nonnegative functions with bounded Laplacian, on boxes). There
is `A ≥ 1` depending only on `d` such that for `r ≥ 1`, if `f ≥ 0` on `box d (2r)` and
`|Δ_{ℤ^d} f| ≤ λ` on `box d (2r - 1)`, then `f(y) ≤ A f(z) + A λ r²` for all `y, z ∈ box d r`. -/
def BoxHarnackBddLapStmt : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ A : ℝ, 1 ≤ A ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (lam : ℝ) (f : Site d → ℝ),
    (∀ y ∈ box d (2 * r), 0 ≤ f y) → (∀ y ∈ box d (2 * r - 1), |lapR f y| ≤ lam) →
    ∀ y ∈ box d r, ∀ z ∈ box d r, f y ≤ A * f z + A * lam * (r : ℝ) ^ 2

/-- Step (exponential growth bound). If `f ≥ 0`, `f(0) = 0` and `Δ_{ℤ^d} f ≤ λ` on `B_R`, then
`f(z) ≤ λ (2d + 1)^{|z|_1}` for `z ∈ B_R`. -/
def ExpGrowthBddLapStmt : Prop :=
  ∀ (d : ℕ) (R lam : ℝ) (f : Site d → ℝ), (∀ x, 0 ≤ f x) → f 0 = 0 → 0 ≤ lam →
    (∀ x ∈ ballZ0 R, lapR f x ≤ lam) →
    ∀ z ∈ ballZ0 R, f z ≤ lam * (2 * (d : ℝ) + 1) ^ (∑ i, (z i).natAbs)

/-- Step (discrete segment). For `x ∈ ℤ^d` and `N ≥ 1` there are lattice points
`c_0 = 0, c_1, …, c_N = x` with `|c_k,i| ≤ |x_i|` for `k ≤ N` and
`|c_{k+1},i - c_k,i| ≤ |x_i| / N + 1`. -/
def LatticeSegmentStmt : Prop :=
  ∀ (d : ℕ) (x : Site d) (N : ℕ), 0 < N → ∃ c : ℕ → Site d, c 0 = 0 ∧ c N = x ∧
    (∀ k ≤ N, ∀ i, |c k i| ≤ |x i|) ∧
    ∀ k < N, ∀ i, |((c (k + 1) i - c k i : ℤ) : ℝ)| ≤ |(x i : ℝ)| / N + 1

/-! ### Support lemmas -/

section Support

variable {d : ℕ}

theorem toE_zero_harnack : toE (0 : Site d) = 0 := by
  ext i; simp

theorem mem_ballZ0_iff_norm (x : Site d) (r : ℝ) : x ∈ ballZ0 r ↔ ‖toE x‖ < r := by
  simp [ballZ0, ballZ, toE_zero_harnack]

theorem toE_add_harnack (y z : Site d) : toE (y + z) = toE y + toE z := by
  ext i; simp

/-- `|x_i| ≤ |x|`. -/
theorem abs_le_norm_toE (x : Site d) (i : Fin d) : |(x i : ℝ)| ≤ ‖toE x‖ := by
  have h := PiLp.norm_apply_le (toE x) i
  simpa [Real.norm_eq_abs] using h

/-- The Euclidean norm is monotone in the absolute values of the coordinates. -/
theorem norm_toE_le_of_abs_le {z x : Site d} (h : ∀ i, |z i| ≤ |x i|) : ‖toE z‖ ≤ ‖toE x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have hi : |(z i : ℝ)| ≤ |(x i : ℝ)| := by exact_mod_cast h i
  simpa [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hi 2

/-- A point of `box d m` has Euclidean norm at most `d m`. -/
theorem norm_toE_le_of_mem_box {z : Site d} {m : ℕ} (hz : z ∈ box d m) :
    ‖toE z‖ ≤ d * m := by
  rw [EuclideanSpace.norm_eq,
    show (d : ℝ) * m = Real.sqrt (((d : ℝ) * m) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin d)), ‖toE z i‖ ^ 2 ≤ (m : ℝ) ^ 2 := by
    intro i _
    have hi : |(z i : ℝ)| ≤ m := by exact_mod_cast hz i
    simpa [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hi 2
  have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) d
  calc ∑ i, ‖toE z i‖ ^ 2 ≤ ∑ _i : Fin d, (m : ℝ) ^ 2 := Finset.sum_le_sum h2
    _ = d * m ^ 2 := by simp
    _ ≤ ((d : ℝ) * m) ^ 2 := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hdd (by positivity)

/-- The Laplacian commutes with translations. -/
theorem lapR_comp_add (f : Site d → ℝ) (c y : Site d) :
    lapR (fun z => f (z + c)) y = lapR f (y + c) := by
  simp only [lapR, nbrSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_right_comm, sub_add_eq_add_sub]

theorem mem_box_mono {m n : ℕ} (h : m ≤ n) {z : Site d} (hz : z ∈ box d m) : z ∈ box d n :=
  fun i => (hz i).trans (by exact_mod_cast h)

end Support

/-! ### The reduction -/

theorem harnackQuadratic_of_steps (hB : BoxHarnackBddLapStmt) (hE : ExpGrowthBddLapStmt)
    (hS : LatticeSegmentStmt) : HarnackQuadraticStmt := by
  intro d hd β hβ0 hβ1 lam
  obtain ⟨A, hA1, hA⟩ := hB d (by omega)
  have hA0 : 0 ≤ A := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set a : ℝ := (1 - β) / (2 * β * d) with ha_def
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  set N : ℕ := ⌈2 / a⌉₊ + 1 with hN_def
  have hNpos : 0 < N := by omega
  have hN2 : 2 / a ≤ (N : ℝ) := by
    have := Nat.le_ceil (2 / a)
    rw [hN_def]; push_cast; linarith
  set M : ℕ := ⌈(d : ℝ) * (4 / a)⌉₊ with hM_def
  set C0 : ℝ := (N : ℝ) * A ^ N * a ^ 2 + (2 * (d : ℝ) + 1) ^ M with hC0_def
  have hC0a : (N : ℝ) * A ^ N * a ^ 2 ≤ C0 := by
    have : 0 ≤ (2 * (d : ℝ) + 1) ^ M := by positivity
    linarith
  have hC0b : (2 * (d : ℝ) + 1) ^ M ≤ C0 := by
    have : 0 ≤ (N : ℝ) * A ^ N * a ^ 2 := by positivity
    linarith
  have hC0nn : 0 ≤ C0 := le_trans (by positivity) hC0b
  refine ⟨|lam| * C0, ?_⟩
  intro R f hf hf0 hlap x hx
  by_cases hx0 : x = 0
  · subst hx0
    rw [hf0, toE_zero_harnack, norm_zero]
    simp
  rw [mem_ballZ0_iff_norm] at hx
  set s := ‖toE x‖ with hs_def
  have hs0 : 0 ≤ s := norm_nonneg _
  have hR : 0 < R := by
    by_contra h
    push Not at h
    nlinarith
  have h0R : (0 : Site d) ∈ ballZ0 R := by
    rw [mem_ballZ0_iff_norm, toE_zero_harnack, norm_zero]; exact hR
  have hlam : 0 ≤ lam := (abs_nonneg _).trans (hlap 0 h0R)
  rw [abs_of_nonneg hlam]
  have hsR : s / β < R := by rw [div_lt_iff₀ hβ0]; linarith
  have hs1 : 1 ≤ s := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (funext h)
    have h1 : (1 : ℝ) ≤ |(x i : ℝ)| := by
      have : (1 : ℤ) ≤ |x i| := Int.one_le_abs hi
      exact_mod_cast this
    exact h1.trans (abs_le_norm_toE x i)
  by_cases hsmall : s < 4 / a
  · -- small `|x|`: the exponential growth bound
    have hxR : x ∈ ballZ0 R := by
      rw [mem_ballZ0_iff_norm]
      nlinarith
    have hcrude :=
      hE d R lam f hf hf0 hlam (fun y hy => (le_abs_self _).trans (hlap y hy)) x hxR
    have hsum : ∑ i, (x i).natAbs ≤ M := by
      have h1 : ((∑ i, (x i).natAbs : ℕ) : ℝ) ≤ (d : ℝ) * (4 / a) := by
        push_cast
        calc ∑ i, ((x i).natAbs : ℝ) ≤ ∑ _i : Fin d, s := by
              apply Finset.sum_le_sum
              intro i _
              have h := abs_le_norm_toE x i
              rw [Nat.cast_natAbs, Int.cast_abs]
              exact h
          _ = d * s := by simp
          _ ≤ d * (4 / a) := mul_le_mul_of_nonneg_left hsmall.le hdpos.le
      have h2 : ((∑ i, (x i).natAbs : ℕ) : ℝ) ≤ (M : ℝ) := h1.trans (Nat.le_ceil _)
      exact_mod_cast h2
    have hpow : (2 * (d : ℝ) + 1) ^ (∑ i, (x i).natAbs) ≤ (2 * (d : ℝ) + 1) ^ M :=
      pow_le_pow_right₀ (by linarith) hsum
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    calc f x ≤ lam * (2 * (d : ℝ) + 1) ^ (∑ i, (x i).natAbs) := hcrude
      _ ≤ lam * (2 * (d : ℝ) + 1) ^ M := mul_le_mul_of_nonneg_left hpow hlam
      _ ≤ lam * C0 := mul_le_mul_of_nonneg_left hC0b hlam
      _ ≤ lam * C0 * s ^ 2 := le_mul_of_one_le_right (by positivity) hs2
  · -- large `|x|`: the Harnack chain along the discrete segment from `0` to `x`
    push Not at hsmall
    have hsa : 4 ≤ s * a := by rwa [div_le_iff₀ ha] at hsmall
    set r : ℕ := ⌊s * a⌋₊ with hr_def
    have hr_le : (r : ℝ) ≤ s * a := Nat.floor_le (by positivity)
    have hr_gt : s * a - 1 < r := by
      have := Nat.lt_floor_add_one (s * a)
      linarith
    have hr1 : 1 ≤ r := by
      have : (1 : ℝ) < r := by linarith
      exact_mod_cast this.le
    obtain ⟨c, hc0, hcN, hcabs, hcstep⟩ := hS d x N hNpos
    have hcnorm : ∀ k ≤ N, ‖toE (c k)‖ ≤ s := fun k hk => norm_toE_le_of_abs_le (hcabs k hk)
    have hdra : (d : ℝ) * (2 * r) ≤ s * (1 - β) / β := by
      have hda : (d : ℝ) * a = (1 - β) / (2 * β) := by
        rw [ha_def]; field_simp
      calc (d : ℝ) * (2 * r) ≤ d * (2 * (s * a)) := by gcongr
        _ = 2 * s * (d * a) := by ring
        _ = s * (1 - β) / β := by rw [hda]; field_simp
    have hbox : ∀ k ≤ N, ∀ y : Site d, y - c k ∈ box d (2 * r) → y ∈ ballZ0 R := by
      intro k hk y hy
      rw [mem_ballZ0_iff_norm]
      have h1 : ‖toE y‖ ≤ ‖toE (c k)‖ + ‖toE (y - c k)‖ := by
        have := norm_add_le (toE (c k)) (toE (y - c k))
        rwa [← toE_add_harnack, add_sub_cancel] at this
      have h2 := norm_toE_le_of_mem_box hy
      push_cast at h2
      have h3 : s + s * (1 - β) / β = s / β := by field_simp; ring
      linarith [hcnorm k hk]
    have hstep : ∀ k < N, f (c (k + 1)) ≤ A * f (c k) + A * lam * (r : ℝ) ^ 2 := by
      intro k hk
      have hmem : c (k + 1) - c k ∈ box d r := by
        intro i
        have h1 := hcstep k hk i
        have h2 : |(x i : ℝ)| / N ≤ s * a / 2 := by
          have hN0 : (0 : ℝ) < 2 / a := by positivity
          calc |(x i : ℝ)| / N ≤ s / N := by
                gcongr
                exact abs_le_norm_toE x i
            _ ≤ s / (2 / a) := div_le_div_of_nonneg_left hs0 hN0 hN2
            _ = s * a / 2 := by field_simp
        have h3 : |((c (k + 1) i - c k i : ℤ) : ℝ)| ≤ r := by linarith
        rw [Pi.sub_apply]
        exact_mod_cast h3
      have h0 : (0 : Site d) ∈ box d r := fun i => by simp
      have := hA r hr1 lam (fun y => f (y + c k)) (fun y _ => hf _) (fun y hy => by
          rw [lapR_comp_add]
          exact hlap _ (hbox k hk.le _ (by
            rw [add_sub_cancel_right]
            exact mem_box_mono (by omega) hy))) _ hmem 0 h0
      simpa [sub_add_cancel] using this
    have hind : ∀ k ≤ N, f (c k) ≤ k * A ^ k * lam * (r : ℝ) ^ 2 := by
      intro k
      induction k with
      | zero => intro _; rw [hc0, hf0]; simp
      | succ k ih =>
        intro hk
        have h1 := hstep k (by omega)
        have h2 := ih (by omega)
        have hAk : A ≤ A ^ (k + 1) := by
          calc A = A ^ 1 := (pow_one A).symm
            _ ≤ A ^ (k + 1) := pow_le_pow_right₀ hA1 (by omega)
        have hL : 0 ≤ lam * (r : ℝ) ^ 2 := by positivity
        have h3 := mul_le_mul_of_nonneg_right hAk hL
        have h4 := mul_le_mul_of_nonneg_left h2 hA0
        calc f (c (k + 1)) ≤ A * f (c k) + A * lam * (r : ℝ) ^ 2 := h1
          _ ≤ A * (k * A ^ k * lam * (r : ℝ) ^ 2) + A ^ (k + 1) * (lam * (r : ℝ) ^ 2) := by
              linarith
          _ = ((k + 1 : ℕ) : ℝ) * A ^ (k + 1) * lam * (r : ℝ) ^ 2 := by push_cast; ring
    have hfin := hind N le_rfl
    rw [hcN] at hfin
    calc f x ≤ N * A ^ N * lam * (r : ℝ) ^ 2 := hfin
      _ ≤ N * A ^ N * lam * (s * a) ^ 2 := by gcongr
      _ = lam * ((N : ℝ) * A ^ N * a ^ 2) * s ^ 2 := by ring
      _ ≤ lam * C0 * s ^ 2 := by gcongr

end RandomSandpile

import RandomSandpile.Proofs.Sec5.HarnackQuadratic
import RandomSandpile.Steps.Sec6.MuLipschitz

/-! # A Harnack chain for nonnegative functions with bounded Laplacian

A nonnegative function `f` on `B̄_n` with `|Δ f| ≤ K` on `B_n` which vanishes at a point of
`B_{βn}` is `O(K n²)` on `B_{δn}`, for `β < δ < 1`.

The proof is the Harnack chain of the reduction `harnackQuadratic_of_steps`
(`RandomSandpile/Steps/Sec5/HarnackQuadratic.lean`), run along the discrete segments
`0 → x₀` and `0 → y` of `latticeSegment`: the box Harnack inequality `boxHarnackBddLap` is
symmetric in its two points, so the chain gives both `f(x) ≤ A^N f(0) + O(K n²)` and
`f(0) ≤ A^N f(x) + O(K n²)` for every `x ∈ B_{δn}`. With `f(x₀) = 0` the second bound gives
`f(0) = O(K n²)` and the first one then bounds `f(y)`. The radius of the boxes is
`r = ⌊n a⌋` with `a = (1 - δ) / (2d)`, so that the boxes of radius `2r` centred at the points of the
segments (which lie in `B_{δn}`) stay in `B_n`. -/

open MeasureTheory LatticeProb

namespace RandomSandpile
namespace StrictConcavityHarnack

/-- The iteration `u (m+1) ≤ A u m + B` gives `u m ≤ A^m u 0 + m A^m B`. -/
theorem chain_bound {A B : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (u : ℕ → ℝ) (N : ℕ)
    (hu : ∀ m < N, u (m + 1) ≤ A * u m + B) :
    ∀ m ≤ N, u m ≤ A ^ m * u 0 + m * A ^ m * B := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := hu m (by omega)
    have h2 := ih (by omega)
    have hA0 : 0 ≤ A := by linarith
    have hAm : 1 ≤ A ^ (m + 1) := one_le_pow₀ hA
    have h3 : B ≤ A ^ (m + 1) * B := le_mul_of_one_le_left hB hAm
    have h4 : A * (A ^ m * u 0 + m * A ^ m * B) + B ≤
        A ^ (m + 1) * u 0 + ((m + 1 : ℕ) : ℝ) * A ^ (m + 1) * B := by
      have e : A * (A ^ m * u 0 + m * A ^ m * B) + B =
          A ^ (m + 1) * u 0 + m * A ^ (m + 1) * B + B := by ring
      have e' : ((m + 1 : ℕ) : ℝ) * A ^ (m + 1) * B = m * A ^ (m + 1) * B + A ^ (m + 1) * B := by
        push_cast; ring
      rw [e, e']
      linarith
    calc u (m + 1) ≤ A * u m + B := h1
      _ ≤ A * (A ^ m * u 0 + m * A ^ m * B) + B := by gcongr
      _ ≤ _ := h4

/-- The Harnack chain along the discrete segment from `0` to a point `x ∈ B_{δ n}`. -/
theorem seg_chain {d : ℕ} {A : ℝ} (hA1 : 1 ≤ A)
    (hA : ∀ (r : ℕ), 1 ≤ r → ∀ (lam : ℝ) (f : Site d → ℝ), (∀ y ∈ box d (2 * r), 0 ≤ f y) →
      (∀ y ∈ box d (2 * r - 1), |lapR f y| ≤ lam) →
      ∀ y ∈ box d r, ∀ z ∈ box d r, f y ≤ A * f z + A * lam * (r : ℝ) ^ 2)
    {a δ : ℝ} (ha : 0 < a) (hda : (d : ℝ) * a = (1 - δ) / 2) (hδ : δ < 1) (N : ℕ)
    (hNpos : 0 < N) (hN2 : 2 / a ≤ (N : ℝ)) {n : ℝ} (hn : 4 ≤ n * a) {K : ℝ} (hK : 0 ≤ K)
    (f : Site d → ℝ) (hf : ∀ y ∈ dClosure (ballZ0 (d := d) n), 0 ≤ f y)
    (hlap : ∀ y ∈ ballZ0 (d := d) n, |lapR f y| ≤ K) {x : Site d} (hx : ‖toE x‖ < δ * n) :
    f x ≤ A ^ N * f 0 + N * A ^ N * (A * K * (n * a) ^ 2) ∧
    f 0 ≤ A ^ N * f x + N * A ^ N * (A * K * (n * a) ^ 2) := by
  have hA0 : 0 ≤ A := by linarith
  have hn0 : 0 ≤ n := by
    by_contra h
    push Not at h
    nlinarith
  have hxn : ‖toE x‖ ≤ n := by nlinarith [mul_nonneg (sub_nonneg.2 hδ.le) hn0]
  set r : ℕ := ⌊n * a⌋₊ with hr_def
  have hr_le : (r : ℝ) ≤ n * a := Nat.floor_le (by linarith)
  have hr_gt : n * a - 1 < r := by
    have := Nat.lt_floor_add_one (n * a)
    linarith
  have hr1 : 1 ≤ r := by
    have : (1 : ℝ) < r := by linarith
    exact_mod_cast this.le
  obtain ⟨c, hc0, hcN, hcabs, hcstep⟩ := latticeSegment d x N hNpos
  have hcnorm : ∀ k ≤ N, ‖toE (c k)‖ ≤ ‖toE x‖ :=
    fun k hk => norm_toE_le_of_abs_le (hcabs k hk)
  have hdra : (d : ℝ) * (2 * r) ≤ (1 - δ) * n := by
    calc (d : ℝ) * (2 * r) ≤ d * (2 * (n * a)) := by gcongr
      _ = 2 * n * (d * a) := by ring
      _ = (1 - δ) * n := by rw [hda]; ring
  have hbox : ∀ k ≤ N, ∀ y : Site d, y - c k ∈ box d (2 * r) → y ∈ ballZ0 (d := d) n := by
    intro k hk y hy
    rw [mem_ballZ0_iff_norm]
    have h1 : ‖toE y‖ ≤ ‖toE (c k)‖ + ‖toE (y - c k)‖ := by
      have := norm_add_le (toE (c k)) (toE (y - c k))
      rwa [← toE_add_harnack, add_sub_cancel] at this
    have h2 := norm_toE_le_of_mem_box hy
    push_cast at h2
    linarith [hcnorm k hk]
  have hstep : ∀ k < N, f (c (k + 1)) ≤ A * f (c k) + A * K * (r : ℝ) ^ 2 ∧
      f (c k) ≤ A * f (c (k + 1)) + A * K * (r : ℝ) ^ 2 := by
    intro k hk
    have hmem : c (k + 1) - c k ∈ box d r := by
      intro i
      have h1 := hcstep k hk i
      have h2 : |(x i : ℝ)| / N ≤ n * a / 2 := by
        have hN0 : (0 : ℝ) < 2 / a := by positivity
        calc |(x i : ℝ)| / N ≤ n / N := by
              gcongr
              exact (abs_le_norm_toE x i).trans hxn
          _ ≤ n / (2 / a) := div_le_div_of_nonneg_left hn0 hN0 hN2
          _ = n * a / 2 := by field_simp
      have h3 : |((c (k + 1) i - c k i : ℤ) : ℝ)| ≤ r := by linarith
      rw [Pi.sub_apply]
      exact_mod_cast h3
    have h0 : (0 : Site d) ∈ box d r := fun i => by simp
    have hh := hA r hr1 K (fun y => f (y + c k))
      (fun y hy => hf _ (Or.inl (hbox k hk.le _ (by
        rw [add_sub_cancel_right]
        exact hy))))
      (fun y hy => by
        rw [lapR_comp_add]
        exact hlap _ (hbox k hk.le _ (by
          rw [add_sub_cancel_right]
          exact mem_box_mono (by omega) hy)))
    constructor
    · have := hh _ hmem 0 h0
      simpa [sub_add_cancel] using this
    · have := hh 0 h0 _ hmem
      simpa [sub_add_cancel] using this
  have hB0 : 0 ≤ A * K * (r : ℝ) ^ 2 := by positivity
  have hup : ∀ m ≤ N, f (c m) ≤ A ^ m * f (c 0) + m * A ^ m * (A * K * (r : ℝ) ^ 2) :=
    chain_bound hA1 hB0 (fun m => f (c m)) N (fun m hm => (hstep m hm).1)
  have hdown : ∀ m ≤ N, f (c (N - m)) ≤
      A ^ m * f (c (N - 0)) + m * A ^ m * (A * K * (r : ℝ) ^ 2) :=
    chain_bound hA1 hB0 (fun m => f (c (N - m))) N (fun m hm => by
      have h1 := (hstep (N - m - 1) (by omega)).2
      have e : N - m - 1 + 1 = N - m := by omega
      rw [e] at h1
      have e2 : N - (m + 1) = N - m - 1 := by omega
      show f (c (N - (m + 1))) ≤ A * f (c (N - m)) + _
      rw [e2]
      exact h1)
  have hU := hup N le_rfl
  have hD := hdown N le_rfl
  rw [hcN, hc0] at hU
  rw [Nat.sub_self, hc0, Nat.sub_zero, hcN] at hD
  have hB : A * K * (r : ℝ) ^ 2 ≤ A * K * (n * a) ^ 2 := by gcongr
  have hm : (N : ℝ) * A ^ N * (A * K * (r : ℝ) ^ 2) ≤ N * A ^ N * (A * K * (n * a) ^ 2) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  exact ⟨by linarith, by linarith⟩

/-- Harnack chain: a nonnegative `f` on `B̄_n` with `|Δf| ≤ K` on `B_n` vanishing at a point of
`B_{βn}` is `O(K n²)` on `B_{δn}`, `β < δ < 1`. -/
theorem harnack_chain {d : ℕ} (hd : 1 ≤ d) {β δ : ℝ} (hβ : 0 < β) (hβδ : β < δ) (hδ : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (K : ℝ) (f : Site d → ℝ), 0 ≤ K →
      (∀ y ∈ dClosure (ballZ0 (d := d) (n : ℝ)), 0 ≤ f y) →
      (∀ y ∈ ballZ0 (d := d) (n : ℝ), |lapR f y| ≤ K) →
      ∀ x₀ ∈ ballZ0 (d := d) (β * n), f x₀ = 0 →
      ∀ y ∈ ballZ0 (d := d) (δ * n), f y ≤ C * K * (n : ℝ) ^ 2 := by
  obtain ⟨A, hA1, hA⟩ := boxHarnackBddLap d hd
  have hA0 : 0 ≤ A := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set a : ℝ := (1 - δ) / (2 * d) with ha_def
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  have hda : (d : ℝ) * a = (1 - δ) / 2 := by
    rw [ha_def]; field_simp
  set N : ℕ := ⌈2 / a⌉₊ + 1 with hN_def
  have hNpos : 0 < N := by omega
  have hN2 : 2 / a ≤ (N : ℝ) := by
    have := Nat.le_ceil (2 / a)
    rw [hN_def]; push_cast; linarith
  refine ⟨((N : ℝ) * A ^ N * A ^ N + N * A ^ N) * (A * a ^ 2), by positivity, ⌈4 / a⌉₊, ?_⟩
  intro n hn K f hK hf hlap x₀ hx₀ hfx₀ y hy
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn4 : 4 ≤ (n : ℝ) * a := by
    have h1 : ((⌈4 / a⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 4 / a ≤ n := (Nat.le_ceil (4 / a)).trans h1
    rwa [div_le_iff₀ ha] at h2
  have hx₀' : ‖toE x₀‖ < δ * n := by
    rw [mem_ballZ0_iff_norm] at hx₀
    have : β * n ≤ δ * n := mul_le_mul_of_nonneg_right hβδ.le hn0
    linarith
  have hy' : ‖toE y‖ < δ * n := by
    rwa [mem_ballZ0_iff_norm] at hy
  obtain ⟨_, h2⟩ := seg_chain hA1 hA ha hda hδ N hNpos hN2 hn4 hK f hf hlap hx₀'
  obtain ⟨h3, _⟩ := seg_chain hA1 hA ha hda hδ N hNpos hN2 hn4 hK f hf hlap hy'
  rw [hfx₀, mul_zero, zero_add] at h2
  have hAN : 0 ≤ A ^ N := by positivity
  have h5 : A ^ N * f 0 ≤ A ^ N * ((N : ℝ) * A ^ N * (A * K * ((n : ℝ) * a) ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 hAN
  calc f y ≤ A ^ N * f 0 + N * A ^ N * (A * K * ((n : ℝ) * a) ^ 2) := h3
    _ ≤ A ^ N * ((N : ℝ) * A ^ N * (A * K * ((n : ℝ) * a) ^ 2)) +
          N * A ^ N * (A * K * ((n : ℝ) * a) ^ 2) := by linarith
    _ = ((N : ℝ) * A ^ N * A ^ N + N * A ^ N) * (A * a ^ 2) * K * (n : ℝ) ^ 2 := by ring

end StrictConcavityHarnack
end RandomSandpile

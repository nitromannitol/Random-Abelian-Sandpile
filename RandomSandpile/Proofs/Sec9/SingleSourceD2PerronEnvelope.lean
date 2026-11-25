import RandomSandpile.Proofs.Sec9.SingleSourceD2Perron
import RandomSandpile.Proofs.Sec7.SplitTouchingJensen

/-!
# Theorem 9.2 in dimension two: the upper envelope of a family of subsolutions

Toward Perron's method (Crandall-Ishii-Lions, *User's guide*, §4) on `ℝ²`, for a continuous
`F(x, r, p, X)`:

* `quad_shift`: the exact expansion of `c + ⟨p, y - z⟩ + q_X(y - z) + δ|y - z|²` around `x`;
* `mem_superJet2_of_quad_max`: a local maximum of `w - φ` for such a quadratic `φ` gives a
  superjet of `w`;
* `superJet2_quad`: the superjets of a quadratic `ψ` at `x` have the slope of `ψ` and a matrix
  above that of `ψ`;
* `uEnv K f`, `lEnv K f`: the upper and lower semicontinuous envelopes of `f` relative to `K`;
* `isSubsolution_uEnv`: the upper envelope of the pointwise supremum of a family of subsolutions,
  bounded on `Ω̄`, is a subsolution (CIL Lemma 4.2).
-/

noncomputable section

open Filter Topology Metric Set
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

open CrandallIshiiLions

/-! ### Quadratics -/

/-- The vector `M h`. -/
def matVec (M : Matrix (Fin 2) (Fin 2) ℝ) (h : Rd 2) : Rd 2 :=
  WithLp.toLp 2 (M *ᵥ WithLp.ofLp h)

theorem continuous_matVec (M : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (matVec M) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _))

theorem matVec_add_smul_one (M : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (h : Rd 2) :
    matVec (M + t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h = matVec M h + t • h := by
  simp only [matVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

/-- The quadratic `c + ⟨p, y - z⟩ + q_X(y - z) + δ|y - z|²`. -/
def quadAt (c : ℝ) (p z : Rd 2) (X : Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ) (y : Rd 2) : ℝ :=
  c + inner ℝ p (y - z) + qM X (y - z) + δ * ‖y - z‖ ^ 2

theorem continuous_quadAt (c : ℝ) (p z : Rd 2) (X : Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ) :
    Continuous (quadAt c p z X δ) := by
  unfold quadAt qM
  fun_prop

theorem quadAt_self (c : ℝ) (p z : Rd 2) (X : Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ) :
    quadAt c p z X δ z = c := by
  simp [quadAt, qM]

/-- **Expansion of the quadratic around `x`.** -/
theorem quad_shift {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : X.IsSymm) (c δ : ℝ) (p z x y : Rd 2) :
    quadAt c p z X δ y = quadAt c p z X δ x +
      inner ℝ (p + matVec (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (x - z)) (y - x) +
      qM (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - x) := by
  have e : y - z = (x - z) + (y - x) := by abel
  have hn : ‖(x - z) + (y - x)‖ ^ 2 = ‖x - z‖ ^ 2 + 2 * inner ℝ (x - z) (y - x) + ‖y - x‖ ^ 2 :=
    norm_add_sq_real _ _
  have hq := SplitJensen.qM_add_sym hX (y - x) (x - z)
  simp only [quadAt]
  rw [e, hq, hn, matVec_add_smul_one, qM_add_smul_one, inner_add_left, inner_add_left,
    inner_add_right, real_inner_smul_left]
  have hmv : WithLp.toLp 2 (X *ᵥ WithLp.ofLp (x - z)) = matVec X (x - z) := rfl
  rw [hmv]
  ring

/-- A local maximum of `w - φ`, `φ` a quadratic, gives a superjet of `w`. -/
theorem mem_superJet2_of_quad_max {O : Set (Rd 2)} {w : Rd 2 → ℝ}
    {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : X.IsSymm) {c δ : ℝ} {p z x : Rd 2}
    (hmax : ∀ᶠ y in 𝓝[O] x, w y - quadAt c p z X δ y ≤ w x - quadAt c p z X δ x) :
    (p + matVec (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (x - z),
      X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∈ superJet2 O w x := by
  refine ⟨hX.add (Matrix.isSymm_one.smul _), fun ε hε => ?_⟩
  filter_upwards [hmax] with y hy
  rw [quad_shift hX c δ p z x y] at hy
  have : 0 ≤ ε * ‖y - x‖ ^ 2 := by positivity
  show w y ≤ w x + inner ℝ (p + matVec (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (x - z))
    (y - x) + qM (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - x) + ε * ‖y - x‖ ^ 2
  linarith

/-- `q_M(t e) = t² q_M(e)`. -/
theorem qM_smul_vec' (M : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (e : Rd 2) :
    qM M (t • e) = t ^ 2 * qM M e := by
  simp only [qM, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

/-- A one-variable estimate: if `t a + t² b ≤ 0` for all small `t > 0`, then `a ≤ 0`. -/
theorem nonpos_of_small {a b ρ : ℝ} (hρ : 0 < ρ) (h : ∀ t, 0 < t → t < ρ → t * a + t ^ 2 * b ≤ 0) :
    a ≤ 0 := by
  by_contra ha
  rw [not_le] at ha
  set t := min (ρ / 2) (a / (2 * (|b| + 1))) with ht
  have hb1 : 0 < |b| + 1 := by positivity
  have htpos : 0 < t := lt_min (half_pos hρ) (div_pos ha (by positivity))
  have htρ : t < ρ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ)
  have htb : t * (|b| + 1) ≤ a / 2 := by
    have h1 : t ≤ a / (2 * (|b| + 1)) := min_le_right _ _
    have h2 : a / (2 * (|b| + 1)) * (|b| + 1) = a / 2 := by field_simp
    calc t * (|b| + 1) ≤ a / (2 * (|b| + 1)) * (|b| + 1) :=
          mul_le_mul_of_nonneg_right h1 hb1.le
      _ = a / 2 := h2
  have hta : 0 < t * a := mul_pos htpos ha
  have h5 : t * |b| ≤ a / 2 := by
    have e : t * (|b| + 1) = t * |b| + t := by ring
    linarith
  have h6 : t * (t * |b|) ≤ t * (a / 2) := mul_le_mul_of_nonneg_left h5 htpos.le
  have h4 : t ^ 2 * (-|b|) ≤ t ^ 2 * b := mul_le_mul_of_nonneg_left (neg_abs_le b) (sq_nonneg t)
  have h3 := h t htpos htρ
  have e1 : t ^ 2 * (-|b|) = -(t * (t * |b|)) := by ring
  have e2 : t * (a / 2) = t * a / 2 := by ring
  linarith

/-- **The superjets of a quadratic.** If `ψ(y) = ψ(x) + ⟨q₀, y - x⟩ + q_N(y - x)` on an open set,
every superjet `(q, M)` of `ψ` at `x` has `q = q₀` and `q_N ≤ q_M`. -/
theorem superJet2_quad {O : Set (Rd 2)} (hO : IsOpen O) {x : Rd 2} (hx : x ∈ O) {ψ : Rd 2 → ℝ}
    {q₀ : Rd 2} {N : Matrix (Fin 2) (Fin 2) ℝ}
    (hψ : ∀ y, ψ y = ψ x + inner ℝ q₀ (y - x) + qM N (y - x)) {q : Rd 2}
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hj : (q, M) ∈ superJet2 O ψ x) :
    q = q₀ ∧ ∀ ξ : Rd 2, qM N ξ ≤ qM M ξ := by
  have hloc : ∀ ε : ℝ, 0 < ε → ∃ ρ > 0, ∀ k : Rd 2, ‖k‖ < ρ →
      inner ℝ (q₀ - q) k + qM N k - qM M k ≤ ε * ‖k‖ ^ 2 := by
    intro ε hε
    have h := hj.2 ε hε
    rw [nhdsWithin_eq_nhds.2 (hO.mem_nhds hx)] at h
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 h
    refine ⟨ρ, hρ, fun k hk => ?_⟩
    have hy := hball (y := x + k) (by rwa [dist_eq_norm, add_sub_cancel_left])
    rw [hψ (x + k), add_sub_cancel_left] at hy
    rw [inner_sub_left]
    linarith
  -- the slope
  have hslope : ∀ e : Rd 2, inner ℝ (q₀ - q) e ≤ 0 := by
    intro e
    obtain ⟨ρ, hρ, hk⟩ := hloc 1 one_pos
    refine nonpos_of_small (b := qM N e - qM M e - ‖e‖ ^ 2) (ρ := ρ / (‖e‖ + 1))
      (by positivity) fun t ht htρ => ?_
    have hnorm : ‖t • e‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have h1 : t * ‖e‖ ≤ t * (‖e‖ + 1) := by nlinarith [norm_nonneg e]
      have h2 : t * (‖e‖ + 1) < ρ := by
        rwa [lt_div_iff₀ (by positivity)] at htρ
      linarith
    have := hk (t • e) hnorm
    rw [real_inner_smul_right, qM_smul_vec', qM_smul_vec', norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs] at this
    nlinarith
  have hq : q = q₀ := by
    have h1 := hslope (q₀ - q)
    rw [real_inner_self_eq_norm_sq] at h1
    have h2 : ‖q₀ - q‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
    have h3 : ‖q₀ - q‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 h2
    exact (sub_eq_zero.1 (norm_eq_zero.1 h3)).symm
  refine ⟨hq, fun ξ => ?_⟩
  -- the matrix
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε' : 0 < ε / (‖ξ‖ ^ 2 + 1) := by positivity
  obtain ⟨ρ, hρ, hk⟩ := hloc _ hε'
  set t := ρ / (2 * (‖ξ‖ + 1)) with ht_def
  have ht : 0 < t := by positivity
  have hnorm : ‖t • ξ‖ < ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, ht_def]
    have h1 : ρ / (2 * (‖ξ‖ + 1)) * ‖ξ‖ < ρ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg ξ]
    exact h1
  have h := hk (t • ξ) hnorm
  rw [hq, sub_self, inner_zero_left, qM_smul_vec', qM_smul_vec', norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at h
  have h2 : qM N ξ - qM M ξ ≤ ε / (‖ξ‖ ^ 2 + 1) * ‖ξ‖ ^ 2 := by
    have ht2 : 0 < t ^ 2 := by positivity
    nlinarith
  have h3 : ε / (‖ξ‖ ^ 2 + 1) * ‖ξ‖ ^ 2 ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Superjets are antitone: if `f ≤ h` on `O` with equality at `x`, a superjet of `h` is one of
`f`. -/
theorem mem_superJet2_of_le_on {O : Set (Rd 2)} {f h : Rd 2 → ℝ} {x : Rd 2}
    (hle : ∀ y ∈ O, f y ≤ h y) (heq : f x = h x) {pX : Rd 2 × Matrix (Fin 2) (Fin 2) ℝ}
    (hj : pX ∈ superJet2 O h x) : pX ∈ superJet2 O f x := by
  refine ⟨hj.1, fun ε hε => ?_⟩
  filter_upwards [hj.2 ε hε, self_mem_nhdsWithin] with y hy hyO
  rw [heq]
  linarith [hle y hyO]

/-- Subjets are monotone: if `f ≤ h` on `O` with equality at `x`, a subjet of `f` is one of
`h`. -/
theorem mem_subJet2_of_le_on {O : Set (Rd 2)} {f h : Rd 2 → ℝ} {x : Rd 2}
    (hle : ∀ y ∈ O, f y ≤ h y) (heq : f x = h x) {pX : Rd 2 × Matrix (Fin 2) (Fin 2) ℝ}
    (hj : pX ∈ subJet2 O f x) : pX ∈ subJet2 O h x := by
  refine ⟨hj.1, fun ε hε => ?_⟩
  filter_upwards [hj.2 ε hε, self_mem_nhdsWithin] with y hy hyO
  rw [← heq]
  linarith [hle y hyO]

/-- Superjets depend only on the values near the point. -/
theorem superJet2_congr {O : Set (Rd 2)} {f h : Rd 2 → ℝ} {x : Rd 2}
    (hfh : ∀ᶠ y in 𝓝[O] x, f y = h y) (hx : f x = h x) {pX : Rd 2 × Matrix (Fin 2) (Fin 2) ℝ}
    (hj : pX ∈ superJet2 O h x) : pX ∈ superJet2 O f x := by
  refine ⟨hj.1, fun ε hε => ?_⟩
  filter_upwards [hj.2 ε hε, hfh] with y hy hyfh
  rw [hyfh, hx]
  exact hy

/-- Subjets depend only on the values near the point. -/
theorem subJet2_congr {O : Set (Rd 2)} {f h : Rd 2 → ℝ} {x : Rd 2}
    (hfh : ∀ᶠ y in 𝓝[O] x, f y = h y) (hx : f x = h x) {pX : Rd 2 × Matrix (Fin 2) (Fin 2) ℝ}
    (hj : pX ∈ subJet2 O h x) : pX ∈ subJet2 O f x := by
  refine ⟨hj.1, fun ε hε => ?_⟩
  filter_upwards [hj.2 ε hε, hfh] with y hy hyfh
  rw [hyfh, hx]
  exact hy

/-! ### Semicontinuous envelopes relative to a set -/

/-- The upper semicontinuous envelope `f^*(x) = inf_r sup_{K ∩ B(x, r)} f`. -/
def uEnv (K : Set (Rd 2)) (f : Rd 2 → ℝ) (x : Rd 2) : ℝ :=
  ⨅ r : {r : ℝ // 0 < r}, sSup (f '' (K ∩ ball x r))

/-- The lower semicontinuous envelope `f_* = -(-f)^*`. -/
def lEnv (K : Set (Rd 2)) (f : Rd 2 → ℝ) (x : Rd 2) : ℝ :=
  -uEnv K (fun y => -f y) x

section Envelope

variable {K : Set (Rd 2)} {f : Rd 2 → ℝ} {C : ℝ}

theorem bddAbove_image_ball (hb : ∀ y ∈ K, |f y| ≤ C) (x : Rd 2) (r : ℝ) :
    BddAbove (f '' (K ∩ ball x r)) := by
  refine ⟨C, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (le_abs_self _).trans (hb y hy.1)

theorem le_sSup_image_ball (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) {r : ℝ}
    (hr : 0 < r) : f x ≤ sSup (f '' (K ∩ ball x r)) :=
  le_csSup (bddAbove_image_ball hb x r) ⟨x, ⟨hx, mem_ball_self hr⟩, rfl⟩

theorem bddBelow_range_uEnv (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) :
    BddBelow (Set.range fun r : {r : ℝ // 0 < r} => sSup (f '' (K ∩ ball x r))) := by
  refine ⟨f x, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact le_sSup_image_ball hb hx r.2

theorem le_uEnv (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) : f x ≤ uEnv K f x := by
  have : Nonempty {r : ℝ // 0 < r} := ⟨⟨1, one_pos⟩⟩
  exact le_ciInf fun r => le_sSup_image_ball hb hx r.2

theorem uEnv_le_sSup (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) {r : ℝ} (hr : 0 < r) :
    uEnv K f x ≤ sSup (f '' (K ∩ ball x r)) :=
  ciInf_le (bddBelow_range_uEnv hb hx) ⟨r, hr⟩

theorem uEnv_le_of (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) {r M : ℝ} (hr : 0 < r)
    (h : ∀ y ∈ K ∩ ball x r, f y ≤ M) : uEnv K f x ≤ M :=
  (uEnv_le_sSup hb hx hr).trans (csSup_le ⟨f x, x, ⟨hx, mem_ball_self hr⟩, rfl⟩
    (by rintro _ ⟨y, hy, rfl⟩; exact h y hy))

theorem abs_uEnv_le (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) : |uEnv K f x| ≤ C := by
  rw [abs_le]
  constructor
  · have := le_uEnv hb hx
    have := neg_abs_le (f x)
    linarith [hb x hx]
  · exact uEnv_le_of hb hx one_pos fun y hy => (le_abs_self _).trans (hb y hy.1)

theorem exists_lt_of_lt_uEnv (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) {r θ : ℝ}
    (hr : 0 < r) (hθ : 0 < θ) : ∃ y ∈ K ∩ ball x r, uEnv K f x - θ < f y := by
  have h1 := uEnv_le_sSup hb hx hr
  obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (s := f '' (K ∩ ball x r))
    ⟨f x, x, ⟨hx, mem_ball_self hr⟩, rfl⟩ (show uEnv K f x - θ < sSup (f '' (K ∩ ball x r)) by
      linarith)
  exact ⟨y, hy, hlt⟩

theorem upperSemicontinuousOn_uEnv (hb : ∀ y ∈ K, |f y| ≤ C) :
    UpperSemicontinuousOn (uEnv K f) K := by
  intro x hx M hM
  have : Nonempty {r : ℝ // 0 < r} := ⟨⟨1, one_pos⟩⟩
  obtain ⟨⟨r, hr⟩, hlt⟩ := exists_lt_of_ciInf_lt hM
  have hsub : ∀ y ∈ K ∩ ball x (r / 2), K ∩ ball y (r / 2) ⊆ K ∩ ball x r := by
    rintro y ⟨-, hy⟩ w ⟨hwK, hw⟩
    refine ⟨hwK, ?_⟩
    rw [mem_ball] at hy hw ⊢
    calc dist w x ≤ dist w y + dist y x := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hw hy
      _ = r := by ring
  have hev : ∀ᶠ y in 𝓝[K] x, y ∈ K ∩ ball x (r / 2) :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (half_pos hr)))
  filter_upwards [hev] with y hy
  calc uEnv K f y ≤ sSup (f '' (K ∩ ball y (r / 2))) := uEnv_le_sSup hb hy.1 (half_pos hr)
    _ ≤ sSup (f '' (K ∩ ball x r)) :=
        csSup_le_csSup (bddAbove_image_ball hb x r)
          ⟨f y, y, ⟨hy.1, mem_ball_self (half_pos hr)⟩, rfl⟩ (image_mono (hsub y hy))
    _ < M := hlt

theorem neg_bound (hb : ∀ y ∈ K, |f y| ≤ C) : ∀ y ∈ K, |(fun y => -f y) y| ≤ C := fun y hy => by
  simpa only [abs_neg] using hb y hy

theorem lEnv_le (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) : lEnv K f x ≤ f x := by
  have := le_uEnv (neg_bound hb) hx
  simp only [lEnv]
  linarith

theorem le_lEnv_of (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) {r M : ℝ} (hr : 0 < r)
    (h : ∀ y ∈ K ∩ ball x r, M ≤ f y) : M ≤ lEnv K f x := by
  have := uEnv_le_of (M := -M) (neg_bound hb) hx hr fun y hy => by simpa using h y hy
  simp only [lEnv]
  linarith

theorem abs_lEnv_le (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) : |lEnv K f x| ≤ C := by
  simpa only [lEnv, abs_neg] using abs_uEnv_le (neg_bound hb) hx

theorem exists_lt_of_lEnv_lt (hb : ∀ y ∈ K, |f y| ≤ C) {x : Rd 2} (hx : x ∈ K) {r θ : ℝ}
    (hr : 0 < r) (hθ : 0 < θ) : ∃ y ∈ K ∩ ball x r, f y < lEnv K f x + θ := by
  obtain ⟨y, hy, hlt⟩ := exists_lt_of_lt_uEnv (neg_bound hb) hx hr hθ
  refine ⟨y, hy, ?_⟩
  simp only [lEnv]
  linarith

theorem lowerSemicontinuousOn_lEnv (hb : ∀ y ∈ K, |f y| ≤ C) :
    LowerSemicontinuousOn (lEnv K f) K := by
  intro x hx M hM
  have h := upperSemicontinuousOn_uEnv (neg_bound hb) x hx (-M) (by simp only [lEnv] at hM; linarith)
  filter_upwards [h] with y hy
  simp only [lEnv]
  linarith

end Envelope

/-! ### The upper envelope of a family of subsolutions (CIL Lemma 4.2) -/

/-- **The upper envelope of the supremum of a bounded family of subsolutions is a
subsolution.** Here `W` is the pointwise supremum on `Ω̄` of the family `S` of subsolutions on
`Ω`, in the sense that every member lies below `W` on `Ω̄` and every value of `W` on `Ω̄` is
approached by members. -/
theorem isSubsolution_uEnv {F : Rd 2 → ℝ → Rd 2 → Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hcont : Continuous (fun w : Rd 2 × ℝ × Rd 2 × Matrix (Fin 2) (Fin 2) ℝ =>
      F w.1 w.2.1 w.2.2.1 w.2.2.2))
    {Ω : Set (Rd 2)} (hΩ : IsOpen Ω) {S : Set (Rd 2 → ℝ)} {W : Rd 2 → ℝ} {C : ℝ}
    (hS : ∀ w ∈ S, IsSubsolution F Ω w) (hSW : ∀ w ∈ S, ∀ y ∈ closure Ω, w y ≤ W y)
    (hWS : ∀ x ∈ closure Ω, ∀ θ : ℝ, 0 < θ → ∃ w ∈ S, W x - θ < w x)
    (hb : ∀ y ∈ closure Ω, |W y| ≤ C) :
    IsSubsolution F Ω (uEnv (closure Ω) W) := by
  set K := closure Ω with hK
  set U := uEnv K W with hU
  refine ⟨(upperSemicontinuousOn_uEnv hb).mono subset_closure, fun z hz pX hpX => ?_⟩
  obtain ⟨p, X⟩ := pX
  have hX : X.IsSymm := hpX.1
  set G : Rd 2 × ℝ × Rd 2 × Matrix (Fin 2) (Fin 2) ℝ → ℝ :=
    fun w => F w.1 w.2.1 w.2.2.1 w.2.2.2 with hG
  -- the inequality for `X + 2δI`
  have hδ : ∀ δ : ℝ, 0 < δ →
      F z (U z) p (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ≤ 0 := by
    intro δ hδ
    have hjet := hpX.2 (δ / 2) (half_pos hδ)
    rw [nhdsWithin_eq_nhds.2 (hΩ.mem_nhds hz)] at hjet
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1
      (hjet.and (hΩ.mem_nhds hz))
    set r := ρ / 2 with hr_def
    have hr : 0 < r := half_pos hρ
    have hcb : closedBall z r ⊆ ball z ρ := closedBall_subset_ball (half_lt_self hρ)
    set φ := quadAt (U z) p z X δ with hφ
    have hφc : Continuous φ := continuous_quadAt _ _ _ _ _
    -- on the closed ball, `U ≤ φ - (δ/2)|x - z|²`
    have hUφ : ∀ x ∈ closedBall z r, x ∈ Ω ∧ U x ≤ φ x - δ / 2 * ‖x - z‖ ^ 2 := by
      intro x hx
      obtain ⟨h1, h2⟩ := hball (hcb hx)
      refine ⟨h2, ?_⟩
      simp only [hφ, quadAt]
      linarith
    have hcbK : closedBall z r ⊆ K := fun x hx => subset_closure (hUφ x hx).1
    -- the approximating members
    have hchoice : ∀ n : ℕ, ∃ y : Rd 2, ∃ w ∈ S, ∃ x ∈ closedBall z r,
        y ∈ K ∧ dist y z < 1 / ((n : ℝ) + 1) ∧ dist y z < r ∧
        U z - 2 * (1 / ((n : ℝ) + 1)) < w y ∧
        IsMaxOn (fun t => w t - φ t) (closedBall z r) x := by
      intro n
      have hθ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨y, ⟨hyK, hyb⟩, hy⟩ := exists_lt_of_lt_uEnv hb (subset_closure hz)
        (lt_min hθ hr) hθ
      rw [mem_ball] at hyb
      obtain ⟨w, hwS, hw⟩ := hWS y hyK _ hθ
      have husc' : UpperSemicontinuousOn (fun t => w t + -φ t) (closedBall z r) :=
        ((hS w hwS).1.mono fun t ht => (hUφ t ht).1).add
          (hφc.neg.continuousOn.upperSemicontinuousOn)
      have husc : UpperSemicontinuousOn (fun t => w t - φ t) (closedBall z r) := by
        simpa only [sub_eq_add_neg] using husc'
      obtain ⟨x, hx, hmax⟩ := husc.exists_isMaxOn ⟨z, mem_closedBall_self hr.le⟩
        (isCompact_closedBall z r)
      exact ⟨y, w, hwS, x, hx, hyK, lt_of_lt_of_le hyb (min_le_left _ _),
        lt_of_lt_of_le hyb (min_le_right _ _), by linarith, hmax⟩
    choose y w hwS x hx hyK hyd hydr hwy hmax using hchoice
    -- convergence of the approximating points
    have hθ0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hyz : Tendsto y atTop (𝓝 z) := by
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg)
        (fun n => (hyd n).le) hθ0)
    have hφy : Tendsto (fun n => φ (y n)) atTop (𝓝 (U z)) := by
      have := (hφc.tendsto z).comp hyz
      rwa [Function.comp_def, hφ, quadAt_self] at this
    -- the key estimate
    have hgap : ∀ n : ℕ, U z - 2 * (1 / ((n : ℝ) + 1)) - φ (y n) < w n (x n) - φ (x n) ∧
        w n (x n) - φ (x n) ≤ -(δ / 2 * ‖x n - z‖ ^ 2) := by
      intro n
      have hyc : y n ∈ closedBall z r := by
        rw [mem_closedBall]; exact (hydr n).le
      have h1 : w n (y n) - φ (y n) ≤ w n (x n) - φ (x n) := isMaxOn_iff.1 (hmax n) _ hyc
      have h2 : w n (x n) ≤ U (x n) :=
        (hSW _ (hwS n) _ (hcbK (hx n))).trans (le_uEnv hb (hcbK (hx n)))
      have h3 := (hUφ _ (hx n)).2
      exact ⟨by linarith [hwy n], by linarith⟩
    have hlow : Tendsto (fun n : ℕ => U z - 2 * (1 / ((n : ℝ) + 1)) - φ (y n)) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := U z)).sub (hθ0.const_mul 2)).sub hφy
      simpa using this
    have hlow' : Tendsto (fun n : ℕ => -(U z - 2 * (1 / ((n : ℝ) + 1)) - φ (y n))) atTop (𝓝 0) := by
      have := hlow.neg
      rwa [neg_zero] at this
    have hsq : Tendsto (fun n => δ / 2 * ‖x n - z‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlow'
      have := hgap n
      linarith [this.1, this.2]
    have hxz : Tendsto x atTop (𝓝 z) := by
      have hsq' : Tendsto (fun n => ‖x n - z‖ ^ 2) atTop (𝓝 0) := by
        have := hsq.const_mul (2 / δ)
        rw [mul_zero] at this
        refine this.congr fun n => ?_
        field_simp [hδ.ne']
      have hnorm : Tendsto (fun n => ‖x n - z‖) atTop (𝓝 0) := by
        have := hsq'.sqrt
        rw [Real.sqrt_zero] at this
        refine this.congr fun n => ?_
        exact Real.sqrt_sq (norm_nonneg _)
      exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm
    have hgap0 : Tendsto (fun n => w n (x n) - φ (x n)) atTop (𝓝 0) := by
      have hup : Tendsto (fun n => -(δ / 2 * ‖x n - z‖ ^ 2)) atTop (𝓝 0) := by
        have := hsq.neg
        rwa [neg_zero] at this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => (hgap n).1.le)
        (fun n => (hgap n).2)
    have hwx : Tendsto (fun n => w n (x n)) atTop (𝓝 (U z)) := by
      have hφx : Tendsto (fun n => φ (x n)) atTop (𝓝 (U z)) := by
        have := (hφc.tendsto z).comp hxz
        rwa [Function.comp_def, hφ, quadAt_self] at this
      have := hgap0.add hφx
      simpa using this
    -- eventually the maximum point is interior and gives a superjet
    have hxr : ∀ᶠ n in atTop, x n ∈ ball z r := hxz (ball_mem_nhds z hr)
    have hsub : ∀ᶠ n in atTop, F (x n) (w n (x n))
        (p + matVec (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (x n - z))
        (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ≤ 0 := by
      filter_upwards [hxr] with n hn
      have hjet' : (p + matVec (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (x n - z),
          X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∈ superJet2 Ω (w n) (x n) := by
        refine mem_superJet2_of_quad_max (c := U z) hX ?_
        have hb' : ball z r ∈ 𝓝[Ω] (x n) := mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hn)
        filter_upwards [hb'] with t ht
        exact isMaxOn_iff.1 (hmax n) t (ball_subset_closedBall ht)
      exact (hS _ (hwS n)).2 (x n) (hUφ _ (hx n)).1 _ hjet'
    have hpn : Tendsto (fun n => p + matVec (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (x n - z)) atTop (𝓝 p) := by
      have h1 : Tendsto (fun n => x n - z) atTop (𝓝 0) := by
        simpa using hxz.sub_const z
      have h2 := ((continuous_matVec (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))).tendsto
        0).comp h1
      have h0 : matVec (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 = 0 := by
        simp [matVec]
      rw [h0] at h2
      simpa using (tendsto_const_nhds (x := p)).add h2
    have hT : Tendsto (fun n => G (x n, w n (x n),
        p + matVec (X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (x n - z),
        X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) atTop
        (𝓝 (G (z, U z, p, X + (2 * δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))) :=
      (hcont.tendsto _).comp (hxz.prodMk_nhds (hwx.prodMk_nhds (hpn.prodMk_nhds
        tendsto_const_nhds)))
    exact le_of_tendsto hT hsub
  -- let `δ → 0`
  have hT : Tendsto (fun n : ℕ => G (z, U z, p,
      X + (2 * (1 / ((n : ℝ) + 1))) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) atTop
      (𝓝 (G (z, U z, p, X))) := by
    have hm : Tendsto (fun n : ℕ => X + (2 * (1 / ((n : ℝ) + 1))) •
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) atTop (𝓝 X) := by
      have h1 : Tendsto (fun n : ℕ => (2 * (1 / ((n : ℝ) + 1))) •
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) atTop (𝓝 ((2 * 0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) :=
        ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2).smul_const _)
      rw [mul_zero, zero_smul] at h1
      simpa using (tendsto_const_nhds (x := X)).add h1
    exact (hcont.tendsto _).comp (tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds
      (tendsto_const_nhds.prodMk_nhds hm)))
  exact le_of_tendsto' hT fun n => hδ _ (by positivity)

end SingleSourceD2

end RandomSandpile

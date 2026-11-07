import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainExit
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainGeometry
import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainBarrier

/-!
# Exit time near the boundary of `W_n` (`GreenDomainBoundaryExitStmt`)

`greenDomainBoundaryExit : GreenDomainBoundaryExitStmt`. Write `A = W_n` and
`u = ∑_{y ∈ A} g_A(·, y)` (expected exit time / `2d`), so `Δu = -1` in `A` and `u = 0` off `A`.

* One step (`exit_step`): let `z ∈ A` be within distance `t` of `ℤ^d ∖ A`, with
  `C₀ ≤ t ≤ r₀ n`. The segment from `z/n` to a nearby outside point meets `∂W`; the uniform
  exterior ball condition (`uniformExteriorBall`) gives a ball of radius `c t / n` outside `W` at
  distance `≤ 2t / n` from `z/n`. With a lattice pole `w₀` near its centre, the barrier
  `b = (F₁ - |· - w₀|^{-4d}) / (F₁ - F₂)` is superharmonic in `A` (`lapR_invPow_nonneg`),
  `≥ 0` next to `A`, `≥ 1` at distance `≥ 12 t` from `w₀`, and `b(z) ≤ θ < 1`, `θ = θ(c, d)`.
  Comparing `u` with `((16t)² - |· - z|²)/(2d) + S b` on `A ∩ B_{15t}(z)` (minimum principle) gives
  `u(z) ≤ (16 t)²/(2d) + θ S` whenever `u ≤ S` on the points of `A` within `17 t` of `ℤ^d ∖ A`.
* Iteration (`greenDomainBoundaryExit`): `J` steps from scale `17^J γ n` down to `γ n`, starting from
  the global bound `u ≤ (R n + 1)²/(2d)` (`greenDomainExitTime`), give
  `u ≤ J (16·17^J γ n)²/(2d) + θ^J (R + 1)² n²/(2d) ≤ δ n²` for `θ^J` and `γ` small.
-/

noncomputable section

open LatticeProb Metric

namespace RandomSandpile

namespace DivisibleHomogenizeDomain

open OdometerLowerBound DivisibleHomogenize

variable {d : ℕ}

/-- A connected closed ball from a point of `W` to a point outside `W` meets `∂W`. -/
theorem exists_frontier_near {W : Set (Rd d)} {a b : Rd d} (ha : a ∈ W) (hb : b ∉ W) :
    ∃ p ∈ frontier W, ‖p - a‖ ≤ ‖b - a‖ := by
  by_contra hcon
  have hS : ∀ p ∈ closedBall a ‖b - a‖, p ∉ frontier W := fun p hp hpf =>
    hcon ⟨p, hpf, by rw [← dist_eq_norm]; exact mem_closedBall.1 hp⟩
  have hsub : closedBall a ‖b - a‖ ⊆ interior W ∪ (closure W)ᶜ := by
    intro p hp
    by_cases hpc : p ∈ closure W
    · left
      by_contra hpi
      exact hS p hp ⟨hpc, hpi⟩
    · right; exact hpc
  have hdisj : Disjoint (interior W) (closure W)ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 interior_subset_closure
  have haI : a ∈ interior W := by
    by_contra hai
    exact hS a (mem_closedBall_self (norm_nonneg _)) ⟨subset_closure ha, hai⟩
  have h := (convex_closedBall a ‖b - a‖).isPreconnected.subset_left_of_subset_union
    isOpen_interior isClosed_closure.isOpen_compl hdisj hsub
    ⟨a, mem_closedBall_self (norm_nonneg _), haI⟩
  have hbm : b ∈ closedBall a ‖b - a‖ := by rw [mem_closedBall, dist_eq_norm]
  exact hb (interior_subset (h hbm))

/-- Every point of `ℝ^d` is within distance `d` of a lattice point. -/
theorem exists_site_near (hd : 1 ≤ d) (v : Rd d) : ∃ w : Site d, ‖toE w - v‖ ≤ d := by
  refine ⟨fun i => ⌊v i⌋, ?_⟩
  have h : ‖toE (fun i => ⌊v i⌋) - v‖ ^ 2 ≤ (d : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(toE (fun i => ⌊v i⌋) - v) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp only [PiLp.sub_apply, toE_apply, Real.norm_eq_abs, sq_abs]
          have h1 := Int.floor_le (v i)
          have h2 := Int.lt_floor_add_one (v i)
          nlinarith
      _ = d := by simp
      _ ≤ (d : ℝ) ^ 2 := by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Nat.cast_nonneg _) (by norm_num)).1 h

theorem mem_discretize_iff_inv {W : Set (Rd d)} {n : ℕ} (hn : 1 ≤ n) {x : Site d} :
    x ∈ discretize W n ↔ (n : ℝ)⁻¹ • toE x ∈ W := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  exact Set.mem_smul_set_iff_inv_smul_mem₀ hn0 _ _

theorem lapR_add_fun (f g : Site d → ℝ) (x : Site d) :
    lapR (fun y => f y + g y) x = lapR f x + lapR g x := by
  simp only [lapR, nbrSum, Finset.sum_add_distrib]; ring

theorem lapR_const_mul_fun (β : ℝ) (g : Site d → ℝ) (x : Site d) :
    lapR (fun y => β * g y) x = β * lapR g x := by
  simp only [lapR, nbrSum, ← mul_add, ← Finset.mul_sum]; ring

theorem lapR_comp_sub (f : Site d → ℝ) (z x : Site d) :
    lapR (fun y => f (y - z)) x = lapR f (x - z) := by
  simp only [lapR, nbrSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_sub_right_comm, sub_right_comm]

theorem lapR_quad_center (hd : 1 ≤ d) (ρ : ℝ) (z x : Site d) :
    lapR (fun y : Site d => (ρ ^ 2 - ‖toE (y - z)‖ ^ 2) / (2 * d)) x = -1 := by
  rw [lapR_comp_sub (fun y : Site d => (ρ ^ 2 - ‖toE y‖ ^ 2) / (2 * d)) z x, lapR_quad hd]

theorem norm_toE_sub_le_one_of_adj {x y : Site d} (h : Adj y x) : ‖toE (y - x)‖ ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [toE_sub, hi, toE_add, sub_add_cancel_left, norm_neg, norm_toE_unit]
  · rw [hi, toE_sub, toE_add, add_sub_cancel_left, norm_toE_unit]

/-- The contraction factor of one step. -/
def exitTheta (c : ℝ) (d : ℕ) : ℝ :=
  (1 - (c / 6) ^ (4 * d)) / (1 - (c / 6) ^ (4 * d) / 2)

theorem exitTheta_lt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) : exitTheta c d < 1 := by
  have ha : 0 < (c / 6) ^ (4 * d) := by positivity
  have ha1 : (c / 6) ^ (4 * d) ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  unfold exitTheta
  rw [div_lt_one (by linarith)]
  linarith

theorem exitTheta_nonneg {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) : 0 ≤ exitTheta c d := by
  have ha : (c / 6) ^ (4 * d) ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  unfold exitTheta
  exact div_nonneg (by linarith) (by linarith)

theorem pow4_eq (x : ℝ) : (x ^ 2) ^ (2 * d) = x ^ (4 * d) := by
  rw [← pow_mul]; ring_nf

/-- The real inequalities behind the barrier: `F₂ < F₁` and `(F₁ - f)/(F₁ - F₂) ≤ θ`. -/
theorem barrier_real (hd1 : 1 ≤ d) {c t r₁ m : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (ht : 0 < t)
    (hr₁h : c * t / 2 ≤ r₁) (hr₁c : r₁ ≤ c * t) (hm0 : 0 < m) (hm : m ≤ 3 * t) :
    (((12 * t) ^ 2) ^ (2 * d))⁻¹ < ((r₁ ^ 2) ^ (2 * d))⁻¹ ∧
      (((r₁ ^ 2) ^ (2 * d))⁻¹ - ((m ^ 2) ^ (2 * d))⁻¹) /
          (((r₁ ^ 2) ^ (2 * d))⁻¹ - (((12 * t) ^ 2) ^ (2 * d))⁻¹) ≤ exitTheta c d := by
  have hr₁0 : 0 < r₁ := by have : 0 < c * t := by positivity
                           linarith
  have hct : c * t ≤ t := by nlinarith
  rw [pow4_eq, pow4_eq, pow4_eq]
  have hn : 4 * d ≠ 0 := by omega
  set a := (c / 6) ^ (4 * d) with ha_def
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  have hP1 : 0 < r₁ ^ (4 * d) := by positivity
  have hP2 : 0 < (12 * t) ^ (4 * d) := by positivity
  have hPm : 0 < m ^ (4 * d) := by positivity
  have h12 : r₁ ^ (4 * d) < (12 * t) ^ (4 * d) := pow_lt_pow_left₀ (by linarith) hr₁0.le hn
  have hF12 : ((12 * t) ^ (4 * d))⁻¹ < (r₁ ^ (4 * d))⁻¹ := (inv_lt_inv₀ hP2 hP1).2 h12
  refine ⟨hF12, ?_⟩
  set F₁ := (r₁ ^ (4 * d))⁻¹ with hF₁
  have hF₁pos : 0 < F₁ := inv_pos.2 hP1
  -- `f ≥ a F₁`
  have hfz : a * F₁ ≤ (m ^ (4 * d))⁻¹ := by
    rw [hF₁, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hP1 hPm, one_mul]
    calc a * m ^ (4 * d) ≤ a * (3 * t) ^ (4 * d) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0.le hm _) ha0.le
      _ = (c * t / 2) ^ (4 * d) := by rw [ha_def, ← mul_pow]; congr 1; ring
      _ ≤ r₁ ^ (4 * d) := pow_le_pow_left₀ (by positivity) hr₁h _
  -- `F₂ ≤ (a/2) F₁`
  have hF2 : ((12 * t) ^ (4 * d))⁻¹ ≤ a / 2 * F₁ := by
    rw [hF₁, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hP2 hP1, one_mul]
    have h2 : (2 : ℝ) ≤ 2 ^ (4 * d) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (4 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h6 : (c / 6) * (12 * t) = 2 * (c * t) := by ring
    have heq : a / 2 * (12 * t) ^ (4 * d) = 2 ^ (4 * d) / 2 * (c * t) ^ (4 * d) := by
      calc a / 2 * (12 * t) ^ (4 * d) = ((c / 6) * (12 * t)) ^ (4 * d) / 2 := by
            rw [ha_def, div_mul_eq_mul_div, ← mul_pow]
        _ = (2 * (c * t)) ^ (4 * d) / 2 := by rw [h6]
        _ = 2 ^ (4 * d) / 2 * (c * t) ^ (4 * d) := by rw [mul_pow]; ring
    have hct0 : 0 ≤ (c * t) ^ (4 * d) := by positivity
    have h3 : r₁ ^ (4 * d) ≤ (c * t) ^ (4 * d) := pow_le_pow_left₀ hr₁0.le hr₁c _
    rw [heq]
    nlinarith
  have h1 : (F₁ - (m ^ (4 * d))⁻¹) / (F₁ - ((12 * t) ^ (4 * d))⁻¹) ≤
      ((1 - a) * F₁) / ((1 - a / 2) * F₁) :=
    div_le_div₀ (mul_nonneg (by linarith) hF₁pos.le) (by nlinarith)
      (mul_pos (by linarith) hF₁pos) (by nlinarith)
  rw [mul_div_mul_right _ _ hF₁pos.ne'] at h1
  exact h1

/-- **The barrier** `b = (F₁ - |· - w₀|^{-4d}) / (F₁ - F₂)`. -/
theorem exit_barrier (hd1 : 1 ≤ d) {c t : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hct : 4 * ((d : ℝ) + 1) ≤ c * t) (w₀ : Site d) :
    ∃ b : Site d → ℝ, (∀ y, c * t - d - 1 ≤ ‖toE (y - w₀)‖ → 0 ≤ b y) ∧
      (∀ y, 12 * t ≤ ‖toE (y - w₀)‖ → 1 ≤ b y) ∧
      (∀ y, 4 * (d : ℝ) ≤ ‖toE (y - w₀)‖ ^ 2 → lapR b y ≤ 0) ∧
      (∀ y, c * t - d ≤ ‖toE (y - w₀)‖ → ‖toE (y - w₀)‖ ≤ 3 * t → b y ≤ exitTheta c d) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have ht : 0 < t := by
    by_contra h
    have : c * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0.le (not_lt.1 h)
    linarith
  set r₁ := c * t - d - 1 with hr₁
  have hr₁h : c * t / 2 ≤ r₁ := by rw [hr₁]; linarith
  have hr₁c : r₁ ≤ c * t := by rw [hr₁]; linarith
  have hr₁0 : 0 < r₁ := by have : 0 < c * t := by positivity
                           linarith
  set f : Site d → ℝ := fun y => ((‖toE (y - w₀)‖ ^ 2) ^ (2 * d))⁻¹ with hf
  set F₁ := ((r₁ ^ 2) ^ (2 * d))⁻¹ with hF₁
  set F₂ := (((12 * t) ^ 2) ^ (2 * d))⁻¹ with hF₂
  obtain ⟨hF12, -⟩ := barrier_real hd1 hc0 hc1 ht hr₁h hr₁c (m := 3 * t) (by positivity) le_rfl
  have hD₀pos : 0 < F₁ - F₂ := by linarith
  have hfle : ∀ (y : Site d) (r : ℝ), 0 < r → r ≤ ‖toE (y - w₀)‖ →
      f y ≤ ((r ^ 2) ^ (2 * d))⁻¹ := fun y r hr h => by
    simp only [hf]
    rw [pow4_eq, pow4_eq]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le h _)
  refine ⟨fun y => F₁ / (F₁ - F₂) + (-(1 / (F₁ - F₂))) * f y, ?_, ?_, ?_, ?_⟩
  · intro y h
    have := hfle y r₁ hr₁0 h
    have e : F₁ / (F₁ - F₂) + (-(1 / (F₁ - F₂))) * f y = (F₁ - f y) / (F₁ - F₂) := by
      field_simp; ring
    dsimp only
    rw [e]; exact div_nonneg (by linarith) hD₀pos.le
  · intro y h
    have := hfle y (12 * t) (by positivity) h
    have e : F₁ / (F₁ - F₂) + (-(1 / (F₁ - F₂))) * f y = (F₁ - f y) / (F₁ - F₂) := by
      field_simp; ring
    dsimp only
    rw [e, le_div_iff₀ hD₀pos, one_mul]; linarith
  · intro y h
    have e1 := lapR_const_add' (F₁ / (F₁ - F₂)) (fun y => (-(1 / (F₁ - F₂))) * f y) y
    have e2 := lapR_const_mul_fun (-(1 / (F₁ - F₂))) f y
    have e3 : 0 ≤ lapR f y := lapR_invPow_nonneg hd1 w₀ y h
    rw [e1, e2]
    have : 0 < 1 / (F₁ - F₂) := by positivity
    nlinarith
  · intro y h1 h2
    have hm0 : 0 < ‖toE (y - w₀)‖ := by linarith
    have e : F₁ / (F₁ - F₂) + (-(1 / (F₁ - F₂))) * f y = (F₁ - f y) / (F₁ - F₂) := by
      field_simp; ring
    dsimp only
    rw [e]
    exact (barrier_real hd1 hc0 hc1 ht hr₁h hr₁c hm0 h2).2

/-- The exterior-ball geometry at a point `z ∈ W_n` within `t` of `ℤ^d ∖ W_n`: a lattice pole
`w₀` at distance `≥ c t - d` from `W_n` and `≤ 2t + d` from `z`. -/
theorem exit_geometry (hd1 : 1 ≤ d) {W : Set (Rd d)} {n : ℕ} (hn : 1 ≤ n) {r₀ c : ℝ}
    (hext : ∀ p ∈ frontier W, ∀ s : ℝ, 0 < s → s ≤ r₀ →
      ∃ w : Rd d, dist w p ≤ s ∧ ∀ y ∈ ball w (c * s), y ∉ W)
    {t : ℝ} (htpos : 0 < t) (htr : t ≤ r₀ * n) {z z' : Site d} (hz : z ∈ discretize W n)
    (hz'A : z' ∉ discretize W n) (hz' : ‖toE (z' - z)‖ ≤ t) :
    ∃ w₀ : Site d, (∀ x ∈ discretize W n, c * t - d ≤ ‖toE (x - w₀)‖) ∧
      ‖toE (z - w₀)‖ ≤ 2 * t + d := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : (n : ℝ)⁻¹ • toE z ∈ W := (mem_discretize_iff_inv hn).1 hz
  have hb : (n : ℝ)⁻¹ • toE z' ∉ W := fun h => hz'A ((mem_discretize_iff_inv hn).2 h)
  obtain ⟨p, hpf, hpa⟩ := exists_frontier_near ha hb
  have hba : ‖(n : ℝ)⁻¹ • toE z' - (n : ℝ)⁻¹ • toE z‖ ≤ t / n := by
    rw [← smul_sub, norm_smul, norm_inv, Real.norm_natCast, ← toE_sub, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hz' hn0.le
  have hs0 : 0 < t / n := div_pos htpos hn0
  have hsr : t / n ≤ r₀ := (div_le_iff₀ hn0).2 htr
  obtain ⟨w, hwp, hwball⟩ := hext p hpf (t / n) hs0 hsr
  have hfar : ∀ x ∈ discretize W n, c * t ≤ ‖toE x - (n : ℝ) • w‖ := by
    intro x hx
    have hxW := (mem_discretize_iff_inv hn).1 hx
    have hnot : ¬ (n : ℝ)⁻¹ • toE x ∈ ball w (c * (t / n)) := fun h => hwball _ h hxW
    rw [mem_ball, not_lt, dist_eq_norm] at hnot
    have heq : toE x - (n : ℝ) • w = (n : ℝ) • ((n : ℝ)⁻¹ • toE x - w) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
    rw [heq, norm_smul, Real.norm_natCast]
    calc c * t = (n : ℝ) * (c * (t / n)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hnot hn0.le
  have hnear : ‖toE z - (n : ℝ) • w‖ ≤ 2 * t := by
    have heq : toE z - (n : ℝ) • w = (n : ℝ) • (((n : ℝ)⁻¹ • toE z - p) + (p - w)) := by
      rw [sub_add_sub_cancel, smul_sub, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
    rw [heq, norm_smul, Real.norm_natCast]
    have h1 : ‖(n : ℝ)⁻¹ • toE z - p‖ ≤ t / n := by rw [norm_sub_rev]; exact hpa.trans hba
    have h2 : ‖p - w‖ ≤ t / n := by rw [← dist_eq_norm, dist_comm]; exact hwp
    calc (n : ℝ) * ‖((n : ℝ)⁻¹ • toE z - p) + (p - w)‖ ≤ (n : ℝ) * (t / n + t / n) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) hn0.le
      _ = 2 * t := by field_simp; ring
  obtain ⟨w₀, hw₀⟩ := exists_site_near hd1 ((n : ℝ) • w)
  refine ⟨w₀, fun x hx => ?_, ?_⟩
  · have h := hfar x hx
    have h2 : ‖toE x - (n : ℝ) • w‖ ≤ ‖toE (x - w₀)‖ + ‖toE w₀ - (n : ℝ) • w‖ := by
      rw [toE_sub, ← sub_add_sub_cancel (toE x) (toE w₀) ((n : ℝ) • w)]
      exact norm_add_le _ _
    linarith
  · have h2 : ‖toE (z - w₀)‖ ≤ ‖toE z - (n : ℝ) • w‖ + ‖toE w₀ - (n : ℝ) • w‖ := by
      rw [toE_sub, ← sub_sub_sub_cancel_right (toE z) (toE w₀) ((n : ℝ) • w)]
      exact norm_sub_le _ _
    linarith

/-- **One step of the boundary exit-time iteration**: if `u ≤ S` on the points of `A = W_n` within
`17 t` of `ℤ^d ∖ A`, then `u(z) ≤ (16 t)²/(2d) + θ S` at the points `z ∈ A` within `t`. -/
theorem exit_step (hd : 2 ≤ d) {W : Set (Rd d)} {n : ℕ} (hn : 1 ≤ n)
    (hA : (discretize W n).Finite) {r₀ c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hext : ∀ p ∈ frontier W, ∀ s : ℝ, 0 < s → s ≤ r₀ →
      ∃ w : Rd d, dist w p ≤ s ∧ ∀ y ∈ ball w (c * s), y ∉ W)
    {t : ℝ} (ht0 : 4 * ((d : ℝ) + 1) / c ≤ t) (htr : t ≤ r₀ * n) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ y ∈ discretize W n, y ∈ nearCompl (discretize W n) (17 * t) →
      greenPotential (discretize W n) (fun _ => 1) y ≤ S)
    {z : Site d} (hz : z ∈ discretize W n) (hzc : z ∈ nearCompl (discretize W n) t) :
    greenPotential (discretize W n) (fun _ => 1) z ≤
      (16 * t) ^ 2 / (2 * d) + exitTheta c d * S := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hct : 4 * ((d : ℝ) + 1) ≤ c * t := by
    have := (div_le_iff₀ hc0).1 ht0; linarith
  have hctt : c * t ≤ t := by
    have : 0 ≤ t := by
      have : 0 < 4 * ((d : ℝ) + 1) / c := by positivity
      linarith
    nlinarith
  have ht1 : 4 * ((d : ℝ) + 1) ≤ t := by linarith
  have htpos : 0 < t := by linarith
  obtain ⟨z', hz'A, hz'⟩ := hzc
  obtain ⟨w₀, hfar, hnear⟩ := exit_geometry hd1 hn hext htpos htr hz hz'A hz'
  have hnear3 : ‖toE (z - w₀)‖ ≤ 3 * t := by linarith
  obtain ⟨b, hb0, hb1, hlapb, hbθ⟩ := exit_barrier hd1 hc0 hc1 hct w₀
  have hbz := hbθ z (hfar z hz) hnear3
  -- comparison on `D = A ∩ B_{15t}(z)`
  obtain ⟨u, hu⟩ : ∃ u : Site d → ℝ, u = greenPotential (discretize W n) (fun _ => 1) := ⟨_, rfl⟩
  rw [← hu]
  obtain ⟨Q, hQ⟩ : ∃ Q : Site d → ℝ, Q = fun y => ((16 * t) ^ 2 - ‖toE (y - z)‖ ^ 2) / (2 * d) :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Set (Site d), D = {y | y ∈ discretize W n ∧ ‖toE (y - z)‖ < 15 * t} :=
    ⟨_, rfl⟩
  have hDfin : D.Finite := hA.subset fun y hy => by rw [hD] at hy; exact hy.1
  have hzz : toE (z - z) = 0 := by rw [sub_self]; ext i; simp [toE_apply]
  have hzD : z ∈ D := by rw [hD]; exact ⟨hz, by rw [hzz, norm_zero]; linarith⟩
  have hglap : ∀ x ∈ D, lapR (fun y => (Q y + S * b y) - u y) x ≤ 0 := by
    intro x hx
    rw [hD] at hx
    have e1 : lapR (fun y => (Q y + S * b y) - u y) x =
        lapR (fun y => Q y + S * b y) x - lapR u x := lapR_sub' (fun y => Q y + S * b y) u x
    have e2 : lapR (fun y => Q y + S * b y) x = lapR Q x + lapR (fun y => S * b y) x :=
      lapR_add_fun Q (fun y => S * b y) x
    have e3 : lapR (fun y => S * b y) x = S * lapR b x := lapR_const_mul_fun S b x
    have e4 : lapR Q x = -1 := by rw [hQ]; exact lapR_quad_center hd1 (16 * t) z x
    have e5 : lapR u x = -1 := by
      rw [hu, lapR_greenPotential hd1 hA _ hx.1]
    have hxw := hfar x hx.1
    have hxw2 : 4 * (d : ℝ) ≤ ‖toE (x - w₀)‖ ^ 2 := by nlinarith
    have e6 : lapR b x ≤ 0 := hlapb x hxw2
    rw [e1, e2, e3, e4, e5]
    have e7 := mul_nonpos_of_nonneg_of_nonpos hS0 e6
    linarith
  obtain ⟨y, hy, hyz⟩ := superharmonicMinPrinciple d hd1 D hDfin
    (fun y => (Q y + S * b y) - u y) hglap z hzD
  have hgy : 0 ≤ (Q y + S * b y) - u y := by
    obtain ⟨hyD, x, hxD, hadj⟩ := mem_bdry.1 hy
    rw [hD] at hxD
    have hyx := norm_toE_sub_le_one_of_adj hadj
    have hxz : ‖toE (x - z)‖ < 15 * t := hxD.2
    have hyz2 : ‖toE (y - z)‖ ≤ 16 * t := by
      have : ‖toE (y - z)‖ ≤ ‖toE (y - x)‖ + ‖toE (x - z)‖ := by
        rw [show y - z = (y - x) + (x - z) by abel, toE_add]; exact norm_add_le _ _
      linarith
    have hQy : 0 ≤ Q y := by
      rw [hQ]
      have : ‖toE (y - z)‖ ^ 2 ≤ (16 * t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyz2 2
      exact div_nonneg (by linarith) (by positivity)
    by_cases hyA : y ∈ discretize W n
    · have h15 : 15 * t ≤ ‖toE (y - z)‖ := by
        by_contra h
        exact hyD (by rw [hD]; exact ⟨hyA, not_le.1 h⟩)
      have hnc : y ∈ nearCompl (discretize W n) (17 * t) := by
        refine ⟨z', hz'A, ?_⟩
        have : ‖toE (z' - y)‖ ≤ ‖toE (z' - z)‖ + ‖toE (z - y)‖ := by
          rw [show z' - y = (z' - z) + (z - y) by abel, toE_add]; exact norm_add_le _ _
        have h2 : ‖toE (z - y)‖ = ‖toE (y - z)‖ := by
          rw [toE_sub, toE_sub, norm_sub_rev]
        linarith
      have huy : u y ≤ S := by rw [hu]; exact hS y hyA hnc
      have hyw : 12 * t ≤ ‖toE (y - w₀)‖ := by
        have : ‖toE (y - z)‖ ≤ ‖toE (y - w₀)‖ + ‖toE (z - w₀)‖ := by
          rw [toE_sub, toE_sub, toE_sub, ← sub_sub_sub_cancel_right (toE y) (toE z) (toE w₀)]
          exact norm_sub_le _ _
        linarith
      have hby := hb1 y hyw
      have := mul_le_mul_of_nonneg_left hby hS0
      linarith
    · have huy : u y = 0 := by rw [hu]; exact greenPotential_eq_zero_of_not_mem _ _ hyA
      have hyw : c * t - d - 1 ≤ ‖toE (y - w₀)‖ := by
        have h1 := hfar x hxD.1
        have : ‖toE (x - w₀)‖ ≤ ‖toE (x - y)‖ + ‖toE (y - w₀)‖ := by
          rw [show x - w₀ = (x - y) + (y - w₀) by abel, toE_add]; exact norm_add_le _ _
        have h2 : ‖toE (x - y)‖ = ‖toE (y - x)‖ := by
          rw [toE_sub, toE_sub, norm_sub_rev]
        linarith
      have hby := hb0 y hyw
      rw [huy]
      have := mul_nonneg hS0 hby
      linarith
  have hQz : Q z = (16 * t) ^ 2 / (2 * d) := by
    rw [hQ]; simp only [hzz, norm_zero]; ring
  have hfinal : u z ≤ Q z + S * b z := by
    have := hgy.trans hyz
    linarith
  rw [hQz] at hfinal
  have := mul_le_mul_of_nonneg_left hbz hS0
  linarith

/-- **The iteration**: `J` steps from scale `17^J γ n` down to `γ n`. -/
theorem exit_iter (hd : 2 ≤ d) {W : Set (Rd d)} {n : ℕ} (hn : 1 ≤ n)
    (hA : (discretize W n).Finite) {r₀ c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hext : ∀ p ∈ frontier W, ∀ s : ℝ, 0 < s → s ≤ r₀ →
      ∃ w : Rd d, dist w p ≤ s ∧ ∀ y ∈ ball w (c * s), y ∉ W)
    {γ : ℝ} (hγ0 : 0 < γ) {J : ℕ} (hγn : 4 * ((d : ℝ) + 1) / c ≤ γ * n)
    (hγr : 17 ^ J * γ ≤ r₀) {G : ℝ} (hG0 : 0 ≤ G)
    (hglob : ∀ y, greenPotential (discretize W n) (fun _ => 1) y ≤ G) :
    ∀ m : ℕ, m ≤ J → ∀ y ∈ discretize W n,
      y ∈ nearCompl (discretize W n) (17 ^ (J - m) * γ * n) →
        greenPotential (discretize W n) (fun _ => 1) y ≤
          m * ((16 * 17 ^ J * γ * n) ^ 2 / (2 * d)) + exitTheta c d ^ m * G := by
  have hd1 : 1 ≤ d := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ0 : 0 ≤ exitTheta c d := exitTheta_nonneg hc0 hc1
  have hθ1 : exitTheta c d ≤ 1 := (exitTheta_lt_one hc0 hc1).le
  intro m
  induction m with
  | zero =>
    intro _ y _ _
    simp only [Nat.cast_zero, zero_mul, pow_zero, one_mul, zero_add]
    exact hglob y
  | succ m ih =>
    intro hm y hy hyc
    have hmJ : m ≤ J := by omega
    set X : ℝ := (16 * 17 ^ J * γ * n) ^ 2 / (2 * d) with hX
    have hX0 : 0 ≤ X := by positivity
    set t : ℝ := 17 ^ (J - (m + 1)) * γ * n with ht
    have h17 : 17 * t = 17 ^ (J - m) * γ * n := by
      have e : J - m = (J - (m + 1)) + 1 := by omega
      rw [ht, e, pow_succ]; ring
    have hpow1 : (1 : ℝ) ≤ 17 ^ (J - (m + 1)) := one_le_pow₀ (by norm_num)
    have hpowJ : (17 : ℝ) ^ (J - (m + 1)) ≤ 17 ^ J := pow_le_pow_right₀ (by norm_num) (by omega)
    have hγn0 : 0 ≤ γ * n := by positivity
    have ht0 : 4 * ((d : ℝ) + 1) / c ≤ t := by
      have : γ * n ≤ t := by rw [ht, mul_assoc]; nlinarith
      linarith
    have htJ : t ≤ 17 ^ J * γ * n := by
      rw [ht, mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hpowJ (by positivity)
    have htr : t ≤ r₀ * n := by
      have : 17 ^ J * γ * n ≤ r₀ * n := mul_le_mul_of_nonneg_right hγr hn0.le
      linarith
    have hS0 : 0 ≤ (m : ℝ) * X + exitTheta c d ^ m * G := by positivity
    have hS : ∀ y ∈ discretize W n, y ∈ nearCompl (discretize W n) (17 * t) →
        greenPotential (discretize W n) (fun _ => 1) y ≤ (m : ℝ) * X + exitTheta c d ^ m * G := by
      rw [h17]; exact ih hmJ
    have hyc' : y ∈ nearCompl (discretize W n) t := by rw [ht]; exact hyc
    have key := exit_step hd hn hA hc0 hc1 hext ht0 htr hS0 hS hy hyc'
    have h16 : (16 * t) ^ 2 / (2 * d) ≤ X := by
      rw [hX]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    have hθS : exitTheta c d * ((m : ℝ) * X + exitTheta c d ^ m * G) ≤
        (m : ℝ) * X + exitTheta c d ^ (m + 1) * G := by
      have : exitTheta c d * ((m : ℝ) * X) ≤ (m : ℝ) * X := by
        have : 0 ≤ (m : ℝ) * X := by positivity
        nlinarith
      rw [mul_add, pow_succ]
      nlinarith
    push_cast
    linarith

/-- The final arithmetic of the iteration. -/
theorem exit_final_bound {δ dR Cg θ T γ nR : ℝ} {J : ℕ} (hδ : 0 < δ) (hd : 0 < dR)
    (hCg0 : 0 ≤ Cg) (hθJ : θ ^ J < δ / (2 * (Cg + 1))) (hT0 : 0 < T) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hγδ : γ ≤ δ * dR / ((J + 1) * T ^ 2)) :
    (J : ℝ) * ((T * γ * nR) ^ 2 / (2 * dR)) + θ ^ J * (Cg * nR ^ 2) ≤ δ * nR ^ 2 := by
  have hγ2 : γ ^ 2 ≤ δ * dR / ((J + 1) * T ^ 2) := by
    have : γ ^ 2 ≤ γ := by nlinarith
    linarith
  have hJT : (J : ℝ) * T ^ 2 * γ ^ 2 ≤ δ * dR := by
    have e : (J : ℝ) * T ^ 2 * (δ * dR / ((J + 1) * T ^ 2)) = (J / (J + 1)) * (δ * dR) := by
      field_simp
    have hJ1 : (J : ℝ) / (J + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc (J : ℝ) * T ^ 2 * γ ^ 2 ≤ J * T ^ 2 * (δ * dR / ((J + 1) * T ^ 2)) := by gcongr
      _ = (J / (J + 1)) * (δ * dR) := e
      _ ≤ δ * dR := by nlinarith [mul_pos hδ hd]
  have h1 : (J : ℝ) * ((T * γ * nR) ^ 2 / (2 * dR)) ≤ δ / 2 * nR ^ 2 := by
    have e : (J : ℝ) * ((T * γ * nR) ^ 2 / (2 * dR)) = (J * T ^ 2 * γ ^ 2) * nR ^ 2 / (2 * dR) := by
      ring
    rw [e, div_le_iff₀ (by positivity)]
    have : 0 ≤ nR ^ 2 := by positivity
    nlinarith
  have h2 : θ ^ J * (Cg * nR ^ 2) ≤ δ / 2 * nR ^ 2 := by
    have hC : Cg / (Cg + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h3 : θ ^ J * Cg ≤ δ / 2 := by
      calc θ ^ J * Cg ≤ δ / (2 * (Cg + 1)) * Cg := mul_le_mul_of_nonneg_right hθJ.le hCg0
        _ = δ / 2 * (Cg / (Cg + 1)) := by field_simp
        _ ≤ δ / 2 := by nlinarith
    have : 0 ≤ nR ^ 2 := by positivity
    nlinarith
  linarith

/-- The global exit-time bound `u ≤ (R + 1)² n² / (2d)`. -/
theorem exit_glob (hd1 : 1 ≤ d) {W : Set (Rd d)} {R : ℝ} (hR0 : 0 ≤ R)
    (hWR : W ⊆ closedBall 0 R) {n : ℕ} (hn1 : 1 ≤ n) (y : Site d) :
    greenPotential (discretize W n) (fun _ => 1) y ≤ (R + 1) ^ 2 / (2 * d) * n ^ 2 := by
  refine (greenDomainExitTime d hd1 W R hR0 hWR n y).trans ?_
  have e : (R + 1) ^ 2 / (2 * d) * n ^ 2 = ((R + 1) * n) ^ 2 / (2 * d) := by ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  nlinarith

end DivisibleHomogenizeDomain

open DivisibleHomogenizeDomain in
/-- **Exit time near the boundary of `W_n`** (`GreenDomainBoundaryExitStmt`). -/
theorem greenDomainBoundaryExit : GreenDomainBoundaryExitStmt := by
  intro d hd W hW δ hδ
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨r₀, c₀, hr₀, hc₀, hext₀⟩ := uniformExteriorBall d W hW
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min c₀ 1 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact lt_min hc₀ one_pos
  have hc1 : c ≤ 1 := by rw [hc]; exact min_le_right _ _
  have hext : ∀ p ∈ frontier W, ∀ s : ℝ, 0 < s → s ≤ r₀ →
      ∃ w : Rd d, dist w p ≤ s ∧ ∀ y ∈ ball w (c * s), y ∉ W := fun p hp s hs hsr => by
    obtain ⟨w, hw, hball⟩ := hext₀ p hp s hs hsr
    refine ⟨w, hw, fun y hy => hball y (ball_subset_ball ?_ hy)⟩
    rw [hc]; exact mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le
  obtain ⟨R, hR0, hWR⟩ := exists_closedBall_of_isBounded hW.1
  have hθ1 : exitTheta c d < 1 := exitTheta_lt_one hc0 hc1
  obtain ⟨Cg, hCg⟩ : ∃ Cg : ℝ, Cg = (R + 1) ^ 2 / (2 * d) := ⟨_, rfl⟩
  have hCg0 : 0 ≤ Cg := by rw [hCg]; positivity
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (2 * (Cg + 1)) by positivity) hθ1
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 16 * 17 ^ J := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = min (min (r₀ / 17 ^ J) 1) (δ * d / ((J + 1) * T ^ 2)) :=
    ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; exact lt_min (lt_min (by positivity) one_pos) (by positivity)
  have hγr : 17 ^ J * γ ≤ r₀ := by
    have : γ ≤ r₀ / 17 ^ J := by rw [hγ]; exact (min_le_left _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hγ1 : γ ≤ 1 := by rw [hγ]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hγδ : γ ≤ δ * d / ((J + 1) * T ^ 2) := by rw [hγ]; exact min_le_right _ _
  refine ⟨γ, hγ0, ⌈4 * ((d : ℝ) + 1) / c / γ⌉₊ + 1, fun n hn z hz => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hγn : 4 * ((d : ℝ) + 1) / c ≤ γ * n := by
    have hcn : ⌈4 * ((d : ℝ) + 1) / c / γ⌉₊ ≤ n := by omega
    have h1 : 4 * ((d : ℝ) + 1) / c / γ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hcn)
    rw [div_le_iff₀ hγ0] at h1
    linarith
  have hA := DivisibleHomogenizeDomain.discretize_finite hW.1 n
  have hglob : ∀ y, greenPotential (discretize W n) (fun _ => 1) y ≤ Cg * n ^ 2 := by
    intro y; rw [hCg]; exact exit_glob hd1 hR0 hWR hn1 y
  by_cases hzA : z ∈ discretize W n
  · have hz' : z ∈ nearCompl (discretize W n) (17 ^ (J - J) * γ * n) := by
      rw [Nat.sub_self, pow_zero, one_mul]; exact hz
    have key := exit_iter hd hn1 hA hc0 hc1 hext hγ0 hγn hγr (by positivity) hglob J le_rfl z
      hzA hz'
    rw [← hT] at key
    exact key.trans (exit_final_bound hδ hdpos hCg0 hJ hT0 hγ0 hγ1 hγδ)
  · rw [greenPotential_eq_zero_of_not_mem _ _ hzA]; positivity

end RandomSandpile

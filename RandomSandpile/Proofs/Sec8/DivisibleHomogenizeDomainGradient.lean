import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainExit
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeHarnack
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeGradient

/-!
# Lemma 8.1: the interior difference estimate on `W_n`

Proof of `GreenDomainGradientSumStmt` from the Lawler-Limic harmonic difference estimate
(`LawlerLimicHarmonicDifferenceStmt`), as the ball case `greenBallGradientSum_of_harnack` of
Lemma 7.3.

For a finite `A ⊆ ℤ^d`, a scale `t ≥ 16 √d`, `x ∈ ℤ^d` and a site `y` with `y ∉ nearCompl A t`
(every site within distance `t` of `y` lies in `A`) and `|x - y| ≥ 16 √d`, put
`m = min (|x - y|, t)` and `R = ⌊m / (4 √d)⌋₊`. Every `w` in the box `[-2R, 2R]^d` has
`|w| ≤ m / 2 ≤ t`, so `y + w ∈ A` and `y + w ≠ x`; hence `u(w) = g_A(x, y + w)` is nonnegative
and harmonic on `[-(2R-1), 2R-1]^d` (`lapR_greenKilled_right`), and the Harnack inequality and
the Lawler-Limic estimate (`gradient_le_of_box`) give
`|g_A(x, y + e_i) - g_A(x, y)| · min (|x - y|, t) ≤ C₁ g_A(x, y)`.

Summing over the sites of `(nearCompl A t)ᶜ`: the finitely many sites with `|x - y| < 16 √d` are
bounded by the weighted occupation bound `weightedSum_le`, as in `sum_abs_grad_le_near`; for the
others `1 / min (D, t) ≤ 1 / D + 1 / t` and the two sums `∑ g(x, y) / |x - y|`, `∑ g(x, y)` are
bounded by `weightedSum_le` and the exit time bound `greenDomainExitTime`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

open OdometerLowerBound DivisibleHomogenize

namespace DivisibleHomogenizeDomain

variable {d : ℕ}

/-! ### Real-number arithmetic -/

/-- The radius `R = ⌊m / (4 s)⌋₊` satisfies `m / (8 s) ≤ R - 1` and `2 ≤ m / (8 s)` once
`m ≥ 16 s`. -/
theorem radius_lower' {s m : ℝ} (hs : 0 < s) (hm : 16 * s ≤ m) :
    2 ≤ m / (8 * s) ∧ m / (8 * s) ≤ (⌊m / (4 * s)⌋₊ : ℝ) - 1 := by
  have h8 : 0 < 8 * s := by positivity
  have h2 : 2 ≤ m / (8 * s) := by
    rw [le_div_iff₀ h8]
    linarith
  refine ⟨h2, ?_⟩
  have hfl := Nat.lt_floor_add_one (m / (4 * s))
  have heq : m / (4 * s) = 2 * (m / (8 * s)) := by
    field_simp
    ring
  linarith

/-- The final division: `A ≤ K / ρ` and `ρ ≥ m / (8 s)` give `A m ≤ 8 s K`. -/
theorem mul_le_of_le_div' {s m ρ A K : ℝ} (hs : 0 < s) (hm : 0 < m)
    (hρ : m / (8 * s) ≤ ρ) (hK : 0 ≤ K) (hA : A ≤ K / ρ) : A * m ≤ K * (8 * s) := by
  have ht : 0 < m / (8 * s) := by positivity
  have h1 : K / ρ ≤ K / (m / (8 * s)) := div_le_div_of_nonneg_left hK ht hρ
  have h2 : K / (m / (8 * s)) * m = K * (8 * s) := by
    field_simp
  calc A * m ≤ K / (m / (8 * s)) * m :=
        mul_le_mul_of_nonneg_right (hA.trans h1) hm.le
    _ = K * (8 * s) := h2

/-- `1 / min (D, t) ≤ 1 / D + 1 / t`. -/
theorem inv_min_le {D t : ℝ} (hD : 0 < D) (ht : 0 < t) : (min D t)⁻¹ ≤ D⁻¹ + t⁻¹ := by
  rcases le_total D t with h | h
  · rw [min_eq_left h]
    linarith [inv_pos.2 ht]
  · rw [min_eq_right h]
    linarith [inv_pos.2 hD]

/-! ### The gradient bound for `g_A(x, ·)` away from `x` and the complement of `A` -/

/-- **Harnack plus Lawler-Limic for a finite set `A`** (the port of
`greenBallHarnackGradient_of_lawlerLimic`, with the radius `min (|x - y|, t)`): there is `C₁`
such that, for every finite `A`, `t ≥ 16 √d`, `x` and `y ∉ nearCompl A t` with
`|x - y| ≥ 16 √d`, one has `|g_A(x, y + e_i) - g_A(x, y)| · min (|x - y|, t) ≤ C₁ g_A(x, y)`. -/
theorem exists_gradient_bound (hLL : LawlerLimicHarmonicDifferenceStmt) (hd : 1 ≤ d) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (A : Set (Site d)), A.Finite → ∀ (t : ℝ) (x y : Site d),
      y ∉ nearCompl A t → 16 * Real.sqrt d ≤ ‖toE (x - y)‖ → 16 * Real.sqrt d ≤ t →
        ∀ i : Fin d, |greenKilled A x (y + unit i) - greenKilled A x y| *
          min ‖toE (x - y)‖ t ≤ C₁ * greenKilled A x y := by
  obtain ⟨C_L, hCL, hLLd⟩ := hLL d hd
  obtain ⟨C_H, hCH1, hHar⟩ := harnack_one_le hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd1
  have hs0 : 0 < Real.sqrt d := by linarith
  refine ⟨C_L * C_H * (8 * Real.sqrt d), by positivity, ?_⟩
  intro A hA t x y hy hD ht i
  have hm16 : 16 * Real.sqrt d ≤ min ‖toE (x - y)‖ t := le_min hD ht
  have hmpos : 0 < min ‖toE (x - y)‖ t := by linarith
  obtain ⟨-, hrad⟩ := radius_lower' hs0 hm16
  obtain ⟨ht2, -⟩ := radius_lower' hs0 hm16
  have hRge : (3 : ℝ) ≤ (⌊min ‖toE (x - y)‖ t / (4 * Real.sqrt d)⌋₊ : ℝ) := by linarith
  set R : ℕ := ⌊min ‖toE (x - y)‖ t / (4 * Real.sqrt d)⌋₊ with hRdef
  have hR2 : 2 ≤ R := by
    have : (2 : ℝ) ≤ R := by linarith
    exact_mod_cast this
  have hmnn : 0 ≤ min ‖toE (x - y)‖ t / (4 * Real.sqrt d) := by positivity
  have hRle : (R : ℝ) ≤ min ‖toE (x - y)‖ t / (4 * Real.sqrt d) := Nat.floor_le hmnn
  have hRm : 4 * Real.sqrt d * R ≤ min ‖toE (x - y)‖ t := by
    rw [le_div_iff₀ (by positivity)] at hRle
    linarith
  have hmD : min ‖toE (x - y)‖ t ≤ ‖toE (x - y)‖ := min_le_left _ _
  have hmt : min ‖toE (x - y)‖ t ≤ t := min_le_right _ _
  -- every point of the box `[-2R, 2R]^d` has norm at most `m / 2`
  have hwnorm : ∀ w ∈ LatticeProb.box d (2 * R), ‖toE w‖ ≤ min ‖toE (x - y)‖ t / 2 := by
    intro w hw
    have h1 := norm_le_of_mem_box hw
    push_cast at h1
    nlinarith
  have hbox_mem : ∀ w ∈ LatticeProb.box d (2 * R), y + w ∈ A := by
    intro w hw
    by_contra hwA
    apply hy
    refine ⟨y + w, hwA, ?_⟩
    rw [add_sub_cancel_left]
    have h1 := hwnorm w hw
    linarith
  have hbox_ne : ∀ w ∈ LatticeProb.box d (2 * R), y + w ≠ x := by
    intro w hw hwx
    have hw' : w = x - y := by rw [← hwx]; abel
    have h1 := hwnorm w hw
    rw [hw'] at h1
    linarith
  have hpos : ∀ w ∈ LatticeProb.box d (2 * R), 0 ≤ (fun w => greenKilled A x (y + w)) w :=
    fun w _ => greenKilled_nonneg _ _ _
  have hharm : ∀ w ∈ LatticeProb.box d (2 * R - 1), lapR (fun w => greenKilled A x (y + w)) w = 0 := by
    intro w hw
    have hw2 : w ∈ LatticeProb.box d (2 * R) := mem_box_of_le (by omega) hw
    rw [lapR_translate (fun z => greenKilled A x z) y w]
    rw [lapR_greenKilled_right hd hA x (hbox_mem w hw2)]
    simp [hbox_ne w hw2]
  have hgrad := gradient_le_of_box hCH1 hLLd hHar
    (fun w => greenKilled A x (y + w)) R hR2 hpos hharm i
  simp only [add_zero] at hgrad
  have hR1 : (((R - 1 : ℕ) : ℝ)) = (R : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hg0 := greenKilled_nonneg A x y
  have hfin := mul_le_of_le_div' hs0 hmpos (ρ := (((R - 1 : ℕ) : ℝ))) (by rw [hR1]; exact hrad)
    (K := C_L * (C_H * greenKilled A x y)) (by positivity) hgrad
  calc _ ≤ _ := hfin
    _ = _ := by ring

/-! ### Near `x`: a general-domain version of `sum_abs_grad_le_near` -/

/-- **`g_A(x, ·)` near `x` from the weighted occupation bound**:
`g_A(x, w) ≤ (|w - x| + 1)(C + 1) m` when `∑_{y ≠ x} g_A(x, y) / |y - x| ≤ C m`, `m ≥ 1`. -/
theorem greenKilled_le_of_weighted' (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) {x : Site d}
    (hx : x ∈ A) {C m : ℝ} (hC : 0 ≤ C) (hm : 1 ≤ m)
    (hW : greenPotential A (fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹) x ≤ C * m)
    (w : Site d) : greenKilled A x w ≤ (‖toE (w - x)‖ + 1) * ((C + 1) * m) := by
  have hCn : 0 ≤ C * m := mul_nonneg hC (by linarith)
  have hsingle : ∀ v, v ≠ x → greenKilled A x v * ‖toE (v - x)‖⁻¹ ≤ C * m := by
    intro v hv
    by_cases hvB : v ∈ A
    · refine le_trans ?_ hW
      rw [greenPotential, finsum_mem_eq_finite_toFinset_sum _ hA]
      have := Finset.single_le_sum
        (f := fun y => greenKilled A x y * (if y = x then 0 else ‖toE (y - x)‖⁻¹))
        (fun y _ => mul_nonneg (greenKilled_nonneg _ _ _) (by split_ifs <;> positivity))
        (hA.mem_toFinset.2 hvB)
      simpa [hv] using this
    · rw [greenKilled_eq_zero_of_not_mem_right hd hA x hvB, zero_mul]
      exact hCn
  by_cases hwx : w = x
  · subst hwx
    have hlap := lapR_greenKilled_right hd hA w hx
    rw [if_pos rfl, lapR, nbrSum] at hlap
    have hne : ∀ i : Fin d, w + unit i ≠ w ∧ w - unit i ≠ w := fun i => by
      constructor <;> intro h <;> have h2 := congrFun h i <;> simp [unit] at h2
    have hnb : ∀ i : Fin d, greenKilled A w (w + unit i) + greenKilled A w (w - unit i) ≤
        2 * (C * m) := by
      intro i
      have h1 := hsingle (w + unit i) (hne i).1
      have h2 := hsingle (w - unit i) (hne i).2
      rw [show w + unit i - w = unit i by abel, norm_toE_unit, inv_one, mul_one] at h1
      rw [show w - unit i - w = 0 - unit i by abel, toE_sub, toE_zero, zero_sub, norm_neg,
        norm_toE_unit, inv_one, mul_one] at h2
      linarith
    have hS : ∑ i : Fin d, (greenKilled A w (w + unit i) + greenKilled A w (w - unit i)) ≤
        2 * (d : ℝ) * (C * m) := by
      calc _ ≤ ∑ _i : Fin d, 2 * (C * m) := Finset.sum_le_sum fun i _ => hnb i
        _ = _ := by simp; ring
    rw [sub_self, toE_zero, norm_zero]
    exact arith_diag (by exact_mod_cast hd) hm hS (by linarith)
  · have hr := one_le_norm_toE (sub_ne_zero.2 hwx)
    have h := hsingle w hwx
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)] at h
    exact arith_off (by linarith) (by linarith) hC h

/-- **Near `x`**: `∑_i |∇_i g_A(x, y)| ≤ 2d (ρ + 2)(C + 1) m` when `|y - x| ≤ ρ`. -/
theorem sum_abs_grad_le_near' (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) {x : Site d}
    (hx : x ∈ A) {C m : ℝ} (hC : 0 ≤ C) (hm : 1 ≤ m)
    (hW : greenPotential A (fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹) x ≤ C * m)
    {ρ : ℝ} (y : Site d) (hy : ‖toE (y - x)‖ ≤ ρ) :
    ∑ i : Fin d, |greenKilled A x (y + unit i) - greenKilled A x y| ≤
      d * (2 * ((ρ + 2) * ((C + 1) * m))) := by
  have hP : 0 ≤ (C + 1) * m := by
    have : 0 ≤ C + 1 := by linarith
    have : 0 ≤ m := by linarith
    positivity
  calc _ ≤ ∑ _i : Fin d, 2 * ((ρ + 2) * ((C + 1) * m)) :=
        Finset.sum_le_sum fun i _ => by
          have h1 := greenKilled_le_of_weighted' hd hA hx hC hm hW (y + unit i)
          have h2 := greenKilled_le_of_weighted' hd hA hx hC hm hW y
          have h3 : ‖toE (y + unit i - x)‖ ≤ ρ + 1 := by
            rw [show y + unit i - x = (y - x) + unit i by abel, toE_add]
            exact (norm_add_le _ _).trans (by rw [norm_toE_unit]; linarith)
          have h1' : greenKilled A x (y + unit i) ≤ (ρ + 2) * ((C + 1) * m) :=
            h1.trans (mul_le_mul_of_nonneg_right (by linarith) hP)
          have h2' : greenKilled A x y ≤ (ρ + 2) * ((C + 1) * m) :=
            h2.trans (mul_le_mul_of_nonneg_right (by linarith) hP)
          have g1 := greenKilled_nonneg A x (y + unit i)
          have g2 := greenKilled_nonneg A x y
          rw [abs_le]
          constructor <;> linarith
    _ = _ := by simp

/-- A partial sum of `g_A(x, y) f(y)` over a subset of `A` is at most the Green potential of a
nonnegative density `f`. -/
theorem sum_le_greenPotential {A : Set (Site d)} (hA : A.Finite) (S : Finset (Site d))
    (hS : ∀ y ∈ S, y ∈ A) (f : Site d → ℝ) (hf : ∀ y, 0 ≤ f y) (x : Site d) :
    ∑ y ∈ S, greenKilled A x y * f y ≤ greenPotential A f x := by
  rw [greenPotential, finsum_mem_eq_finite_toFinset_sum _ hA]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro y hy
    exact hA.mem_toFinset.2 (hS y hy)
  · intro y _ _
    exact mul_nonneg (greenKilled_nonneg _ _ _) (hf y)

/-- The constant bounding the (at most `(2⌈16 √d⌉ + 1)^d`) near sites in
`finsum_gradient_le`. -/
def nearConst (d : ℕ) : ℝ :=
  (((2 * ⌈16 * Real.sqrt d⌉₊ + 1) ^ d : ℕ) : ℝ) *
    ((d : ℝ) * (2 * ((16 * Real.sqrt d + 2) * (3 + 1))))

/-- `nearConst d` is nonnegative. -/
theorem nearConst_nonneg (d : ℕ) : 0 ≤ nearConst d := by
  unfold nearConst
  positivity

/-! ### The sum over the interior -/

/-- **The sum of the gradient over the interior of `A`**: for finite `A ⊆ {|y| ≤ ρ}`, `x ∈ A`,
`t ≥ 16 √d`, if the pointwise gradient bound holds with constant `C₁` and the exit time is at most
`(ρ + 1)² / (2d)`, then
`∑_{y ∈ (nearCompl A t)ᶜ} ∑_i |g_A(x, y + e_i) - g_A(x, y)| ≤
  nearConst d (ρ + 1) + d C₁ (3 (ρ + 1) + t⁻¹ (ρ + 1)² / (2d))`. -/
theorem finsum_gradient_le (hd : 2 ≤ d) {C₁ : ℝ} (hC₁ : 0 < C₁) {A : Set (Site d)}
    (hA : A.Finite) {ρ : ℝ} (hρ : 0 ≤ ρ) (hAρ : ∀ y ∈ A, ‖toE y‖ ≤ ρ) {t : ℝ}
    (ht : 16 * Real.sqrt d ≤ t) {x : Site d} (hx : x ∈ A)
    (hExit : greenPotential A (fun _ => 1) x ≤ (ρ + 1) ^ 2 / (2 * d))
    (hgrad : ∀ y : Site d, y ∉ nearCompl A t → 16 * Real.sqrt d ≤ ‖toE (x - y)‖ →
      ∀ i : Fin d, |greenKilled A x (y + unit i) - greenKilled A x y| *
        min ‖toE (x - y)‖ t ≤ C₁ * greenKilled A x y) :
    ∑ᶠ y ∈ (nearCompl A t)ᶜ, ∑ i : Fin d,
        |greenKilled A x (y + unit i) - greenKilled A x y| ≤
      nearConst d * (ρ + 1) +
        (d : ℝ) * C₁ * (3 * (ρ + 1) + t⁻¹ * ((ρ + 1) ^ 2 / (2 * d))) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hs1 : 1 ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd1'
  have hs0 : 0 < Real.sqrt d := by linarith
  have ht0 : 0 < t := by linarith
  have hsub : (nearCompl A t)ᶜ ⊆ A := by
    intro y hy
    by_contra hyA
    apply hy
    exact ⟨y, hyA, by rw [sub_self, toE_zero, norm_zero]; exact ht0.le⟩
  have hfinT : ((nearCompl A t)ᶜ).Finite := hA.subset hsub
  rw [finsum_mem_eq_finite_toFinset_sum _ hfinT]
  have hT : ∀ y, y ∈ hfinT.toFinset ↔ y ∉ nearCompl A t := fun y => by
    rw [Set.Finite.mem_toFinset, Set.mem_compl_iff]
  have hWx : greenPotential A (fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹) x ≤
      3 * (ρ + 1) := weightedSum_le hd hA hAρ hx
  rw [← Finset.sum_filter_add_sum_filter_not hfinT.toFinset
    (fun y => ‖toE (x - y)‖ < 16 * Real.sqrt d)]
  -- near `x`
  have hnear : ∑ y ∈ hfinT.toFinset.filter (fun y => ‖toE (x - y)‖ < 16 * Real.sqrt d),
      ∑ i : Fin d, |greenKilled A x (y + unit i) - greenKilled A x y| ≤
        nearConst d * (ρ + 1) := by
    have hcard : (hfinT.toFinset.filter (fun y => ‖toE (x - y)‖ < 16 * Real.sqrt d)).card ≤
        (2 * ⌈16 * Real.sqrt d⌉₊ + 1) ^ d := by
      rw [← card_box d ⌈16 * Real.sqrt d⌉₊]
      refine Finset.card_le_card_of_injOn (fun y => y - x) (fun y hy => ?_)
        (fun y _ z _ h => by simpa using h)
      have hy' := (Finset.mem_filter.1 hy).2
      rw [Finset.mem_coe, mem_box]
      intro i
      have h1 := abs_coord_le_norm (y - x) i
      rw [← norm_toE_sub_comm] at h1
      have h2 : 16 * Real.sqrt d ≤ (⌈16 * Real.sqrt d⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : |((y - x) i : ℝ)| < ⌈16 * Real.sqrt d⌉₊ := by linarith
      exact_mod_cast h3.le
    have hcon : 0 ≤ (d : ℝ) * (2 * ((16 * Real.sqrt d + 2) * ((3 + 1) * (ρ + 1)))) := by positivity
    calc _ ≤ ∑ _y ∈ hfinT.toFinset.filter (fun y => ‖toE (x - y)‖ < 16 * Real.sqrt d),
          (d : ℝ) * (2 * ((16 * Real.sqrt d + 2) * ((3 + 1) * (ρ + 1)))) :=
          Finset.sum_le_sum fun y hy => sum_abs_grad_le_near' hd1 hA hx (C := 3) (m := ρ + 1)
            (by norm_num) (by linarith) hWx y (by
              rw [← norm_toE_sub_comm]; exact (Finset.mem_filter.1 hy).2.le)
      _ = ((hfinT.toFinset.filter (fun y => ‖toE (x - y)‖ < 16 * Real.sqrt d)).card : ℝ) *
            ((d : ℝ) * (2 * ((16 * Real.sqrt d + 2) * ((3 + 1) * (ρ + 1))))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((2 * ⌈16 * Real.sqrt d⌉₊ + 1) ^ d : ℕ) : ℝ) *
            ((d : ℝ) * (2 * ((16 * Real.sqrt d + 2) * ((3 + 1) * (ρ + 1))))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hcon
      _ = nearConst d * (ρ + 1) := by unfold nearConst; ring
  -- far from `x`
  have hfar : ∑ y ∈ hfinT.toFinset.filter (fun y => ¬ ‖toE (x - y)‖ < 16 * Real.sqrt d),
      ∑ i : Fin d, |greenKilled A x (y + unit i) - greenKilled A x y| ≤
        (d : ℝ) * C₁ * (3 * (ρ + 1) + t⁻¹ * ((ρ + 1) ^ 2 / (2 * d))) := by
    have hFA : ∀ y ∈ hfinT.toFinset.filter (fun y => ¬ ‖toE (x - y)‖ < 16 * Real.sqrt d),
        y ∈ A := fun y hy => hsub (hfinT.mem_toFinset.1 (Finset.mem_filter.1 hy).1)
    have hterm : ∀ y ∈ hfinT.toFinset.filter
        (fun y => ¬ ‖toE (x - y)‖ < 16 * Real.sqrt d),
        ∑ i : Fin d, |greenKilled A x (y + unit i) - greenKilled A x y| ≤
          (d : ℝ) * C₁ * (greenKilled A x y * (if y = x then 0 else ‖toE (y - x)‖⁻¹) +
            t⁻¹ * (greenKilled A x y * 1)) := by
      intro y hy
      obtain ⟨hyS, hyR⟩ := Finset.mem_filter.1 hy
      have hyR' : 16 * Real.sqrt d ≤ ‖toE (x - y)‖ := not_lt.1 hyR
      have hpos : 0 < ‖toE (x - y)‖ := by linarith
      have hyx : y ≠ x := by
        rintro rfl
        rw [sub_self, toE_zero, norm_zero] at hpos
        exact lt_irrefl _ hpos
      have hmpos : 0 < min ‖toE (x - y)‖ t := lt_min hpos ht0
      have hg0 := greenKilled_nonneg A x y
      rw [if_neg hyx, ← norm_toE_sub_comm]
      calc _ ≤ ∑ _i : Fin d, C₁ * (greenKilled A x y * ‖toE (x - y)‖⁻¹ +
            t⁻¹ * (greenKilled A x y * 1)) := Finset.sum_le_sum fun i _ => by
            have h := hgrad y ((hT y).1 hyS) hyR' i
            rw [← le_div_iff₀ hmpos, div_eq_mul_inv] at h
            have hinv := inv_min_le hpos ht0
            calc _ ≤ C₁ * greenKilled A x y * (min ‖toE (x - y)‖ t)⁻¹ := h
              _ ≤ C₁ * greenKilled A x y * (‖toE (x - y)‖⁻¹ + t⁻¹) :=
                mul_le_mul_of_nonneg_left hinv (mul_nonneg hC₁.le hg0)
              _ = _ := by ring
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    have h1 : ∑ y ∈ hfinT.toFinset.filter (fun y => ¬ ‖toE (x - y)‖ < 16 * Real.sqrt d),
        greenKilled A x y * (if y = x then 0 else ‖toE (y - x)‖⁻¹) ≤ 3 * (ρ + 1) :=
      (sum_le_greenPotential hA _ hFA _ (fun y => by split_ifs <;> positivity) x).trans hWx
    have h2 : ∑ y ∈ hfinT.toFinset.filter (fun y => ¬ ‖toE (x - y)‖ < 16 * Real.sqrt d),
        greenKilled A x y * 1 ≤ (ρ + 1) ^ 2 / (2 * d) :=
      (sum_le_greenPotential hA _ hFA (fun _ => 1) (fun _ => zero_le_one) x).trans hExit
    calc _ ≤ ∑ y ∈ hfinT.toFinset.filter (fun y => ¬ ‖toE (x - y)‖ < 16 * Real.sqrt d),
          (d : ℝ) * C₁ * (greenKilled A x y * (if y = x then 0 else ‖toE (y - x)‖⁻¹) +
            t⁻¹ * (greenKilled A x y * 1)) := Finset.sum_le_sum hterm
      _ = (d : ℝ) * C₁ * (∑ y ∈ hfinT.toFinset.filter
            (fun y => ¬ ‖toE (x - y)‖ < 16 * Real.sqrt d),
              greenKilled A x y * (if y = x then 0 else ‖toE (y - x)‖⁻¹) +
            t⁻¹ * ∑ y ∈ hfinT.toFinset.filter
              (fun y => ¬ ‖toE (x - y)‖ < 16 * Real.sqrt d), greenKilled A x y * 1) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 ht0.le)))
          (mul_nonneg hdpos.le hC₁.le)
  exact add_le_add hnear hfar

/-! ### The final arithmetic -/

/-- `a (R n + 1) + c (3 (R n + 1) + (β n)⁻¹ (R n + 1)² / D) ≤
(a (R + 1) + c (3 (R + 1) + (R + 1)² / (D β))) n` for `n ≥ 1`. -/
theorem final_arith {a c R β n D : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hR : 0 ≤ R) (hβ : 0 < β)
    (hn : 1 ≤ n) (hD : 0 < D) :
    a * (R * n + 1) + c * (3 * (R * n + 1) + (β * n)⁻¹ * ((R * n + 1) ^ 2 / D)) ≤
      (a * (R + 1) + c * (3 * (R + 1) + (R + 1) ^ 2 / (D * β))) * n := by
  have hn0 : 0 < n := by linarith
  have h1 : R * n + 1 ≤ (R + 1) * n := by nlinarith
  have hsq : (R * n + 1) ^ 2 ≤ ((R + 1) * n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h2 : (β * n)⁻¹ * ((R * n + 1) ^ 2 / D) ≤ (R + 1) ^ 2 / (D * β) * n := by
    calc (β * n)⁻¹ * ((R * n + 1) ^ 2 / D) ≤ (β * n)⁻¹ * (((R + 1) * n) ^ 2 / D) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right hsq hD.le
      _ = (R + 1) ^ 2 / (D * β) * n := by
          field_simp
  have h3 : a * (R * n + 1) ≤ a * ((R + 1) * n) := mul_le_mul_of_nonneg_left h1 ha
  have h4 : c * (3 * (R * n + 1) + (β * n)⁻¹ * ((R * n + 1) ^ 2 / D)) ≤
      c * (3 * ((R + 1) * n) + (R + 1) ^ 2 / (D * β) * n) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  calc _ ≤ a * ((R + 1) * n) + c * (3 * ((R + 1) * n) + (R + 1) ^ 2 / (D * β) * n) :=
        add_le_add h3 h4
    _ = _ := by ring

end DivisibleHomogenizeDomain

open DivisibleHomogenizeDomain

/-! ### The theorem -/

/-- **The interior difference estimate on `W_n`** (Lemma 8.1): the Lawler-Limic harmonic
difference estimate gives `∑_{y : dist(y, ℤ^d ∖ W_n) > βn} ∑_i |g_n(x, y + e_i) - g_n(x, y)| ≤
C_β n` for all `n ≥ n₀` and `x ∈ ℤ^d`. -/
theorem greenDomainGradientSum_of_lawlerLimic (hLL : LawlerLimicHarmonicDifferenceStmt) :
    GreenDomainGradientSumStmt := by
  intro d hd W hW β hβ
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hs1 : 1 ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd1'
  obtain ⟨C₁, hC₁, hgrad⟩ := exists_gradient_bound hLL hd1
  obtain ⟨R, hR0, hWR⟩ := exists_closedBall_of_isBounded hW
  have hconst : 0 ≤ nearConst d * (R + 1) +
      (d : ℝ) * C₁ * (3 * (R + 1) + (R + 1) ^ 2 / (2 * d * β)) := by
    have := nearConst_nonneg d
    positivity
  refine ⟨nearConst d * (R + 1) +
      (d : ℝ) * C₁ * (3 * (R + 1) + (R + 1) ^ 2 / (2 * d * β)), ⌈16 * Real.sqrt d / β⌉₊ + 1,
    fun n hn x => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hβn : 16 * Real.sqrt d ≤ β * n := by
    have h1 : 16 * Real.sqrt d / β ≤ (⌈16 * Real.sqrt d / β⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈16 * Real.sqrt d / β⌉₊ + 1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ hβ] at h1
    nlinarith
  by_cases hx : x ∈ discretize W n
  · have hfin : (discretize W n).Finite :=
      discretize_finite (Metric.isBounded_closedBall.subset hWR) n
    have hρ : 0 ≤ R * n := mul_nonneg hR0 (Nat.cast_nonneg n)
    have hmain := finsum_gradient_le (by omega) hC₁ hfin hρ
      (fun y hy => norm_le_of_mem_discretize hWR hy) hβn hx
      (greenDomainExitTime d hd1 W R hR0 hWR n x)
      (fun y hy hD i => hgrad _ hfin _ x y hy hD hβn i)
    refine hmain.trans ?_
    have := final_arith (nearConst_nonneg d) (mul_nonneg hdpos.le hC₁.le) hR0 hβ hn1
      (by positivity : (0 : ℝ) < 2 * d)
    exact this
  · have h0 : ∀ y, greenKilled (discretize W n) x y = 0 :=
      fun y => greenKilled_eq_zero_of_not_mem_left _ hx y
    simp only [h0, sub_self, abs_zero, Finset.sum_const_zero, finsum_zero]
    exact mul_nonneg hconst (Nat.cast_nonneg n)

end RandomSandpile

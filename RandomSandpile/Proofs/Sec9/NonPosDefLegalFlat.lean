import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatContact

/-!
# Operator fact (11) from the steps

`nonPosDefLegalFlat_of_steps`: `NonPosDefLegalFlatStmt d` (every `d ≥ 2`) from
`StableQuadApproxStmt` and `BoundaryMinStmt`; `contactBend` and
`locLegal_le_of_bdry` are proved.

Proof (the note's §6 with the bend supplied by Lemma 6.2). If `α = μ̄(0, Q) > 0`, gives a
locally legal `u` on `B_n`, a contact `x₀`, a slope `p₀` and `δ > 0` with `u ≤ P - δ n²` on `∂B_n`,
`P(y) = q_Q(y) + p₀·y + c₀`, `P(x₀) = u(x₀)`. By take `v` stabilizing with
`|v - q_Q - c| ≤ δ n²/8`; with the integer affine `ℓ` (slopes `p₀` rounded) and an integer `K`,
`z = v + ℓ + K` (zero off `B̄_n`) is within `err` of `P - δ n²/2`. with `u ≥ 0` gives
`P ≥ δ n² - C (n + 1)` on `B̄_n`, so `z ≥ 0`: `z` is a toppling function, stabilizing, and above `u`
on `∂B_n`. Least action gives `u(x₀) ≤ z(x₀) ≤ u(x₀) - δ n²/2 + err`, a contradiction.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

theorem abs_coord_le_dClosure {R : ℝ} {y : Site d} (hy : y ∈ dClosure (ballZ0 (d := d) R))
    (j : Fin d) : |(y j : ℝ)| ≤ R + 1 := by
  have hb : ∀ x ∈ ballZ0 (d := d) R, |(x j : ℝ)| ≤ R := fun x hx => by
    rw [MuLipschitz.mem_ballZ0] at hx
    have : ‖toE x j‖ ≤ ‖toE x‖ := PiLp.norm_apply_le (toE x) j
    rw [toE_apply, Real.norm_eq_abs] at this
    linarith
  rw [dClosure_eq] at hy
  rcases hy with hy | hy
  · linarith [hb y hy]
  · obtain ⟨-, x, hx, hadj⟩ := mem_bdry.1 hy
    have h1 := adj_iff_sum_abs.1 hadj
    have h2 : |x j - y j| ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun i => |x i - y i|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h3 : |(x j : ℝ) - y j| ≤ 1 := by exact_mod_cast h2
    have := hb x hx
    have := abs_sub_abs_le_abs_sub (y j : ℝ) (x j)
    rw [abs_sub_comm] at h3
    linarith

theorem locLegal_nonneg {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (hu : u ∈ locLegal η A) (x : Site d) : 0 ≤ u x := by
  obtain ⟨w, uh, hw, huh, rfl, -⟩ := hu
  exact add_nonneg (hw.1 x) (huh.1 x)

/-- The Laplacian of `v + ℓ + K` with `ℓ` an integer linear function equals that of `v`. -/
theorem lap_add_linear (v : Site d → ℤ) (m : Fin d → ℤ) (K : ℤ) (x : Site d) :
    lap (fun y => v y + (∑ i, m i * y i) + K) x = lap v x := by
  rw [lap_eq_sum_second_diff, lap_eq_sum_second_diff]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (∑ j, m j * (x + unit i) j) = (∑ j, m j * x j) + m i := by
    simp [unit, Pi.single_apply, mul_add, Finset.sum_add_distrib]
  have h2 : (∑ j, m j * (x - unit i) j) = (∑ j, m j * x j) - m i := by
    simp [unit, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  simp only [h1, h2]
  ring

theorem lap_indicator_dClosure {A : Set (Site d)} (f : Site d → ℤ) {x : Site d} (hx : x ∈ A) :
    lap ((dClosure A).indicator f) x = lap f x := by
  have hxc : x ∈ dClosure A := mem_dClosure_of_mem hx
  rw [lap_eq_sum_second_diff, lap_eq_sum_second_diff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Set.indicator_of_mem hxc, Set.indicator_of_mem (mem_dClosure_of_adj hx (adj_add_unit x i)),
    Set.indicator_of_mem (mem_dClosure_of_adj hx (adj_sub_unit x i))]

theorem inner_toE_eq_sum (p : Rd d) (y : Site d) :
    inner ℝ p (toE y) = ∑ i, (y i : ℝ) * p i := by
  simp [PiLp.inner_apply]

/-- Rounding the slopes of `p` gives an integer linear function within `(d/2)(R+1)` of `p·` on the
closure of `B_R`. -/
theorem exists_int_linear {R : ℝ} (_hR : 0 ≤ R) (p : Rd d) :
    ∃ m : Fin d → ℤ, ∀ y ∈ dClosure (ballZ0 (d := d) R),
      |((∑ i, m i * y i : ℤ) : ℝ) - inner ℝ p (toE y)| ≤ d / 2 * (R + 1) := by
  refine ⟨fun i => ⌊p i + 1 / 2⌋, fun y hy => ?_⟩
  rw [inner_toE_eq_sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, ((⌊p i + 1 / 2⌋ : ℝ) * y i - y i * p i)|
      ≤ ∑ i, |((⌊p i + 1 / 2⌋ : ℝ) * y i - y i * p i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (1 / 2 * (R + 1)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := Int.floor_le (p i + 1 / 2)
        have h2 := Int.lt_floor_add_one (p i + 1 / 2)
        have h3 : |(⌊p i + 1 / 2⌋ : ℝ) - p i| ≤ 1 / 2 := by
          rw [abs_le]; constructor <;> linarith
        have h4 := abs_coord_le_dClosure hy i
        calc |(⌊p i + 1 / 2⌋ : ℝ) * y i - y i * p i|
            = |(⌊p i + 1 / 2⌋ : ℝ) - p i| * |(y i : ℝ)| := by
              rw [← abs_mul]; congr 1; ring
          _ ≤ 1 / 2 * (R + 1) := by
              apply mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)
    _ = d / 2 * (R + 1) := by simp; ring

/-- **Operator fact (11)** from and. -/
theorem nonPosDefLegalFlat_of_steps (h1 : StableQuadApproxStmt) (h2 : BoundaryMinStmt)
    {d : ℕ} (hd : 2 ≤ d) : NonPosDefLegalFlatStmt d := by
  intro E hE Q hQ hnot hF
  by_contra hne
  have hα : 0 < muBar E 0 Q :=
    lt_of_le_of_ne (EffectiveOperatorBasic.muBar_nonneg E 0 Q) (Ne.symm hne)
  obtain ⟨δ, hδ, hcb⟩ := contactBend d hd E Q hQ hα
  obtain ⟨C, hC0, hS2⟩ := h2 d hd Q hQ hnot
  have h1' := h1 d hd E hE Q hQ hF
  obtain ⟨η, ⟨n₀, hn₀⟩, hη1⟩ := (hcb.and h1').exists
  obtain ⟨R₀, hR₀⟩ := hη1 (δ / 8) (by positivity)
  set Kc : ℝ := d / 2 + C + 1 with hKc
  have hKc0 : 0 < Kc := by rw [hKc]; positivity
  set n : ℕ := max (max n₀ R₀) (max 1 ⌈8 * Kc / δ⌉₊) with hn
  have hnn₀ : n₀ ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have hnR₀ : R₀ ≤ n := (le_max_right _ _).trans (le_max_left _ _)
  have hn1 : 1 ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hnbig : 8 * Kc / δ ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans (le_max_right _ _))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn8 : 8 * Kc ≤ δ * n := by
    have := (div_le_iff₀ hδ).1 hnbig
    linarith
  -- the key size estimate
  have hB : (d / 2 + C) * ((n : ℝ) + 1) + 1 ≤ δ * (n : ℝ) ^ 2 / 4 := by
    have : (d / 2 + C) * ((n : ℝ) + 1) + 1 ≤ Kc * (2 * n) := by
      rw [hKc]; nlinarith [hC0, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  obtain ⟨u, x₀, p₀, hu, hx₀, hbd⟩ := hn₀ n hnn₀
  obtain ⟨v, c, hvstab, hvapp⟩ := hR₀ n hnR₀
  obtain ⟨m, hm⟩ := exists_int_linear (R := (n : ℝ)) (by positivity) p₀
  set c₀ : ℝ := u x₀ - qMZ Q x₀ - inner ℝ p₀ (toE x₀) with hc₀
  set P : Site d → ℝ := fun y => qMZ Q y + inner ℝ p₀ (toE y) + c₀ with hP
  set K : ℤ := ⌊c₀ - c - δ * (n : ℝ) ^ 2 / 2⌋ with hK
  set err : ℝ := δ / 8 * (n : ℝ) ^ 2 + d / 2 * ((n : ℝ) + 1) + 1 with herr
  have hbdP : ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)), (u y : ℝ) ≤ P y - δ * (n : ℝ) ^ 2 := by
    intro y hy
    have := hbd y hy
    simp only [hP, hc₀, inner_sub_right] at this ⊢
    linarith
  set f : Site d → ℤ := fun y => v y + (∑ i, m i * y i) + K with hf
  have hf_approx : ∀ y ∈ dClosure (ballZ0 (d := d) (n : ℝ)),
      |(f y : ℝ) - (P y - δ * (n : ℝ) ^ 2 / 2)| ≤ err := by
    intro y hy
    have a1 := hvapp y hy
    have a2 := hm y hy
    have k1 := Int.floor_le (c₀ - c - δ * (n : ℝ) ^ 2 / 2)
    have k2 := Int.lt_floor_add_one (c₀ - c - δ * (n : ℝ) ^ 2 / 2)
    rw [abs_le] at a1 a2 ⊢
    simp only [hf, hP, Int.cast_add]
    rw [← hK] at k1 k2
    simp only [herr]
    constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2]
  -- P is large on the closure
  have hPlow : ∀ y ∈ dClosure (ballZ0 (d := d) (n : ℝ)),
      δ * (n : ℝ) ^ 2 - C * ((n : ℝ) + 1) ≤ P y := by
    intro y hy
    obtain ⟨b, hb, hbl⟩ := hS2 n p₀ y hy
    have hub : (0 : ℝ) ≤ u b := by exact_mod_cast locLegal_nonneg hu b
    have := hbdP b hb
    simp only [hP] at this ⊢
    linarith
  have hfnn : ∀ y ∈ dClosure (ballZ0 (d := d) (n : ℝ)), 0 ≤ f y := by
    intro y hy
    have a := hf_approx y hy
    have b := hPlow y hy
    rw [abs_le] at a
    have : (0 : ℝ) ≤ f y := by
      simp only [herr] at a
      nlinarith [a.1, hB, mul_nonneg hδ.le (sq_nonneg (n : ℝ))]
    exact_mod_cast this
  set z : Site d → ℤ := (dClosure (ballZ0 (d := d) (n : ℝ))).indicator f with hz
  have hztop : IsTopplingFn (ballZ0 (d := d) (n : ℝ)) z := by
    refine ⟨fun x => ?_, fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ dClosure (ballZ0 (d := d) (n : ℝ))
    · rw [hz, Set.indicator_of_mem hx]; exact hfnn x hx
    · rw [hz, Set.indicator_of_notMem hx]
  have hzstab : z ∈ stabilizing η (ballZ0 (d := d) (n : ℝ)) := by
    refine ⟨hztop, fun x hx => ?_⟩
    rw [hz, lap_indicator_dClosure f hx, hf, lap_add_linear]
    exact hvstab x hx
  have hzf : ∀ y ∈ dClosure (ballZ0 (d := d) (n : ℝ)), z y = f y := fun y hy => by
    rw [hz, Set.indicator_of_mem hy]
  have hle : u ≤ z := locLegal_le_of_bdry hu hzstab fun y hy => by
    rw [hzf y (bdry_subset_dClosure _ hy)]
    have a := hf_approx y (bdry_subset_dClosure _ hy)
    have b := hbdP y hy
    rw [abs_le] at a
    have : (u y : ℝ) ≤ f y := by
      simp only [herr] at a
      nlinarith [a.1, hB, mul_nonneg hδ.le (sq_nonneg (n : ℝ))]
    exact_mod_cast this
  have hx₀c : x₀ ∈ dClosure (ballZ0 (d := d) (n : ℝ)) := mem_dClosure_of_mem hx₀
  have h3 : (u x₀ : ℝ) ≤ f x₀ := by
    have := hle x₀
    rw [hzf x₀ hx₀c] at this
    exact_mod_cast this
  have a := hf_approx x₀ hx₀c
  rw [abs_le] at a
  have hPx : P x₀ = u x₀ := by simp only [hP, hc₀]; ring
  simp only [herr] at a
  nlinarith [a.2, hPx, hB, mul_pos hδ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]

end SingleSourceH0

end RandomSandpile

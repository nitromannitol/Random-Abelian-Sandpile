import RandomSandpile.Steps.Sec7.DivisibleHomogenize
import RandomSandpile.Inputs.Proposed
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeSymm
import RandomSandpile.Proofs.Sec7.DivisibleHomogenizeCore
import LatticeProb.Walk.Harnack.SmallR

/-!
# The gradient bound for the killed Green's function (Lemma 7.3)

Proof of `GreenBallHarnackGradientStmt` from the Lawler-Limic harmonic difference estimate
(`LawlerLimicHarmonicDifferenceStmt`) and the Harnack inequality of Lattice-Probability
(`LatticeProb.harnack`).

Fix `δ ∈ (0, 1)` and `x, y ∈ B_{(1-δ)n}` with `|x - y| ≥ R₀ := 32 √d / δ`. Put
`m = min (|x - y|, δ n)`, `R = ⌊m / (4 √d)⌋₊` and `u(w) = g_n(x, y + w)`. Every `w` in the box
`[-2R, 2R]^d` has `|w| ≤ m / 2`, so `y + w ∈ B_n` and `y + w ≠ x`; hence `u ≥ 0` there and
`Δ u = 0` on `[-(2R-1), 2R-1]^d` (the Poisson equation in the second variable,
`lapR_greenKilled_right`). The Harnack inequality gives `u ≤ C_H u(0)` on the box `[-R, R]^d`, and
the Lawler-Limic estimate applied to `u - u(0)` on the ball `B_{R-1}` (whose closure lies in
`[-R, R]^d`) gives `|u(e_i) - u(0)| ≤ C_L C_H u(0) / (R - 1)`. Finally `R - 1 ≥ δ |x - y| / (16 √d)`
since `|x - y| < 2n`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

variable {d : ℕ}

namespace DivisibleHomogenize

open OdometerLowerBound

/-! ### Elementary lattice facts -/

/-- The Laplacian of a translate. -/
theorem lapR_translate (F : Site d → ℝ) (y w : Site d) :
    lapR (fun v => F (y + v)) w = lapR F (y + w) := by
  simp only [lapR, nbrSum, add_assoc, add_sub_assoc]

/-- The Laplacian ignores additive constants. -/
theorem lapR_sub_const (u : Site d → ℝ) (c : ℝ) (z : Site d) :
    lapR (fun v => u v - c) z = lapR u z := by
  have h : ∀ i : Fin d, (u (z + unit i) - c) + (u (z - unit i) - c) =
      (u (z + unit i) + u (z - unit i)) - 2 * c := fun i => by ring
  simp only [lapR, nbrSum, h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A lattice point of norm `< R` lies in the box `[-R, R]^d`. -/
theorem mem_box_of_norm_lt {z : Site d} {R : ℕ} (h : ‖toE z‖ < R) : z ∈ box d R := by
  intro i
  have h1 := abs_coord_le_norm z i
  have h2 : ((|z i| : ℤ) : ℝ) ≤ (R : ℝ) := by rw [Int.cast_abs]; linarith
  exact_mod_cast h2

/-- Coordinates of a point of `[-R, R]^d` are at most `R`. -/
theorem abs_coord_le_of_mem_box {z : Site d} {R : ℕ} (h : z ∈ box d R) (i : Fin d) :
    |(z i : ℝ)| ≤ R := by
  have h2 : ((|z i| : ℤ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast h i
  rwa [Int.cast_abs] at h2

/-- A point of the box `[-R, R]^d` has norm at most `√d R`. -/
theorem norm_le_of_mem_box {z : Site d} {R : ℕ} (h : z ∈ box d R) :
    ‖toE z‖ ≤ Real.sqrt d * R :=
  norm_toE_le_sqrt_mul z (Nat.cast_nonneg R) (abs_coord_le_of_mem_box h)

/-- The Harnack constant of Lattice-Probability, enlarged to be at least `1`. -/
theorem harnack_one_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (R : ℕ) (u : Site d → ℝ), 1 ≤ R →
      (∀ x ∈ box d (2 * R), 0 ≤ u x) →
      (∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) →
      ∀ x ∈ box d R, ∀ y ∈ box d R, u x ≤ C * u y := by
  obtain ⟨C, hC, h⟩ := LatticeProb.harnack d hd
  refine ⟨max C 1, le_max_right _ _, fun R u hR hpos hharm x hx y hy => ?_⟩
  have hy0 : 0 ≤ u y := hpos y (mem_box_of_le (by omega) hy)
  calc u x ≤ C * u y := h R u hR hpos hharm x hx y hy
    _ ≤ max C 1 * u y := mul_le_mul_of_nonneg_right (le_max_left _ _) hy0

/-! ### The gradient bound in the box -/

/-- **Harnack plus Lawler-Limic**: if `u ≥ 0` on `[-2R, 2R]^d` and `Δ u = 0` on
`[-(2R-1), 2R-1]^d`, then `|u(e_i) - u(0)| ≤ C_L C_H u(0) / (R - 1)`. -/
theorem gradient_le_of_box {C_L C_H : ℝ} (hCH : 1 ≤ C_H)
    (hLLd : ∀ (n : ℕ), 1 ≤ n → ∀ (f : Site d → ℝ) (M : ℝ),
      (∀ z ∈ ballZ0 (n : ℝ), lapR f z = 0) → (∀ z ∈ dClosure (ballZ0 (n : ℝ)), |f z| ≤ M) →
        ∀ i : Fin d, |f (unit i) - f 0| ≤ C_L * M / n)
    (hHar : ∀ (R : ℕ) (u : Site d → ℝ), 1 ≤ R →
      (∀ x ∈ box d (2 * R), 0 ≤ u x) →
      (∀ x ∈ box d (2 * R - 1), nbrSum u x = 2 * (d : ℝ) * u x) →
      ∀ x ∈ box d R, ∀ y ∈ box d R, u x ≤ C_H * u y)
    (u : Site d → ℝ) (R : ℕ) (hR : 2 ≤ R)
    (hpos : ∀ w ∈ box d (2 * R), 0 ≤ u w)
    (hharm : ∀ w ∈ box d (2 * R - 1), lapR u w = 0) (i : Fin d) :
    |u (unit i) - u 0| ≤ C_L * (C_H * u 0) / ((R - 1 : ℕ) : ℝ) := by
  have hR1 : (((R - 1 : ℕ) : ℝ)) = (R : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h0box : ∀ r : ℕ, (0 : Site d) ∈ box d r := fun r j => by simp
  have hu0 : 0 ≤ u 0 := hpos 0 (h0box _)
  have hnbr : ∀ w ∈ box d (2 * R - 1), nbrSum u w = 2 * (d : ℝ) * u w := by
    intro w hw
    have h := hharm w hw
    unfold lapR at h
    linarith
  have hlt : ∀ z ∈ dClosure (ballZ0 (((R - 1 : ℕ)) : ℝ)), z ∈ box d R := by
    intro z hz
    rw [dClosure_eq] at hz
    apply mem_box_of_norm_lt
    rcases hz with hz | hz
    · have := mem_ballZ0.1 hz
      linarith
    · have := norm_lt_of_mem_bdry_ballZ0 hz
      linarith
  have hbound : ∀ z ∈ dClosure (ballZ0 (((R - 1 : ℕ)) : ℝ)), |u z - u 0| ≤ C_H * u 0 := by
    intro z hz
    have hzbox := hlt z hz
    have hz1 : u z ≤ C_H * u 0 :=
      hHar R u (by omega) hpos hnbr z hzbox 0 (h0box _)
    have hz0 : 0 ≤ u z := hpos z (mem_box_of_le (by omega) hzbox)
    have hCu : 0 ≤ (C_H - 1) * u 0 := mul_nonneg (by linarith) hu0
    rw [abs_le]
    constructor <;> nlinarith
  have key := hLLd (R - 1) (by omega) (fun w => u w - u 0) (C_H * u 0) ?_ hbound i
  · simpa using key
  · intro z hz
    rw [lapR_sub_const]
    apply hharm
    have hzn := mem_ballZ0.1 hz
    have hzbox : z ∈ box d (R - 1) := mem_box_of_norm_lt hzn
    exact mem_box_of_le (by omega) hzbox

/-! ### Real-number arithmetic -/

/-- The radius `R = ⌊min (D, δ n) / (4 s)⌋₊` satisfies `δ D / (16 s) ≤ R - 1` and
`2 ≤ δ D / (16 s)`, once `D ≥ 32 s / δ` and `D ≤ 2 n`. -/
theorem radius_lower {s δ D n : ℝ} (hs : 0 < s) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : 32 * s / δ ≤ D) (hDn : D ≤ 2 * n) :
    2 ≤ δ * D / (16 * s) ∧
      δ * D / (16 * s) ≤ (⌊min D (δ * n) / (4 * s)⌋₊ : ℝ) - 1 := by
  have h32 : 32 * s ≤ δ * D := by
    rw [div_le_iff₀ hδ0] at hD
    linarith
  have hD0 : 0 ≤ D := by
    have : 0 < 32 * s / δ := by positivity
    linarith
  have ht : 2 ≤ δ * D / (16 * s) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine ⟨ht, ?_⟩
  have hm : δ * D / 2 ≤ min D (δ * n) := by
    apply le_min
    · nlinarith
    · nlinarith
  have hm' : (δ * D / 2) / (4 * s) ≤ min D (δ * n) / (4 * s) :=
    div_le_div_of_nonneg_right hm (by positivity)
  have heq : (δ * D / 2) / (4 * s) = 2 * (δ * D / (16 * s)) := by
    field_simp
    ring
  have hfl := Nat.lt_floor_add_one (min D (δ * n) / (4 * s))
  linarith

/-- The final division: `A ≤ K / ρ`, `ρ ≥ δ D / (16 s) > 0` give `A D ≤ K (16 s / δ)`. -/
theorem mul_le_of_le_div {s δ D ρ A K : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hD : 0 < D)
    (hρ : δ * D / (16 * s) ≤ ρ) (hK : 0 ≤ K) (hA : A ≤ K / ρ) :
    A * D ≤ K * (16 * s / δ) := by
  have ht : 0 < δ * D / (16 * s) := by positivity
  have h1 : K / ρ ≤ K / (δ * D / (16 * s)) := div_le_div_of_nonneg_left hK ht hρ
  have h2 : K / (δ * D / (16 * s)) * D = K * (16 * s / δ) := by
    field_simp
  calc A * D ≤ K / (δ * D / (16 * s)) * D :=
        mul_le_mul_of_nonneg_right (hA.trans h1) hD.le
    _ = K * (16 * s / δ) := h2

end DivisibleHomogenize

/-! ### The theorem -/

open DivisibleHomogenize OdometerLowerBound in
/-- **The gradient bound for the killed Green's function**: the Lawler-Limic
harmonic difference estimate and the Harnack inequality give
`|∇_i g_n(x, y)| |x - y| ≤ C_δ g_n(x, y)` for `x, y ∈ B_{(1-δ)n}` with `|x - y| ≥ R₀`. -/
theorem greenBallHarnackGradient_of_lawlerLimic (hLL : LawlerLimicHarmonicDifferenceStmt) :
    GreenBallHarnackGradientStmt := by
  intro d hd2 δ hδ0 hδ1
  have hd : 1 ≤ d := by omega
  obtain ⟨C_L, hCL, hLLd⟩ := hLL d hd
  obtain ⟨C_H, hCH1, hHar⟩ := harnack_one_le hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd1
  have hs0 : 0 < Real.sqrt d := by linarith
  refine ⟨C_L * C_H * 16 * Real.sqrt d / δ, 32 * Real.sqrt d / δ, by positivity, ?_⟩
  intro n x y hx hy hD i
  set s : ℝ := Real.sqrt d with hs
  set D : ℝ := ‖toE (x - y)‖ with hDdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hxn := mem_ballZ0.1 hx
  have hyn := mem_ballZ0.1 hy
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hDn : D ≤ 2 * n := by
    have h1 : D ≤ ‖toE x‖ + ‖toE y‖ := by
      rw [hDdef, toE_sub]
      exact norm_sub_le _ _
    nlinarith
  obtain ⟨-, hrad⟩ := radius_lower hs0 hδ0 hδ1.le hD hDn
  obtain ⟨ht2, -⟩ := radius_lower hs0 hδ0 hδ1.le hD hDn
  set R : ℕ := ⌊min D (δ * n) / (4 * s)⌋₊ with hRdef
  have hRge : (3 : ℝ) ≤ R := by linarith
  have hR2 : 2 ≤ R := by
    have : (2 : ℝ) ≤ R := by linarith
    exact_mod_cast this
  have hmpos : 0 ≤ min D (δ * n) / (4 * s) := by
    apply div_nonneg _ (by positivity)
    exact le_min hDpos.le (by positivity)
  have hRle : (R : ℝ) ≤ min D (δ * n) / (4 * s) := Nat.floor_le hmpos
  have hRm : 4 * s * R ≤ min D (δ * n) := by
    rw [le_div_iff₀ (by positivity)] at hRle
    linarith
  have hmD : min D (δ * n) ≤ D := min_le_left _ _
  have hmδ : min D (δ * n) ≤ δ * n := min_le_right _ _
  -- every point of the box `[-2R, 2R]^d` has norm at most `m / 2`
  have hwnorm : ∀ w ∈ box d (2 * R), ‖toE w‖ ≤ min D (δ * n) / 2 := by
    intro w hw
    have h1 := norm_le_of_mem_box hw
    push_cast at h1
    nlinarith
  have hbox_mem : ∀ w ∈ box d (2 * R), y + w ∈ ballZ0 (n : ℝ) := by
    intro w hw
    rw [mem_ballZ0, toE_add]
    have h1 := hwnorm w hw
    have h2 : ‖toE y + toE w‖ ≤ ‖toE y‖ + ‖toE w‖ := norm_add_le _ _
    nlinarith
  have hbox_ne : ∀ w ∈ box d (2 * R), y + w ≠ x := by
    intro w hw hwx
    have hw' : w = x - y := by rw [← hwx]; abel
    have h1 := hwnorm w hw
    rw [hw'] at h1
    linarith
  have hpos : ∀ w ∈ box d (2 * R), 0 ≤ (fun w => greenKilled (ballZ0 (n : ℝ)) x (y + w)) w :=
    fun w _ => greenKilled_nonneg _ _ _
  have hharm : ∀ w ∈ box d (2 * R - 1),
      lapR (fun w => greenKilled (ballZ0 (n : ℝ)) x (y + w)) w = 0 := by
    intro w hw
    have hw2 : w ∈ box d (2 * R) := mem_box_of_le (by omega) hw
    rw [lapR_translate (fun z => greenKilled (ballZ0 (n : ℝ)) x z) y w]
    rw [lapR_greenKilled_right hd (ballZ0_finite _) x (hbox_mem w hw2)]
    simp [hbox_ne w hw2]
  have hgrad := gradient_le_of_box hCH1 hLLd hHar
    (fun w => greenKilled (ballZ0 (n : ℝ)) x (y + w)) R hR2 hpos hharm i
  simp only [add_zero] at hgrad
  have hR1 : (((R - 1 : ℕ) : ℝ)) = (R : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hg0 := greenKilled_nonneg (ballZ0 (n : ℝ)) x y
  have hfin := mul_le_of_le_div hs0 hδ0 hDpos (ρ := (((R - 1 : ℕ) : ℝ))) (by rw [hR1]; exact hrad)
    (K := C_L * (C_H * greenKilled (ballZ0 (n : ℝ)) x y)) (by positivity) hgrad
  calc _ ≤ _ := hfin
    _ = _ := by ring

end RandomSandpile

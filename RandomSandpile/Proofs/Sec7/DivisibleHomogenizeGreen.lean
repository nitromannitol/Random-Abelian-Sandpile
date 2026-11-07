import RandomSandpile.Steps.Sec7.DivisibleHomogenize
import RandomSandpile.Proofs.Sec7.OdometerLowerBound

/-!
# Proofs of the Green potential bounds `GreenBallExitTimeStmt` and `GreenBallBoundaryLayerStmt`

Two of the steps of Lemma 7.3 (`paper/random_piles-corrected.tex`, 1146-1148), both by
comparison with a quadratic through the discrete minimum principle
(`superharmonicMinPrinciple`, `Proofs/Sec7/OdometerLowerBound.lean`).

* `greenPotential_le_of_lapR_le`: if `Δ w ≤ -f` in the finite set `A` and `w ≥ 0` on `∂A`, then the
  Green potential `u` of `f` in `A` is at most `w` in `A`. The difference `w - u` is superharmonic
  in `A` (`lapR_greenPotential`) and is `w ≥ 0` on `∂A`, where `u = 0`
  (`greenPotential_eq_zero_of_not_mem`).
* `greenBallExitTime`: `w = ((n + 1)² - |y|²) / (2d)`, whose Laplacian is `-1`
  (`OdometerLowerBound.lapR_qlZ`), and `w ≥ 0` on `∂B_n` since `|y| < n + 1`.
* `greenBallBoundaryLayer`: `w = min(((n + 1)² - |y|²) / (2d), ((n + 1)² - ρ²) / (2d))`. Where
  `|z| ≥ ρ` the minimum is attained by the quadratic, and where `|z| < ρ` by the constant; in both
  cases `Δ w(z) ≤ -1_{|z| ≥ ρ}` by `lapR_le_of_le_of_eq`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

open OdometerLowerBound

variable {d : ℕ}

namespace DivisibleHomogenize

/-- The discrete Laplacian of a constant vanishes. -/
theorem lapR_const' (c : ℝ) (z : Site d) : lapR (fun _ => c) z = 0 := by
  simp only [lapR, nbrSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Adding a constant does not change the discrete Laplacian. -/
theorem lapR_const_add' (c : ℝ) (g : Site d → ℝ) (z : Site d) :
    lapR (fun y => c + g y) z = lapR g z := by
  simp only [lapR, nbrSum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Monotonicity of `Δ` at a point of contact: if `w ≤ v` and `w z = v z`, then
`Δ w(z) ≤ Δ v(z)`. -/
theorem lapR_le_of_le_of_eq {w v : Site d → ℝ} (hwv : ∀ y, w y ≤ v y) {z : Site d}
    (hz : w z = v z) : lapR w z ≤ lapR v z := by
  have h : nbrSum w z ≤ nbrSum v z :=
    Finset.sum_le_sum fun i _ => add_le_add (hwv _) (hwv _)
  simp only [lapR, hz]
  linarith

/-- **Comparison for Green potentials**: if `Δ w ≤ -f` in the finite set `A` and `w ≥ 0` on
`∂A`, then `∑_{y ∈ A} g_A(x, y) f(y) ≤ w(x)` for `x ∈ A`. -/
theorem greenPotential_le_of_lapR_le (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite)
    (f w : Site d → ℝ) (hw : ∀ z ∈ A, lapR w z ≤ -f z) (hb : ∀ y ∈ bdry A, 0 ≤ w y) :
    ∀ x ∈ A, greenPotential A f x ≤ w x := by
  intro x hx
  set g : Site d → ℝ := fun y => w y - greenPotential A f y with hg_def
  have hsuper : ∀ z ∈ A, lapR g z ≤ 0 := by
    intro z hz
    rw [hg_def, lapR_sub', lapR_greenPotential hd hA _ hz]
    linarith [hw z hz]
  obtain ⟨y, hy, hgy⟩ := superharmonicMinPrinciple d hd A hA g hsuper x hx
  have hyA : y ∉ A := (mem_bdry.1 hy).1
  have hr : greenPotential A f y = 0 := greenPotential_eq_zero_of_not_mem _ _ hyA
  have hgy' : g y = w y := by simp only [hg_def, hr, sub_zero]
  have hgx : g x = w x - greenPotential A f x := rfl
  linarith [hb y hy]

/-- The quadratic `((n + 1)² - |y|²) / (2d)` has Laplacian `-1`. -/
theorem lapR_quadBall (hd : 1 ≤ d) (n : ℕ) (z : Site d) :
    lapR (fun y : Site d => (((n : ℝ) + 1) ^ 2 - ‖toE y‖ ^ 2) / (2 * d)) z = -1 := by
  have hfun : (fun y : Site d => (((n : ℝ) + 1) ^ 2 - ‖toE y‖ ^ 2) / (2 * d)) =
      fun y => ((n : ℝ) + 1) ^ 2 / (2 * d) + qlZ (-1) y := funext fun y => by
    rw [qlZ_eq]; ring
  rw [hfun, lapR_const_add', lapR_qlZ hd]

/-- The quadratic `((n + 1)² - |y|²) / (2d)` is nonnegative on `∂B_n`. -/
theorem quadBall_nonneg_of_mem_bdry {n : ℕ} {y : Site d} (hy : y ∈ bdry (ballZ0 (n : ℝ))) :
    0 ≤ (((n : ℝ) + 1) ^ 2 - ‖toE y‖ ^ 2) / (2 * d) := by
  have hyn : ‖toE y‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_lt_of_mem_bdry_ballZ0 hy).le 2
  exact div_nonneg (by linarith) (by positivity)

end DivisibleHomogenize

open DivisibleHomogenize

/-- **(exit_time)**, first line (1147). -/
theorem greenBallExitTime : GreenBallExitTimeStmt := by
  intro d hd n x hx
  refine greenPotential_le_of_lapR_le hd (ballZ0_finite _) (fun _ => 1)
    (fun y => (((n : ℝ) + 1) ^ 2 - ‖toE y‖ ^ 2) / (2 * d)) (fun z _ => ?_)
    (fun y hy => quadBall_nonneg_of_mem_bdry hy) x hx
  rw [lapR_quadBall hd]

/-- **Boundary layer**. -/
theorem greenBallBoundaryLayer : GreenBallBoundaryLayerStmt := by
  intro d hd n ρ hρ0 hρn x
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set B := ballZ0 (d := d) (n : ℝ)
  set q : Site d → ℝ := fun y => (((n : ℝ) + 1) ^ 2 - ‖toE y‖ ^ 2) / (2 * d) with hq_def
  set c : ℝ := (((n : ℝ) + 1) ^ 2 - ρ ^ 2) / (2 * d) with hc_def
  have hc0 : 0 ≤ c := by
    have : ρ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ hρ0 (by linarith) 2
    exact div_nonneg (by linarith) (by positivity)
  by_cases hxB : x ∈ B
  · set w : Site d → ℝ := fun y => min (q y) c with hw_def
    have key : greenPotential B (fun y => if ρ ≤ ‖toE y‖ then 1 else 0) x ≤ w x := by
      refine greenPotential_le_of_lapR_le hd (ballZ0_finite _)
        (fun y => if ρ ≤ ‖toE y‖ then 1 else 0) w (fun z _ => ?_) (fun y hy => ?_) x hxB
      · by_cases hz : ρ ≤ ‖toE z‖
        · have hqc : q z ≤ c := by
            have : ρ ^ 2 ≤ ‖toE z‖ ^ 2 := pow_le_pow_left₀ hρ0 hz 2
            exact div_le_div_of_nonneg_right (by linarith) (by positivity)
          have h := lapR_le_of_le_of_eq (w := w) (v := q) (fun y => min_le_left _ _) (z := z)
            (min_eq_left hqc)
          rw [hq_def, lapR_quadBall hd] at h
          simpa only [hz, if_true] using h
        · have hqc : c ≤ q z := by
            have : ‖toE z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (not_le.1 hz).le 2
            exact div_le_div_of_nonneg_right (by linarith) (by positivity)
          have h := lapR_le_of_le_of_eq (w := w) (v := fun _ => c) (fun y => min_le_right _ _)
            (z := z) (min_eq_right hqc)
          rw [lapR_const'] at h
          simpa only [hz, if_false, neg_zero] using h
      · exact le_min (quadBall_nonneg_of_mem_bdry hy) hc0
    exact key.trans (min_le_right _ _)
  · rw [greenPotential_eq_zero_of_not_mem _ _ hxB]
    exact hc0

end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceD2Equicont
import RandomSandpile.Inputs.CrandallIshiiLions

/-!
# Theorem 9.2 in dimension two: jets and test functions

Adapters between the second-order jets of Crandall-Ishii-Lions (Def. 2.2, `superJet2`, `subJet2`
in `Inputs/CrandallIshiiLions.lean`) and the repository's `C²`-test predicates:
* a `C²` function touching `u` from below (above) at `x` gives `(Dφ(x), D²φ(x))` in the subjet
  (superjet) of `u` at `x` (`mem_subJet2_of_isLocalMin`, `mem_superJet2_of_isLocalMax`);
* jets shift under adding `a + c|y|²` (`mem_subJet2_add_quad`, `mem_superJet2_add_quad`);
* for an operator with the shift identity `G(M + tI) = G(M) - 2t`, a test-function supersolution
  (subsolution) satisfies the inequality on all of its subjet (superjet): the quadratic with matrix
  `X ∓ ηI` touches strictly, and `η → 0` (`nonneg_of_mem_subJet2`, `nonpos_of_mem_superJet2`).
-/

noncomputable section

open Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

open CrandallIshiiLions

/-- A `C²` test function touching from above gives, for every `κ > 0`, a quadratic touching from
above with matrix `D²φ(x) + κI`. -/
theorem touch_above_of_isLocalMax {v φ : Rd 2 → ℝ} {x : Rd 2} (hφ : ContDiffAt ℝ 2 φ x)
    (hmax : IsLocalMax (fun y => v y - φ y) x) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ y in 𝓝 x, v y ≤ v x + inner ℝ ((InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x))
      (y - x) + qM (hessian φ x + κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - x) := by
  obtain ⟨ρ, hρ, hT⟩ := ContDiffAt.taylor_two hφ (κ := κ / 2) (half_pos hκ)
  filter_upwards [hmax, Metric.ball_mem_nhds x hρ] with y hy hyb
  have h1 := abs_le.1 (hT y (by rwa [Metric.mem_ball, dist_eq_norm] at hyb))
  rw [InnerProductSpace.toDual_symm_apply, qM_add_smul_one]
  have hy' : v y - φ y ≤ v x - φ x := hy
  linarith [h1.2]

/-- A `C²` function touching `u` from below at `x` gives a subjet of `u` at `x`. -/
theorem mem_subJet2_of_isLocalMin (O : Set (Rd 2)) {u φ : Rd 2 → ℝ} {x : Rd 2}
    (hφ : ContDiffAt ℝ 2 φ x) (hmin : IsLocalMin (fun y => u y - φ y) x) :
    ((InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x), hessian φ x) ∈ subJet2 O u x := by
  simp only [subJet2, Set.mem_setOf_eq]
  refine ⟨hessian_isSymm_of_contDiffAt hφ, fun ε hε => ?_⟩
  have h := touch_below_of_isLocalMin hφ hmin (κ := 2 * ε) (by linarith)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with y hy
  rw [qM_sub_mat, qM_smul_one] at hy
  linarith

/-- A `C²` function touching `u` from above at `x` gives a superjet of `u` at `x`. -/
theorem mem_superJet2_of_isLocalMax (O : Set (Rd 2)) {u φ : Rd 2 → ℝ} {x : Rd 2}
    (hφ : ContDiffAt ℝ 2 φ x) (hmax : IsLocalMax (fun y => u y - φ y) x) :
    ((InnerProductSpace.toDual ℝ (Rd 2)).symm (fderiv ℝ φ x), hessian φ x) ∈ superJet2 O u x := by
  simp only [superJet2, Set.mem_setOf_eq]
  refine ⟨hessian_isSymm_of_contDiffAt hφ, fun ε hε => ?_⟩
  have h := touch_above_of_isLocalMax hφ hmax (κ := 2 * ε) (by linarith)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with y hy
  rw [qM_add_smul_one] at hy
  linarith

/-- `|y|² = |x|² + 2⟨x, y - x⟩ + |y - x|²`. -/
theorem norm_sq_expand (x y : Rd 2) :
    ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
  have h := norm_add_sq_real x (y - x)
  have e : x + (y - x) = y := by abel
  rw [e] at h
  exact h

/-- Subjets shift under adding `a + c|y|²`. -/
theorem mem_subJet2_add_quad {O : Set (Rd 2)} {u v : Rd 2 → ℝ} {a c : ℝ}
    (hv : ∀ y, v y = u y + (a + c * ‖y‖ ^ 2)) {x p : Rd 2} {X : Matrix (Fin 2) (Fin 2) ℝ}
    (h : (p, X) ∈ subJet2 O u x) :
    (p + (2 * c) • x, X + (2 * c) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∈ subJet2 O v x := by
  simp only [subJet2, Set.mem_setOf_eq] at h ⊢
  refine ⟨h.1.add (Matrix.isSymm_one.smul _), fun ε hε => ?_⟩
  filter_upwards [h.2 ε hε] with y hy
  rw [hv, hv, inner_add_left, real_inner_smul_left, qM_add_smul_one]
  have e : c * ‖y‖ ^ 2 = c * ‖x‖ ^ 2 + 2 * c * inner ℝ x (y - x) + c * ‖y - x‖ ^ 2 := by
    rw [norm_sq_expand x y]
    ring
  linarith

/-- Superjets shift under adding `a + c|y|²`. -/
theorem mem_superJet2_add_quad {O : Set (Rd 2)} {u v : Rd 2 → ℝ} {a c : ℝ}
    (hv : ∀ y, v y = u y + (a + c * ‖y‖ ^ 2)) {x p : Rd 2} {X : Matrix (Fin 2) (Fin 2) ℝ}
    (h : (p, X) ∈ superJet2 O u x) :
    (p + (2 * c) • x, X + (2 * c) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∈ superJet2 O v x := by
  simp only [superJet2, Set.mem_setOf_eq] at h ⊢
  refine ⟨h.1.add (Matrix.isSymm_one.smul _), fun ε hε => ?_⟩
  filter_upwards [h.2 ε hε] with y hy
  rw [hv, hv, inner_add_left, real_inner_smul_left, qM_add_smul_one]
  have e : c * ‖y‖ ^ 2 = c * ‖x‖ ^ 2 + 2 * c * inner ℝ x (y - x) + c * ‖y - x‖ ^ 2 := by
    rw [norm_sq_expand x y]
    ring
  linarith

/-- A viscosity inequality `G(D²w) ≤ 0` tested from above, at a quadratic touching from above. -/
theorem ViscFromAboveLE.le_of_touch' {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {O : Set (Rd 2)}
    {w : Rd 2 → ℝ} (hw : ViscFromAboveLE G O w) {b q : Rd 2} {Y : Matrix (Fin 2) (Fin 2) ℝ}
    (hY : Y.IsSymm) (hb : b ∈ O)
    (ht : ∀ᶠ y in 𝓝 b, w y ≤ w b + inner ℝ q (y - b) + qM Y (y - b)) : G Y ≤ 0 := by
  have hmax : IsLocalMax (fun y => w y - (w b + innerSL ℝ q (y - b) + qM Y (y - b))) b := by
    filter_upwards [ht] with y hy
    simp only [innerSL_apply_apply, sub_self, inner_zero_right, qM_zero_right, add_zero]
    linarith
  have h := hw b hb _ ((contDiff_paraboloid (w b) q b Y (n := 2)).contDiffAt) hmax
  rwa [hessian_quadratic _ _ _ hY] at h

/-- **Test-function supersolutions are jet supersolutions**. -/
theorem nonneg_of_mem_subJet2 {O : Set (Rd 2)} (hO : IsOpen O)
    {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hG : HasTraceShift G) {u : Rd 2 → ℝ}
    (hu : ViscFromBelowGE G O u) {x : Rd 2} (hx : x ∈ O) {p : Rd 2}
    {X : Matrix (Fin 2) (Fin 2) ℝ} (h : (p, X) ∈ subJet2 O u x) : 0 ≤ G X := by
  simp only [subJet2, Set.mem_setOf_eq] at h
  have key : ∀ η : ℝ, 0 < η → 0 ≤ G X + 2 * η := by
    intro η hη
    have hY : (X + (-η) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm :=
      h.1.add (Matrix.isSymm_one.smul _)
    have ht : ∀ᶠ y in 𝓝 x, u x + inner ℝ p (y - x) +
        qM (X + (-η) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - x) ≤ u y := by
      have h2 := h.2 (η / 2) (half_pos hη)
      rw [nhdsWithin_eq_nhds.2 (hO.mem_nhds hx)] at h2
      filter_upwards [h2] with y hy
      rw [qM_add_smul_one]
      linarith
    have h3 := hu.le_of_touch hY hx ht
    rw [hG X h.1 (-η)] at h3
    linarith
  by_contra hneg
  have hlt := not_le.1 hneg
  have := key (-(G X) / 4) (by linarith)
  linarith

/-- **Test-function subsolutions are jet subsolutions**. -/
theorem nonpos_of_mem_superJet2 {O : Set (Rd 2)} (hO : IsOpen O)
    {G : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hG : HasTraceShift G) {u : Rd 2 → ℝ}
    (hu : ViscFromAboveLE G O u) {x : Rd 2} (hx : x ∈ O) {p : Rd 2}
    {X : Matrix (Fin 2) (Fin 2) ℝ} (h : (p, X) ∈ superJet2 O u x) : G X ≤ 0 := by
  simp only [superJet2, Set.mem_setOf_eq] at h
  have key : ∀ η : ℝ, 0 < η → G X - 2 * η ≤ 0 := by
    intro η hη
    have hY : (X + η • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm :=
      h.1.add (Matrix.isSymm_one.smul _)
    have ht : ∀ᶠ y in 𝓝 x, u y ≤ u x + inner ℝ p (y - x) +
        qM (X + η • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - x) := by
      have h2 := h.2 (η / 2) (half_pos hη)
      rw [nhdsWithin_eq_nhds.2 (hO.mem_nhds hx)] at h2
      filter_upwards [h2] with y hy
      rw [qM_add_smul_one]
      linarith
    have h3 := ViscFromAboveLE.le_of_touch' hu hY hx ht
    rw [hG X h.1 η] at h3
    exact h3
  by_contra hneg
  have hlt := not_le.1 hneg
  have := key (G X / 4) (by linarith)
  linarith

end SingleSourceD2

end RandomSandpile

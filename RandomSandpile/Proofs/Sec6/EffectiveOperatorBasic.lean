import RandomSandpile.Steps.Sec6.EffectiveOperatorBasic
import RandomSandpile.Proofs.Sec6.MuMonotone

/-! # Lemma 6.4: the deterministic steps

* `muShift : MuShiftStmt`: `q_l + q_{M + tI} = q_{l + dt} + q_M`;
* `muMatrixMonotone : MuMatrixMonotoneStmt`: Lemma 6.1 with `q_A`, `A ≥ 0`. For
  `w ∈ S(l, M)`, `w - q_A ∈ S(l, M + A)` and `p ↦ p - A x` maps `∂⁺(w, x)` into `∂⁺(w - q_A, x)`
  (convexity of `q_A`). For `w ∈ S*(l, M + A)`, `w + q_A ∈ S*(l, M)` and `p ↦ p + A x` maps
  `∂⁻(w, x)` into `∂⁻(w + q_A, x)`;
* `muPositive : MuPositiveStmt`: for `l ≥ d(|M|₂ + 1)` the parabola `-(q_l + q_M)` (zero toppling)
  has `B̄(-∇(q_l + q_M)(x), 1/2) ⊆ ∂⁺(·, x, B_n)` at every `x ∈ B_n`, because distinct lattice
  points are at distance `≥ 1`. -/

open MeasureTheory LatticeProb Filter Set Metric
open scoped ENNReal Topology Matrix

namespace RandomSandpile

namespace EffectiveOperatorBasic

open MuLipschitz

variable {d : ℕ}

theorem qMZ_add (M A : Matrix (Fin d) (Fin d) ℝ) (x : Site d) :
    qMZ (M + A) x = qMZ M x + qMZ A x := by
  simp only [qMZ, qM, Matrix.add_mulVec, dotProduct_add]; ring

theorem norm_toE_sq (x : Site d) :
    ‖toE x‖ ^ 2 = WithLp.ofLp (toE x) ⬝ᵥ WithLp.ofLp (toE x) := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

theorem qlZ_add_qMZ_shift (hd : 1 ≤ d) (l t : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (x : Site d) :
    qlZ l x + qMZ (M + t • 1) x = qlZ (l + d * t) x + qMZ M x := by
  have hd0 : (d : ℝ) ≠ 0 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                               exact this.ne'
  rw [qMZ_add]
  simp only [qlZ, ql, qMZ, qM, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]
  rw [norm_toE_sq]
  field_simp
  ring

/-- **Step 2** (`MuShiftStmt`). -/
theorem muShift : MuShiftStmt := by
  intro d hd η n l t M
  have hfun : ∀ u : Site d → ℤ, (fun x => (u x : ℝ) - (qlZ l x + qMZ (M + t • 1) x)) =
      (fun x => (u x : ℝ) - (qlZ (l + d * t) x + qMZ M x)) := fun u => by
    funext x; rw [qlZ_add_qMZ_shift hd]
  have h1 : perturbedSub (ballZ0 (n : ℝ)) η l (M + t • 1) =
      perturbedSub (ballZ0 (n : ℝ)) η (l + d * t) M := by
    simp only [perturbedSub, hfun]
  have h2 : perturbedSuper (ballZ0 (n : ℝ)) η l (M + t • 1) =
      perturbedSuper (ballZ0 (n : ℝ)) η (l + d * t) M := by
    simp only [perturbedSuper, hfun]
  exact ⟨by rw [mu, mu, h1], by rw [muStar, muStar, h2]⟩

/-- The gradient `A x` of `q_A` at a lattice point. -/
noncomputable def gradQ (A : Matrix (Fin d) (Fin d) ℝ) (x : Site d) : Rd d :=
  WithLp.toLp 2 (A *ᵥ WithLp.ofLp (toE x))

theorem inner_gradQ (A : Matrix (Fin d) (Fin d) ℝ) (x y : Site d) :
    inner ℝ (gradQ A x) (toE y - toE x) =
      (WithLp.ofLp (toE y) - WithLp.ofLp (toE x)) ⬝ᵥ (A *ᵥ WithLp.ofLp (toE x)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp [gradQ]

/-- Second-order expansion of `q_A` for symmetric `A`:
`q_A(y) - q_A(x) - A x · (y - x) = q_A(y - x)`. -/
theorem qMZ_expand {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm) (x y : Site d) :
    qMZ A y - qMZ A x - inner ℝ (gradQ A x) (toE y - toE x) =
      (1 / 2 : ℝ) * ((WithLp.ofLp (toE y) - WithLp.ofLp (toE x)) ⬝ᵥ
        (A *ᵥ (WithLp.ofLp (toE y) - WithLp.ofLp (toE x)))) := by
  rw [inner_gradQ]
  set a := WithLp.ofLp (toE x)
  set b := WithLp.ofLp (toE y)
  have hsym : b ⬝ᵥ (A *ᵥ a) = a ⬝ᵥ (A *ᵥ b) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]
  simp only [qMZ, qM]
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
  change (1 / 2 : ℝ) * (b ⬝ᵥ A *ᵥ b) - (1 / 2 : ℝ) * (a ⬝ᵥ A *ᵥ a) -
    (b ⬝ᵥ (A *ᵥ a) - a ⬝ᵥ (A *ᵥ a)) = _
  rw [hsym]; ring

/-- Convexity of `q_A` for `A ≥ 0`. -/
theorem qMZ_convex {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) (x y : Site d) :
    qMZ A x + inner ℝ (gradQ A x) (toE y - toE x) ≤ qMZ A y := by
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.1 hA.1
  have h := qMZ_expand hsymm x y
  have hpsd := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hA).2
    (WithLp.ofLp (toE y) - WithLp.ofLp (toE x))
  rw [star_trivial] at hpsd
  nlinarith

theorem perturbedSub_add_matrix (B : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M A : Matrix (Fin d) (Fin d) ℝ) {w : Site d → ℝ} (hw : w ∈ perturbedSub B η l M) :
    w - qMZ A ∈ perturbedSub B η l (M + A) := by
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.1 hw
  refine mem_perturbedSub.2 ⟨u, hu, ?_⟩
  funext x; simp only [Pi.sub_apply, qMZ_add]; ring

theorem perturbedSuper_add_matrix (B : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M A : Matrix (Fin d) (Fin d) ℝ) {w : Site d → ℝ} (hw : w ∈ perturbedSuper B η l (M + A)) :
    w + qMZ A ∈ perturbedSuper B η l M := by
  obtain ⟨v, hv, rfl⟩ := mem_perturbedSuper.1 hw
  refine mem_perturbedSuper.2 ⟨v, hv, ?_⟩
  funext x; simp only [Pi.add_apply, qMZ_add]; ring

/-- **Step 1** (`MuMatrixMonotoneStmt`). -/
theorem muMatrixMonotone : MuMatrixMonotoneStmt := by
  intro d η n l M A hA
  set B : Set (Site d) := ballZ0 (n : ℝ)
  refine ⟨?_, ?_⟩
  · refine iSup₂_le fun w hw => ?_
    refine le_trans ?_ (le_iSup₂_of_le (w - qMZ A) (perturbedSub_add_matrix B η l M A hw) le_rfl)
    refine volume_supGradSet_le_of_shift supGradSetVolume (fun x => -gradQ A x)
      fun x _ p hp y hy => ?_
    have h1 := hp y hy
    have h2 := qMZ_convex hA x y
    simp only [Pi.sub_apply, ← sub_eq_add_neg, inner_sub_left]
    linarith
  · refine iSup₂_le fun w hw => ?_
    refine le_trans ?_ (le_iSup₂_of_le (w + qMZ A) (perturbedSuper_add_matrix B η l M A hw) le_rfl)
    refine volume_subGradSet_le_of_shift supGradSetVolume (fun x => gradQ A x)
      fun x _ p hp y hy => ?_
    have h1 := hp y hy
    have h2 := qMZ_convex hA x y
    simp only [Pi.add_apply, inner_add_left]
    linarith

end EffectiveOperatorBasic

end RandomSandpile

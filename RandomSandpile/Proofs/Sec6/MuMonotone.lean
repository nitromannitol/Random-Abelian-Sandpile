import RandomSandpile.Steps.Sec6.MuMonotone

/-! # Lemma 6.1 (monotonicity of `μ` and `μ*` in `l`): proofs of the steps

Proofs of the step statements of `RandomSandpile/Steps/Sec6/MuMonotone.lean` and of Lemma 6.1
itself, `muMonotone : MuMonotoneStmt`.

* `perturbedShift`: `S(A, η, l + s, M) = S(A, η, l, M) - q_s` and
  `S*(A, η, l - s, M) = S*(A, η, l, M) + q_s`;
* `supGradShift`: the supergradient shift `p ↦ p - ∇q_s(x)`;
* `supGradSetVolume`: `|∂⁺(w, A)| = ∑_{x ∈ A} |∂⁺(w, x, A)|`, since supergradient sets at distinct
  points meet inside a Lebesgue-null hyperplane;
* `muMonotone`: Lemma 6.1. -/

open MeasureTheory LatticeProb

namespace RandomSandpile

variable {d : ℕ}

/-! ### Step 1: the parabola `q_l` is additive in `l` -/

theorem qlZ_add (l s : ℝ) (x : Site d) : qlZ (l + s) x = qlZ l x + qlZ s x := by
  simp only [qlZ, ql]; ring

theorem qlZ_sub (l s : ℝ) (x : Site d) : qlZ (l - s) x = qlZ l x - qlZ s x := by
  simp only [qlZ, ql]; ring

/-- `S(A, η, l + s, M) = S(A, η, l, M) - q_s`. -/
theorem perturbedSub_add (A : Set (Site d)) (η : Site d → ℤ) (l s : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    perturbedSub A η (l + s) M = (fun w => w - qlZ s) '' perturbedSub A η l M := by
  simp only [perturbedSub, Set.image_image]
  congr 1
  funext u x
  simp only [Pi.sub_apply, qlZ_add]
  ring

/-- `S*(A, η, l - s, M) = S*(A, η, l, M) + q_s`. -/
theorem perturbedSuper_sub (A : Set (Site d)) (η : Site d → ℤ) (l s : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    perturbedSuper A η (l - s) M = (fun w => w + qlZ s) '' perturbedSuper A η l M := by
  simp only [perturbedSuper, Set.image_image]
  congr 1
  funext u x
  simp only [Pi.add_apply, qlZ_sub]
  ring

theorem perturbedShift : PerturbedShiftStmt := fun _ A η l s M =>
  ⟨perturbedSub_add A η l s M, perturbedSuper_sub A η l s M⟩

/-! ### Step 2: shifting supergradients by `∇q_s(x) = (s / d) x` -/

/-- Second-order expansion of `q_s` on the lattice:
`q_s(y) - q_s(x) - ∇q_s(x) · (y - x) = s |y - x|² / (2d)`. -/
theorem qlZ_sub_qlZ_sub_inner (s : ℝ) (x y : Site d) :
    qlZ s y - qlZ s x - inner ℝ ((s / d) • toE x) (toE y - toE x) =
      s * ‖toE y - toE x‖ ^ 2 / (2 * d) := by
  simp only [qlZ, ql, real_inner_smul_left, inner_sub_right, norm_sub_sq_real,
    real_inner_self_eq_norm_sq, real_inner_comm (toE x) (toE y)]
  ring

theorem qlZ_sub_qlZ_sub_inner_nonneg {s : ℝ} (hs : 0 ≤ s) (x y : Site d) :
    0 ≤ qlZ s y - qlZ s x - inner ℝ ((s / d) • toE x) (toE y - toE x) := by
  rw [qlZ_sub_qlZ_sub_inner]
  exact div_nonneg (mul_nonneg hs (sq_nonneg _)) (by positivity)

theorem supGradShift : SupGradShiftStmt := by
  intro d w x A s hs
  refine ⟨fun p hp y hy => ?_, fun p hp y hy => ?_⟩
  · have h1 := hp y hy
    have h2 := qlZ_sub_qlZ_sub_inner_nonneg hs x y
    simp only [Pi.sub_apply, inner_sub_left]
    linarith
  · have h1 := hp y hy
    have h2 := qlZ_sub_qlZ_sub_inner_nonneg hs x y
    simp only [Pi.add_apply, inner_add_left]
    linarith

/-! ### Step 3: the measure of the supergradient set is the sum of the pointwise measures -/

theorem toE_injective : Function.Injective (toE (d := d)) := fun x y h => by
  funext i
  have := congrArg (fun z : Rd d => z i) h
  simpa using this

/-- A hyperplane `{p : p · u = c}` with `u ≠ 0` is Lebesgue-null in `ℝ^d`. -/
theorem volume_inner_eq_null {u : Rd d} (hu : u ≠ 0) (c : ℝ) :
    volume {p : Rd d | inner ℝ p u = c} = 0 := by
  rcases Set.eq_empty_or_nonempty {p : Rd d | inner ℝ p u = c} with h | ⟨p0, hp0⟩
  · rw [h, measure_empty]
  set K : Submodule ℝ (Rd d) := LinearMap.ker (innerₛₗ ℝ u)
  refine measure_mono_null (t := (AffineSubspace.mk' p0 K : Set (Rd d))) ?_
    (Measure.addHaar_affineSubspace _ _ ?_)
  · intro p hp
    simp only [Set.mem_ofPred_eq] at hp hp0
    simp only [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, K, LinearMap.mem_ker,
      innerₛₗ_apply_apply, inner_sub_right]
    rw [real_inner_comm p u, real_inner_comm p0 u, hp, hp0, sub_self]
  · intro htop
    have hmem : p0 + u ∈ AffineSubspace.mk' p0 K := by rw [htop]; exact AffineSubspace.mem_top _ _ _
    rw [AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left] at hmem
    simp only [K, LinearMap.mem_ker, innerₛₗ_apply_apply, inner_self_eq_zero] at hmem
    exact hu hmem

/-- If closed sets `f x`, `x ∈ A`, meet pairwise inside the hyperplanes
`{p : p · (y - x) = w(y) - w(x)}`, their union has measure `∑_{x ∈ A} |f x|`. -/
theorem volume_biUnion_eq_tsum_of_inner_eq {A : Set (Site d)} {w : Site d → ℝ}
    (f : Site d → Set (Rd d)) (hf : ∀ x, IsClosed (f x))
    (hH : ∀ x ∈ A, ∀ y ∈ A, ∀ p ∈ f x ∩ f y, inner ℝ p (toE y - toE x) = w y - w x) :
    volume (⋃ x ∈ A, f x) = ∑' x : A, volume (f x) := by
  refine measure_biUnion₀ A.to_countable (fun x hx y hy hxy => ?_)
    (fun x _ => (hf x).measurableSet.nullMeasurableSet)
  have hu : toE y - toE x ≠ 0 := sub_ne_zero.mpr fun h => hxy (toE_injective h).symm
  exact measure_mono_null (fun p hp => hH x hx y hy p hp) (volume_inner_eq_null hu (w y - w x))

theorem isClosed_supGrad (w : Site d → ℝ) (x : Site d) (A : Set (Site d)) :
    IsClosed (supGrad w x A) := by
  have : supGrad w x A = ⋂ y ∈ dClosure A, {p : Rd d | w y ≤ w x + inner ℝ p (toE y - toE x)} := by
    ext p; simp [supGrad]
  rw [this]
  exact isClosed_biInter fun y _ =>
    isClosed_le continuous_const (continuous_const.add (continuous_id.inner continuous_const))

theorem isClosed_subGrad (w : Site d → ℝ) (x : Site d) (A : Set (Site d)) :
    IsClosed (subGrad w x A) := by
  have : subGrad w x A = ⋂ y ∈ dClosure A, {p : Rd d | w x + inner ℝ p (toE y - toE x) ≤ w y} := by
    ext p; simp [subGrad]
  rw [this]
  exact isClosed_biInter fun y _ =>
    isClosed_le (continuous_const.add (continuous_id.inner continuous_const)) continuous_const

theorem supGradSetVolume : SupGradSetVolumeStmt := by
  intro d w A
  refine ⟨volume_biUnion_eq_tsum_of_inner_eq (w := w) _ (isClosed_supGrad w · A) ?_,
    volume_biUnion_eq_tsum_of_inner_eq (w := w) _ (isClosed_subGrad w · A) ?_⟩
  all_goals
    intro x hx y hy p hp
    have h1 := hp.1 y (subset_dClosure A hy)
    have h2 := hp.2 x (subset_dClosure A hx)
    simp only [inner_sub_right] at h1 h2 ⊢
    linarith

/-! ### Lemma 6.1 -/

/-- Lemma 6.1 (monotonicity): `μ(B_n, η, l, M) ≤ μ(B_n, η, l + s, M)` and
`μ*(B_n, η, l, M) ≤ μ*(B_n, η, l - s, M)` for `s ≥ 0`. -/
theorem muMonotone : MuMonotoneStmt :=
  muMonotone_of_steps perturbedShift supGradShift supGradSetVolume

end RandomSandpile

import RandomSandpile.Draft.Section6

/-! # Lemma 6.1 (monotonicity of `μ` and `μ*` in `l`): proof steps

The printed proof of Lemma 6.1 (`MuMonotoneStmt`) decomposed into step statements, and the
reduction `muMonotone_of_steps` concluding exactly `MuMonotoneStmt` from them.

* `PerturbedShiftStmt` (implicit): `q_l` is additive in `l`, so
  `S(A, η, l + s, M) = S(A, η, l, M) - q_s` and `S*(A, η, l - s, M) = S*(A, η, l, M) + q_s`;
* `SupGradShiftStmt`: for `s ≥ 0`, `p ∈ ∂⁺(w, x, A)` implies
  `p - ∇q_s(x) ∈ ∂⁺(w - q_s, x, A)`, and dually `p ∈ ∂⁻(w, x, A)` implies
  `p + ∇q_s(x) ∈ ∂⁻(w + q_s, x, A)`. Here `q_s(x) = s |x|² / (2d)`, so
  `∇q_s(x) = (s / d) x`; the printed computation is written with `q_s = s |x|² / 2`;
* `SupGradSetVolumeStmt` ("By Lemma 5.3"): `|∂⁺(w, A)| = ∑_{x ∈ A} |∂⁺(w, x, A)|`, and
  likewise for `∂⁻`.

On the use of Lemma 5.3. The proof invokes Lemma 5.3 (`MongeAmpereRepStmt`) on the ball `B_n`, while
Lemma 5.3 is stated (and drafted) on cubes `Q_n` in dimension `d ≥ 2`, and Lemma 6.1 is stated in
every dimension. Only the first equality of Lemma 5.3 is used, and it holds on every set
`A ⊆ ℤ^d`: two supergradient sets `∂⁺(w, x, A)`, `∂⁺(w, y, A)` with `x ≠ y` meet inside the
hyperplane `{p : p · (y - x) = w(y) - w(x)}`, which is Lebesgue-null. `SupGradSetVolumeStmt` states
this general form; it is proved in `RandomSandpile/Proofs/Sec6/MuMonotone.lean`, so the reduction
carries no literature hypothesis. -/

open MeasureTheory LatticeProb

namespace RandomSandpile

/-- Step 1 (implicit). Since `q_{l+s} = q_l + q_s`, the perturbed subsolutions for `l + s`
are those for `l` shifted by `-q_s`, and the perturbed supersolutions for `l - s` are those for `l`
shifted by `+q_s`. -/
def PerturbedShiftStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)) (η : Site d → ℤ) (l s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
    perturbedSub A η (l + s) M = (fun w => w - qlZ s) '' perturbedSub A η l M ∧
      perturbedSuper A η (l - s) M = (fun w => w + qlZ s) '' perturbedSuper A η l M

/-- Step 2. For `s ≥ 0` the parabola `q_s` is convex with gradient
`∇q_s(x) = (s / d) x`, so subtracting it moves each supergradient `p ∈ ∂⁺(w, x, A)` to
`p - ∇q_s(x) ∈ ∂⁺(w - q_s, x, A)`, and adding it moves each subgradient `p ∈ ∂⁻(w, x, A)` to
`p + ∇q_s(x) ∈ ∂⁻(w + q_s, x, A)`. -/
def SupGradShiftStmt : Prop :=
  ∀ (d : ℕ) (w : Site d → ℝ) (x : Site d) (A : Set (Site d)) (s : ℝ), 0 ≤ s →
    (∀ p ∈ supGrad w x A, p - (s / d) • toE x ∈ supGrad (w - qlZ s) x A) ∧
      (∀ p ∈ subGrad w x A, p + (s / d) • toE x ∈ subGrad (w + qlZ s) x A)

/-- Step 3 (the first equality of Lemma 5.3 on an arbitrary set `A ⊆ ℤ^d`, in every
dimension): the Lebesgue measure of the supergradient set is the sum of the measures of the
pointwise supergradient sets, `|∂⁺(w, A)| = ∑_{x ∈ A} |∂⁺(w, x, A)|`, and likewise for the
subgradient set `∂⁻(w, A)`. -/
def SupGradSetVolumeStmt : Prop :=
  ∀ (d : ℕ) (w : Site d → ℝ) (A : Set (Site d)),
    volume (supGradSet w A) = ∑' x : A, volume (supGrad w x A) ∧
      volume (subGradSet w A) = ∑' x : A, volume (subGrad w x A)

/-- Lebesgue measure on `ℝ^d` is invariant under the translation `p ↦ p + c`. -/
theorem volume_preimage_add_right_Rd {d : ℕ} (c : Rd d) (S : Set (Rd d)) :
    volume ((fun p => p + c) ⁻¹' S) = volume S :=
  measure_preimage_add_right volume c S

/-- If each `∂⁺(w, x, A)` translated by a vector `c x` lies in `∂⁺(w', x, A)`, then
`|∂⁺(w, A)| ≤ |∂⁺(w', A)|`. -/
theorem volume_supGradSet_le_of_shift (hvol : SupGradSetVolumeStmt) {d : ℕ} {w w' : Site d → ℝ}
    {A : Set (Site d)} (c : Site d → Rd d)
    (hshift : ∀ x ∈ A, ∀ p ∈ supGrad w x A, p + c x ∈ supGrad w' x A) :
    volume (supGradSet w A) ≤ volume (supGradSet w' A) := by
  rw [(hvol d w A).1, (hvol d w' A).1]
  refine ENNReal.tsum_le_tsum fun x => ?_
  calc volume (supGrad w x A)
      ≤ volume ((fun p => p + c x) ⁻¹' supGrad w' x A) :=
        measure_mono fun p hp => hshift x x.2 p hp
    _ = volume (supGrad w' x A) := volume_preimage_add_right_Rd _ _

/-- The subgradient analogue of `volume_supGradSet_le_of_shift`. -/
theorem volume_subGradSet_le_of_shift (hvol : SupGradSetVolumeStmt) {d : ℕ} {w w' : Site d → ℝ}
    {A : Set (Site d)} (c : Site d → Rd d)
    (hshift : ∀ x ∈ A, ∀ p ∈ subGrad w x A, p + c x ∈ subGrad w' x A) :
    volume (subGradSet w A) ≤ volume (subGradSet w' A) := by
  rw [(hvol d w A).2, (hvol d w' A).2]
  refine ENNReal.tsum_le_tsum fun x => ?_
  calc volume (subGrad w x A)
      ≤ volume ((fun p => p + c x) ⁻¹' subGrad w' x A) :=
        measure_mono fun p hp => hshift x x.2 p hp
    _ = volume (subGrad w' x A) := volume_preimage_add_right_Rd _ _

/-- Reduction of Lemma 6.1 to the steps: for `w ∈ S(B_n, η, l, M)`,
`w - q_s ∈ S(B_n, η, l + s, M)` and `|∂⁺(w, B_n)| ≤ |∂⁺(w - q_s, B_n)|`; taking suprema gives
`μ(B_n, η, l, M) ≤ μ(B_n, η, l + s, M)`. "The proof for `μ*` is identical", with `w + q_s`. -/
theorem muMonotone_of_steps (hS : PerturbedShiftStmt) (hgrad : SupGradShiftStmt)
    (hvol : SupGradSetVolumeStmt) : MuMonotoneStmt := by
  intro d η n l s M hs
  set A : Set (Site d) := ballZ0 (n : ℝ)
  refine ⟨?_, ?_⟩
  · refine iSup₂_le fun w hw => ?_
    have hw' : w - qlZ s ∈ perturbedSub A η (l + s) M := by
      rw [(hS d A η l s M).1]; exact Set.mem_image_of_mem _ hw
    refine le_trans ?_ (le_iSup₂_of_le (w - qlZ s) hw' le_rfl)
    refine volume_supGradSet_le_of_shift hvol (fun x => -((s / d) • toE x)) fun x _ p hp => ?_
    simpa [sub_eq_add_neg] using (hgrad d w x A s hs).1 p hp
  · refine iSup₂_le fun w hw => ?_
    have hw' : w + qlZ s ∈ perturbedSuper A η (l - s) M := by
      rw [(hS d A η l s M).2]; exact Set.mem_image_of_mem _ hw
    refine le_trans ?_ (le_iSup₂_of_le (w + qlZ s) hw' le_rfl)
    exact volume_subGradSet_le_of_shift hvol (fun x => (s / d) • toE x) fun x _ p hp =>
      (hgrad d w x A s hs).2 p hp

end RandomSandpile

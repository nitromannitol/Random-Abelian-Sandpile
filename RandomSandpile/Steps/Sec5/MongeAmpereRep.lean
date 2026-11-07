import RandomSandpile.Draft.Section5
import RandomSandpile.Steps.Sec6.MuMonotone

/-! # Lemma 5.3 (the Monge-Ampère measure of the concave envelope): proof steps

The printed proof of Lemma 5.3 (`MongeAmpereRepStmt`, `paper/random_piles-corrected.tex`)
decomposed into step statements, and the reduction `mongeAmpereRep_of_steps` concluding exactly
`MongeAmpereRepStmt`. Notation: `Q_n = cubeZ0 n`, `Q̄_n = dClosure Q_n`, `𝒬_n = cubeHull d n`,
`𝒬̄_n = cubeHullClosure d n`, `Γ_w = concaveEnvelope w n`.

* Step 1, `|∂⁺(w, Q_n)| = ∑_{x ∈ Q_n} |∂⁺(w, x, Q_n)|`, is `SupGradSetVolumeStmt`,
  decomposed in Lemma 6.1 (`RandomSandpile/Steps/Sec6/MuMonotone.lean`), which states it for every
  `A ⊆ ℤ^d`;
* `SupGradInterNullStmt`: supergradient sets at two distinct points of `Ā` meet in a
  Lebesgue-null set. A common supergradient `p` of `w` at `x ≠ y` satisfies
  `p · (y - x) = w(y) - w(x)`, a hyperplane; this replaces the printed argument through the
  non-differentiability of the discrete Legendre transform `w*`, and it also covers points of `∂A`;
* `ContactSupGradStmt`: at `x ∈ Q_n`, `∂⁺(w, x, Q_n) = ∅` off the contact set
  `{Γ_w = w}`, and `∂⁺(w, x, Q_n) = ∂⁺(Γ_w, x, Q_n)` on it;
* `ConcaveEnvelopeAttainedStmt`: the supremum in Proposition 5.1 is attained, so
  `Γ_w(x) = ∑ λ_i w(x_i)` for a convex combination `x = ∑ λ_i x_i` of points of `Q̄_n`.
  Proposition 5.1 (`ConcaveEnvelopeRepStmt`) only asserts a supremum; the printed proof writes
  `Γ_w(x)` as such a sum, which needs the supremum to be a maximum (it is: the admissible
  `(λ, x_i)` form a compact set);
* `SupGradOfRepStmt`: if `p ∈ ∂⁺(Γ_w, x, Q_n)` and `Γ_w(x) = ∑ λ_i w(x_i)`, then
  `p ∈ ∂⁺(w, x_i, Q_n)` for every `i` with `λ_i > 0`.

The reduction: for `x ∈ 𝒬_n`, either some `x_i` with `λ_i > 0` lies in `Q_n`,
or two of them are distinct points of `Q̄_n` (and `p` lies in a null set by
`SupGradInterNullStmt`), or all of them equal one point `z ∈ ∂Q_n`, so that `x = z ∉ 𝒬_n`, which
is impossible. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal

namespace RandomSandpile

/-- Step. Supergradient sets of `w` at two distinct points of `Ā` meet in a
Lebesgue-null set. -/
def SupGradInterNullStmt : Prop :=
  ∀ (d : ℕ) (w : Site d → ℝ) (A : Set (Site d)) (x y : Site d), x ∈ dClosure A →
    y ∈ dClosure A → x ≠ y → volume (supGrad w x A ∩ supGrad w y A) = 0

/-- Step. At `x ∈ Q_n`, the supergradient set `∂⁺(w, x, Q_n)` is empty off the
contact set `{Γ_w = w}`; on the contact set it is the supergradient set of `Γ_w` at `x`, tested on
`𝒬̄_n`. -/
def ContactSupGradStmt : Prop :=
  ∀ (d n : ℕ) (w : Site d → ℝ) (x : Site d), x ∈ cubeZ0 (n : ℝ) →
    (concaveEnvelope w n (toE x) ≠ w x → supGrad w x (cubeZ0 (n : ℝ)) = ∅) ∧
    (concaveEnvelope w n (toE x) = w x →
      supGrad w x (cubeZ0 (n : ℝ)) =
        supGradR (concaveEnvelope w n) (toE x) (cubeHullClosure d n))

/-- Step. For `x ∈ 𝒬̄_n` the supremum of Proposition 5.1 is attained:
`Γ_w(x) = ∑_{i=1}^{d+1} λ_i w(x_i)` for some `x_i ∈ Q̄_n`, `λ_i ≥ 0`, `∑ λ_i = 1`,
`∑ λ_i x_i = x`. -/
def ConcaveEnvelopeAttainedStmt : Prop :=
  ∀ (d n : ℕ) (w : Site d → ℝ), ∀ x ∈ cubeHullClosure d n,
    ∃ (lam : Fin (d + 1) → ℝ) (xs : Fin (d + 1) → Site d),
      (∀ i, xs i ∈ dClosure (cubeZ0 (n : ℝ))) ∧ (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧
        ∑ i, lam i • toE (xs i) = x ∧ concaveEnvelope w n x = ∑ i, lam i * w (xs i)

/-- Step. If `p ∈ ∂⁺(Γ_w, x, Q_n)` (tested on `𝒬̄_n`) and
`Γ_w(x) = ∑ λ_i w(x_i)` for a convex combination `x = ∑ λ_i x_i` of points of `Q̄_n`, then `p` is a
supergradient of `w` at every `x_i` with `λ_i > 0`: `p ∈ ∂⁺(w, x_i, Q_n)`. -/
def SupGradOfRepStmt : Prop :=
  ∀ (d n : ℕ) (w : Site d → ℝ) (x p : Rd d), x ∈ cubeHullClosure d n →
    p ∈ supGradR (concaveEnvelope w n) x (cubeHullClosure d n) →
    ∀ (lam : Fin (d + 1) → ℝ) (xs : Fin (d + 1) → Site d),
      (∀ i, xs i ∈ dClosure (cubeZ0 (n : ℝ))) → (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 →
      ∑ i, lam i • toE (xs i) = x → concaveEnvelope w n x = ∑ i, lam i * w (xs i) →
      ∀ i, 0 < lam i → p ∈ supGrad w (xs i) (cubeZ0 (n : ℝ))

/-! ### Support lemmas -/

section Support

variable {d n : ℕ}

/-- `𝒬_n ⊆ 𝒬̄_n`. -/
theorem cubeHull_subset_cubeHullClosure : cubeHull d n ⊆ cubeHullClosure d n :=
  convexHull_mono (Set.image_mono (subset_dClosure _))

/-- The open box `{y : |y_i| < r for all i}` is convex. -/
theorem convex_setOf_abs_lt (r : ℝ) : Convex ℝ {y : Rd d | ∀ i, |y i| < r} := by
  intro a ha b hb s t hs ht hst i
  have h := convex_Ioo (-r) r (abs_lt.mp (ha i)) (abs_lt.mp (hb i)) hs ht hst
  simpa [abs_lt] using h

/-- A site `z ∉ Q_n` is not in the hull `𝒬_n`: `𝒬_n` lies in the open box `|y|_∞ < n`. -/
theorem toE_not_mem_cubeHull {z : Site d} (hz : z ∉ cubeZ0 (n : ℝ)) : toE z ∉ cubeHull d n := by
  have hsub : cubeHull d n ⊆ {y : Rd d | ∀ i, |y i| < n} := by
    refine convexHull_min ?_ (convex_setOf_abs_lt _)
    rintro _ ⟨y, hy, rfl⟩ i
    simpa [cubeZ0, cubeZ] using hy i
  intro hmem
  apply hz
  intro i
  simpa using hsub hmem i

/-- Step 1 of the printed proof transported to the contact set: by `ContactSupGradStmt`,
`∑_{x ∈ Q_n} |∂⁺(w, x, Q_n)| = ∑_{x ∈ Q_n, Γ_w(x) = w(x)} |∂⁺(Γ_w, x, Q_n)|`. -/
theorem tsum_supGrad_eq_tsum_contact (hcontact : ContactSupGradStmt) (d n : ℕ)
    (w : Site d → ℝ) :
    (∑' x : (cubeZ0 (d := d) (n : ℝ)), volume (supGrad w x (cubeZ0 (n : ℝ)))) =
      ∑' x : {x : Site d | x ∈ cubeZ0 (n : ℝ) ∧ concaveEnvelope w n (toE x) = w x},
        volume (supGradR (concaveEnvelope w n) (toE (x : Site d)) (cubeHullClosure d n)) := by
  set C : Set (Site d) :=
    {x : Site d | x ∈ cubeZ0 (n : ℝ) ∧ concaveEnvelope w n (toE x) = w x} with hC
  rw [tsum_subtype (cubeZ0 (n : ℝ)) (fun x => volume (supGrad w x (cubeZ0 (n : ℝ)))),
    tsum_subtype C (fun x => volume (supGradR (concaveEnvelope w n) (toE x) (cubeHullClosure d n)))]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ cubeZ0 (n : ℝ)
  · by_cases hc : concaveEnvelope w n (toE x) = w x
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x ∈ C from ⟨hx, hc⟩),
        (hcontact d n w x hx).2 hc]
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_notMem (show x ∉ C from fun h => hc h.2),
        (hcontact d n w x hx).1 hc, measure_empty]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (show x ∉ C from fun h => hx h.1)]

end Support

/-! ### The reduction -/

/-- Lemma 5.3 from its steps. -/
theorem mongeAmpereRep_of_steps (hvol : SupGradSetVolumeStmt) (hnull : SupGradInterNullStmt)
    (hcontact : ContactSupGradStmt) (hattain : ConcaveEnvelopeAttainedStmt)
    (hrep : SupGradOfRepStmt) : MongeAmpereRepStmt := by
  intro d _ n w
  set Q : Set (Site d) := cubeZ0 (n : ℝ) with hQ
  set Γ := concaveEnvelope w n with hΓdef
  have h1 := (hvol d w Q).1.symm
  have h2 := tsum_supGrad_eq_tsum_contact hcontact d n w
  -- `∂⁺(w, Q_n) ⊆ ∂⁺(Γ_w, 𝒬_n)`
  have hsub : supGradSet w Q ⊆ supGradSetR Γ (cubeHull d n) (cubeHullClosure d n) := by
    intro p hp
    simp only [supGradSet, Set.mem_iUnion] at hp
    obtain ⟨x, hx, hp⟩ := hp
    have hc : Γ (toE x) = w x := by
      by_contra hc
      rw [(hcontact d n w x hx).1 hc] at hp
      exact hp
    rw [(hcontact d n w x hx).2 hc] at hp
    exact Set.mem_biUnion (subset_convexHull ℝ _ (Set.mem_image_of_mem toE hx)) hp
  -- the null set of common supergradients at two distinct points of `Q̄_n`
  set N : Set (Rd d) := ⋃ z₁ : Site d, ⋃ z₂ : Site d,
    ⋃ (_ : z₁ ∈ dClosure Q ∧ z₂ ∈ dClosure Q ∧ z₁ ≠ z₂), supGrad w z₁ Q ∩ supGrad w z₂ Q with hN
  have hN0 : volume N = 0 :=
    measure_iUnion_null fun z₁ => measure_iUnion_null fun z₂ => measure_iUnion_null fun h =>
      hnull d w Q z₁ z₂ h.1 h.2.1 h.2.2
  -- `∂⁺(Γ_w, 𝒬_n) ⊆ ∂⁺(w, Q_n) ∪ N`
  have hcover : supGradSetR Γ (cubeHull d n) (cubeHullClosure d n) ⊆ supGradSet w Q ∪ N := by
    intro p hp
    simp only [supGradSetR, Set.mem_iUnion] at hp
    obtain ⟨x, hx, hp⟩ := hp
    have hx' : x ∈ cubeHullClosure d n := cubeHull_subset_cubeHullClosure hx
    obtain ⟨lam, xs, hxs, h0, hsum, hxx, hΓ⟩ := hattain d n w x hx'
    have hpi := hrep d n w x p hx' hp lam xs hxs h0 hsum hxx hΓ
    by_cases hin : ∃ i, 0 < lam i ∧ xs i ∈ Q
    · obtain ⟨i, hi, hiQ⟩ := hin
      exact Or.inl (Set.mem_biUnion hiQ (hpi i hi))
    by_cases hdist : ∃ i j, 0 < lam i ∧ 0 < lam j ∧ xs i ≠ xs j
    · obtain ⟨i, j, hi, hj, hij⟩ := hdist
      refine Or.inr ?_
      simp only [hN, Set.mem_iUnion]
      exact ⟨xs i, xs j, ⟨hxs i, hxs j, hij⟩, hpi i hi, hpi j hj⟩
    push Not at hin hdist
    obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < lam i := by
      by_contra h
      push Not at h
      have : ∑ i, lam i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (h0 i)
      linarith
    have hxz : x = toE (xs i₀) := by
      rw [← hxx]
      have hterm : ∀ i, lam i • toE (xs i) = lam i • toE (xs i₀) := fun i => by
        rcases (h0 i).lt_or_eq with h | h
        · rw [hdist i i₀ h hi₀]
        · rw [← h, zero_smul, zero_smul]
      simp_rw [hterm, ← Finset.sum_smul, hsum, one_smul]
    exact absurd (hxz ▸ hx) (toE_not_mem_cubeHull (hin i₀ hi₀))
  have h3 : volume (supGradSet w Q) =
      volume (supGradSetR Γ (cubeHull d n) (cubeHullClosure d n)) := by
    refine le_antisymm (measure_mono hsub) ?_
    calc volume (supGradSetR Γ (cubeHull d n) (cubeHullClosure d n))
        ≤ volume (supGradSet w Q ∪ N) := measure_mono hcover
      _ ≤ volume (supGradSet w Q) + volume N := measure_union_le _ _
      _ = volume (supGradSet w Q) := by rw [hN0, add_zero]
  exact ⟨h1, h1.symm.trans h2, h2.symm.trans (h1.trans h3)⟩

end RandomSandpile

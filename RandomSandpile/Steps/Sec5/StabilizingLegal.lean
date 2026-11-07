import RandomSandpile.Draft.Section5

/-! # Lemma 5.1 (stabilizing-legal): steps and reduction

The printed proof has two ingredients.

* `LocLegalLeStabilizingStmt`: the comparison principle with boundary data. A locally legal
  toppling `u ∈ 𝓛(η, A)` lies below every stabilizing toppling `v ∈ 𝒮(η, A)` with `v = u` on `∂A`
  ("by the least action principle and boundary assumption, `h ≥ u`"). It reduces to the
  least action principle `LegalLeStabilizingStmt` (Proposition 3.1, step 1) applied to `η + Δw`,
  where `u = w + û` is the decomposition of `𝓛(η, A)`.
* `SupGradSetMonoStmt` and `SubGradSetMonoStmt`: the translation argument. If `u ≤ h` in `A`
  and `h = u` on `∂A`, a supporting plane `u(x) + p · (y - x)` of `u` from above, translated
  upward by `t = max_{y ∈ Ā} (h(y) - u(x) - p · (y - x)) ≥ 0`, touches `h` from above at a point
  of `A`, so `∂⁺(u, A) ⊆ ∂⁺(h, A)`; dually for subgradients and touching from below. The maximum
  is attained at a point of `A` because `A` is finite and, on `∂A`, the translated quantity is
  at most `0 ≤ t` (this is where `h = u` on `∂A` enters).

Neither step uses `h ∈ 𝓛(η, A)` in the first half, nor `h ∈ 𝒮(η, A)` in the second half, nor
`d ≥ 2`; no existence of the solution `h` is needed, since `StabilizingLegalStmt` quantifies over
every such `h`. -/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Step 1 of Lemma 5.1, the comparison principle with boundary data: if
`u ∈ 𝓛(η, A)`, `v ∈ 𝒮(η, A)` and `v = u` on `∂A`, then `u ≤ v`. No finiteness of `A` is
needed. -/
def LocLegalLeStabilizingStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)) (η u v : Site d → ℤ), u ∈ locLegal η A → v ∈ stabilizing η A →
    (∀ x ∈ bdry A, v x = u x) → u ≤ v

/-- Step 2 of Lemma 5.1, the translation argument for supergradients: for finite
`A`, if `u ≤ h` in `A` and `h = u` on `∂A`, then `∂⁺(u, A) ⊆ ∂⁺(h, A)`. -/
def SupGradSetMonoStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)), A.Finite → ∀ u h : Site d → ℝ, (∀ y ∈ A, u y ≤ h y) →
    (∀ x ∈ bdry A, h x = u x) → supGradSet u A ⊆ supGradSet h A

/-- Step 3 of Lemma 5.1, the translation argument for subgradients ("the proof for subgradients
is similar"): for finite `A`, if `h ≤ v` in `A` and `h = v` on `∂A`, then
`∂⁻(v, A) ⊆ ∂⁻(h, A)`. -/
def SubGradSetMonoStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)), A.Finite → ∀ v h : Site d → ℝ, (∀ y ∈ A, h y ≤ v y) →
    (∀ x ∈ bdry A, h x = v x) → subGradSet v A ⊆ subGradSet h A

/-- **Reduction of Lemma 5.1** to its three steps. In the first half, `u ≤ h` by step 1 applied
to `u ∈ 𝓛(η, A)` and `h ∈ 𝒮(η, A)`; in the second half, `h* ≤ v` by step 1 applied to
`h* ∈ 𝓛(η, A)` and `v ∈ 𝒮(η, A)`. -/
theorem stabilizingLegal_of_steps (h1 : LocLegalLeStabilizingStmt) (h2 : SupGradSetMonoStmt)
    (h3 : SubGradSetMonoStmt) : StabilizingLegalStmt := by
  intro d _ η A hA
  refine ⟨fun u h hu hh hbd => ?_, fun v h hv hh hbd => ?_⟩
  · have hle := h1 d A η u h hu hh.2 hbd
    exact h2 d A hA _ _ (fun y _ => by exact_mod_cast hle y)
      (fun x hx => by simp only [hbd x hx])
  · have hle := h1 d A η h v hh.1 hv (fun x hx => (hbd x hx).symm)
    exact h3 d A hA _ _ (fun y _ => by exact_mod_cast hle y)
      (fun x hx => by simp only [hbd x hx])

end RandomSandpile

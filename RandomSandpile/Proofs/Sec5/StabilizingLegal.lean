import RandomSandpile.Steps.Sec5.StabilizingLegal
import RandomSandpile.Proofs.Sec3.LeastAction

/-! # Lemma 5.1 (stabilizing-legal): proofs of the steps

* `locLegalLeStabilizing : LocLegalLeStabilizingStmt`, from the least action principle
  `legalLeStabilizing` (Proposition 3.1, step 1) applied to `η + Δw`;
* `supGradSetMono : SupGradSetMonoStmt` and `subGradSetMono : SubGradSetMonoStmt`, the
  translation argument (touching from above, resp. below);
* `stabilizingLegal : StabilizingLegalStmt`, Lemma 5.1. -/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- The lattice Laplacian is additive: `Δ(v - w) = Δv - Δw`. -/
theorem lap_sub_apply (v w : Site d → ℤ) (x : Site d) : lap (v - w) x = lap v x - lap w x := by
  simp only [lap, nbrSumZ, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- **Step 1 of Lemma 5.1**, the comparison principle with boundary data. Write
`u = w + û ∈ 𝓛(η, A)` with `w = 0` in `A` and `û = 0` on `∂A`, `û` legal for `η + Δw`. Since
`v = u = w` on `∂A`, the function `v - w` is a toppling function on `Ā`, and it is stabilizing for
`η + Δw` because `Δ(v - w) + η + Δw = Δv + η`. The least action principle gives `û ≤ v - w`. -/
theorem locLegalLeStabilizing : LocLegalLeStabilizingStmt := by
  intro d A η u v hu hv hbd
  obtain ⟨w, uh, hw, -, rfl, hwA, huh, hleg⟩ := hu
  have hst : (v - w) ∈ stabilizing (fun y => lap w y + η y) A := by
    refine ⟨⟨fun x => ?_, fun x hx => ?_⟩, fun x hx => ?_⟩
    · by_cases hxA : x ∈ A
      · simp only [Pi.sub_apply, hwA x hxA, sub_zero]
        exact hv.1.1 x
      · by_cases hxb : x ∈ bdry A
        · have h := hbd x hxb
          simp only [Pi.add_apply, huh x hxb, add_zero] at h
          simp only [Pi.sub_apply, h, sub_self, le_refl]
        · have hxc : x ∉ dClosure A := by
            rw [dClosure_eq]; exact fun h => h.elim hxA hxb
          simp only [Pi.sub_apply, hv.1.2 x hxc, hw.2 x hxc, sub_self, le_refl]
    · simp only [Pi.sub_apply, hv.1.2 x hx, hw.2 x hx, sub_self]
    · rw [lap_sub_apply]
      have := hv.2 x hx
      linarith
  have hle := legalLeStabilizing d A _ uh (v - w) hleg hst
  intro y
  have := hle y
  simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
  linarith

/-- **Step 2 of Lemma 5.1**, the translation argument for supergradients. For
`p ∈ ∂⁺(u, x, A)`, choose `y₀ ∈ A` maximizing `h(y) - p · (y - x)` over the finite set `A`. On
`∂A` this quantity is `u(y) - p · (y - x) ≤ u(x) ≤ h(x)`, which is its value at `x ∈ A`; so `y₀`
maximizes it over `Ā`, i.e. the plane `h(y₀) + p · (y - y₀)` touches `h` from above at `y₀` on `Ā`. -/
theorem supGradSetMono : SupGradSetMonoStmt := by
  intro d A hA u h hle hbd p hp
  simp only [supGradSet, Set.mem_iUnion] at hp ⊢
  obtain ⟨x, hxA, hpx⟩ := hp
  obtain ⟨y₀, hy₀A, hmax⟩ :=
    Set.exists_max_image A (fun z => h z - inner ℝ p (toE z - toE x)) hA ⟨x, hxA⟩
  have hmax' : ∀ z ∈ dClosure A,
      h z - inner ℝ p (toE z - toE x) ≤ h y₀ - inner ℝ p (toE y₀ - toE x) := by
    intro z hz
    have hz' : z ∈ A ∪ bdry A := by rwa [dClosure_eq] at hz
    rcases hz' with hzA | hzb
    · exact hmax z hzA
    · have h1 : u z ≤ u x + inner ℝ p (toE z - toE x) := hpx z hz
      have h2 := hmax x hxA
      have h3 := hle x hxA
      simp only [sub_self, inner_zero_right, sub_zero] at h2
      rw [hbd z hzb]
      linarith
  refine ⟨y₀, hy₀A, ?_⟩
  intro z hz
  have hsplit : inner ℝ p (toE z - toE y₀) =
      inner ℝ p (toE z - toE x) - inner ℝ p (toE y₀ - toE x) := by
    rw [← inner_sub_right]; congr 1; abel
  have := hmax' z hz
  rw [hsplit]
  linarith

/-- **Step 3 of Lemma 5.1**, the translation argument for subgradients, dual to
`supGradSetMono`: for `p ∈ ∂⁻(v, x, A)`, a minimizer `y₀ ∈ A` of `h(y) - p · (y - x)` over `A`
minimizes it over `Ā`, so the plane `h(y₀) + p · (y - y₀)` touches `h` from below at `y₀`. -/
theorem subGradSetMono : SubGradSetMonoStmt := by
  intro d A hA v h hle hbd p hp
  simp only [subGradSet, Set.mem_iUnion] at hp ⊢
  obtain ⟨x, hxA, hpx⟩ := hp
  obtain ⟨y₀, hy₀A, hmin⟩ :=
    Set.exists_min_image A (fun z => h z - inner ℝ p (toE z - toE x)) hA ⟨x, hxA⟩
  have hmin' : ∀ z ∈ dClosure A,
      h y₀ - inner ℝ p (toE y₀ - toE x) ≤ h z - inner ℝ p (toE z - toE x) := by
    intro z hz
    have hz' : z ∈ A ∪ bdry A := by rwa [dClosure_eq] at hz
    rcases hz' with hzA | hzb
    · exact hmin z hzA
    · have h1 : v x + inner ℝ p (toE z - toE x) ≤ v z := hpx z hz
      have h2 := hmin x hxA
      have h3 := hle x hxA
      simp only [sub_self, inner_zero_right, sub_zero] at h2
      rw [hbd z hzb]
      linarith
  refine ⟨y₀, hy₀A, ?_⟩
  intro z hz
  have hsplit : inner ℝ p (toE z - toE y₀) =
      inner ℝ p (toE z - toE x) - inner ℝ p (toE y₀ - toE x) := by
    rw [← inner_sub_right]; congr 1; abel
  have := hmin' z hz
  rw [hsplit]
  linarith

/-- **Lemma 5.1** (stabilizing-legal): legal, stabilizing toppling functions
maximize curvature among legal (resp. stabilizing) ones with the same boundary values. -/
theorem stabilizingLegal : StabilizingLegalStmt :=
  stabilizingLegal_of_steps locLegalLeStabilizing supGradSetMono subGradSetMono

end RandomSandpile

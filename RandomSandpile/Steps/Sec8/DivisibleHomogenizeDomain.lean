import RandomSandpile.Draft.Section8
import RandomSandpile.Steps.Sec7.DivisibleHomogenize

/-!
# Steps of Lemma 8.1 (homogenization of the Green potentials on `W_n`)

Carving of `RandomSandpile.DivisibleHomogenizeDomainStmt` (Lemma 8.1, `divisible_homogenize2`,
`paper/random_piles-corrected.tex`) into steps and the reduction
`divisibleHomogenizeDomain_of_steps`. The paper gives no proof: Lemma 8.1 is introduced as "the
form of Lemma 7.3 we use", but the proof of Lemma 7.3 uses estimates
specific to the ball `B_n`. The decomposition below follows the proof of
Lemma 7.3 as formalized in `Steps/Sec7/DivisibleHomogenize.lean`, with the ball replaced by
`W_n = ℤ^d ∩ nW`, `W` a bounded Lipschitz domain.

Notation: `W_n = discretize W n`, `g_n = greenKilled W_n`, `η_avg = E η(0)`
(`meanEtaReal`), `r_n - d_n = ∑_{y ∈ W_n} g_n(·, y) (η(y) - η_avg)`.

* **(ergodic)**, for real environments: step `CubeErgodicRealStmt`, the analogue of
  `CubeErgodicStmt` for a `RealRandomEnvironment`. Same proof (Lattice-Probability's
  rectangle ergodic theorem, transported to all orthants by reflections).
* **Deterministic homogenization on `W_n`**: step `GreenDomainHomogenizeStmt`, for every bounded
  `f` with vanishing dyadic cube averages, `sup_x |∑_{y ∈ W_n} g_n(x, y) f(y)| = o(n²)`. The cube
  decomposition of Lemma 7.3 (pooling at the cube average, discrete Poincaré inequality) applies
  verbatim to the cubes of side `2^{-j} N` contained in the interior region
  `{y : dist(y, ℤ^d ∖ W_n) > β n}`; the remaining cubes lie in a boundary layer. It uses:
  * **(exit_time) on `W_n`**: step `GreenDomainExitTimeStmt`,
    `∑_{y ∈ W_n} g_n(x, y) ≤ (R n + 1)² / (2d)` when `W ⊆ B̄_R(0)`, by comparison with the
    quadratic `((R n + 1)² - |y|²) / (2d)` (equivalently, monotonicity of the killed Green's
    function in the domain, `W_n ⊆ B_{Rn+1}`);
  * **interior differences**: step `GreenDomainGradientSumStmt`,
    `∑_{y : dist(y, ℤ^d ∖ W_n) > βn} ∑_i |g_n(x, y + e_i) - g_n(x, y)| ≤ C_β n`, from the
    Lawler-Limic difference estimate on balls `B(y, c min(|x - y|, βn)) ⊆ W_n ∖ {x}`, the Harnack
    inequality, the weighted occupation bound `∑_y g_n(x, y) / |x - y| ≤ C (Rn + 1)` and
    (exit_time), as for the ball (`GreenBallHarnackGradientStmt`, `GreenBallWeightedSumStmt`);
  * **boundary layer**: step `GreenDomainBoundaryLayerStmt`, for every `δ > 0` there is `γ > 0`
    with `∑_{y ∈ W_n, dist(y, ℤ^d ∖ W_n) ≤ γ n} g_n(x, y) ≤ δ n²` for all `x` and large `n`.
    For the ball this was the exact comparison `GreenBallBoundaryLayerStmt`; for a Lipschitz
    domain it is reduced by the maximum principle (the occupation density of the layer is harmonic
    off the layer, so its maximum is attained on the layer) to step
    `GreenDomainBoundaryExitStmt`: the expected exit time from `W_n` is at most `δ n²` from every
    point of the layer of width `γ n`. That step follows from the uniform exterior ball condition
    of Lipschitz domains (step `UniformExteriorBallStmt`) by iterating, over the dyadic scales
    between `γ n` and `ρ n`, a barrier argument: the walk started within `r` of `∂(nW)` leaves
    `W_n` before leaving the ball of radius `K r` with probability at least `p = p_d > 0`
    (comparison with the discretely subharmonic function `|y - w|^{-4d}` centred in an exterior
    ball).

No literature input is used beyond the Lawler-Limic difference estimate
(`LawlerLimicHarmonicDifferenceStmt`, `Inputs/Proposed.lean`), already used for Lemma 7.3.

The reduction `divisibleHomogenizeDomain_of_steps` (this file) takes `CubeErgodicRealStmt` and
`GreenDomainHomogenizeStmt`, with `C = 1`.
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-- The sites of `ℤ^d` within Euclidean distance `t` of a site outside `A`. For `A = W_n` and
`t = γ n`, `A ∩ nearCompl A t` is the boundary layer of width `γ n` of `W_n`, and the complement
`(nearCompl A t)ᶜ = {y : every site within distance t of y lies in A}` is the interior region. -/
def nearCompl (A : Set (Site d)) (t : ℝ) : Set (Site d) :=
  {y | ∃ z, z ∉ A ∧ ‖toE (z - y)‖ ≤ t}

/-- **(ergodic)** for real environments (1131-1140). Almost surely, for every
dyadic scale `2^{-j}` and every `k ∈ ℤ^d`, the average of `η - E η(0)` over the dyadic cube
`Q_{j,k}(N)`, normalised by `N^d`, tends to `0` as `N → ∞`. -/
def CubeErgodicRealStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RealRandomEnvironment d, ∀ᵐ η ∂E.P, ∀ (j : ℕ) (k : Site d),
    Tendsto (fun N : ℕ => (∑ y ∈ dyadicCube j k N, (η y - meanEtaReal E.P)) / (N : ℝ) ^ d)
      atTop (𝓝 0)

/-- **Deterministic homogenization of the Green potential on `W_n`** (the proof of Lemma 7.3, on `W_n`). For `d ≥ 2`, a bounded Lipschitz domain `W` and a bounded
`f : ℤ^d → ℝ` whose normalised dyadic cube sums tend to `0`, for every `ε > 0`, eventually
`|∑_{y ∈ W_n} g_n(x, y) f(y)| ≤ ε n²` for all `x ∈ ℤ^d`. -/
def GreenDomainHomogenizeStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∀ (f : Site d → ℝ) (K : ℝ), (∀ y, |f y| ≤ K) →
    (∀ (j : ℕ) (k : Site d),
      Tendsto (fun N : ℕ => (∑ y ∈ dyadicCube j k N, f y) / (N : ℝ) ^ d) atTop (𝓝 0)) →
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x : Site d,
      |greenPotential (discretize W n) f x| ≤ ε * (n : ℝ) ^ 2

/-- **(exit_time) on `W_n`**: if `W ⊆ B̄_R(0)` then
`∑_{y ∈ W_n} g_n(x, y) ≤ (R n + 1)² / (2d)` for every `x`, by comparison with the quadratic
`((R n + 1)² - |y|²) / (2d)`, whose Laplacian is `-1` and which is nonnegative on `W̄_n`. -/
def GreenDomainExitTimeStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (W : Set (Rd d)) (R : ℝ), 0 ≤ R → W ⊆ Metric.closedBall 0 R →
    ∀ (n : ℕ) (x : Site d),
      greenPotential (discretize W n) (fun _ => 1) x ≤ (R * n + 1) ^ 2 / (2 * d)

/-- **Interior differences, summed** (the analogue on `W_n` of `GreenBallGradientSumStmt`): for
`d ≥ 2`, bounded `W` and `β > 0` there are `C_β`, `n₀` with
`∑_{y : dist(y, ℤ^d ∖ W_n) > βn} ∑_i |g_n(x, y + e_i) - g_n(x, y)| ≤ C_β n` for all `n ≥ n₀`
and `x ∈ ℤ^d`. -/
def GreenDomainGradientSumStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), Bornology.IsBounded W → ∀ β : ℝ, 0 < β →
    ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x : Site d,
      ∑ᶠ y ∈ (nearCompl (discretize W n) (β * n))ᶜ, ∑ i : Fin d,
        |greenKilled (discretize W n) x (y + unit i) - greenKilled (discretize W n) x y| ≤
          C * n

/-- **Boundary layer on `W_n`** (the analogue of `GreenBallBoundaryLayerStmt`): for `d ≥ 2`, a
bounded Lipschitz domain `W` and `δ > 0` there are `γ > 0` and `n₀` with
`∑_{y ∈ W_n, dist(y, ℤ^d ∖ W_n) ≤ γ n} g_n(x, y) ≤ δ n²` for all `n ≥ n₀` and `x ∈ ℤ^d`. -/
def GreenDomainBoundaryLayerStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ δ : ℝ, 0 < δ →
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x : Site d,
      greenPotential (discretize W n)
          ((nearCompl (discretize W n) (γ * n)).indicator fun _ => 1) x ≤ δ * (n : ℝ) ^ 2

/-- **Exit time near the boundary**: for `d ≥ 2`, a bounded Lipschitz domain `W` and `δ > 0`
there are `γ > 0` and `n₀` with `E^z τ_{W_n} / (2d) = ∑_{y ∈ W_n} g_n(z, y) ≤ δ n²` for every
`z` within distance `γ n` of `ℤ^d ∖ W_n` and `n ≥ n₀`. -/
def GreenDomainBoundaryExitStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → ∀ δ : ℝ, 0 < δ →
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ z ∈ nearCompl (discretize W n) (γ * n),
        greenPotential (discretize W n) (fun _ => 1) z ≤ δ * (n : ℝ) ^ 2

/-- **Uniform exterior ball condition** of a bounded Lipschitz domain: there are `r₀ > 0` and
`c > 0` such that for every `p ∈ ∂W` and `0 < s ≤ r₀` some ball `B(w, c s)` with `|w - p| ≤ s`
does not meet `W` (in a Lipschitz chart at `p` with constant `L`, take `w = p - s e` and
`c = 1 / (2 (L + 1))`; a finite subcover of the compact `∂W` makes `L` and the chart radius
uniform). -/
def UniformExteriorBallStmt : Prop :=
  ∀ (d : ℕ) (W : Set (Rd d)), IsLipschitzDomain W → ∃ r₀ c : ℝ, 0 < r₀ ∧ 0 < c ∧
    ∀ p ∈ frontier W, ∀ s : ℝ, 0 < s → s ≤ r₀ →
      ∃ w : Rd d, dist w p ≤ s ∧ ∀ y ∈ Metric.ball w (c * s), y ∉ W

namespace DivisibleHomogenizeDomain

/-- `W_n = ℤ^d ∩ nW` is finite for bounded `W` (as `SubadditiveLipschitz.discretize_finite`). -/
theorem discretize_finite {V : Set (Rd d)} (hV : Bornology.IsBounded V) (n : ℕ) :
    (discretize V n).Finite := by
  obtain ⟨R, hR⟩ := (hV.smul₀ (n : ℝ)).exists_norm_le
  refine (Set.finite_Icc (fun _ : Fin d => -⌈R⌉) (fun _ => ⌈R⌉)).subset ?_
  intro x hx
  have hx' : ‖toE x‖ ≤ R := hR _ hx
  have hi : ∀ i, |(x i : ℝ)| ≤ R := fun i => by
    have := PiLp.norm_apply_le (toE x) i
    simpa using this.trans hx'
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.mp (hi i)).1
    have h2 : (-(⌈R⌉ : ℤ) : ℝ) ≤ x i := by
      linarith [Int.le_ceil R]
    exact_mod_cast h2
  · have := (abs_le.mp (hi i)).2
    have h2 : (x i : ℝ) ≤ (⌈R⌉ : ℤ) := by linarith [Int.le_ceil R]
    exact_mod_cast h2

/-- `r_n - d_n` is the Green potential of `η - m` in `W_n` (bounded `W`). -/
theorem greenPotentialDomain_sub_mean {W : Set (Rd d)} (hW : Bornology.IsBounded W) (n : ℕ)
    (η : Site d → ℝ) (m : ℝ) (x : Site d) :
    greenPotentialDomain W n η x - greenPotentialDomainMean W n m x =
      greenPotential (discretize W n) (fun y => η y - m) x := by
  obtain ⟨B, hB⟩ := (discretize_finite hW n).exists_finset_coe
  rw [greenPotentialDomain, greenPotentialDomainMean, ← hB, greenPotential_coe_finset,
    greenPotential_coe_finset, greenPotential_coe_finset, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

end DivisibleHomogenizeDomain

/-- **Reduction for Lemma 8.1**: (ergodic) for real environments and the deterministic
homogenization of the Green potential on `W_n` give `DivisibleHomogenizeDomainStmt`, with
`C = 1`. Almost surely `η` is bounded by `η_min, η_max` at every site (countably many), so
`f = η - E η(0)` is bounded. -/
theorem divisibleHomogenizeDomain_of_steps (hErg : CubeErgodicRealStmt)
    (hHom : GreenDomainHomogenizeStmt) : DivisibleHomogenizeDomainStmt := by
  intro d hd
  refine ⟨1, fun E W hW => ?_⟩
  have hb : ∀ᵐ η ∂E.P, ∀ x : Site d, E.ηmin ≤ η x ∧ η x ≤ E.ηmax :=
    ae_all_iff.2 E.bounded
  filter_upwards [hErg d hd E, hb] with η hη hηb
  set m := meanEtaReal E.P
  have hK : ∀ y, |η y - m| ≤ |E.ηmin| + |E.ηmax| + |m| := by
    intro y
    have h3 : |η y| ≤ |E.ηmin| + |E.ηmax| := by
      have h1 := (hηb y).1
      have h2 := (hηb y).2
      rw [abs_le]; constructor <;> cases abs_cases E.ηmin <;>
        cases abs_cases E.ηmax <;> linarith
    calc |η y - m| ≤ |η y| + |m| := abs_sub _ _
      _ ≤ _ := by linarith
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hHom d hd W hW (fun y => η y - m) _ hK hη ε hε
  refine ⟨n₀, fun n hn x _ => ?_⟩
  rw [DivisibleHomogenizeDomain.greenPotentialDomain_sub_mean hW.1, mul_one]
  exact hn₀ n hn x

end RandomSandpile

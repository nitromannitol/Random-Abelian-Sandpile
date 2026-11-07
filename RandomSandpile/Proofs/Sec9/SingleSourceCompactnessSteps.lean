import RandomSandpile.Steps.Sec9.SingleSource

/-! # Theorem 9.2: decomposition of `SSCompactnessStmt`

Not proved yet. Notation: `v_n = singleSourceOdometer η n`, `h = n^{1/d}`,
`v̄_n(x) = h^{-2} v_n([h x])`. Route (Pegden-Smart 2013, proof of Lemma 3.1):

1. **Outer bound** (`SSOuterBoundStmt`, requested literature input): `v_n = 0` outside
   `B_{R h}`, `R = R(d, η_min)`.
2. **Lattice fundamental solution** (`SSLatticeGreenStmt`): `g : ℤ^d → ℝ` with `Δ g = -δ_0` and
   `g(z) - G(z) - κ = o(|z|^{2-d})` (`κ = 0` for `d ≥ 3`). From the Lawler-Limic asymptotics
   `LatticeProb.External.PotentialKernelAsymptotics d` (Theorems 4.3.1 and 4.4.4; requested input)
   and `Δ srwGreenInf = -2d δ_0` (`d ≥ 3`), resp. the potential kernel (`d = 2`).
3. `w_n = v_n - n g` has `|Δ w_n| ≤ 2d - 1 - η_min` everywhere (the final configuration of
   `η + n δ_0` lies in `[η_min, 2d - 1]` off the origin and the charge `n` at `0` cancels). On
   `B_{R h}^c` it equals `-n g`; by the discrete maximum principle with the barrier
   `Λ |z|²/(2d)`, `h^{-2} w_n - c_n` is bounded on `B_{2R h}`, with `c_n = 0` for `d ≥ 3` and
   `c_n = -(1/2π) log h - κ` for `d = 2`.
4. **Interior regularity** (`SSInteriorLipschitzStmt`, deterministic, provable from the Lawler-Limic input and the
   Green potential of the ball): Lipschitz bounds `C (K/ρ + Λ ρ)` for real lattice functions with
   `|w| ≤ K`, `|Δ w| ≤ Λ` on a ball of radius `ρ`. Applied at scale `ρ ≍ h`, the rescalings
   `h^{-2} w_n([h ·]) - c_n` are bounded and asymptotically equi-Lipschitz on `B_{R}`.
5. Arzela-Ascoli on `B̄_{R}` (as `asymptoticArzelaAscoli_core`, `Proofs/Sec7/CompactnessArzelaAscoli`):
   a subsequence converges uniformly to a continuous `v`; and
   `h^{d-2} g([h x]) + c_n → G(x)` locally uniformly on `x ≠ 0` (step 2 and the homogeneity of `G`),
   so `v̄_n → v + G` locally uniformly on `ℝ^d \ {0}`, with `v = -G` outside `B_R`.
-/

open MeasureTheory LatticeProb Filter Metric
open scoped Topology

namespace RandomSandpile

/-- **Outer bound for the single-source toppled set** (Pegden-Smart (3.1) in the proof of Lemma 3.1;
Fey-Levine-Peres 2010 / Levine-Peres 2009 for backgrounds `≤ 2d - 2`). -/
def SSOuterBoundStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ ηmin : ℤ, ∃ R : ℝ, 0 < R ∧ ∀ η : Site d → ℤ,
    (∀ x, ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2) → ∀ (n : ℕ) (z : Site d),
      R * ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ ‖toE z‖ → singleSourceOdometer η n z = 0

/-- **A lattice fundamental solution with the asymptotics of `G`** (step 2). -/
def SSLatticeGreenStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ g : Site d → ℝ, (∀ z, lapR g z = -(if z = 0 then 1 else 0)) ∧
    ∃ κ : ℝ, Tendsto (fun z : Site d => ‖toE z‖ ^ (d - 2) *
      |g z - fundamentalSolution d (toE z) - κ|) cofinite (𝓝 0)

/-- **Interior Lipschitz bound for real lattice functions with bounded Laplacian** (step 4;
deterministic). -/
def SSInteriorLipschitzStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ (w : Site d → ℝ) (z0 : Site d) (ρ K Λ : ℝ), 1 ≤ ρ →
    (∀ z, ‖toE (z - z0)‖ ≤ ρ → |w z| ≤ K ∧ |lapR w z| ≤ Λ) →
    ∀ x y : Site d, ‖toE (x - z0)‖ ≤ ρ / 2 → ‖toE (y - z0)‖ ≤ ρ / 2 →
      |w x - w y| ≤ C * (K / ρ + Λ * ρ) * ‖toE (x - y)‖

end RandomSandpile

import RandomSandpile.Defs.Effective
import RandomSandpile.Defs.Viscosity

/-!
# The obstacle problems of Theorems 1.1 and 9.2

`paper/random_piles-corrected.tex` (Theorem 1.1) and 1610-1620 (Theorem 9.2).

## Theorem 1.1

The scaling limit of the free-boundary odometers is the least element of the constraint set
(`obstacleSet E W`)
`{v ∈ C(ℝ^d) : v ≥ 0, F̄_η(D²v) ≥ 0 in W, F̄_0(D²v) ≤ 0 in ℝ^d}`,
with both differential inequalities in the viscosity-*supersolution* sense of Crandall, Ishii and
Lions: they are tested by `C²` functions `φ` touching `v` from below
(`ViscFromBelowGE (effOp E) W v` and `ViscFromBelowLE (effOp0 d) univ v`).

The sign of the `F̄_η` inequality follows the correction [C3]: the paper prints `F̄_η(D²v̄) ≤ 0 in W`. The operator `F̄_η = l_M`
(`effOp`) is nonincreasing in `M` (Lemma 6.4(1), `EffectiveOperatorBasicStmt`), while `F̄_0`
(`effOp0`) is nondecreasing in `M`. A constraint set whose least element is sought must be stable
under pointwise minima (`obstacleSet_min_mem` below), which every "touching from below" condition
is; the printed sign `F̄_η(D²φ) ≤ 0` for `φ` touching from below is never satisfied
(take `φ` very concave: `F̄_η(M) → +∞` as `M → -∞ I`, since `F̄_η(M + sI) = F̄_η(M) - d s` by
`q_l + q_M = q_{M + (l/d) I}`), and at a point where the limit is twice differentiable the
heuristic gives `F̄_η(D²v̄) ≥ 0`.

The least element is `obstacleSolution E W`, the pointwise infimum of the constraint set. Its
junk values: the infimum of the empty set is `0`; every member is `≥ 0`, so the pointwise
infimum is otherwise a genuine infimum. Whether it belongs to the set (and so is its least
element) is the content of Theorem 1.1: `isLeast_obstacleSolution_iff` shows that `IsLeast` is
exactly membership.

## Theorem 9.2

`fundamentalSolution d` is the fundamental solution `G` of the Laplacian on `ℝ^d` with the sign
convention `ΔG = -δ_0` (Evans, *Partial Differential Equations*, §2.2.1; this is the convention
forced by Theorem 9.2, where the rescaled odometers of `n δ_0`, which are nonnegative and large near
the origin, converge to `v̄ + G` with `v̄` continuous):
`G(x) = -(1/2π) log |x|` for `d = 2` and `G(x) = |x|^{2-d} / (d (d-2) ω_d)` for `d ≥ 3`, where
`ω_d = |B_1|` is the volume of the unit ball (`unitBallVolume`). The second formula also gives the
fundamental solution `-|x|/2` for `d = 1`. Junk value: `G(0) = 0` (`Real.log 0 = 0` and
`0 ^ y = 0` for `y ≠ 0`).

The constraint set of Theorem 9.2 (`singleSourceObstacleSet E`) is
`{v ∈ C(ℝ^d) : v ≥ -G, F̄_η(D²(v + G)) ≥ 0}`, the `F̄_η` inequality again with the [C3] sign
(the paper prints `≤ 0`) and in the viscosity-supersolution sense. Since `G` is singular
at the origin, both constraints are imposed on `ℝ^d \ {0}` only: there `v + G` is continuous, and
`v ≥ -G` is void at `0` (where `-G = -∞`); imposing it at `0` with the junk value `G(0) = 0` would
add the spurious constraint `v(0) ≥ 0`. The paper writes `inf`; `singleSourceObstacleSolution E` is
the pointwise infimum (junk value `0` where the values are unbounded below or the set is empty), and
the statement asserts that it is the least element.
-/

noncomputable section

open MeasureTheory

namespace RandomSandpile

variable {d : ℕ}

/-! ### Theorem 1.1 -/

/-- The constraint set of the obstacle problem of Theorem 1.1, with the
correction [C3]:
`{v ∈ C(ℝ^d) : v ≥ 0, F̄_η(D²v) ≥ 0 in W, F̄_0(D²v) ≤ 0 in ℝ^d}`, both differential inequalities
in the viscosity-supersolution sense (test functions touching from below). The paper prints
`F̄_η(D²v̄) ≤ 0 in W`; see the module docstring. -/
def obstacleSet (E : RandomEnvironment d) (W : Set (Rd d)) : Set (Rd d → ℝ) :=
  {v | Continuous v ∧ 0 ≤ v ∧ ViscFromBelowGE (effOp E) W v ∧
    ViscFromBelowLE (effOp0 d) Set.univ v}

/-- The solution `v̄ = min obstacleSet` of the obstacle problem of Theorem 1.1, defined
as the pointwise infimum `v̄(x) = inf {v(x) : v ∈ obstacleSet E W}` (junk value `0` if the set is
empty). That the infimum is attained, i.e. `IsLeast (obstacleSet E W) (obstacleSolution E W)`, is
part of Theorem 1.1. -/
def obstacleSolution (E : RandomEnvironment d) (W : Set (Rd d)) : Rd d → ℝ :=
  fun x => sInf ((fun v : Rd d → ℝ => v x) '' obstacleSet E W)

/-- If `min(u, w) - φ` has a local minimum at a point `x` where `u(x) ≤ w(x)`, then so does
`u - φ`. -/
theorem isLocalMin_sub_of_min {u w φ : Rd d → ℝ} {x : Rd d} (hx : u x ≤ w x)
    (h : IsLocalMin (fun y => min (u y) (w y) - φ y) x) : IsLocalMin (fun y => u y - φ y) x := by
  refine Filter.Eventually.mono h fun y hy => ?_
  simp only [min_eq_left hx] at hy
  linarith [min_le_left (u y) (w y)]

/-- Supersolution-type conditions (test functions touching from below) are stable under pointwise
minima. -/
theorem ViscFromBelowGE.min {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U : Set (Rd d)}
    {u w : Rd d → ℝ} (hu : ViscFromBelowGE F U u) (hw : ViscFromBelowGE F U w) :
    ViscFromBelowGE F U (fun y => min (u y) (w y)) := by
  intro x hx φ hφ hmin
  rcases le_total (u x) (w x) with h | h
  · exact hu x hx φ hφ (isLocalMin_sub_of_min h hmin)
  · refine hw x hx φ hφ (isLocalMin_sub_of_min h ?_)
    simpa only [min_comm] using hmin

/-- Supersolution-type conditions (test functions touching from below) are stable under pointwise
minima. -/
theorem ViscFromBelowLE.min {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U : Set (Rd d)}
    {u w : Rd d → ℝ} (hu : ViscFromBelowLE F U u) (hw : ViscFromBelowLE F U w) :
    ViscFromBelowLE F U (fun y => min (u y) (w y)) := by
  intro x hx φ hφ hmin
  rcases le_total (u x) (w x) with h | h
  · exact hu x hx φ hφ (isLocalMin_sub_of_min h hmin)
  · refine hw x hx φ hφ (isLocalMin_sub_of_min h ?_)
    simpa only [min_comm] using hmin

/-- Sanity check: the constraint set of Theorem 1.1 is stable under pointwise minima, as the
constraint set of a minimum problem must be. -/
theorem obstacleSet_min_mem {E : RandomEnvironment d} {W : Set (Rd d)} {u w : Rd d → ℝ}
    (hu : u ∈ obstacleSet E W) (hw : w ∈ obstacleSet E W) :
    (fun y => min (u y) (w y)) ∈ obstacleSet E W :=
  ⟨hu.1.min hw.1, fun y => le_min (hu.2.1 y) (hw.2.1 y), hu.2.2.1.min hw.2.2.1,
    hu.2.2.2.min hw.2.2.2⟩

/-- Sanity check: `obstacleSolution E W` is the least element of the constraint set as soon as it
belongs to it (the members are bounded below by `0`). -/
theorem isLeast_obstacleSolution_iff {E : RandomEnvironment d} {W : Set (Rd d)} :
    IsLeast (obstacleSet E W) (obstacleSolution E W) ↔
      obstacleSolution E W ∈ obstacleSet E W := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun w hw x => ?_⟩⟩
  exact csInf_le ⟨0, by rintro _ ⟨v, hv, rfl⟩; exact hv.2.1 x⟩ ⟨w, hw, rfl⟩

/-- Sanity check: a least element of the constraint set is `obstacleSolution E W`. -/
theorem obstacleSolution_eq_of_isLeast {E : RandomEnvironment d} {W : Set (Rd d)}
    {v : Rd d → ℝ} (hv : IsLeast (obstacleSet E W) v) : obstacleSolution E W = v := by
  funext x
  refine IsLeast.csInf_eq ⟨⟨v, hv.1, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hv.2 hw x

/-! ### The fundamental solution of the Laplacian (Theorem 9.2) -/

/-- The volume `ω_d = |B_1|` of the unit ball of `ℝ^d`. -/
def unitBallVolume (d : ℕ) : ℝ := (volume (Metric.ball (0 : Rd d) 1)).toReal

/-- `ω_d = π^{d/2} / Γ(d/2 + 1)` for `d ≥ 1`. -/
theorem unitBallVolume_eq (hd : 1 ≤ d) :
    unitBallVolume d = Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hG : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  simp only [unitBallVolume, EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one,
    one_pow, one_mul]
  exact ENNReal.toReal_ofReal (div_nonneg (by positivity) hG.le)

theorem unitBallVolume_pos (hd : 1 ≤ d) : 0 < unitBallVolume d := by
  rw [unitBallVolume_eq hd]
  exact div_pos (pow_pos (Real.sqrt_pos.2 Real.pi_pos) d)
    (Real.Gamma_pos_of_pos (by positivity))

/-- The fundamental solution `G` of the Laplacian on `ℝ^d` with `ΔG = -δ_0` (Theorem 9.2; Evans §2.2.1, Pegden-Smart's `G`): `G(x) = -(1/2π) log |x|` for `d = 2` and
`G(x) = |x|^{2-d} / (d (d-2) ω_d)` otherwise (for `d ≥ 3`; for `d = 1` this is `-|x|/2`).
Junk value `G(0) = 0`. -/
def fundamentalSolution (d : ℕ) (x : Rd d) : ℝ :=
  if d = 2 then -(1 / (2 * Real.pi)) * Real.log ‖x‖
  else ‖x‖ ^ (2 - (d : ℝ)) / ((d : ℝ) * ((d : ℝ) - 2) * unitBallVolume d)

/-- Sanity check of the sign convention `ΔG = -δ_0`: for `d ≥ 3`, `G > 0` away from the
origin. -/
theorem fundamentalSolution_pos_of_three_le (hd : 3 ≤ d) {x : Rd d} (hx : x ≠ 0) :
    0 < fundamentalSolution d x := by
  have hd2 : d ≠ 2 := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [fundamentalSolution, hd2, ite_false]
  exact div_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hx) _)
    (mul_pos (mul_pos (by linarith) (by linarith)) (unitBallVolume_pos (by omega)))

/-- Sanity check of the sign convention `ΔG = -δ_0`: for `d = 2`, `G(x) = -(1/2π) log |x| > 0`
for `0 < |x| < 1`. -/
theorem fundamentalSolution_pos_of_two {x : Rd 2} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    0 < fundamentalSolution 2 x := by
  simp only [fundamentalSolution, ite_true]
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg (norm_pos_iff.2 hx) hx1
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  nlinarith

/-! ### Theorem 9.2 -/

/-- The constraint set of the obstacle problem of Theorem 9.2, with the
correction [C3]:
`{v ∈ C(ℝ^d) : v ≥ -G and F̄_η(D²(v + G)) ≥ 0}`, the differential inequality in the
viscosity-supersolution sense (test functions touching `v + G` from below), both constraints on
`ℝ^d \ {0}`, where `G = fundamentalSolution d` is finite (see the module docstring). The paper
prints `F̄_η(D²(v̄ + G)) ≤ 0`. -/
def singleSourceObstacleSet (E : RandomEnvironment d) : Set (Rd d → ℝ) :=
  {v | Continuous v ∧ (∀ x : Rd d, x ≠ 0 → -fundamentalSolution d x ≤ v x) ∧
    ViscFromBelowGE (effOp E) {x | x ≠ 0} (fun x => v x + fundamentalSolution d x)}

/-- The solution `v̄ = inf singleSourceObstacleSet` of the obstacle problem of Theorem 9.2, the pointwise infimum (junk value `0` at points where the values are unbounded below,
or everywhere if the set is empty). Theorem 9.2 asserts that it is the least element. -/
def singleSourceObstacleSolution (E : RandomEnvironment d) : Rd d → ℝ :=
  fun x => sInf ((fun v : Rd d → ℝ => v x) '' singleSourceObstacleSet E)

/-- Sanity check: a least element of the constraint set of Theorem 9.2 is
`singleSourceObstacleSolution E`. -/
theorem singleSourceObstacleSolution_eq_of_isLeast {E : RandomEnvironment d} {v : Rd d → ℝ}
    (hv : IsLeast (singleSourceObstacleSet E) v) : singleSourceObstacleSolution E = v := by
  funext x
  refine IsLeast.csInf_eq ⟨⟨v, hv.1, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hv.2 hw x

end RandomSandpile

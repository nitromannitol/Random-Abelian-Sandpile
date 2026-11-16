import RandomSandpile.Defs.Viscosity

/-! # Locality of second-order Peano expansions

An expansion at an interior point depends only on the values of the function near that point.
-/

noncomputable section

open Filter
open scoped Topology

namespace RandomSandpile

/-- Equal germs have the same second-order expansion with the same coefficients. -/
theorem hasSecondOrderTaylorAt_congr {d : ℕ} {u u' : Rd d → ℝ} {x p : Rd d}
    {X : Matrix (Fin d) (Fin d) ℝ} (hu : u =ᶠ[𝓝 x] u') :
    HasSecondOrderTaylorAt u x p X ↔ HasSecondOrderTaylorAt u' x p X := by
  have hx : u x = u' x := hu.eq_of_nhds
  unfold HasSecondOrderTaylorAt
  apply Asymptotics.isLittleO_congr ?_ Filter.EventuallyEq.rfl
  filter_upwards [hu] with y hy
  rw [hy, hx]

/-- Equal functions on the unit ball have the same second-order expansions at its points. -/
theorem hasSecondOrderTaylorAt_ball_congr {d : ℕ} {u u' : Rd d → ℝ} {x p : Rd d}
    {X : Matrix (Fin d) (Fin d) ℝ}
    (hu : ∀ y ∈ Metric.ball (0 : Rd d) 1, u y = u' y)
    (hx : x ∈ Metric.ball (0 : Rd d) 1) :
    HasSecondOrderTaylorAt u x p X ↔ HasSecondOrderTaylorAt u' x p X := by
  apply hasSecondOrderTaylorAt_congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  exact hu y hy

/-- Equal functions on the unit ball have the same Peano differentiability at its points. -/
theorem peanoTwiceDifferentiableAt_ball_congr {d : ℕ} {u u' : Rd d → ℝ} {x : Rd d}
    (hu : ∀ y ∈ Metric.ball (0 : Rd d) 1, u y = u' y)
    (hx : x ∈ Metric.ball (0 : Rd d) 1) :
    PeanoTwiceDifferentiableAt u x ↔ PeanoTwiceDifferentiableAt u' x := by
  simp only [PeanoTwiceDifferentiableAt, hasSecondOrderTaylorAt_ball_congr hu hx]

end RandomSandpile

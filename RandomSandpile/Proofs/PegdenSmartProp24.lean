import RandomSandpile.Proofs.PegdenSmart
import RandomSandpile.Proofs.HessianLpAdapter
import LatticeProb.Analysis.PegdenSmartProp24Peano

/-! # Peano differentiability of weak Poisson solutions

The interior Hessian estimate gives the almost-everywhere second-order Peano expansion
for weak solutions with bounded Laplacian.
-/

open MeasureTheory Filter

namespace RandomSandpile

/-- A weak Poisson solution with bounded right-hand side is twice Peano differentiable almost
    everywhere in the unit ball. -/
theorem pegden_smart_prop24_stmt : PegdenSmartProp24Stmt := by
  intro d hd s u hs hu hweak
  have h := LatticeProb.PegdenSmart.pegdenSmartProp24Peano
    HessianAdapter.hessianLpStmt_proved (Rd d) volume s u hs hu
    ((isWeakSolutionLaplace_iff _ u s).1 hweak)
  filter_upwards [h] with x hx
  obtain ⟨p, B, hB, hexp⟩ := hx
  obtain ⟨X, hX, hq⟩ := exists_matrix_of_isSelfAdjoint B hB
  refine ⟨p, X, hX, ?_⟩
  unfold HasSecondOrderTaylorAt
  simp_rw [hq]
  exact hexp

end RandomSandpile

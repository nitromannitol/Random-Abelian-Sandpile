import LatticeProb.Analysis.HessianLpReduction
import LatticeProb.Analysis.HessianLpCover
import LatticeProb.Analysis.HessianLpScale
import LatticeProb.Analysis.HessianLpL2
import LatticeProb.Analysis.HessianLpEnergy
import LatticeProb.Analysis.HessianLpIdentity
import RandomSandpile.Proofs.HessianAdapterL6
import RandomSandpile.Proofs.HessianAdapterL7
import RandomSandpile.Proofs.HessianAdapterL8
import RandomSandpile.Proofs.HessianAdapterL9
import RandomSandpile.Proofs.HessianAdapterL10
import RandomSandpile.Proofs.HessianAdapterL11

/-!
# The Hessian Lᵖ estimate

The local Hessian estimate follows from the model-space estimate, the coordinate estimates,
and the covering and scaling reductions.
-/

namespace HessianAdapter

open PDE

/-- The Hessian Lᵖ estimate on finite-dimensional real inner product spaces. -/
theorem hessianLpStmt_proved : LatticeProb.PegdenSmart.HessianLpStmt := by
  intro E _ _ _ _ _ μ _
  refine L1_infinite_rhs μ ?_
  by_cases h0 : Module.finrank ℝ E = 0
  · exact L2_dim_zero μ h0
  · have hd : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero h0
    exact L3_model_space μ
      (L4_cover _ (L5_scale _ (L6_coordinates _ (L7_apply_erl _ (L8_erl_lp _ hd)
        (L9_smooth_h1 _) (L10_smooth_equation _)
        (L11_l2_coordinates _ (L12c_assemble _ (L12a_energy_ineq _)
          (L12b_hessian_energy _)))))))

example : LatticeProb.PegdenSmart.HessianLpStmt := hessianLpStmt_proved

end HessianAdapter

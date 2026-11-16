import RandomSandpile.Proofs.Sec7.PegdenSmartAdapterPeano
import RandomSandpile.Proofs.Sec7.LimitObstacleGamma

/-!
# Trace of a difference expansion

The trace of a second-order expansion of a difference is the difference of the traces of
second-order expansions of its two terms at the same point.
-/

namespace RandomSandpile

/-- The traces of three same-point Peano expansions are compatible with subtraction. -/
theorem trace_of_taylor_sub {d : ℕ} {u v : Rd d → ℝ} {y p p₂ q : Rd d}
    {X X₂ Y : Matrix (Fin d) (Fin d) ℝ} {s₁ s₂ : ℝ}
    (hu : HasSecondOrderTaylorAt u y p X) (hv : HasSecondOrderTaylorAt v y p₂ X₂)
    (hsub : HasSecondOrderTaylorAt (fun z => u z - v z) y q Y)
    (hX : X.trace = s₁) (hX₂ : X₂.trace = s₂) : Y.trace = s₁ - s₂ := by
  have hq : ∀ h : Rd d, qM Y h = qM (X - X₂) h :=
    PegdenSmartAdapter.qM_eq_of_taylor hsub (PegdenSmartAdapter.taylor_sub hu hv)
  have htrace : Y.trace = (X - X₂).trace :=
    le_antisymm (trace_le_trace_of_qM_le fun h => (hq h).le)
      (trace_le_trace_of_qM_le fun h => (hq h).ge)
  rw [htrace, Matrix.trace_sub, hX, hX₂]

end RandomSandpile

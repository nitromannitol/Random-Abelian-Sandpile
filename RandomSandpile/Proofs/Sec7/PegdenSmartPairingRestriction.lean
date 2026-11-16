import RandomSandpile.Proofs.Sec7.PegdenSmartAdapterWeak
import RandomSandpile.Proofs.Sec7.PegdenSmartDensityTestIntegrability

/-!
# Restriction of weak-solution pairings

For a smooth compactly supported test in an open set, both pairings in the weak Laplace
predicate are integrable and their ambient integrals agree with the integrals over the set.
-/

noncomputable section

open MeasureTheory

namespace RandomSandpile.PegdenSmartAdapter

variable {d : ℕ}

/-- The Hessian pairing is integrable and its ambient integral is the integral on the domain. -/
theorem integrable_and_integral_mul_trace_hessian_eq {U : Set (Rd d)} (hU : IsOpen U)
    {u φ : Rd d → ℝ} (hu : ContinuousOn u U) (hφ : ContDiff ℝ ⊤ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun x => u x * Matrix.trace (hessian φ x)) ∧
      (∫ x, u x * Matrix.trace (hessian φ x)) =
        ∫ x in U, u x * Matrix.trace (hessian φ x) := by
  refine ⟨integrable_mul_trace_hessian hU hu (hφ.of_le le_top) hφc hφU,
    (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm⟩
  intro x hx
  have hxφ : x ∉ tsupport φ := fun h => hx (hφU h)
  rw [hessian_eq_zero_of_not_mem_tsupport hxφ, Matrix.trace_zero, mul_zero]

/-- The density pairing is integrable and its ambient integral is the integral on the domain. -/
theorem integrable_and_integral_mul_test_eq {U : Set (Rd d)} {s φ : Rd d → ℝ}
    (hs : MemLp s ⊤ (volume.restrict U)) (hφ : ContDiff ℝ ⊤ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun x => s x * φ x) ∧
      (∫ x, s x * φ x) = ∫ x in U, s x * φ x := by
  refine ⟨integrable_mul_test_of_memLp_top hs hφ hφc hφU,
    (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm⟩
  intro x hx
  have hxφ : x ∉ tsupport φ := fun h => hx (hφU h)
  have hzero : φ x = 0 := by
    by_contra h
    exact hxφ (subset_tsupport φ h)
  rw [hzero, mul_zero]

end RandomSandpile.PegdenSmartAdapter

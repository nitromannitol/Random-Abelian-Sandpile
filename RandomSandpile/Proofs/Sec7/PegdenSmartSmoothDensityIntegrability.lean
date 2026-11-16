import RandomSandpile.Inputs.PegdenSmartProp25

/-!
# Integrability of smooth test pairings

A density that is essentially bounded on a domain pairs integrably with a compactly supported
smooth test supported in that domain.
-/

noncomputable section

open MeasureTheory

namespace RandomSandpile.PegdenSmartAdapter

variable {d : ℕ}

/-- A restricted essentially bounded density times a compactly supported smooth test is
integrable on the ambient space when the test is supported in the domain. -/
theorem integrable_mul_smooth_test_of_memLp_top {U : Set (Rd d)} {s φ : Rd d → ℝ}
    (hs : MemLp s ⊤ (volume.restrict U)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun x => s x * φ x) := by
  have hφi : Integrable φ (volume.restrict U) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφc).restrict
  have hpair : IntegrableOn (fun x => s x * φ x) U volume := by
    change Integrable (s * φ) (volume.restrict U)
    exact hφi.mul_of_top_right hs
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hpair
  intro x hx
  apply hφU
  apply subset_tsupport φ
  intro hzero
  exact hx (by simp [hzero])

end RandomSandpile.PegdenSmartAdapter

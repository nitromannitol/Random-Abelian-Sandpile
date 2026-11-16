import RandomSandpile.Inputs.PegdenSmartProp25

/-!
# Integrability of density pairings

A locally essentially bounded density pairs integrably with a compactly supported smooth test,
including when the density has arbitrary values outside the domain.
-/

noncomputable section

open MeasureTheory

namespace RandomSandpile.PegdenSmartAdapter

variable {d : ℕ}

/-- A restricted essentially bounded density times a smooth test supported in the domain is
integrable on the ambient space. -/
theorem integrable_mul_test_of_memLp_top {U : Set (Rd d)} {s φ : Rd d → ℝ}
    (hs : MemLp s ⊤ (volume.restrict U)) (hφ : ContDiff ℝ ⊤ φ)
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

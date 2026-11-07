import RandomSandpile.Defs.Effective

/-! # Recurrent curvature quantities of correction C13

Comparison uses signed integer functions and the local boundary of each finite test set.
The limiting densities follow the same ball normalization as `muBar` and `muStarBar`.
-/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal

namespace RandomSandpile

variable {d : ℕ}

/-- A signed stabilizing function with the local recurrent comparison property. -/
def IsRecurrentFunction (η : Site d → ℤ) (A : Set (Site d)) (r : Site d → ℤ) : Prop :=
  (∀ x ∈ A, lap r x + η x ≤ 2 * (d : ℤ) - 1) ∧
  ∀ E : Set (Site d), E.Finite → E.Nonempty → E ⊆ A →
    ∀ w : Site d → ℤ, (∀ x ∈ E, lap w x + η x ≤ 2 * (d : ℤ) - 1) →
      ∀ x ∈ E, ∃ y ∈ bdry E, r x - w x ≤ r y - w y

/-- The recurrent perturbations used for both upper and lower gradient measures. -/
def recurrentPerturbed (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : Set (Site d → ℝ) :=
  (fun r x => (r x : ℝ) - (qlZ l x + qMZ M x)) '' {r | IsRecurrentFunction η A r}

/-- Recurrent upper gradient measure. -/
noncomputable def muRecurrent (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : ℝ≥0∞ :=
  ⨆ w ∈ recurrentPerturbed A η l M, volume (supGradSet w A)

/-- Recurrent lower gradient measure. Signed functions are allowed, as in C13. -/
noncomputable def muStarRecurrent (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : ℝ≥0∞ :=
  ⨆ w ∈ recurrentPerturbed A η l M, volume (subGradSet w A)

/-- Deterministic recurrent upper density, with the normalization of `muBar`. -/
noncomputable def muRecurrentBar (E : RandomEnvironment d) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (∫⁻ η, limsup (fun n : ℕ => muRecurrent (ballZ0 (n : ℝ)) η l M /
    ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P).toReal

/-- Deterministic recurrent lower density. -/
noncomputable def muStarRecurrentBar (E : RandomEnvironment d) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (∫⁻ η, limsup (fun n : ℕ => muStarRecurrent (ballZ0 (n : ℝ)) η l M /
    ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P).toReal

/-- The common zero defines the recurrent effective operator when it exists uniquely. -/
noncomputable def effOpRecurrent (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup {l : ℝ | muRecurrentBar E l M = 0 ∧ muStarRecurrentBar E l M = 0}

/-- Restricting a recurrent function preserves recurrence. -/
theorem IsRecurrentFunction.mono {η : Site d → ℤ} {A B : Set (Site d)}
    {r : Site d → ℤ} (h : IsRecurrentFunction η A r) (hBA : B ⊆ A) :
    IsRecurrentFunction η B r := by
  refine ⟨fun x hx => h.1 x (hBA hx), ?_⟩
  intro E hfin hne hEB w hw x hx
  exact h.2 E hfin hne (hEB.trans hBA) w hw x hx

end RandomSandpile

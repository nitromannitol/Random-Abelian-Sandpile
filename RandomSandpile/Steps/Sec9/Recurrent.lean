import RandomSandpile.Draft.Section9Recurrent
import RandomSandpile.Proofs.Sec9.SingleSource

/-! # Reduction of C13 to recurrent compactness and comparison steps

The open steps are stated independently of the final limit. The assembly uses the existing
single-source subsequence machinery and the uniqueness of a least element.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- Recurrent compactness with the vanishing-tail hypothesis, including the source singularity. -/
def RecurrentSSCompactnessStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ᵐ η ∂E.P, SingleSourceFinite η → SingleSourceVanishingTail η →
      ∀ nk : ℕ → ℕ, StrictMono nk → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ v : Rd d → ℝ, Continuous v ∧
          TendstoLocallyUniformlyOn
            (fun j => rescaleSingleSource (singleSourceOdometer η (nk (ψ j))) (nk (ψ j)))
            (fun x => v x + fundamentalSolution d x) atTop {x : Rd d | x ≠ 0}

/-- Recurrent correctors yield the viscosity inequality and obstacle constraint for every limit. -/
def RecurrentSSAdmissibilityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ᵐ η ∂E.P, SingleSourceFinite η → SingleSourceVanishingTail η →
      ∀ v : Rd d → ℝ, Continuous v →
        IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
          v ∈ recurrentSingleSourceObstacleSet E

/-- The recurrent comparison and far-field argument put every limit below each competitor. -/
def RecurrentSSMinimalityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ᵐ η ∂E.P, SingleSourceFinite η → SingleSourceVanishingTail η →
      ∀ v : Rd d → ℝ, Continuous v →
        IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
          ∀ w ∈ recurrentSingleSourceObstacleSet E, ∀ x, v x ≤ w x

/-- The printed height bound implies the vanishing tail almost surely. -/
def RecurrentSSTailFromHeightStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    E.ηmax ≤ 2 * (d : ℤ) - 2 → ∀ᵐ η ∂E.P, SingleSourceVanishingTail η

/-- The upper and lower recurrent densities have a unique common zero. -/
def RecurrentCommonZeroStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ M : Matrix (Fin d) (Fin d) ℝ,
      ∃! l : ℝ, muRecurrentBar E l M = 0 ∧ muStarRecurrentBar E l M = 0

/-- Fixed-boundary recurrentization preserves the lower gradient measure. -/
def RecurrentMuStarEqualityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (A : Set (Site d)), A.Finite → ∀ (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ), muStarRecurrent A η l M = muStar A η l M

/-- The recurrent upper gradient measure is bounded by the legal upper measure. -/
def RecurrentMuLeStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (A : Set (Site d)), A.Finite → ∀ (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ), muRecurrent A η l M ≤ mu A η l M

/-- Recurrent background comparison yields equality of the finite upper measures. -/
def RecurrentMuEqualityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (A : Set (Site d)), A.Finite → ∀ (η : Site d → ℤ),
    IsStableOn η A → IsRecurrentOn η A → ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
      muRecurrent A η l M = mu A η l M

/-- Assembly of the VT theorem from compactness, admissibility and minimality. -/
theorem singleSourceRecurrentVT_of_steps (hc : RecurrentSSCompactnessStmt)
    (ha : RecurrentSSAdmissibilityStmt) (hm : RecurrentSSMinimalityStmt) :
    SingleSourceTheoremRecurrentVTStmt := by
  intro d hd E hvt
  have hall := (hc d hd E).and ((ha d hd E).and (hm d hd E))
  have hall' := hvt.and hall
  obtain ⟨η₀, hvt₀, hc₀, ha₀, hm₀⟩ := hall'.exists
  obtain ⟨ψ, hψ, v₀, hv₀c, hv₀⟩ := hc₀ hvt₀.1 hvt₀.2 id strictMono_id
  have hv₀L : IsSSSubseqLimit η₀ (fun x => v₀ x + fundamentalSolution d x) := ⟨ψ, hψ, hv₀⟩
  have hleast : IsLeast (recurrentSingleSourceObstacleSet E) v₀ :=
    ⟨ha₀ hvt₀.1 hvt₀.2 v₀ hv₀c hv₀L, fun w hw x => hm₀ hvt₀.1 hvt₀.2 v₀ hv₀c hv₀L w hw x⟩
  refine ⟨v₀, hleast, ?_⟩
  filter_upwards [hall'] with η hη
  refine ⟨hη.1.1, ?_⟩
  refine tendstoLocallyUniformlyOn_of_subseq isOpen_ne fun nk hnk => ?_
  obtain ⟨φ, hφ, v, hvc, hv⟩ := hη.2.1 hη.1.1 hη.1.2 nk hnk
  have hvL : IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) :=
    ⟨nk ∘ φ, hnk.comp hφ, hv⟩
  have heq : v = v₀ := funext fun x => le_antisymm
    (hη.2.2.2 hη.1.1 hη.1.2 v hvc hvL v₀ hleast.1 x)
    (hleast.2 (hη.2.2.1 hη.1.1 hη.1.2 v hvc hvL) x)
  rw [heq] at hv
  exact ⟨φ, hφ, hv⟩

/-- Assembly of the printed height-bound theorem from VT and the known finiteness lemma. -/
theorem singleSourceRecurrent_of_steps (hc : RecurrentSSCompactnessStmt)
    (ha : RecurrentSSAdmissibilityStmt) (hm : RecurrentSSMinimalityStmt)
    (ht : RecurrentSSTailFromHeightStmt) : SingleSourceTheoremRecurrentStmt := by
  intro d hd E hmax
  apply singleSourceRecurrentVT_of_steps hc ha hm d hd E
  have hb := ae_all_iff.2 E.bounded
  filter_upwards [hb, ht d hd E hmax] with η hη htail
  exact ⟨ssNonempty d (by omega) η (fun x => (hη x).2.trans hmax), htail⟩

end RandomSandpile

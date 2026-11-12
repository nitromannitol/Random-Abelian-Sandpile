import RandomSandpile.Draft.Section9PartialV2
import RandomSandpile.Proofs.Sec7.FlatTiltedZero

/-!
# Section 9, version 2: relation to the flatness hypothesis

* `stabThresholdZero_of_flatEff`: `FlatEff E` implies `StabThresholdZero E` (flatness at `M = 0`
  forces `F̄_η(0) ≤ 0`, hence `μ*(l, 0) = 0` for `l > 0`).
* `singleSourceTheoremFlat_of_v2`: `SingleSourceTheoremFlatV2Stmt` implies
  `SingleSourceTheoremFlatStmt`; the V2 hypothesis is weaker.
* `not_stabThresholdZero_of_le`: `StabThresholdZero` fails for every environment with
  `η ≤ d - 1` almost surely (in particular `η ≡ -1`): there `H_η(0) ≥ d > 0`, the open case.
-/

noncomputable section

open MeasureTheory

namespace RandomSandpile

variable {d : ℕ}

theorem stabThresholdZero_of_flatEff (hd : 2 ≤ d) {E : RandomEnvironment d} (h : FlatEff E) :
    StabThresholdZero E := by
  have hflat : FlatAt E 0 := h 0 Matrix.isSymm_zero
  have hle : effOp E 0 ≤ 0 := by
    by_contra hpos
    exact not_flatAt_zero_of_effOp_pos hd E (not_le.1 hpos) hflat
  intro l hl
  have hanti := EffectiveOperatorBasic.muStarBar_anti muMonotone (by omega) E
    (0 : Matrix (Fin d) (Fin d) ℝ) (hle.trans hl.le)
  exact le_antisymm (hflat.2 ▸ hanti) (EffectiveOperatorBasic.muStarBar_nonneg E l 0)

theorem not_stabThresholdZero_of_le (hd : 2 ≤ d) (E : RandomEnvironment d)
    (hE : ∀ᵐ η ∂E.P, ∀ x, η x ≤ (d : ℤ) - 1) : ¬ StabThresholdZero E := by
  intro h
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have := h ((d : ℝ) / 2) (by positivity)
  exact (muStarBar_zero_pos (by omega) E hE (by linarith)).ne' this

theorem singleSourceTheoremFlat_of_v2 (h : SingleSourceTheoremFlatV2Stmt) :
    SingleSourceTheoremFlatStmt := fun d hd E hE hflat =>
  h d hd E hE (stabThresholdZero_of_flatEff hd hflat)

theorem singleSourceTheorem_of_conclusion (h : ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    E.ηmax = 2 * (d : ℤ) - 2 → SingleSourceConclusion E) : SingleSourceTheoremStmt :=
  fun d hd E hE => h d hd E hE

end RandomSandpile

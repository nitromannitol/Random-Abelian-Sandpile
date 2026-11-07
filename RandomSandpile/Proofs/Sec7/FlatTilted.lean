import RandomSandpile.Steps.Sec9.SingleSource
import RandomSandpile.Proofs.Sec6.EffectiveOperatorBasicFinal
import RandomSandpile.Proofs.Sec5.SubadditiveErgodicFinal

/-!
# Flatness of `F̄_η` is a property of the line `M + ℝ I`

 §1. The shift identities `μ(l, M + tI) = μ(l + dt, M)`,
`μ*(l, M + tI) = μ*(l + dt, M)` (`EffectiveOperatorBasic.muBar_shift`) and
`F̄_η(M + tI) = F̄_η(M) - dt` (`effOp_add_smul_one`, from Lemma 5.5) give

* `flatAt_add_smul_one_iff`: `F̄_η` is flat at `M + tI` iff it is flat at `M`;
* `flatEff_of_line`: flatness at one point of every line `M + ℝ I` is flatness everywhere
  (`FlatEff`, the hypothesis of the partial variant `SingleSourceTheoremFlatStmt`);
* `flatEff_of_tiltedFlat`: the author's "tilted" range `tr M + E η(0) > 2d - 1` meets every line, so
  flatness on it (`TiltedFlatEff`) is `FlatEff`;
* `flatEff_of_flat_on_neg`, `flatEff_of_flat_on_nonneg`: the ranges `F̄_η(M) < 0` (used by the
  supersolution step of Theorem 9.2) and `F̄_η(M) ≥ 0` (used by the minimality step) also meet every
  line, so flatness there is again `FlatEff`.

So no restriction of the flatness hypothesis to one of these ranges weakens it.
-/

noncomputable section

open MeasureTheory

namespace RandomSandpile

open EffectiveOperatorBasic

variable {d : ℕ}

/-- `F̄_η` is *flat* at `M`: `μ(F̄_η(M), M) = μ*(F̄_η(M), M) = 0` (the conclusion of Lemma 7.5). -/
def FlatAt (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  muBar E (effOp E M) M = 0 ∧ muStarBar E (effOp E M) M = 0

theorem flatEff_iff_forall_flatAt (E : RandomEnvironment d) :
    FlatEff E ↔ ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → FlatAt E M :=
  Iff.rfl

/-- Flatness is invariant under `M ↦ M + tI`. -/
theorem flatAt_add_smul_one_iff (hd : 2 ≤ d) (E : RandomEnvironment d)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (t : ℝ) :
    FlatAt E (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) ↔ FlatAt E M := by
  have h1 := effOp_add_smul_one muConvergence_unconditional hd E hM t
  obtain ⟨h2, h3⟩ := muBar_shift muShift (by omega) E (effOp E (M + t • 1)) t M
  have h4 : effOp E (M + t • 1) + d * t = effOp E M := by rw [h1]; ring
  rw [h4] at h2 h3
  simp only [FlatAt, h2, h3]

/-- Flatness at one point of every line `M + ℝ I` is flatness everywhere. -/
theorem flatEff_of_line (hd : 2 ≤ d) (E : RandomEnvironment d)
    (h : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm →
      ∃ t : ℝ, FlatAt E (M + t • (1 : Matrix (Fin d) (Fin d) ℝ))) :
    FlatEff E := fun M hM => by
  obtain ⟨t, ht⟩ := h M hM
  exact (flatAt_add_smul_one_iff hd E hM t).1 ht

theorem isSymm_add_smul_one {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (t : ℝ) :
    (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
  hM.add (Matrix.isSymm_one.smul t)

theorem trace_add_smul_one (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)).trace = M.trace + d * t := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    mul_comm]

/-- **Tilted flatness**: flatness at every symmetric `M`
whose tilted configuration `η + Δ q_M` has high density, `tr M + E η(0) > 2d - 1`. -/
def TiltedFlatEff (E : RandomEnvironment d) : Prop :=
  ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → 2 * (d : ℝ) - 1 < M.trace + meanEta E.P →
    FlatAt E M

/-- Tilted flatness is flatness everywhere: the tilted range meets every line `M + ℝ I`. -/
theorem flatEff_of_tiltedFlat (hd : 2 ≤ d) (E : RandomEnvironment d) (h : TiltedFlatEff E) :
    FlatEff E := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine flatEff_of_line hd E fun M hM => ?_
  refine ⟨(2 * (d : ℝ) - M.trace - meanEta E.P) / d, h _ (isSymm_add_smul_one hM _) ?_⟩
  rw [trace_add_smul_one, mul_div_cancel₀ _ hd0.ne']
  linarith

theorem tiltedFlat_iff_flatEff (hd : 2 ≤ d) (E : RandomEnvironment d) :
    TiltedFlatEff E ↔ FlatEff E :=
  ⟨flatEff_of_tiltedFlat hd E, fun h M hM _ => h M hM⟩

/-- Flatness on `{M : F̄_η(M) < 0}` (the matrices at which the supersolution step of Theorem 9.2
uses it) is flatness everywhere. -/
theorem flatEff_of_flat_on_neg (hd : 2 ≤ d) (E : RandomEnvironment d)
    (h : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → effOp E M < 0 → FlatAt E M) :
    FlatEff E := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine flatEff_of_line hd E fun M hM => ?_
  refine ⟨(|effOp E M| + 1) / d, h _ (isSymm_add_smul_one hM _) ?_⟩
  rw [effOp_add_smul_one muConvergence_unconditional hd E hM, mul_div_cancel₀ _ hd0.ne']
  linarith [le_abs_self (effOp E M)]

/-- Flatness on `{M : F̄_η(M) ≥ 0}` (the matrices at which the minimality step of Theorem 9.2 uses
it) is flatness everywhere. -/
theorem flatEff_of_flat_on_nonneg (hd : 2 ≤ d) (E : RandomEnvironment d)
    (h : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → 0 ≤ effOp E M → FlatAt E M) :
    FlatEff E := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine flatEff_of_line hd E fun M hM => ?_
  refine ⟨-(|effOp E M| + 1) / d, h _ (isSymm_add_smul_one hM _) ?_⟩
  rw [effOp_add_smul_one muConvergence_unconditional hd E hM, mul_div_cancel₀ _ hd0.ne']
  linarith [neg_abs_le (effOp E M)]

end RandomSandpile

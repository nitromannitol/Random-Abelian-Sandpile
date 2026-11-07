import RandomSandpile.Proofs.Sec9.RecurrentElliptic
import RandomSandpile.Proofs.Sec9.RecurrentSymmetric

/-! Continuity, ellipticity and trace shift of the recurrent effective operator. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal
noncomputable section
namespace RandomSandpile
open EffectiveOperatorBasic MuLipschitzShell
variable {d : ℕ}

/-- The recurrent operator depends only on the symmetric part of a matrix. -/
theorem effOpRecurrent_symmPart (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    effOpRecurrent E (symmPart M) = effOpRecurrent E M := by
  simp only [effOpRecurrent, muRecurrentBar_symmPart, muStarRecurrentBar_symmPart]

/-- The trace shift and ellipticity give the operator-norm continuity estimate. -/
theorem effOpRecurrent_ge_sub (hd : 2 ≤ d) (E : RandomEnvironment d)
    {M N : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (hN : N.IsSymm) :
    effOpRecurrent E M - d * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (M - N)‖ ≤
      effOpRecurrent E N := by
  let t := ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (M - N)‖
  have hA : (M - N + t • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef :=
    posSemidef_add_smul_one (hM.sub hN)
  have hsym : (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    hM.add (Matrix.isSymm_one.smul t)
  have hdiff : (M + t • (1 : Matrix (Fin d) (Fin d) ℝ)) - N =
      M - N + t • (1 : Matrix (Fin d) (Fin d) ℝ) := by abel
  have h := recurrent_degenerateElliptic hd E N (M + t • 1) hN hsym (hdiff ▸ hA)
  rw [effOpRecurrent_shift hd E M t] at h
  exact h

/-- The recurrent operator has a global estimate on symmetric parts. -/
theorem effOpRecurrent_abs_sub_le (hd : 2 ≤ d) (E : RandomEnvironment d)
    (M N : Matrix (Fin d) (Fin d) ℝ) :
    |effOpRecurrent E M - effOpRecurrent E N| ≤
      d * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (symmPart M - symmPart N)‖ := by
  have h1 := effOpRecurrent_ge_sub hd E (symmPart_isSymm M) (symmPart_isSymm N)
  have h2 := effOpRecurrent_ge_sub hd E (symmPart_isSymm N) (symmPart_isSymm M)
  have hnorm : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (symmPart N - symmPart M)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (symmPart M - symmPart N)‖ := by
    rw [← neg_sub, map_neg, norm_neg]
  rw [effOpRecurrent_symmPart, effOpRecurrent_symmPart] at h1 h2
  rw [hnorm] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The recurrent effective operator is continuous on all real matrices. -/
theorem continuous_effOpRecurrent (hd : 2 ≤ d) (E : RandomEnvironment d) :
    Continuous (effOpRecurrent E) := by
  have hsym : Continuous (symmPart : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
    unfold symmPart
    have hid : Continuous (id : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := continuous_id
    exact (continuous_const : Continuous (fun _ : Matrix (Fin d) (Fin d) ℝ => (1 / 2 : ℝ))).smul
      (hid.add hid.matrix_transpose)
  have hmap : Continuous (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  apply continuous_iff_continuousAt.mpr
  intro M
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun N : Matrix (Fin d) (Fin d) ℝ =>
      (d : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (symmPart N - symmPart M)‖)
      (𝓝 M) (𝓝 0) := by
    have hcont : Continuous (fun N : Matrix (Fin d) (Fin d) ℝ =>
        (d : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
          (symmPart N - symmPart M)‖) :=
      continuous_const.mul ((hmap.comp (hsym.sub continuous_const)).norm)
    simpa using hcont.tendsto M
  refine squeeze_zero (fun N => norm_nonneg _) ?_ ht
  intro N
  simpa [Real.norm_eq_abs] using effOpRecurrent_abs_sub_le hd E N M

/-- The basic recurrent operator properties in correction C13. -/
theorem recurrentOperatorBasic : RecurrentOperatorBasicStmt := by
  intro d hd E
  exact ⟨continuous_effOpRecurrent hd E, recurrent_degenerateElliptic hd E,
    fun M t => effOpRecurrent_shift hd E M t⟩

end RandomSandpile

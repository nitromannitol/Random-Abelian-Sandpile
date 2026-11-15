import RandomSandpile.Proofs.HessianAdapterDefs

/-!
# The `L^p` row estimate from the ERL `L^p` estimate

This file derives the row estimate `LocalUnitVecStmt` from four inputs: the ERL interior `L^p`
estimate for `a = 1` (`ErlLpStmt`), the identification of `∂ᵢ w` as an `H¹` function on the unit
ball (`SmoothH1Stmt`), its weak equation with `F = -(Δ w) eᵢ` (`SmoothEqStmt`) and the `L²` bound
for the rows of the Hessian (`L2HessVecStmt`). The `L²` norms on the finite-measure ball `B_{4/3}`
are bounded by finite multiples of the `L^p` and `L^∞` norms there.
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal

namespace HessianAdapter

open PDE

/-- The Euclidean norm of `c eᵢ` is `|c|`. -/
theorem vecEuclideanNorm_pi_single {d : ℕ} (i : Fin d) (c : ℝ) :
    vecEuclideanNorm (Pi.single i c : Vec d) = |c| := by
  unfold vecEuclideanNorm vecNormSq vecDot
  simp [Pi.single_apply, Real.sqrt_mul_self_eq_abs]

/-- On `B_{4/3}`, the `L²` norm is bounded by a finite multiple of the `L^q` norm for `2 ≤ q`. -/
theorem exists_eLpNorm_two_le_mul (d : ℕ) {q : ℝ≥0∞} (hq : 2 ≤ q) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ f : Vec d → ℝ,
      eLpNorm f 2 (volumeOn (euclideanBall (0 : Vec d) (4 / 3))) ≤
        eLpNorm f q (volumeOn (euclideanBall (0 : Vec d) (4 / 3))) * c := by
  refine ⟨volumeOn (euclideanBall (0 : Vec d) (4 / 3)) Set.univ ^
      (1 / (2 : ℝ≥0∞).toReal - 1 / q.toReal), ?_,
    fun f => eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hq (by norm_num)⟩
  have hexp : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / q.toReal := by
    rcases eq_or_ne q ⊤ with rfl | hqt
    · simp
    · have h2q : (2 : ℝ) ≤ q.toReal := by simpa using ENNReal.toReal_mono hqt hq
      have h : 1 / q.toReal ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2q
      simp only [ENNReal.toReal_ofNat]
      linarith
  refine ENNReal.rpow_ne_top_of_nonneg hexp ?_
  rw [Measure.restrict_apply_univ]
  exact volume_euclideanBall_ne_top 0 (by norm_num)

/-- The `L^p` row estimate `LocalUnitVecStmt` follows from the ERL `L^p` estimate, the `H¹`
identification of `∂ᵢ w`, its weak equation and the `L²` bound for the rows of the Hessian. -/
theorem L7_apply_erl (d : ℕ) (hE : ErlLpStmt d) (hH : SmoothH1Stmt d) (hQ : SmoothEqStmt d)
    (hL : L2HessVecStmt d) : LocalUnitVecStmt d := by
  intro p hp2 hptop
  have hq : (2 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hptop hp2
  have hpq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop
  obtain ⟨K₁, hK₁, hE'⟩ := hE p.toReal hq
  obtain ⟨C₂, hC₂, hL'⟩ := hL
  obtain ⟨c₁, hc₁, hA⟩ := exists_eLpNorm_two_le_mul d hp2
  obtain ⟨c₂, hc₂, hW⟩ := exists_eLpNorm_two_le_mul d (le_top : (2 : ℝ≥0∞) ≤ ⊤)
  refine ⟨K₁ * (C₂ * (c₁ + c₂) + 1),
    ENNReal.mul_ne_top hK₁ (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hC₂ (ENNReal.add_ne_top.2 ⟨hc₁, hc₂⟩), ENNReal.one_ne_top⟩), ?_⟩
  intro w hw _ i
  obtain ⟨u, hu, hgrad⟩ := hH w hw i
  obtain ⟨hFm, hFLp, hsol⟩ := hQ w hw i u hu hgrad
  have h1 := hE' u (fun x => Pi.single i (-lapVec w x)) hFm (hFLp _) hsol
  rw [hpq, hgrad] at h1
  have hF : eLpNorm (fun x => vecEuclideanNorm (Pi.single i (-lapVec w x) : Vec d)) p
      (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
      eLpNorm (lapVec w) p (volumeOn (euclideanBall (0 : Vec d) (4 / 3))) := by
    refine (eLpNorm_mono (hFLp p).aestronglyMeasurable fun x => ?_).trans
      (eLpNorm_mono_measure _ (Measure.restrict_mono
        (euclideanBall_mono (by norm_num) (by norm_num)) le_rfl))
    simp [vecEuclideanNorm_pi_single]
  set A := eLpNorm (lapVec w) p (volumeOn (euclideanBall (0 : Vec d) (4 / 3)))
  set W := eLpNorm w ⊤ (volumeOn (euclideanBall (0 : Vec d) (4 / 3)))
  have key : A * c₁ + W * c₂ ≤ (c₁ + c₂) * (A + W) :=
    calc A * c₁ + W * c₂ ≤ A * c₁ + W * c₂ + (A * c₂ + W * c₁) := le_self_add
      _ = (c₁ + c₂) * (A + W) := by ring
  calc _ ≤ _ := h1
    _ ≤ K₁ * (C₂ * (A * c₁ + W * c₂) + A) := by
      gcongr
      exact (hL' w hw i).trans (by gcongr; exacts [hA _, hW _])
    _ ≤ K₁ * (C₂ * ((c₁ + c₂) * (A + W)) + (A + W)) := by
      gcongr
      exact le_self_add
    _ = K₁ * (C₂ * (c₁ + c₂) + 1) * (A + W) := by ring

end HessianAdapter

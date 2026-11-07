import RandomSandpile.Steps.Sec6.StrictConcavity

/-! # Lemma 6.2 (`β`-dependent form): proofs of the steps

* `ballCount : BallCountStmt`: lattice-point counting in Euclidean balls,
  `|B_{βn}| / |B_n| → β^d`. It is derived from Mathlib's
  `ZLattice.covolume.tendsto_card_div_pow'`, applied to the integer lattice
  `ℤ^d = span_ℤ (standard basis)` and the balls `ball(0, β)`, `ball(0, 1)`, whose frontiers (spheres)
  are null.
* `strictConcavityBeta_of_bending`: the `β`-dependent Lemma 6.2 (`StrictConcavityBetaStmt`) from
  Lemma 6.2' (`NearMaxBendingStmt`) and the shell estimate (`ShellBoundStmt`). -/

open MeasureTheory LatticeProb Filter Metric Module
open scoped Topology Pointwise

namespace RandomSandpile

namespace BallCount

open MuLipschitz

variable {d : ℕ}

/-- The integer lattice `ℤ^d ⊂ ℝ^d`, the `ℤ`-span of the standard basis. -/
abbrev intLattice (d : ℕ) : Submodule ℤ (Rd d) :=
  Submodule.span ℤ (Set.range (PiLp.basisFun 2 ℝ (Fin d)))

theorem mem_intLattice {v : Rd d} : v ∈ intLattice d ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = v i := by
  rw [Basis.mem_span_iff_repr_mem]
  simp [PiLp.basisFun_repr]

theorem toE_injective' : Function.Injective (toE (d := d)) := fun x y h => by
  funext i
  have := congrArg (fun v : Rd d => v i) h
  simpa [toE_apply] using this

/-- The lattice points of `ball(0, r)` at scale `1/n` are the rescaled points of `B_{rn}`. -/
theorem card_ball_inter_eq {n : ℕ} (hn : 1 ≤ n) (r : ℝ) :
    Nat.card ↥(ball (0 : Rd d) r ∩ (n : ℝ)⁻¹ • (intLattice d : Set (Rd d))) =
      (ballZ0 (d := d) (r * n)).ncard := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.card_coe_set_eq]
  have hset : ball (0 : Rd d) r ∩ (n : ℝ)⁻¹ • (intLattice d : Set (Rd d)) =
      (fun z : Site d => (n : ℝ)⁻¹ • toE z) '' ballZ0 (r * n) := by
    ext v
    rw [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hn0.ne'), inv_inv,
      SetLike.mem_coe, mem_intLattice, mem_ball_zero_iff]
    constructor
    · rintro ⟨hv, hL⟩
      choose k hk using hL
      have hz : toE k = (n : ℝ) • v := by
        ext i
        simp [toE_apply, hk i]
      refine ⟨k, mem_ballZ0.2 ?_, ?_⟩
      · rw [hz, norm_smul, Real.norm_natCast]
        nlinarith
      · simp only [hz, smul_smul, inv_mul_cancel₀ hn0.ne', one_smul]
    · rintro ⟨z, hz, rfl⟩
      have hz' := mem_ballZ0.1 hz
      refine ⟨?_, fun i => ⟨z i, ?_⟩⟩
      · rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hn0]
        linarith
      · simp [smul_smul, mul_inv_cancel₀ hn0.ne', toE_apply]
  rw [hset]
  exact Set.ncard_image_of_injective _
    ((smul_right_injective _ (inv_ne_zero hn0.ne')).comp toE_injective')

/-- `|B_{rn}| / n^d → |ball(0, r)| / covol(ℤ^d)`. -/
theorem tendsto_ncard_div_pow (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => ((ballZ0 (d := d) (r * n)).ncard : ℝ) / (n : ℝ) ^ d) atTop
      (𝓝 (volume.real (ball (0 : Rd d) r) / ZLattice.covolume (intLattice d))) := by
  haveI : NeZero d := ⟨by omega⟩
  have h := ZLattice.covolume.tendsto_card_div_pow' (intLattice d) (s := ball (0 : Rd d) r)
    isBounded_ball measurableSet_ball
    (by rw [frontier_ball 0 hr.ne']; exact Measure.addHaar_sphere _ _ _)
  rw [finrank_euclideanSpace_fin] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [card_ball_inter_eq hn r]

end BallCount

open BallCount in
/-- **Lattice-point counting in balls**: `|B_{βn}| / |B_n| → β^d`. -/
theorem ballCount : BallCountStmt := by
  intro d hd β hβ
  haveI : NeZero d := ⟨by omega⟩
  have h1 := tendsto_ncard_div_pow hd hβ
  have h2 := tendsto_ncard_div_pow hd one_pos
  simp only [one_mul] at h2
  have hcov := ZLattice.covolume_pos (intLattice d)
  have hvol1 : 0 < volume.real (ball (0 : Rd d) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hvolβ : volume.real (ball (0 : Rd d) β) = β ^ d * volume.real (ball (0 : Rd d) 1) := by
    rw [measureReal_def, Measure.addHaar_ball _ _ hβ.le, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hβ.le d), measureReal_def]
  have hlim := h1.div h2 (div_pos hvol1 hcov).ne'
  have heq : volume.real (ball (0 : Rd d) β) / ZLattice.covolume (intLattice d) /
      (volume.real (ball (0 : Rd d) 1) / ZLattice.covolume (intLattice d)) = β ^ d := by
    rw [hvolβ]
    field_simp
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnd : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (by exact_mod_cast hn) d
  simp only [Pi.div_apply]
  field_simp

/-- **Lemma 6.2, `β`-dependent form, from Lemma 6.2' and the shell estimate.** -/
theorem strictConcavityBeta_of_bending (hbend : NearMaxBendingStmt) (hshell : ShellBoundStmt) :
    StrictConcavityBetaStmt :=
  strictConcavityBeta_of_steps hbend hshell ballCount

end RandomSandpile

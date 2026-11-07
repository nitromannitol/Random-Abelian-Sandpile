import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlat
import RandomSandpile.Infra.SupConvolution

/-!
# Operator fact (11): from and

`stableQuadApprox_of_steps`: `StableQuadApproxStmt` from the flat correctors for `F*(A) = 0`
(`FlatCorrectorStmt`) and the integer concave correction `ψ_s` (`IntegerConcaveStmt`). For
`F*(A) > 0` put `s = F*(A)/d` and `Q = A + sI`, so `F*(Q) = 0`; the correctors `v` of `Q` plus `ψ_s`
are stabilizing (`Δψ_s ≤ 0`) and `v + ψ_s - q_A - c - D/2 = (v - q_Q - c) + (ψ_s + s|z|²/2 - D/2)`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

theorem lap_add_apply (u v : Site d → ℤ) (x : Site d) : lap (u + v) x = lap u x + lap v x := by
  simp only [lap, nbrSumZ, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem stableQuadApprox_of_steps (hflat : FlatCorrectorStmt) (hψ : IntegerConcaveStmt) :
    StableQuadApproxStmt := by
  intro d hd E hE A hA hF
  have hE1 : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hE]; omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rcases hF.eq_or_lt with h0 | hpos
  · exact hflat d hd E hE A hA h0.symm
  · set s : ℝ := effOpStar E A / d with hs
    have hs0 : 0 < s := by positivity
    set Q : Matrix (Fin d) (Fin d) ℝ := A + s • (1 : Matrix (Fin d) (Fin d) ℝ) with hQ
    have hQs : Q.IsSymm := hA.add (Matrix.isSymm_one.smul _)
    have hFQ : effOpStar E Q = 0 := by
      rw [hQ, effOpStar_add_smul_one (by omega) E hE1 hA, hs]
      field_simp
      ring
    obtain ⟨ψ, hψlap, hψb⟩ := hψ d (by omega) s hs0
    set D : ℝ := d / (8 * s) + 1 with hD
    have hD0 : 0 < D := by rw [hD]; positivity
    filter_upwards [hflat d hd E hE Q hQs hFQ] with η hη ε hε
    obtain ⟨R₀, hR₀⟩ := hη (ε / 2) (by positivity)
    refine ⟨max R₀ ⌈D / ε⌉₊ + 1, fun R hR => ?_⟩
    have hR1 : R₀ ≤ R := by omega
    have hR2 : D / ε ≤ R := by
      have : ⌈D / ε⌉₊ ≤ R := by omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast this)
    have hR3 : (1 : ℝ) ≤ R := by
      have : 1 ≤ R := by omega
      exact_mod_cast this
    obtain ⟨v, c, hv1, hv2⟩ := hR₀ R hR1
    refine ⟨v + ψ, c + D / 2, fun x hx => ?_, fun z hz => ?_⟩
    · rw [lap_add_apply]
      linarith [hv1 x hx, hψlap x]
    · have a := hv2 z hz
      have b := hψb z
      have hq : qMZ Q z = qMZ A z + s / 2 * ‖toE z‖ ^ 2 := by
        simp only [qMZ, hQ, qM_add_smul_one]
      have hDR : D ≤ ε * R := by
        have := (div_le_iff₀ hε).1 hR2
        linarith
      have hRR : (R : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
      have hDR2 : D ≤ ε * (R : ℝ) ^ 2 := by nlinarith
      rw [abs_le] at a ⊢
      simp only [Pi.add_apply, Int.cast_add]
      constructor <;> nlinarith [a.1, a.2, b.1, b.2]

end SingleSourceH0

end RandomSandpile

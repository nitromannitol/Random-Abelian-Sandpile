import RandomSandpile.Proofs.Sec9.RecurrentCompactnessLap
import RandomSandpile.Proofs.Sec9.RecurrentCompactnessEquicontAA

/-! # Compactness from local estimates on the single-source corrector

The final Arzelà–Ascoli passage is adapted from `SingleSourceCompactness.lean`.
-/

noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

/-- Local corrector bounds and asymptotic equicontinuity give a continuous regular part. -/
theorem recurrent_compactness_of_corrector_equicontinuity {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (nk : ℕ → ℕ) (hnk : StrictMono nk) (κ C1 R1 : ℝ)
    (hR1 : 1 ≤ R1)
    (hasymp : ∀ z : Site d, R1 ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C1 * ‖toE z‖ ^ (-(d : ℝ)))
    (hK : ∀ m : ℕ, ∃ K : ℝ, ∀ (j : ℕ) (x : Rd d), ‖x‖ ≤ m →
      |ssCorrector d η κ (nk (j + 1)) x| ≤ K)
    (hE : ∀ m : ℕ, ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ,
      ∀ j ≥ N, ∀ (x y : Rd d), ‖x‖ ≤ m → ‖y‖ ≤ m → dist x y < δ →
      |ssCorrector d η κ (nk (j + 1)) x - ssCorrector d η κ (nk (j + 1)) y| < ε) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ v : Rd d → ℝ, Continuous v ∧
      TendstoLocallyUniformlyOn
        (fun j => rescaleSingleSource (singleSourceOdometer η (nk (ψ j))) (nk (ψ j)))
        (fun x => v x + fundamentalSolution d x) atTop {x : Rd d | x ≠ 0} := by
  set F : ℕ → Rd d → ℝ := fun j => ssCorrector d η κ (nk (j + 1)) with hF
  have hnkT : Tendsto (fun j => nk (j + 1)) atTop atTop :=
    hnk.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨φ, hφ, V, hV, hTLU⟩ :=
    arzelaAscoli_locallyUniform_of_asymptoticEquicontinuous d F hK hE
  refine ⟨fun j => φ j + 1, fun a b hab => Nat.add_lt_add_right (hφ hab) 1, V, hV, ?_⟩
  beta_reduce
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ne]
  intro K hKs hKc
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hU := Metric.tendstoUniformlyOn_iff.1
    ((tendstoLocallyUniformly_iff_forall_isCompact.1 hTLU) K hKc) (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := ssGreenErr_small hd hR1 hasymp hKc (fun x hx => hKs hx)
    (by positivity : 0 < ε / 2)
  have hev : ∀ᶠ j in atTop, N ≤ nk (φ j + 1) :=
    (hnkT.comp hφ.tendsto_atTop).eventually_ge_atTop N
  filter_upwards [hU, hev] with j hj hjN x hx
  have h1 : |V x - ssCorrector d η κ (nk (φ j + 1)) x| < ε / 2 := by
    have := hj x hx
    rwa [Real.dist_eq] at this
  have h2 := hN _ hjN x hx
  rw [rescale_eq η κ (nk (φ j + 1)) x, Real.dist_eq]
  calc |V x + fundamentalSolution d x - (ssCorrector d η κ (nk (φ j + 1)) x
        + ssGreenErr d κ (nk (φ j + 1)) x + fundamentalSolution d x)|
      = |(V x - ssCorrector d η κ (nk (φ j + 1)) x) - ssGreenErr d κ (nk (φ j + 1)) x| := by
        congr 1; ring
    _ ≤ |V x - ssCorrector d η κ (nk (φ j + 1)) x| + |ssGreenErr d κ (nk (φ j + 1)) x| :=
        abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end RandomSandpile

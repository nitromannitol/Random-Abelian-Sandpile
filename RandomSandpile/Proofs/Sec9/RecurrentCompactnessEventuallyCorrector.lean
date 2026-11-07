import RandomSandpile.Proofs.Sec9.RecurrentCompactnessLap
import RandomSandpile.Proofs.Sec9.RecurrentCompactnessEventuallyAA
import RandomSandpile.Proofs.Sec9.RecurrentCompactnessAnchor
import RandomSandpile.Steps.Sec9.Recurrent
import LatticeProb.Prob.KolmogorovPi

/-! # Compactness from local estimates on the single-source corrector

The final Arzelà–Ascoli passage is adapted from `SingleSourceCompactness.lean`.
-/

noncomputable section
open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

/-- An eventually bounded anchor and a local asymptotic modulus bound every
closed ball eventually, by chaining through its convex hull. -/
theorem eventual_local_bounds_of_anchor {d : ℕ} (F : ℕ → Rd d → ℝ) (x₀ : Rd d) (B : ℝ)
    (hB : ∀ᶠ j : ℕ in atTop, |F j x₀| ≤ B)
    (hE : ∀ m : ℕ, ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ,
      ∀ j ≥ N, ∀ x y, ‖x‖ ≤ m → ‖y‖ ≤ m → dist x y < δ → |F j x - F j y| < ε) :
    ∀ m : ℕ, ∃ K : ℝ, ∃ N : ℕ, ∀ j ≥ N, ∀ x, ‖x‖ ≤ m → |F j x| ≤ K := by
  intro m
  let M := max m ⌈‖x₀‖⌉₊
  obtain ⟨δ, hδ, N, hN⟩ := hE M 1 zero_lt_one
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hB
  let L : ℕ := ⌈((m : ℝ) + ‖x₀‖) / δ⌉₊ + 1
  have hL : 0 < L := by dsimp [L]; omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep : ((m : ℝ) + ‖x₀‖) / (L : ℝ) < δ := by
    have hceil := Nat.le_ceil (((m : ℝ) + ‖x₀‖) / δ)
    have hlt : (((m : ℝ) + ‖x₀‖) / δ) < L := by
      dsimp [L]; push_cast; linarith
    rw [div_lt_iff₀ hLr]
    have := (div_lt_iff₀ hδ).1 hlt
    nlinarith
  refine ⟨B + L, max N N₀, ?_⟩
  intro j hj x hx
  have hxM : ‖x‖ ≤ (M : ℝ) := hx.trans (by exact_mod_cast le_max_left m ⌈‖x₀‖⌉₊)
  have hx₀M : ‖x₀‖ ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right m ⌈‖x₀‖⌉₊)
  have hdist : dist x₀ x / (L : ℝ) < δ := by
    have hd := dist_le_norm_add_norm x₀ x
    have hbound : dist x₀ x ≤ (m : ℝ) + ‖x₀‖ := by linarith
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right hbound hLr.le) hstep
  have hmod : ∀ u ∈ Metric.closedBall (0 : Rd d) M, ∀ v ∈ Metric.closedBall (0 : Rd d) M,
      dist u v < δ → |F j u - F j v| ≤ 1 := by
    intro u hu v hv huv
    exact (hN j (le_trans (le_max_left _ _) hj) u v
      (mem_closedBall_zero_iff.1 hu) (mem_closedBall_zero_iff.1 hv) huv).le
  have hchain := LatticeProb.abs_sub_le_of_modulus_on_convex
    (convex_closedBall (0 : Rd d) M) (mem_closedBall_zero_iff.2 hx₀M)
    (mem_closedBall_zero_iff.2 hxM) hL hdist hmod
  have htri : |F j x| ≤ |F j x - F j x₀| + |F j x₀| := by
    have := abs_add_le (F j x - F j x₀) (F j x₀)
    simpa using this
  linarith [hN₀ j (le_trans (le_max_right _ _) hj)]

/-- Local corrector bounds and asymptotic equicontinuity give a continuous regular part. -/
theorem recurrent_compactness_of_corrector_eventual_bounds {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (nk : ℕ → ℕ) (hnk : StrictMono nk) (κ C1 R1 : ℝ)
    (hR1 : 1 ≤ R1)
    (hasymp : ∀ z : Site d, R1 ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C1 * ‖toE z‖ ^ (-(d : ℝ)))
    (hK : ∀ m : ℕ, ∃ K : ℝ, ∃ N : ℕ, ∀ j ≥ N, ∀ (x : Rd d), ‖x‖ ≤ m →
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
    arzelaAscoli_locallyUniform_of_eventualBounds d F hK hE
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

/-- Vanishing tails and asymptotic corrector equicontinuity imply compactness. -/
theorem recurrent_compactness_of_tail_equicontinuity {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (htail : SingleSourceVanishingTail η)
    (nk : ℕ → ℕ) (hnk : StrictMono nk) (κ C Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ)))
    (hE : ∀ m : ℕ, ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ,
      ∀ j ≥ N, ∀ (x y : Rd d), ‖x‖ ≤ m → ‖y‖ ≤ m → dist x y < δ →
      |ssCorrector d η κ (nk (j + 1)) x - ssCorrector d η κ (nk (j + 1)) y| < ε) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ v : Rd d → ℝ, Continuous v ∧
      TendstoLocallyUniformlyOn
        (fun j => rescaleSingleSource (singleSourceOdometer η (nk (ψ j))) (nk (ψ j)))
        (fun x => v x + fundamentalSolution d x) atTop {x : Rd d | x ≠ 0} := by
  obtain ⟨x₀, _, B, hB⟩ := recurrent_corrector_anchor hd η htail κ C Rg hRg hasymp
  have hnkT : Tendsto (fun j => nk (j + 1)) atTop atTop :=
    hnk.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hK := eventual_local_bounds_of_anchor (fun j => ssCorrector d η κ (nk (j + 1)))
    x₀ B (hnkT.eventually hB) hE
  exact recurrent_compactness_of_corrector_eventual_bounds hd η nk hnk κ C Rg hRg hasymp hK hE

/-- Asymptotic local equicontinuity of recurrent single-source correctors. -/
def RecurrentCorrectorEquicontinuityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
    ∀ᵐ η ∂E.P, SingleSourceFinite η → SingleSourceVanishingTail η →
      ∀ (nk : ℕ → ℕ), StrictMono nk → ∀ κ : ℝ, ∀ m : ℕ, ∀ ε > 0,
        ∃ δ > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x y : Rd d,
          ‖x‖ ≤ m → ‖y‖ ≤ m → dist x y < δ →
          |ssCorrector d η κ (nk (j + 1)) x - ssCorrector d η κ (nk (j + 1)) y| < ε

/-- The recurrent compactness step reduces to corrector equicontinuity. -/
theorem recurrentSSCompactness_of_corrector_equicontinuity
    (h : RecurrentCorrectorEquicontinuityStmt) : RecurrentSSCompactnessStmt := by
  intro d hd E
  obtain ⟨κ, C, Rg, hRg, hasymp⟩ := ssGreen_asymp hd
  filter_upwards [h d hd E] with η hη
  intro hfinite htail nk hnk
  exact recurrent_compactness_of_tail_equicontinuity hd η htail nk hnk κ C Rg hRg hasymp
    (hη hfinite htail nk hnk κ)

end RandomSandpile

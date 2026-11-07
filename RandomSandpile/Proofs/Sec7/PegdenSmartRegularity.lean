import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityHessianTrace

/-!
# Lemma 7.6 (regularity; Pegden-Smart): assembly

`pegdenSmartRegularity_of_touching`: `PegdenSmartRegularityStmt` from Pegden-Smart's
Proposition 2.5 (`PegdenSmartTouchingStmt`, part 1, a literature input) and the three remaining
steps of `RandomSandpile/Steps/Sec7/PegdenSmartRegularity.lean`: `FreeOdometerLimitRegularStmt`,
`LipschitzDomainFrontierNullStmt` (part 1) and `FreeOdometerLimitHessianTraceStmt` (part 3). The
steps `PegdenSmartIntegerSuperharmonicStmt` (Lemma 4.1, part 2) and
`IntegerSuperharmonicOfTraceStmt` (Rossin's observation, part 3) are proved
(`pegdenSmartIntegerSuperharmonic`, `integerSuperharmonicOfTrace`).

Parts 2 and 3 hold for every uniform limit of rescaled free odometers, hence for `v'` as well as for
`v`: `pegdenSmart_part2` and `pegdenSmart_part3_of_hessianTrace`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter

namespace RandomSandpile

open PegdenSmartRegularity

/-- **Lemma 7.6(2)** for every uniform limit `v` of rescaled free odometers (any `η`, any `W`), at
every `a ∉ W̄` where `v` has a second-order Peano expansion with symmetric `X`. -/
theorem pegdenSmart_part2 {d : ℕ} (hd : 2 ≤ d) {W : Set (Rd d)} (η : Config d) {nk : ℕ → ℕ}
    (hnk : StrictMono nk) {v : Rd d → ℝ}
    (hv : TendstoUniformly
      (fun k => rescaleOdo (freeOdometer η (discretize W (nk k))) (nk k)) v atTop)
    {a : Rd d} (ha : a ∉ closure W) {p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ} (hX : X.IsSymm)
    (hTay : HasSecondOrderTaylorAt v a p X) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : Site d → ℤ, ∀ x : Site d, lap u x ≤ 2 * (d : ℤ) - 1 ∧
      qMZ (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ (u x : ℝ) :=
  pegdenSmart_part2_of_steps pegdenSmartIntegerSuperharmonic hd η hnk hv ha hX hTay ε hε

/-- **Lemma 7.6(3)** for every uniform limit `v` of rescaled free odometers of `η ∈ Ω₁`, at every
`a ∈ W` where `v` has a second-order Peano expansion with symmetric `X`, from the Hessian trace
step; `u ≥ q_{X - εI}` holds on all of `ℤ^d`. -/
theorem pegdenSmart_part3_of_hessianTrace (htrace : FreeOdometerLimitHessianTraceStmt) (d : ℕ)
    (hd : 2 ≤ d) (E : RandomEnvironment d) (hHD : HighDensity E.P) (W : Set (Rd d))
    (hW : IsLipschitzDomain W) :
    ∃ Ω₁ : Set (Config d), E.P Ω₁ᶜ = 0 ∧ ∀ η ∈ Ω₁, ∀ nk : ℕ → ℕ, StrictMono nk →
      ∀ v : Rd d → ℝ,
        TendstoUniformly
          (fun k => rescaleOdo (freeOdometer η (discretize W (nk k))) (nk k)) v atTop →
        ∀ a ∈ W, ∀ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ), X.IsSymm →
          HasSecondOrderTaylorAt v a p X → ∀ ε : ℝ, 0 < ε → ∃ u : Site d → ℤ, ∀ x : Site d,
            lap u x ≤ 2 * (d : ℤ) - 1 ∧
              qMZ (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ (u x : ℝ) := by
  obtain ⟨Ω₁, hΩ₁, htr⟩ := htrace d hd E W hW
  refine ⟨Ω₁, hΩ₁, fun η hη nk hnk v hv a ha p X hX hTay ε hε => ?_⟩
  have h1 := htr η hη nk hnk v hv a ha p X hX hTay
  have hHD' : 2 * (d : ℝ) - 1 < meanEta E.P := hHD
  have h0 : (0 : ℝ) ≤ d := by positivity
  exact pegdenSmart_part3_of_trace integerSuperharmonicOfTrace hX (by linarith) ε hε

/-- **Lemma 7.6** from Pegden-Smart's Proposition 2.5 and the remaining steps. -/
theorem pegdenSmartRegularity_of_touching (hT : PegdenSmartTouchingStmt)
    (hreg : FreeOdometerLimitRegularStmt) (hnull : LipschitzDomainFrontierNullStmt)
    (htrace : FreeOdometerLimitHessianTraceStmt) : PegdenSmartRegularityStmt :=
  pegdenSmartRegularity_of_steps hT hreg hnull htrace pegdenSmartIntegerSuperharmonic
    integerSuperharmonicOfTrace

/-- **Lemma 7.6(3)** for every uniform limit of rescaled free odometers (unconditional): almost
surely, at every `a ∈ W` where the limit has a second-order Peano expansion with symmetric `X`,
there is `u : ℤ^d → ℤ` with `Δ_{ℤ^d} u ≤ 2d - 1` and `u ≥ q_{X - εI}` on all of `ℤ^d`. -/
theorem pegdenSmart_part3 (d : ℕ) (hd : 2 ≤ d) (E : RandomEnvironment d) (hHD : HighDensity E.P)
    (W : Set (Rd d)) (hW : IsLipschitzDomain W) :
    ∃ Ω₁ : Set (Config d), E.P Ω₁ᶜ = 0 ∧ ∀ η ∈ Ω₁, ∀ nk : ℕ → ℕ, StrictMono nk →
      ∀ v : Rd d → ℝ,
        TendstoUniformly
          (fun k => rescaleOdo (freeOdometer η (discretize W (nk k))) (nk k)) v atTop →
        ∀ a ∈ W, ∀ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ), X.IsSymm →
          HasSecondOrderTaylorAt v a p X → ∀ ε : ℝ, 0 < ε → ∃ u : Site d → ℤ, ∀ x : Site d,
            lap u x ≤ 2 * (d : ℤ) - 1 ∧
              qMZ (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ (u x : ℝ) :=
  pegdenSmart_part3_of_hessianTrace freeOdometerLimitHessianTrace d hd E hHD W hW

/-- **Lemma 7.6** from Pegden-Smart's Proposition 2.5 (`PegdenSmartTouchingStmt`) and the two
part 1 steps; parts 2 and 3 are proved. -/
theorem pegdenSmartRegularity_of_touching_regular (hT : PegdenSmartTouchingStmt)
    (hreg : FreeOdometerLimitRegularStmt) (hnull : LipschitzDomainFrontierNullStmt) :
    PegdenSmartRegularityStmt :=
  pegdenSmartRegularity_of_touching hT hreg hnull freeOdometerLimitHessianTrace

end RandomSandpile

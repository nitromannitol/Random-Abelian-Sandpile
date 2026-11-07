import RandomSandpile.Proofs.Sec9.SingleSourceH0Equal
import RandomSandpile.Proofs.Sec9.SingleSourceFstarFinal
import RandomSandpile.Proofs.Sec9.SingleSourceCompactness
import RandomSandpile.Proofs.Sec9.SingleSourceD2Main

/-!
# Theorem 9.2 for `d ≥ 3` with `H(0) = 0`

`singleSourceConclusion_of_star`: the conclusion of Theorem 9.2 for an environment with
`StabThresholdZero E` from the starred theorem (`SingleSourceTheoremStarStmt`) and the operator
facts `F̄ ≤ F*` (`effOpLeStar_gen`, proved) and `F̄ = F*` (`effOp_eq_effOpStar`, from (11)). Same
reduction as `singleSourceTheoremD2_of_star`: `F̄ ≤ F*` puts every member of the `F̄`-set in the
`F*`-set, so `v*` lies below it; `F̄ = F*` puts `v*` in the `F̄`-set.

`singleSourceTheoremH0`: `SingleSourceTheoremH0Stmt` from Fey-Levine-Peres (outer bound and
compactness), Alexandrov, Pegden-Smart Propositions 2.4-2.5 (with `ViscosityWeakLaplaceStmt`) and
(11) (`NonPosDefLegalFlatStmt`, the operator comparison).
-/

noncomputable section

open MeasureTheory Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

theorem singleSourceConclusion_of_star (hd : 2 ≤ d) (hStar : SingleSourceTheoremStarStmt)
    (h11 : NonPosDefLegalFlatStmt d) (E : RandomEnvironment d)
    (hE : E.ηmax = 2 * (d : ℤ) - 2) (hZ : StabThresholdZero E) : SingleSourceConclusion E := by
  obtain ⟨hleast, hae⟩ := hStar d hd E hE
  have hE1 : E.ηmax ≤ 2 * (d : ℤ) - 1 := by rw [hE]; omega
  have hmem : singleSourceObstacleSolutionStar E ∈ singleSourceObstacleSet E := by
    refine ⟨hleast.1.1, hleast.1.2.1, ?_⟩
    intro x hx φ hφ hmin
    have h := (viscFromBelowMuStar_iff (by omega) E hE1 _ _).1 hleast.1.2.2 x hx φ hφ hmin
    rw [effOp_eq_effOpStar hd h11 E hE hZ (hessian_isSymm_of_contDiffAt hφ)]
    exact h
  have hlow : singleSourceObstacleSolutionStar E ∈ lowerBounds (singleSourceObstacleSet E) := by
    intro w hw
    apply hleast.2
    refine ⟨hw.1, hw.2.1, ?_⟩
    rw [viscFromBelowMuStar_iff (by omega) E hE1]
    intro x hx φ hφ hmin
    exact (hw.2.2 x hx φ hφ hmin).trans
      (effOpLeStar_gen hd E (hessian_isSymm_of_contDiffAt hφ))
  have hL : IsLeast (singleSourceObstacleSet E) (singleSourceObstacleSolutionStar E) :=
    ⟨hmem, hlow⟩
  unfold SingleSourceConclusion
  rw [singleSourceObstacleSolution_eq_of_isLeast hL]
  exact ⟨hL, hae⟩

/-- **Theorem 9.2 for every `d ≥ 3` when `H_η(0) = 0`**, from the admitted literature inputs
(Fey-Levine-Peres Theorem 1.1, Alexandrov, Pegden-Smart Propositions 2.4 and 2.5 with
`ViscosityWeakLaplaceStmt`) and the operator fact of the operator comparison
(`NonPosDefLegalFlatStmt`, not yet formalized). -/
theorem singleSourceTheoremH0 (hFLP : External.FeyLevinePeresRadius) (hA : AlexandrovStmt)
    (h25 : PegdenSmartProp25Stmt) (h24 : PegdenSmartProp24Stmt) (hVW : ViscosityWeakLaplaceStmt)
    (h11 : ∀ d : ℕ, 3 ≤ d → NonPosDefLegalFlatStmt d) : SingleSourceTheoremH0Stmt := fun d hd E hE hZ =>
  singleSourceConclusion_of_star (by omega)
    (SingleSourceFstar.singleSourceTheoremFstar_ps13 (ssCompactness_of_flp hFLP)
      (ssOuterBound_of_flp hFLP) h25 h24 hVW hA)
    (h11 d hd) E hE hZ

end SingleSourceH0

end RandomSandpile

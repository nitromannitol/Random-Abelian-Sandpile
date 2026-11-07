import RandomSandpile.Proofs.Sec9.SingleSourceH0Main
import RandomSandpile.Proofs.Sec9.SingleSourceH0HighStable

/-!
# Theorem 9.2 with `H(0) = 0`: final statements

* `singleSourceTheoremFlatV2`: `SingleSourceTheoremFlatV2Stmt` (every `d ≥ 2`, every background with
  `StabThresholdZero E`) from the admitted literature inputs, the proved `d = 2` theorem
  (`singleSourceTheorem_d2`) and, for `d ≥ 3`, the operator fact (`NonPosDefLegalFlatStmt`).
* `singleSourceConclusion_of_highStable`: for `d ≥ 3` and every background with `d ≤ η ≤ 2d - 2`
  (`d ≤ E.ηmin`, `E.ηmax = 2d - 2`), the conclusion of Theorem 9.2.
-/

open LatticeProb

namespace RandomSandpile

open SingleSourceH0 SingleSourceD2

/-- **Theorem 9.2 for every `d ≥ 2` and every background with `H_η(0) = 0`.** -/
theorem singleSourceTheoremFlatV2 (hFLP : External.FeyLevinePeresRadius) (hA : AlexandrovStmt)
    (h25 : PegdenSmartProp25Stmt) (h24 : PegdenSmartProp24Stmt) (hVW : ViscosityWeakLaplaceStmt)
    (hTS : CrandallIshiiLions.CILTheoremOfSumsStmt) (hP : CrandallIshiiLions.CILPerronStmt)
    (h11 : ∀ d : ℕ, 3 ≤ d → NonPosDefLegalFlatStmt d) : SingleSourceTheoremFlatV2Stmt := by
  intro d hd E hE hZ
  rcases Nat.eq_or_lt_of_le hd with h2 | h3
  · subst h2
    exact singleSourceTheorem_d2 hFLP hA h25 hTS hP E hE
  · exact singleSourceTheoremH0 hFLP hA h25 h24 hVW h11 d h3 E hE hZ

/-- **Theorem 9.2 for `d ≥ 3` and every background with `d ≤ η ≤ 2d - 2`** (`d ≤ E.ηmin`,
`E.ηmax = 2d - 2`): the pointwise range of the high-stable backgrounds. -/
theorem singleSourceConclusion_of_highStable (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (h24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) (h11 : ∀ d : ℕ, 3 ≤ d → NonPosDefLegalFlatStmt d)
    {d : ℕ} (hd : 3 ≤ d) (E : RandomEnvironment d) (hmin : (d : ℤ) ≤ E.ηmin)
    (hmax : E.ηmax = 2 * (d : ℤ) - 2) : SingleSourceConclusion E :=
  singleSourceTheoremH0 hFLP hA h25 h24 hVW h11 d hd E hmax
    (stabThresholdZero_of_ge (by omega) E hmin)

#print axioms singleSourceTheoremFlatV2
#print axioms singleSourceConclusion_of_highStable
#print axioms stabThresholdZero_of_ge
#print axioms effOpLeStar_gen
#print axioms effOp_eq_effOpStar
#print axioms stabThresholdZero_of_flatEff

end RandomSandpile

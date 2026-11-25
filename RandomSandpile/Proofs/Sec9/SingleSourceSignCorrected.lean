import RandomSandpile.Proofs.Sec9.SingleSourceD2Main
import RandomSandpile.Proofs.Sec9.SingleSourceD2PerronProof
import RandomSandpile.Proofs.Sec9.SingleSourceD2ObsCompareProof
import RandomSandpile.Proofs.Alexandrov
import RandomSandpile.Proofs.PegdenSmart
import RandomSandpile.Proofs.PegdenSmartProp24
import RandomSandpile.Proofs.ViscosityWeakLaplace
import LatticeProb.External.FeyLevinePeresRadiusProved

/-!
# The single-source theorem with the original operator in dimension two

Theorem 9.2 is proved as corrected in C13, with the recurrent operator, in every dimension
(`singleSourceTheoremRecurrent_final`). This file proves, in dimension two, the statement with
correction C3 alone, that is, with the operator `F̄_η` in place of the recurrent operator, with
every proved literature input supplied.

* `singleSourceTheorem_d2_final`: in dimension two, with no hypothesis. The two steps of the
  two-dimensional proof that the earlier assembly took from Crandall-Ishii-Lions (Theorem 3.2, the
  theorem of sums, and Theorem 4.1, Perron's method) are proved: Perron's method with bounded
  barriers (`perronBounded_proved`) and comparison for the obstacle problem from Alexandrov's
  theorem (`obsComparison_proved`).
* `singleSourceTheorem_d2_of_cil`: the same from the two Crandall-Ishii-Lions statements of
  `Inputs/CrandallIshiiLions.lean`.
-/

open LatticeProb

namespace RandomSandpile

open SingleSourceD2

/-- **Theorem 9.2 with the original operator in dimension two**, from the theorem of sums and
Perron's method of Crandall, Ishii and Lions. -/
theorem singleSourceTheorem_d2_of_cil (hTS : CrandallIshiiLions.CILTheoremOfSumsStmt)
    (hP : CrandallIshiiLions.CILPerronStmt) : SingleSourceD2.SingleSourceTheoremD2Stmt :=
  SingleSourceD2.singleSourceTheorem_d2 External.feyLevinePeresRadius_holds alexandrovStmt_proved
    (pegdenSmartProp25Stmt_of_prop24 pegden_smart_prop24_stmt) hTS hP

/-- Perron's method with bounded barriers on open sets of `ℝ²`. -/
theorem perronBounded_proved : SingleSourceD2.PerronBoundedStmt :=
  fun _ _ hΩ hprop hcont hcomp _ _ hul huu henv hle _ hC =>
    perron_exists_of_bounded hΩ hprop hcont hcomp hul huu henv hle hC

/-- Comparison for the obstacle Dirichlet problem on bounded open sets of `ℝ²`. -/
theorem obsComparison_proved : SingleSourceD2.ObsComparisonStmt :=
  fun _ hΩ hΩb _ hg _ hA hAd _ _ _ hw hv =>
    obsComparison_of_alexandrov alexandrovStmt_proved hΩ hΩb hg hA hAd hw hv

/-- **Theorem 9.2 with the original operator in dimension two.** -/
theorem singleSourceTheorem_d2_final : SingleSourceD2.SingleSourceTheoremD2Stmt :=
  singleSourceTheoremD2_of_regFamily External.feyLevinePeresRadius_holds alexandrovStmt_proved
    (pegdenSmartProp25Stmt_of_prop24 pegden_smart_prop24_stmt)
    (ssLimitSubStarD2 (ssCompactness_of_flp External.feyLevinePeresRadius_holds)
      (pegdenSmartProp25Stmt_of_prop24 pegden_smart_prop24_stmt))
    (regularizedFamily_gen perronBounded_proved obsComparison_proved alexandrovStmt_proved)

end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceD2Main
import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatFinal
import RandomSandpile.Proofs.Alexandrov
import RandomSandpile.Proofs.PegdenSmart
import RandomSandpile.Proofs.PegdenSmartProp24
import RandomSandpile.Proofs.ViscosityWeakLaplace
import LatticeProb.External.FeyLevinePeresRadiusProved

/-!
# Theorem 9.2 with the original operator: what is proved

Theorem 9.2 with correction C3 alone, that is, with the operator `F̄_η` in place of the recurrent
operator of correction C13 (`SingleSourceTheoremStmt`), with every proved literature input
supplied.

* `singleSourceTheorem_d2_of_cil`: in dimension two, from Crandall-Ishii-Lions Theorems 3.2
  (the theorem of sums) and 4.1 (Perron's method), stated in `Inputs/CrandallIshiiLions.lean`.
* `singleSourceTheoremH0_of_flatCorrector`: in dimension `d ≥ 3`, for the backgrounds with
  `μ*(l, 0) = 0` for every `l > 0` (`StabThresholdZero`), from the step `FlatCorrectorStmt`.

In dimension `d ≥ 3` and for general backgrounds the statement is open.
-/

open LatticeProb

namespace RandomSandpile

open SingleSourceH0 SingleSourceD2

/-- **Theorem 9.2 with the original operator in dimension two**, from the theorem of sums and
Perron's method of Crandall, Ishii and Lions. -/
theorem singleSourceTheorem_d2_of_cil (hTS : CrandallIshiiLions.CILTheoremOfSumsStmt)
    (hP : CrandallIshiiLions.CILPerronStmt) : SingleSourceD2.SingleSourceTheoremD2Stmt :=
  SingleSourceD2.singleSourceTheorem_d2 External.feyLevinePeresRadius_holds alexandrovStmt_proved
    (pegdenSmartProp25Stmt_of_prop24 pegden_smart_prop24_stmt) hTS hP

/-- **Theorem 9.2 with the original operator in dimension `d ≥ 3`, for the backgrounds with
`μ*(l, 0) = 0` for every `l > 0`**, from the step `FlatCorrectorStmt`. -/
theorem singleSourceTheoremH0_of_flatCorrector (hflat : FlatCorrectorStmt) :
    SingleSourceTheoremH0Stmt :=
  singleSourceTheoremH0 External.feyLevinePeresRadius_holds alexandrovStmt_proved
    (pegdenSmartProp25Stmt_of_prop24 pegden_smart_prop24_stmt) pegden_smart_prop24_stmt
    viscosityWeakLaplace (fun _ hd => nonPosDefLegalFlat_of_flatCorrector hflat (by omega))

end RandomSandpile

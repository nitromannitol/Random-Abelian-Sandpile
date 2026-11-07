import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatBoundary
import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatPsi
import RandomSandpile.Proofs.Sec9.SingleSourceH0Final

/-!
# Theorem 9.2 with `H(0) = 0`: (11) reduced to the flat correctors

`nonPosDefLegalFlat_of_flatCorrector`: `NonPosDefLegalFlatStmt d` for all `d ≥ 2` from the single
remaining step `FlatCorrectorStmt` (S1b `integerConcave`, S2 `boundaryMin`, S3 `contactBend`,
S4 `locLegal_le_of_bdry` are proved). `singleSourceTheoremFlatV2_of_flatCorrector` replaces the
hypothesis (11) of `singleSourceTheoremFlatV2` by.
-/

open LatticeProb

namespace RandomSandpile

open SingleSourceH0

theorem nonPosDefLegalFlat_of_flatCorrector (hflat : FlatCorrectorStmt) {d : ℕ} (hd : 2 ≤ d) :
    NonPosDefLegalFlatStmt d :=
  nonPosDefLegalFlat_of_steps (stableQuadApprox_of_steps hflat integerConcave) boundaryMin hd

/-- **Theorem 9.2 for every `d ≥ 2` and every background with `H_η(0) = 0`**, with the single
step `FlatCorrectorStmt` in place of the operator fact. -/
theorem singleSourceTheoremFlatV2_of_flatCorrector (hFLP : External.FeyLevinePeresRadius)
    (hA : AlexandrovStmt) (h25 : PegdenSmartProp25Stmt) (h24 : PegdenSmartProp24Stmt)
    (hVW : ViscosityWeakLaplaceStmt) (hTS : CrandallIshiiLions.CILTheoremOfSumsStmt)
    (hP : CrandallIshiiLions.CILPerronStmt) (hflat : FlatCorrectorStmt) :
    SingleSourceTheoremFlatV2Stmt :=
  singleSourceTheoremFlatV2 hFLP hA h25 h24 hVW hTS hP
    (fun _ hd => nonPosDefLegalFlat_of_flatCorrector hflat (by omega))

#print axioms nonPosDefLegalFlat_of_flatCorrector
#print axioms singleSourceTheoremFlatV2_of_flatCorrector
#print axioms SingleSourceH0.boundaryMin
#print axioms SingleSourceH0.integerConcave
#print axioms SingleSourceH0.contactBend

end RandomSandpile

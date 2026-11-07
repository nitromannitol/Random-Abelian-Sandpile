import Mathlib
import RandomSandpile.Assembly.Main
import RandomSandpileAudit.SingleSource.SolutionBasic

/-!
# Bridge: the audit vocabulary is the library's

Each definition of `RandomSandpileAudit/SingleSource/SolutionBasic.lean` is identified with the
library definition of the same content. The identifications are `rfl`: the audit definitions are
token-for-token copies of the library bodies, with the library names written in Mathlib-only form.

The random environment is a structure, so it is repacked field by field (`toLibEnv`, `ofLibEnv`).
The two repackings are inverse by structure eta, and the conclusion and the statement transport
along them (`singleSourceRecurrentConclusion_iff`, `singleSourceTheoremRecurrentStmt_iff`).
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal Matrix

namespace RandomSandpile
namespace StatementAudit
namespace SingleSource

/-! ## Sites, the continuum and the configuration space -/

theorem Site_eq (d : ℕ) : Site d = _root_.LatticeProb.Site d := rfl

theorem Rd_eq (d : ℕ) : Rd d = _root_.RandomSandpile.Rd d := rfl

theorem Config_eq (d : ℕ) : Config d = _root_.RandomSandpile.Config d := rfl

theorem unit_eq {d : ℕ} (i : Fin d) : unit i = _root_.LatticeProb.unit i := rfl

theorem lattice_eq (d : ℕ) : lattice d = _root_.LatticeProb.lattice d := rfl

theorem toE_eq {d : ℕ} (x : Site d) : toE x = _root_.RandomSandpile.toE x := rfl

theorem ballZ_eq {d : ℕ} (x : Site d) (r : ℝ) :
    ballZ x r = _root_.RandomSandpile.ballZ x r := rfl

theorem ballZ0_eq {d : ℕ} (r : ℝ) : ballZ0 (d := d) r = _root_.RandomSandpile.ballZ0 r := rfl

theorem dirac_eq {d : ℕ} (z : Site d) : dirac z = _root_.LatticeProb.Sandpile.dirac z := rfl

theorem nbrSumZ_eq {d : ℕ} (u : Site d → ℤ) (x : Site d) :
    nbrSumZ u x = _root_.LatticeProb.Sandpile.nbrSumZ u x := rfl

theorem lap_eq {d : ℕ} (u : Site d → ℤ) (x : Site d) :
    lap u x = _root_.LatticeProb.Sandpile.lap u x := rfl

theorem outerBoundary_eq {V : Type*} (G : SimpleGraph V) (A : Set V) :
    outerBoundary G A = _root_.LatticeProb.Graph.outerBoundary G A := rfl

theorem closureN_eq {V : Type*} (G : SimpleGraph V) (A : Set V) :
    closureN G A = _root_.LatticeProb.Graph.closureN G A := rfl

theorem bdry_eq {d : ℕ} (A : Set (Site d)) : bdry A = _root_.RandomSandpile.bdry A := rfl

theorem dClosure_eq {d : ℕ} (A : Set (Site d)) :
    dClosure A = _root_.RandomSandpile.dClosure A := rfl

theorem shift_eq {d : ℕ} (y : Site d) (η : Config d) :
    shift y η = _root_.RandomSandpile.shift y η := rfl

/-! ## The random environment: repacking the structure -/

/-- The library random environment with the data of the audit environment `E`. -/
def toLibEnv {d : ℕ} (E : RandomEnvironment d) : _root_.RandomSandpile.RandomEnvironment d where
  P := E.P
  isProb := E.isProb
  ηmin := E.ηmin
  ηmax := E.ηmax
  bounded := E.bounded
  stationary := E.stationary
  ergodic := E.ergodic

/-- The audit random environment with the data of the library environment `E`. -/
def ofLibEnv {d : ℕ} (E : _root_.RandomSandpile.RandomEnvironment d) : RandomEnvironment d where
  P := E.P
  isProb := E.isProb
  ηmin := E.ηmin
  ηmax := E.ηmax
  bounded := E.bounded
  stationary := E.stationary
  ergodic := E.ergodic

theorem toLibEnv_ofLibEnv {d : ℕ} (E : _root_.RandomSandpile.RandomEnvironment d) :
    toLibEnv (ofLibEnv E) = E := rfl

theorem ofLibEnv_toLibEnv {d : ℕ} (E : RandomEnvironment d) : ofLibEnv (toLibEnv E) = E := rfl

/-! ## Toppling functions, odometers and the fundamental solution -/

theorem IsTopplingFn_eq {d : ℕ} (A : Set (Site d)) (u : Site d → ℤ) :
    IsTopplingFn A u = _root_.RandomSandpile.IsTopplingFn A u := rfl

theorem stabilizing_eq {d : ℕ} (η : Site d → ℤ) (A : Set (Site d)) :
    stabilizing η A = _root_.RandomSandpile.stabilizing η A := rfl

theorem pointwiseInf_eq {d : ℕ} (S : Set (Site d → ℤ)) :
    pointwiseInf S = _root_.RandomSandpile.pointwiseInf S := rfl

theorem singleSourceOdometer_eq {d : ℕ} (η : Site d → ℤ) (m : ℕ) :
    singleSourceOdometer η m = _root_.RandomSandpile.singleSourceOdometer η m := rfl

theorem latticeRound_eq {d : ℕ} (x : Rd d) :
    latticeRound x = _root_.RandomSandpile.latticeRound x := rfl

theorem rescaleSingleSource_eq {d : ℕ} (v : Site d → ℤ) (n : ℕ) :
    rescaleSingleSource v n = _root_.RandomSandpile.rescaleSingleSource v n := rfl

theorem unitBallVolume_eq (d : ℕ) : unitBallVolume d = _root_.RandomSandpile.unitBallVolume d := rfl

theorem fundamentalSolution_eq (d : ℕ) (x : Rd d) :
    fundamentalSolution d x = _root_.RandomSandpile.fundamentalSolution d x := rfl

/-! ## Quadratics and gradient sets -/

theorem qM_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) :
    qM M x = _root_.RandomSandpile.qM M x := rfl

theorem ql_eq {d : ℕ} (l : ℝ) (x : Rd d) : ql l x = _root_.RandomSandpile.ql l x := rfl

theorem qMZ_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Site d) :
    qMZ M x = _root_.RandomSandpile.qMZ M x := rfl

theorem qlZ_eq {d : ℕ} (l : ℝ) (x : Site d) : qlZ l x = _root_.RandomSandpile.qlZ l x := rfl

theorem supGrad_eq {d : ℕ} (v : Site d → ℝ) (x : Site d) (A : Set (Site d)) :
    supGrad v x A = _root_.RandomSandpile.supGrad v x A := rfl

theorem subGrad_eq {d : ℕ} (v : Site d → ℝ) (x : Site d) (A : Set (Site d)) :
    subGrad v x A = _root_.RandomSandpile.subGrad v x A := rfl

theorem supGradSet_eq {d : ℕ} (v : Site d → ℝ) (A : Set (Site d)) :
    supGradSet v A = _root_.RandomSandpile.supGradSet v A := rfl

theorem subGradSet_eq {d : ℕ} (v : Site d → ℝ) (A : Set (Site d)) :
    subGradSet v A = _root_.RandomSandpile.subGradSet v A := rfl

/-! ## The recurrent functions and the recurrent effective operator -/

theorem IsRecurrentFunction_eq {d : ℕ} (η : Site d → ℤ) (A : Set (Site d)) (r : Site d → ℤ) :
    IsRecurrentFunction η A r = _root_.RandomSandpile.IsRecurrentFunction η A r := rfl

theorem recurrentPerturbed_eq {d : ℕ} (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    recurrentPerturbed A η l M = _root_.RandomSandpile.recurrentPerturbed A η l M := rfl

theorem muRecurrent_eq {d : ℕ} (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    muRecurrent A η l M = _root_.RandomSandpile.muRecurrent A η l M := rfl

theorem muStarRecurrent_eq {d : ℕ} (A : Set (Site d)) (η : Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    muStarRecurrent A η l M = _root_.RandomSandpile.muStarRecurrent A η l M := rfl

theorem muRecurrentBar_eq {d : ℕ} (E : RandomEnvironment d) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    muRecurrentBar E l M = _root_.RandomSandpile.muRecurrentBar (toLibEnv E) l M := rfl

theorem muStarRecurrentBar_eq {d : ℕ} (E : RandomEnvironment d) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    muStarRecurrentBar E l M = _root_.RandomSandpile.muStarRecurrentBar (toLibEnv E) l M := rfl

theorem effOpRecurrent_eq {d : ℕ} (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) :
    effOpRecurrent E M = _root_.RandomSandpile.effOpRecurrent (toLibEnv E) M := rfl

/-! ## Viscosity test functions and the Taylor expansion -/

theorem hessian_eq {d : ℕ} (φ : Rd d → ℝ) (x : Rd d) :
    hessian φ x = _root_.RandomSandpile.hessian φ x := rfl

theorem HasSecondOrderTaylorAt_eq {d : ℕ} (u : Rd d → ℝ) (a p : Rd d)
    (X : Matrix (Fin d) (Fin d) ℝ) :
    HasSecondOrderTaylorAt u a p X = _root_.RandomSandpile.HasSecondOrderTaylorAt u a p X := rfl

theorem ViscFromBelowGE_eq {d : ℕ} (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d))
    (u : Rd d → ℝ) :
    ViscFromBelowGE F U u = _root_.RandomSandpile.ViscFromBelowGE F U u := rfl

/-! ## The obstacle class, the conclusion and the literature inputs -/

theorem recurrentSingleSourceObstacleSet_eq {d : ℕ} (E : RandomEnvironment d) :
    recurrentSingleSourceObstacleSet E =
      _root_.RandomSandpile.recurrentSingleSourceObstacleSet (toLibEnv E) := rfl

theorem SingleSourceFinite_eq {d : ℕ} (η : Site d → ℤ) :
    SingleSourceFinite η = _root_.RandomSandpile.SingleSourceFinite η := rfl

theorem SingleSourceRecurrentConclusion_eq {d : ℕ} (E : RandomEnvironment d) :
    SingleSourceRecurrentConclusion E =
      _root_.RandomSandpile.SingleSourceRecurrentConclusion (toLibEnv E) := rfl

theorem podo_eq {d : ℕ} (s0 : Site d → ℤ) :
    ∀ t : ℕ, podo s0 t = _root_.LatticeProb.Sandpile.podo s0 t
  | 0 => rfl
  | t + 1 => by
      rw [podo.eq_2, _root_.LatticeProb.Sandpile.podo.eq_2, podo_eq s0 t]
      rfl

theorem FeyLevinePeresRadius_eq :
    FeyLevinePeresRadius = _root_.LatticeProb.External.FeyLevinePeresRadius := by
  unfold FeyLevinePeresRadius _root_.LatticeProb.External.FeyLevinePeresRadius
  simp only [podo_eq]
  rfl

theorem AlexandrovStmt_eq : AlexandrovStmt = _root_.RandomSandpile.AlexandrovStmt := rfl

/-! ## The conclusion and the statement transport along the repacking -/

theorem singleSourceRecurrentConclusion_iff {d : ℕ} (E : RandomEnvironment d) :
    SingleSourceRecurrentConclusion E ↔
      _root_.RandomSandpile.SingleSourceRecurrentConclusion (toLibEnv E) :=
  Iff.rfl

theorem singleSourceTheoremRecurrentStmt_iff :
    (∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d,
        E.ηmax ≤ 2 * (d : ℤ) - 2 → SingleSourceRecurrentConclusion E) ↔
      _root_.RandomSandpile.SingleSourceTheoremRecurrentStmt := by
  constructor
  · intro h d hd E hE
    exact (singleSourceRecurrentConclusion_iff (ofLibEnv E)).1 (h d hd (ofLibEnv E) hE)
  · intro h d hd E hE
    exact (singleSourceRecurrentConclusion_iff E).2 (h d hd (toLibEnv E) hE)

end SingleSource
end StatementAudit
end RandomSandpile

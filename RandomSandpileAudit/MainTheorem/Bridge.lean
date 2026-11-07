import Mathlib
import RandomSandpile.Proofs.FinalSteps
import RandomSandpile.Proofs.Sec7.PegdenSmartAdapter
import RandomSandpileAudit.MainTheorem.SolutionBasic

/-!
# Bridge: the restated main statement is the library's

Each restated definition of `SolutionBasic.lean` (Mathlib only) equals the library definition of the same
name: the lemmas below are `rfl`, because the bodies agree up to the names of the constants. The random
environment is a structure, so it is transported field by field by `toLib`; the environment-dependent
definitions are identified after `toLib`. The only transport of a statement is `mainTheoremStmt_of_lib`.
-/

namespace RandomSandpile.StatementAudit.MainTheorem

/-! ## Random environments -/

/-- The library random environment with the same law, bounds, stationarity and ergodicity as `E`. -/
def toLib {d : ℕ} (E : RandomEnvironment d) : _root_.RandomSandpile.RandomEnvironment d :=
  @_root_.RandomSandpile.RandomEnvironment.mk d E.P E.isProb E.ηmin E.ηmax E.bounded E.stationary
    E.ergodic

theorem toLib_P {d : ℕ} (E : RandomEnvironment d) : (toLib E).P = E.P := rfl

theorem toLib_ηmax {d : ℕ} (E : RandomEnvironment d) : (toLib E).ηmax = E.ηmax := rfl

/-! ## Lattice-Probability vocabulary -/

theorem Site_eq (d : ℕ) : LatticeProb.Site d = _root_.LatticeProb.Site d := rfl

theorem unit_eq {d : ℕ} (i : Fin d) : LatticeProb.unit i = _root_.LatticeProb.unit i := rfl

theorem lattice_eq (d : ℕ) : LatticeProb.lattice d = _root_.LatticeProb.lattice d := rfl

theorem nbrSum_eq {d : ℕ} (u : LatticeProb.Site d → ℝ) (x : LatticeProb.Site d) :
    LatticeProb.nbrSum u x = _root_.LatticeProb.nbrSum u x := rfl

theorem outerBoundary_eq {V : Type*} (G : SimpleGraph V) (A : Set V) :
    LatticeProb.Graph.outerBoundary G A = _root_.LatticeProb.Graph.outerBoundary G A := rfl

theorem closureN_eq {V : Type*} (G : SimpleGraph V) (A : Set V) :
    LatticeProb.Graph.closureN G A = _root_.LatticeProb.Graph.closureN G A := rfl

theorem dirac_eq {d : ℕ} (z : LatticeProb.Site d) :
    LatticeProb.Sandpile.dirac z = _root_.LatticeProb.Sandpile.dirac z := rfl

theorem nbrSumZ_eq {d : ℕ} (u : LatticeProb.Site d → ℤ) (x : LatticeProb.Site d) :
    LatticeProb.Sandpile.nbrSumZ u x = _root_.LatticeProb.Sandpile.nbrSumZ u x := rfl

theorem lap_eq {d : ℕ} (u : LatticeProb.Site d → ℤ) (x : LatticeProb.Site d) :
    LatticeProb.Sandpile.lap u x = _root_.LatticeProb.Sandpile.lap u x := rfl

/-! ## The lattice, the continuum and the discrete operators -/

theorem Rd_eq (d : ℕ) : Rd d = _root_.RandomSandpile.Rd d := rfl

theorem toE_eq {d : ℕ} (x : LatticeProb.Site d) : toE x = _root_.RandomSandpile.toE x := rfl

theorem bdry_eq {d : ℕ} (A : Set (LatticeProb.Site d)) :
    bdry A = _root_.RandomSandpile.bdry A := rfl

theorem dClosure_eq {d : ℕ} (A : Set (LatticeProb.Site d)) :
    dClosure A = _root_.RandomSandpile.dClosure A := rfl

theorem lapR_eq {d : ℕ} (f : LatticeProb.Site d → ℝ) (x : LatticeProb.Site d) :
    lapR f x = _root_.RandomSandpile.lapR f x := rfl

theorem ballZ_eq {d : ℕ} (x : LatticeProb.Site d) (r : ℝ) :
    ballZ x r = _root_.RandomSandpile.ballZ x r := rfl

theorem ballZ0_eq {d : ℕ} (r : ℝ) : ballZ0 (d := d) r = _root_.RandomSandpile.ballZ0 (d := d) r :=
  rfl

theorem discretize_eq {d : ℕ} (W : Set (Rd d)) (n : ℕ) :
    discretize W n = _root_.RandomSandpile.discretize W n := rfl

theorem latticeRound_eq {d : ℕ} (x : Rd d) :
    latticeRound x = _root_.RandomSandpile.latticeRound x := rfl

theorem qM_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) :
    qM M x = _root_.RandomSandpile.qM M x := rfl

theorem ql_eq {d : ℕ} (l : ℝ) (x : Rd d) : ql l x = _root_.RandomSandpile.ql l x := rfl

theorem qMZ_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : LatticeProb.Site d) :
    qMZ M x = _root_.RandomSandpile.qMZ M x := rfl

theorem qlZ_eq {d : ℕ} (l : ℝ) (x : LatticeProb.Site d) :
    qlZ l x = _root_.RandomSandpile.qlZ l x := rfl

theorem supGrad_eq {d : ℕ} (v : LatticeProb.Site d → ℝ) (x : LatticeProb.Site d)
    (A : Set (LatticeProb.Site d)) : supGrad v x A = _root_.RandomSandpile.supGrad v x A := rfl

theorem subGrad_eq {d : ℕ} (v : LatticeProb.Site d → ℝ) (x : LatticeProb.Site d)
    (A : Set (LatticeProb.Site d)) : subGrad v x A = _root_.RandomSandpile.subGrad v x A := rfl

theorem supGradSet_eq {d : ℕ} (v : LatticeProb.Site d → ℝ) (A : Set (LatticeProb.Site d)) :
    supGradSet v A = _root_.RandomSandpile.supGradSet v A := rfl

theorem subGradSet_eq {d : ℕ} (v : LatticeProb.Site d → ℝ) (A : Set (LatticeProb.Site d)) :
    subGradSet v A = _root_.RandomSandpile.subGradSet v A := rfl

/-! ## Domains, environments and toppling -/

theorem IsLipschitzDomain_eq {d : ℕ} (W : Set (Rd d)) :
    IsLipschitzDomain W = _root_.RandomSandpile.IsLipschitzDomain W := rfl

theorem Config_eq (d : ℕ) : Config d = _root_.RandomSandpile.Config d := rfl

theorem shift_eq {d : ℕ} (y : LatticeProb.Site d) (η : Config d) :
    shift y η = _root_.RandomSandpile.shift y η := rfl

theorem meanEta_eq {d : ℕ} (P : MeasureTheory.Measure (Config d)) :
    meanEta P = _root_.RandomSandpile.meanEta P := rfl

theorem HighDensity_eq {d : ℕ} (P : MeasureTheory.Measure (Config d)) :
    HighDensity P = _root_.RandomSandpile.HighDensity P := rfl

theorem IsTopplingFn_eq {d : ℕ} (A : Set (LatticeProb.Site d)) (u : LatticeProb.Site d → ℤ) :
    IsTopplingFn A u = _root_.RandomSandpile.IsTopplingFn A u := rfl

theorem IsLegal_eq {d : ℕ} (η : LatticeProb.Site d → ℤ) (A : Set (LatticeProb.Site d))
    (u : LatticeProb.Site d → ℤ) : IsLegal η A u = _root_.RandomSandpile.IsLegal η A u := rfl

theorem locLegal_eq {d : ℕ} (η : LatticeProb.Site d → ℤ) (A : Set (LatticeProb.Site d)) :
    locLegal η A = _root_.RandomSandpile.locLegal η A := rfl

theorem stabilizing_eq {d : ℕ} (η : LatticeProb.Site d → ℤ) (A : Set (LatticeProb.Site d)) :
    stabilizing η A = _root_.RandomSandpile.stabilizing η A := rfl

/-! ## Perturbed sets, `μ`, `μ*` and the effective operators -/

theorem perturbedSub_eq {d : ℕ} (A : Set (LatticeProb.Site d)) (η : LatticeProb.Site d → ℤ)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    perturbedSub A η l M = _root_.RandomSandpile.perturbedSub A η l M := rfl

theorem perturbedSuper_eq {d : ℕ} (A : Set (LatticeProb.Site d)) (η : LatticeProb.Site d → ℤ)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    perturbedSuper A η l M = _root_.RandomSandpile.perturbedSuper A η l M := rfl

theorem mu_eq {d : ℕ} (A : Set (LatticeProb.Site d)) (η : LatticeProb.Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : mu A η l M = _root_.RandomSandpile.mu A η l M := rfl

theorem muStar_eq {d : ℕ} (A : Set (LatticeProb.Site d)) (η : LatticeProb.Site d → ℤ) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) : muStar A η l M = _root_.RandomSandpile.muStar A η l M := rfl

theorem muBar_eq {d : ℕ} (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muBar E l M = _root_.RandomSandpile.muBar (toLib E) l M := rfl

theorem muStarBar_eq {d : ℕ} (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStarBar E l M = _root_.RandomSandpile.muStarBar (toLib E) l M := rfl

theorem muEqSet_eq {d : ℕ} (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) :
    muEqSet E M = _root_.RandomSandpile.muEqSet (toLib E) M := rfl

theorem effOp_eq {d : ℕ} (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) :
    effOp E M = _root_.RandomSandpile.effOp (toLib E) M := rfl

theorem effOp0_eq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    effOp0 d M = _root_.RandomSandpile.effOp0 d M := rfl

/-! ## Viscosity vocabulary -/

theorem hessian_eq {d : ℕ} (φ : Rd d → ℝ) (x : Rd d) :
    hessian φ x = _root_.RandomSandpile.hessian φ x := rfl

theorem HasSecondOrderTaylorAt_eq {d : ℕ} (u : Rd d → ℝ) (a p : Rd d)
    (X : Matrix (Fin d) (Fin d) ℝ) :
    HasSecondOrderTaylorAt u a p X = _root_.RandomSandpile.HasSecondOrderTaylorAt u a p X := rfl

theorem PeanoTwiceDifferentiableAt_eq {d : ℕ} (u : Rd d → ℝ) (a : Rd d) :
    PeanoTwiceDifferentiableAt u a = _root_.RandomSandpile.PeanoTwiceDifferentiableAt u a := rfl

theorem DegenerateElliptic_eq {d : ℕ} (F : Matrix (Fin d) (Fin d) ℝ → ℝ) :
    DegenerateElliptic F = _root_.RandomSandpile.DegenerateElliptic F := rfl

theorem ViscFromAboveGE_eq {d : ℕ} (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d))
    (u : Rd d → ℝ) : ViscFromAboveGE F U u = _root_.RandomSandpile.ViscFromAboveGE F U u := rfl

theorem ViscFromBelowLE_eq {d : ℕ} (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d))
    (u : Rd d → ℝ) : ViscFromBelowLE F U u = _root_.RandomSandpile.ViscFromBelowLE F U u := rfl

theorem ViscFromBelowGE_eq {d : ℕ} (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d))
    (u : Rd d → ℝ) : ViscFromBelowGE F U u = _root_.RandomSandpile.ViscFromBelowGE F U u := rfl

theorem WeakStarTendsto_eq {d : ℕ} (f : ℕ → Rd d → ℝ) (s : Rd d → ℝ) :
    WeakStarTendsto f s = _root_.RandomSandpile.WeakStarTendsto f s := rfl

/-! ## The obstacle problem and the odometers -/

theorem obstacleSet_eq {d : ℕ} (E : RandomEnvironment d) (W : Set (Rd d)) :
    obstacleSet E W = _root_.RandomSandpile.obstacleSet (toLib E) W := rfl

theorem obstacleSolution_eq {d : ℕ} (E : RandomEnvironment d) (W : Set (Rd d)) :
    obstacleSolution E W = _root_.RandomSandpile.obstacleSolution (toLib E) W := rfl

theorem pointwiseInf_eq {d : ℕ} (S : Set (LatticeProb.Site d → ℤ)) :
    pointwiseInf S = _root_.RandomSandpile.pointwiseInf S := rfl

theorem freeOdometer_eq {d : ℕ} (η : LatticeProb.Site d → ℤ) (Wn : Set (LatticeProb.Site d)) :
    freeOdometer η Wn = _root_.RandomSandpile.freeOdometer η Wn := rfl

theorem freeSandpile_eq {d : ℕ} (η : LatticeProb.Site d → ℤ) (Wn : Set (LatticeProb.Site d)) :
    freeSandpile η Wn = _root_.RandomSandpile.freeSandpile η Wn := rfl

theorem rescaleOdo_eq {d : ℕ} (v : LatticeProb.Site d → ℤ) (n : ℕ) :
    rescaleOdo v n = _root_.RandomSandpile.rescaleOdo v n := rfl

theorem rescaleSandpile_eq {d : ℕ} (s : LatticeProb.Site d → ℤ) (n : ℕ) :
    rescaleSandpile s n = _root_.RandomSandpile.rescaleSandpile s n := rfl

/-! ## The literature inputs -/

theorem IsWeakSolutionLaplace_eq {d : ℕ} (U : Set (Rd d)) (u s : Rd d → ℝ) :
    IsWeakSolutionLaplace U u s = _root_.RandomSandpile.IsWeakSolutionLaplace U u s := rfl

theorem AlexandrovStmt_eq : AlexandrovStmt = _root_.RandomSandpile.AlexandrovStmt := rfl

theorem LawlerLimicHarmonicDifferenceStmt_eq :
    LawlerLimicHarmonicDifferenceStmt = _root_.RandomSandpile.LawlerLimicHarmonicDifferenceStmt :=
  rfl

theorem PegdenSmartProp25Stmt_eq :
    PegdenSmartProp25Stmt = _root_.RandomSandpile.PegdenSmartProp25Stmt := rfl

theorem PegdenSmartProp24Stmt_eq :
    PegdenSmartProp24Stmt = _root_.RandomSandpile.PegdenSmartProp24Stmt := rfl

theorem ViscosityWeakLaplaceStmt_eq :
    ViscosityWeakLaplaceStmt = _root_.RandomSandpile.ViscosityWeakLaplaceStmt := rfl

/-! ## The main statement -/

/-- The library's `MainTheoremStmt` implies the restated one: each restated environment is sent to
the library by `toLib`, and the restated conclusions are the library's after `toLib`. -/
theorem mainTheoremStmt_of_lib (h : _root_.RandomSandpile.MainTheoremStmt) :
    MainTheoremStmt := by
  intro d hd W hW ηmax
  obtain ⟨R, hR, hL⟩ := h d hd W hW ηmax
  exact ⟨R, hR, fun E hE hHD => hL (toLib E) hE hHD⟩

end RandomSandpile.StatementAudit.MainTheorem

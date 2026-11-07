import RandomSandpile.Defs.Lattice

/-! # Viscosity-solution vocabulary (Sections 1, 7 and 9)

Test-function definitions of viscosity sub- and supersolutions of `F(D²u) = 0` in the style of
Crandall, Ishii and Lions (*User's guide to viscosity solutions*, Bull. AMS 27 (1992), Def. 2.2),
together with the notions of convergence used in the paper's main theorems.

* `hessian φ x`: the Hessian matrix `D²φ(x)`, entries `D²φ(x)(eᵢ, eⱼ)` (second Fréchet
  derivative evaluated on the standard basis);
* `HasSecondOrderTaylorAt u a p X`: second-order Taylor expansion with Peano remainder,
  `u(x) = u(a) + p·(x-a) + ½(x-a)ᵀX(x-a) + o(|x-a|²)`;
* `PeanoTwiceDifferentiableAt u a`: "twice differentiable at `a`" in the sense of Lemma 7.6, i.e. such an expansion with a symmetric `X`;
* `DegenerateElliptic F`: `F` nonincreasing in the Loewner order (Crandall-Ishii-Lions convention);
* `ViscFromAboveLE`, `ViscFromAboveGE`, `ViscFromBelowLE`, `ViscFromBelowGE`: the four
  test-function inequalities (touching from above or from below, `F ≤ 0` or `F ≥ 0`);
* `ViscSubsolutionLE := ViscFromAboveLE`, `ViscSupersolutionGE := ViscFromBelowGE`: the
  Crandall-Ishii-Lions subsolution and supersolution properties;
* `ViscositySolution F U u`: both (Theorem 9.1);
* `WeakStarTendsto f s`: weak-* convergence in `L^∞(ℝ^d) = (L¹(ℝ^d))*` (Theorem 1.1).

## Which inequality reading the main theorems use

The paper writes "`F̄_η(D²v̄) ≤ 0` in `W` and `F̄_0(D²v̄) ≤ 0` in `ℝ^d`, in the viscosity sense"
 and "`F̄_η(D²(v̄+G)) ≤ 0`". The constraint set of an obstacle problem
defined as a minimum (infimum) must be stable under pointwise minima, so both inequalities must be
tested by `C²` functions touching from below (supersolution type). `F̄_0` is nondecreasing in `M`
(Pegden-Smart convention: `D²u ∈ Γ̄`), so its condition is `ViscFromBelowLE (effOp0 d) univ v̄`.
`F̄_η` is nonincreasing in `M` (Lemma 6.4(1)), so the min-stable condition is
`ViscFromBelowGE (effOp E) W v̄` (proposed correction [C3]). All four
predicates are provided so that the statements can use either reading.

## Locally uniform convergence away from the origin

Theorem 9.2 asserts convergence "locally uniformly away from the origin". This is
Mathlib's `TendstoLocallyUniformlyOn F f atTop {x | x ≠ 0}`: since `{x | x ≠ 0}` is open and `ℝ^d`
is locally compact, it is equivalent to uniform convergence on every compact subset of
`ℝ^d \ {0}` (`tendstoLocallyUniformlyOn_iff_forall_isCompact`). Uniform convergence on `ℝ^d`
(Theorems 1.1 and 9.1) is Mathlib's `TendstoUniformly`. No new definition is needed. -/

noncomputable section

open MeasureTheory Filter Topology Asymptotics
open scoped Matrix

namespace RandomSandpile

variable {d : ℕ}

/-! ### Hessians and second-order Taylor expansions -/

/-- The Hessian matrix `D²φ(x)`: the `(i, j)` entry is the second Fréchet derivative
`D²φ(x)(eᵢ, eⱼ) = fderiv ℝ (fderiv ℝ φ) x eᵢ eⱼ`, with `eᵢ` the standard basis of `ℝ^d`.
For `φ` twice differentiable at `x` with symmetric second derivative (e.g. `φ` of class `C²`
near `x`) it is a symmetric matrix; otherwise it carries Mathlib's junk value `0` for
non-differentiable functions. -/
def hessian (φ : Rd d → ℝ) (x : Rd d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

theorem hessian_apply (φ : Rd d → ℝ) (x : Rd d) (i j : Fin d) :
    hessian φ x i j =
      fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
  rfl

/-- Second-order Taylor expansion with Peano remainder at `a`, with gradient `p` and matrix `X`:
`u(x) = u(a) + p·(x-a) + ½(x-a)ᵀX(x-a) + o(|x-a|²)` as `x → a` (the expansion, `½ yᵀXy = qM X y`). Only the symmetric part of `X` is determined by `u`. -/
def HasSecondOrderTaylorAt (u : Rd d → ℝ) (a p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (fun x => u x - u a - inner ℝ p (x - a) - qM X (x - a)) =o[𝓝 a] fun x => ‖x - a‖ ^ 2

/-- "`u` is twice differentiable at `a`" in the sense of Lemma 7.6 (after
Pegden-Smart): `u` admits a second-order Taylor expansion with Peano remainder at `a` with some
gradient `p = Du(a)` and some symmetric matrix `X = D²u(a)` (this is the sense of Alexandrov's
theorem, the reading). Symmetry makes `X` unique. -/
def PeanoTwiceDifferentiableAt (u : Rd d → ℝ) (a : Rd d) : Prop :=
  ∃ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ), X.IsSymm ∧ HasSecondOrderTaylorAt u a p X

/-! ### The quadratic test functions `q_M`

The quadratics `q_M(x) = ½ xᵀMx` are the basic test functions; computing their
Hessian checks the convention of `hessian`: `D²q_M = ½(M + Mᵀ)`, which is `M` for symmetric `M`. -/

/-- The bilinear form `(x, y) ↦ xᵀ M y` on `ℝ^d`, as a continuous bilinear map. -/
def matrixBilin (M : Matrix (Fin d) (Fin d) ℝ) : Rd d →L[ℝ] Rd d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Rd d →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Rd d →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun x y : Rd d => WithLp.ofLp x ⬝ᵥ M *ᵥ WithLp.ofLp y)
        (fun x x' y => by simp [add_dotProduct])
        (fun c x y => by simp [smul_dotProduct])
        (fun x y y' => by simp [Matrix.mulVec_add, dotProduct_add])
        (fun c x y => by simp [Matrix.mulVec_smul, dotProduct_smul]))

theorem matrixBilin_apply (M : Matrix (Fin d) (Fin d) ℝ) (x y : Rd d) :
    matrixBilin M x y = WithLp.ofLp x ⬝ᵥ M *ᵥ WithLp.ofLp y :=
  rfl

theorem qM_eq_matrixBilin (M : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) :
    qM M x = (1 / 2 : ℝ) * matrixBilin M x x :=
  rfl

/-- The derivative of `q_M` as a continuous linear map of the base point:
`Dq_M(x) h = ½ (xᵀ M h + hᵀ M x)`. -/
def qMDeriv (M : Matrix (Fin d) (Fin d) ℝ) : Rd d →L[ℝ] Rd d →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (matrixBilin M + (matrixBilin M).flip)

theorem hasFDerivAt_qM (M : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) :
    HasFDerivAt (qM M) (qMDeriv M x) x := by
  have h := ((matrixBilin M).hasFDerivAt_of_bilinear (hasFDerivAt_id x)
    (hasFDerivAt_id x)).const_mul (1 / 2 : ℝ)
  refine h.congr_fderiv ?_
  ext v
  rfl

theorem fderiv_qM (M : Matrix (Fin d) (Fin d) ℝ) : fderiv ℝ (qM M) = qMDeriv M :=
  funext fun x => (hasFDerivAt_qM M x).fderiv

theorem contDiff_qM (M : Matrix (Fin d) (Fin d) ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (qM M) := by
  show ContDiff ℝ n (fun x => (1 / 2 : ℝ) * matrixBilin M x x)
  exact contDiff_const.mul
    ((matrixBilin M).isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id))

/-- `D²q_M = ½(M + Mᵀ)` at every point. -/
theorem hessian_qM (M : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) :
    hessian (qM M) x = (1 / 2 : ℝ) • (M + Mᵀ) := by
  have h2 : fderiv ℝ (fderiv ℝ (qM M)) x = qMDeriv M := by
    rw [fderiv_qM]
    exact (qMDeriv M).fderiv
  ext i j
  rw [hessian_apply, h2]
  have hs : ∀ k : Fin d, WithLp.ofLp (EuclideanSpace.single k (1 : ℝ)) = Pi.single k 1 :=
    fun k => rfl
  show (1 / 2 : ℝ) * (matrixBilin M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      matrixBilin M (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) =
    (1 / 2 : ℝ) * (M i j + M j i)
  rw [matrixBilin_apply, matrixBilin_apply, hs, hs, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one, single_dotProduct, single_dotProduct]
  simp

/-- `D²q_M = M` for symmetric `M`. -/
theorem hessian_qM_of_isSymm {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (x : Rd d) :
    hessian (qM M) x = M := by
  rw [hessian_qM, hM.eq, ← two_smul ℝ M, smul_smul]
  norm_num

/-! ### Degenerate ellipticity -/

/-- Degenerate ellipticity in the Crandall-Ishii-Lions convention: `F(Y) ≤ F(X)` whenever
`X ≤ Y` in the Loewner order (`Y - X` positive semidefinite), for symmetric `X`, `Y`.
The effective operator `F̄_η` is degenerate elliptic in this sense (Lemma 6.4(1)); the
single-source operator `F̄_0` is nondecreasing, so `-F̄_0` is. -/
def DegenerateElliptic (F : Matrix (Fin d) (Fin d) ℝ → ℝ) : Prop :=
  ∀ X Y : Matrix (Fin d) (Fin d) ℝ, X.IsSymm → Y.IsSymm → (Y - X).PosSemidef → F Y ≤ F X

/-! ### Test-function inequalities

In all four predicates, `U` is the set on which the inequality is imposed (open in every use;
openness is a hypothesis of statements, not of the definitions), `u : ℝ^d → ℝ` is the tested
function, and test functions `φ` are of class `C²` near the touching point: `ContDiffAt ℝ 2 φ x`
means `φ` is `C²` on a neighbourhood of `x` (`ContDiffAt.eventually`). Touching is a local
extremum of `u - φ` at `x` in `ℝ^d`; for `x` in the open set `U` this is the same as a local
extremum relative to `U`. Semicontinuity of `u` is not part of the definitions: statements
assume `u ∈ C(ℝ^d)` separately, as the paper does. -/

/-- `F(D²u) ≤ 0` in `U` tested from above: whenever `φ` is `C²` near `x ∈ U` and `u - φ` has a
local maximum at `x`, then `F(D²φ(x)) ≤ 0`. For a degenerate elliptic `F`
(`DegenerateElliptic`) this is the Crandall-Ishii-Lions viscosity subsolution property. -/
def ViscFromAboveLE (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMax (fun y => u y - φ y) x →
    F (hessian φ x) ≤ 0

/-- `F(D²u) ≥ 0` in `U` tested from above: whenever `φ` is `C²` near `x ∈ U` and `u - φ` has a
local maximum at `x`, then `F(D²φ(x)) ≥ 0`. For a nondecreasing `F` (i.e. `-F` degenerate
elliptic) this is the Crandall-Ishii-Lions subsolution property of `-F(D²u) = 0`. -/
def ViscFromAboveGE (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMax (fun y => u y - φ y) x →
    0 ≤ F (hessian φ x)

/-- `F(D²u) ≤ 0` in `U` tested from below: whenever `φ` is `C²` near `x ∈ U` and `u - φ` has a
local minimum at `x`, then `F(D²φ(x)) ≤ 0`. For a nondecreasing `F` this is the
Crandall-Ishii-Lions supersolution property of `-F(D²u) = 0`; it is the Pegden-Smart reading of
`F̄_0(D²v̄) ≤ 0` (`D²v̄ ∈ Γ̄` in the viscosity sense) in Theorem 1.1. -/
def ViscFromBelowLE (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMin (fun y => u y - φ y) x →
    F (hessian φ x) ≤ 0

/-- `F(D²u) ≥ 0` in `U` tested from below: whenever `φ` is `C²` near `x ∈ U` and `u - φ` has a
local minimum at `x`, then `F(D²φ(x)) ≥ 0`. For a degenerate elliptic `F` this is the
Crandall-Ishii-Lions viscosity supersolution property; it is the min-stable reading of the
`F̄_η` constraint in Theorems 1.1 and 9.2 proposed as a correction. -/
def ViscFromBelowGE (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ∀ x ∈ U, ∀ φ : Rd d → ℝ, ContDiffAt ℝ 2 φ x → IsLocalMin (fun y => u y - φ y) x →
    0 ≤ F (hessian φ x)

/-- Crandall-Ishii-Lions viscosity subsolution of `F(D²u) = 0` in `U` (for `F` degenerate
elliptic, i.e. nonincreasing): `F(D²φ(x)) ≤ 0` at local maxima of `u - φ`. -/
abbrev ViscSubsolutionLE (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ViscFromAboveLE F U u

/-- Crandall-Ishii-Lions viscosity supersolution of `F(D²u) = 0` in `U` (for `F` degenerate
elliptic, i.e. nonincreasing): `F(D²φ(x)) ≥ 0` at local minima of `u - φ`. -/
abbrev ViscSupersolutionGE (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ViscFromBelowGE F U u

/-- Crandall-Ishii-Lions viscosity solution of `F(D²u) = 0` in `U`: a viscosity subsolution
(`F ≤ 0` tested from above) and a viscosity supersolution (`F ≥ 0` tested from below). This is
the sense of "`F̄_η(D²v̄) = 0` in `W`" in Theorem 9.1; continuity of `u` and the
boundary condition are separate conjuncts of the statement. -/
def ViscositySolution (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d)) (u : Rd d → ℝ) :
    Prop :=
  ViscSubsolutionLE F U u ∧ ViscSupersolutionGE F U u

theorem viscositySolution_iff (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d))
    (u : Rd d → ℝ) :
    ViscositySolution F U u ↔ ViscFromAboveLE F U u ∧ ViscFromBelowGE F U u :=
  Iff.rfl

theorem ViscFromAboveLE.mono {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U V : Set (Rd d)}
    {u : Rd d → ℝ} (h : ViscFromAboveLE F U u) (hVU : V ⊆ U) : ViscFromAboveLE F V u :=
  fun x hx => h x (hVU hx)

theorem ViscFromAboveGE.mono {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U V : Set (Rd d)}
    {u : Rd d → ℝ} (h : ViscFromAboveGE F U u) (hVU : V ⊆ U) : ViscFromAboveGE F V u :=
  fun x hx => h x (hVU hx)

theorem ViscFromBelowLE.mono {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U V : Set (Rd d)}
    {u : Rd d → ℝ} (h : ViscFromBelowLE F U u) (hVU : V ⊆ U) : ViscFromBelowLE F V u :=
  fun x hx => h x (hVU hx)

theorem ViscFromBelowGE.mono {F : Matrix (Fin d) (Fin d) ℝ → ℝ} {U V : Set (Rd d)}
    {u : Rd d → ℝ} (h : ViscFromBelowGE F U u) (hVU : V ⊆ U) : ViscFromBelowGE F V u :=
  fun x hx => h x (hVU hx)

/-- Testing `-F` from below with `≥` is testing `F` from below with `≤`. -/
theorem viscFromBelowGE_neg_iff (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d))
    (u : Rd d → ℝ) : ViscFromBelowGE (fun X => -F X) U u ↔ ViscFromBelowLE F U u := by
  simp only [ViscFromBelowGE, ViscFromBelowLE, neg_nonneg]

/-- Testing `-F` from above with `≤` is testing `F` from above with `≥`. -/
theorem viscFromAboveLE_neg_iff (F : Matrix (Fin d) (Fin d) ℝ → ℝ) (U : Set (Rd d))
    (u : Rd d → ℝ) : ViscFromAboveLE (fun X => -F X) U u ↔ ViscFromAboveGE F U u := by
  simp only [ViscFromAboveLE, ViscFromAboveGE, neg_nonpos]

/-! ### Weak-* convergence in `L^∞(ℝ^d)` -/

/-- Weak-* convergence of `f n` to `s` in `L^∞(ℝ^d) = (L¹(ℝ^d))*` (Theorem 1.1):
`∫ f n · g → ∫ s · g` for every Lebesgue-integrable `g : ℝ^d → ℝ`. The weak-* topology is
tested against `L¹`, so the definition only quantifies over integrable `g`. Measurability and
essential boundedness of the `f n` (uniformly in `n`) and of `s`, which make the integrands
integrable (the Bochner integral is `0` otherwise), are not part of the definition: they are
hypotheses or conjuncts of the statements using it (`s ∈ L^∞(ℝ^d)`). -/
def WeakStarTendsto (f : ℕ → Rd d → ℝ) (s : Rd d → ℝ) : Prop :=
  ∀ g : Rd d → ℝ, Integrable g →
    Tendsto (fun n => ∫ x, f n x * g x) atTop (𝓝 (∫ x, s x * g x))

end RandomSandpile

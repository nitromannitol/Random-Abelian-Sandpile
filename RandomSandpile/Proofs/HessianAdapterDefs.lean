import CZStatements.Identity

/-!
# Coordinate definitions for the Hessian estimate
-/

open MeasureTheory Metric Filter Topology
open scoped InnerProductSpace ContDiff ENNReal

namespace HessianAdapter

open PDE

/-- `∂ᵢ w` in coordinates. -/
noncomputable def dirDeriv {d : ℕ} (w : Vec d → ℝ) (i : Fin d) : Vec d → ℝ :=
  fun x => fderiv ℝ w x (basisVec i)

/-- The coordinate gradient of `f`. -/
noncomputable def gradVec {d : ℕ} (f : Vec d → ℝ) : Vec d → Vec d :=
  fun x j => fderiv ℝ f x (basisVec j)

/-- The coordinate Laplacian of `w`. -/
noncomputable def lapVec {d : ℕ} (w : Vec d → ℝ) : Vec d → ℝ :=
  fun x => ∑ j, fderiv ℝ (dirDeriv w j) x (basisVec j)

/-- The row estimate in ERL coordinates: `‖∇ ∂ᵢ w‖` in `L^p(B_{1/2})`. -/
def LocalUnitVecStmt (d : ℕ) : Prop :=
  ∀ (p : ℝ≥0∞), 2 ≤ p → p ≠ ⊤ → ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
    ∀ w : Vec d → ℝ, ContDiffOn ℝ ∞ w (euclideanBall (0 : Vec d) (4 / 3)) →
      eLpNorm (lapVec w) p (volumeOn (euclideanBall (0 : Vec d) (4 / 3))) +
        eLpNorm w ⊤ (volumeOn (euclideanBall (0 : Vec d) (4 / 3))) ≠ ⊤ →
      ∀ i : Fin d,
        eLpNorm (fun x => vecEuclideanNorm (gradVec (dirDeriv w i) x)) p
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          K * (eLpNorm (lapVec w) p (volumeOn (euclideanBall (0 : Vec d) (4 / 3))) +
            eLpNorm w ⊤ (volumeOn (euclideanBall (0 : Vec d) (4 / 3))))
/-- ERL's `L^p` estimate for `a = 1`, in `eLpNorm` form, for the ball pair `(1/2, 1)`. -/
def ErlLpStmt (d : ℕ) : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
    ∀ (u : H1Function (euclideanBall (0 : Vec d) 1)) (F : Vec d → Vec d),
      (∀ i : Fin d,
        AEStronglyMeasurable (fun x => F x i) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec d) 1)) →
      IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) (euclideanBall (0 : Vec d) 1) u
        (0 : Vec d → ℝ) F →
      eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
        K * (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
            (volumeOn (euclideanBall (0 : Vec d) 1)) +
          eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) 1)))

/-- `∂ᵢ w`, with its coordinate gradient, is an `H1Function` on the unit ball. -/
def SmoothH1Stmt (d : ℕ) : Prop :=
  ∀ w : Vec d → ℝ, ContDiffOn ℝ ∞ w (euclideanBall (0 : Vec d) (4 / 3)) → ∀ i : Fin d,
    ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
      u.toFun = dirDeriv w i ∧ u.grad = gradVec (dirDeriv w i)

/-- With `a = 1`, `f = 0`, `F = -(Δ w) eᵢ`, `∂ᵢ w` solves `-div (a ∇u) = f + div F` weakly on the
unit ball, and the hypotheses on `F` hold for every exponent. -/
def SmoothEqStmt (d : ℕ) : Prop :=
  ∀ w : Vec d → ℝ, ContDiffOn ℝ ∞ w (euclideanBall (0 : Vec d) (4 / 3)) → ∀ i : Fin d,
    ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      u.toFun = dirDeriv w i → u.grad = gradVec (dirDeriv w i) →
      (∀ j : Fin d,
        AEStronglyMeasurable (fun x => (Pi.single i (-lapVec w x) : Vec d) j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
      (∀ q : ℝ≥0∞,
        MemLp (fun x => vecEuclideanNorm (Pi.single i (-lapVec w x) : Vec d)) q
          (volumeOn (euclideanBall (0 : Vec d) 1))) ∧
      IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) (euclideanBall (0 : Vec d) 1) u
        (0 : Vec d → ℝ) (fun x => Pi.single i (-lapVec w x))

/-- The `L²` bound for the rows of the Hessian, in ERL coordinates. -/
def L2HessVecStmt (d : ℕ) : Prop :=
  ∃ C₂ : ℝ≥0∞, C₂ ≠ ⊤ ∧
    ∀ w : Vec d → ℝ, ContDiffOn ℝ ∞ w (euclideanBall (0 : Vec d) (4 / 3)) → ∀ i : Fin d,
      eLpNorm (fun x => vecEuclideanNorm (gradVec (dirDeriv w i) x)) 2
          (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
        C₂ * (eLpNorm (lapVec w) 2 (volumeOn (euclideanBall (0 : Vec d) (4 / 3))) +
          eLpNorm w 2 (volumeOn (euclideanBall (0 : Vec d) (4 / 3))))

end HessianAdapter

import RandomSandpile.Draft.Section5
import RandomSandpile.Infra.ConcaveEnvelope

/-! # Lemma 5.2 (the discrete Alexandroff-Bakelman-Pucci estimate): proof steps

The printed proof of Lemma 5.2 (`ABPStmt`, `paper/random_piles-corrected.tex`) decomposed
into step statements, and the reduction `abp_of_steps` concluding exactly `ABPStmt`. Notation:
`B_n = ballZ0 n`, `B̄_n = dClosure B_n`, `∂B_n = bdry B_n`.

* `TiltedPlaneAboveStmt` (ABPeq:1): if `a := w(x) - max_{∂A} w > 0` and
  `|p| D < a`, where `D` bounds `|z - x|` on `Ā`, then the plane of slope `p` through
  `(x, w(x))` lies strictly above `w` on `∂A`. Following the distance bound is
  required on the closure `Ā` (the printed proof states it on `B_n` with `diam(B_n)` but uses
  it at points of `∂B_n`);
* `SlidePlaneStmt`: if a plane of slope `p` through `(x, w(x))`, `x ∈ A`, lies
  strictly above `w` on `∂A`, then lowering it until it touches the graph of `w` over the finite
  set `Ā` gives a touching point `y ∈ A` (not on `∂A`), so `p ∈ ∂⁺(w, y, A) ⊆ ∂⁺(w, A)`;
* `ClosureBallDiamStmt` (the standard fact `diam(B̄_n) ≤ C n`): `|z - x| ≤ 3n` for
  `x ∈ B_n`, `z ∈ B̄_n`;
* `BallVolumeRadiusStmt` (the volume of a Euclidean ball): a set `E ⊆ ℝ^d`
  containing the ball `B_r(0)` has `r ≤ c_d |E|^{1/d}`;
* `SubGradNegVolumeStmt` ("the proof for `μ*` is identical"):
  `|∂⁻(w, A)| = |∂⁺(-w, A)|`, since `p ∈ ∂⁻(w, y, A)` iff `-p ∈ ∂⁺(-w, y, A)`.

The reduction proves the supergradient estimate `max_{B_n} w ≤ S + 3 c_d n |∂⁺(w, B_n)|^{1/d}` for
every upper bound `S` of `w` on `∂B_n` (`abp_supGrad_of_steps`) and applies it to `w` (for `μ`) and
to `-w` (for `μ*`). -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal

namespace RandomSandpile

namespace ABP

/-! ### Lattice balls (helpers) -/

variable {d : ℕ}

theorem toE_zero : toE (0 : Site d) = 0 := by
  ext i; simp

theorem toE_add (x y : Site d) : toE (x + y) = toE x + toE y := by
  ext i; simp

theorem mem_ballZ0 {r : ℝ} {x : Site d} : x ∈ ballZ0 r ↔ ‖toE x‖ < r := by
  simp [ballZ0, ballZ, toE_zero]

theorem ballZ0_subset_cubeZ0 (r : ℝ) : (ballZ0 r : Set (Site d)) ⊆ cubeZ0 r := by
  intro x hx
  simp only [cubeZ0, cubeZ, Set.mem_setOf_eq, Pi.zero_apply, sub_zero]
  intro i
  have h1 := PiLp.norm_apply_le (toE x) i
  simp only [toE_apply, Real.norm_eq_abs] at h1
  linarith [mem_ballZ0.1 hx]

/-- The lattice ball `B_r` is finite. -/
theorem ballZ0_finite (r : ℝ) : (ballZ0 (d := d) r).Finite :=
  (cubeZ0_finite r).subset (ballZ0_subset_cubeZ0 r)

theorem norm_toE_unit (i : Fin d) : ‖toE (unit i)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [unit, Pi.single_apply, apply_ite]

end ABP

open ABP

/-- Step (ABPeq:1). Let `x ∈ A`, let `S` bound `w` from above on `∂A` and
`D` bound `|z - x|` on `Ā`. If `|p| D < w(x) - S`, the plane `z ↦ w(x) + p · (z - x)` lies
strictly above `w` on `∂A`. -/
def TiltedPlaneAboveStmt : Prop :=
  ∀ (d : ℕ) (w : Site d → ℝ) (A : Set (Site d)) (x : Site d), x ∈ A → ∀ (S D : ℝ) (p : Rd d),
    (∀ z ∈ bdry A, w z ≤ S) → (∀ z ∈ dClosure A, ‖toE z - toE x‖ ≤ D) →
      ‖p‖ * D < w x - S → ∀ z ∈ bdry A, w z < w x + inner ℝ p (toE z - toE x)

/-- Step, the sliding argument. Let `A` be finite and `x ∈ A`. If the plane
`z ↦ w(x) + p · (z - x)` lies strictly above `w` on `∂A`, then `p ∈ ∂⁺(w, A)`: the plane, lowered
until it touches the graph of `w` over `Ā`, touches it at a point of `A`. -/
def SlidePlaneStmt : Prop :=
  ∀ (d : ℕ) (w : Site d → ℝ) (A : Set (Site d)), A.Finite → ∀ x ∈ A, ∀ p : Rd d,
    (∀ z ∈ bdry A, w z < w x + inner ℝ p (toE z - toE x)) → p ∈ supGradSet w A

/-- Step (standard fact, `diam(B̄_n) ≤ C n`). For `x ∈ B_n` and `z ∈ B̄_n`, `|z - x| ≤ 3n`. -/
def ClosureBallDiamStmt : Prop :=
  ∀ (d : ℕ) (n : ℕ), ∀ x ∈ ballZ0 (d := d) (n : ℝ), ∀ z ∈ dClosure (ballZ0 (d := d) (n : ℝ)),
    ‖toE z - toE x‖ ≤ 3 * n

/-- Step (the volume of a Euclidean ball). For `d ≥ 1` there is `c_d > 0` such that
every `E ⊆ ℝ^d` of finite Lebesgue measure containing the ball `B_r(0)`, `r ≥ 0`, satisfies
`r ≤ c_d |E|^{1/d}`. -/
def BallVolumeRadiusStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∃ c : ℝ, 0 < c ∧ ∀ (r : ℝ), 0 ≤ r → ∀ E : Set (Rd d),
    Metric.ball (0 : Rd d) r ⊆ E → volume E ≠ ⊤ → r ≤ c * (volume E).toReal ^ (1 / (d : ℝ))

/-- Step. The subgradient set of `w` and the supergradient set of `-w` have the same
Lebesgue measure: `p ∈ ∂⁻(w, y, A)` iff `-p ∈ ∂⁺(-w, y, A)`. -/
def SubGradNegVolumeStmt : Prop :=
  ∀ (d : ℕ) (w : Site d → ℝ) (A : Set (Site d)),
    volume (subGradSet w A) = volume (supGradSet (fun z => -w z) A)

/-- The supergradient ABP estimate on `B_n` from the steps: for every upper bound `S` of `w` on
`∂B_n` and every finite upper bound `V` of `|∂⁺(w, B_n)|`,
`w(x) ≤ S + 3 c n V^{1/d}` on `B_n`. -/
theorem abp_supGrad_of_steps (hT : TiltedPlaneAboveStmt) (hS : SlidePlaneStmt)
    (hD : ClosureBallDiamStmt) {d : ℕ} {c : ℝ} (hc : 0 < c)
    (hrad : ∀ (r : ℝ), 0 ≤ r → ∀ E : Set (Rd d), Metric.ball (0 : Rd d) r ⊆ E → volume E ≠ ⊤ →
      r ≤ c * (volume E).toReal ^ (1 / (d : ℝ)))
    (n : ℕ) (w : Site d → ℝ) (S : ℝ) (hSb : ∀ z ∈ bdry (ballZ0 (d := d) (n : ℝ)), w z ≤ S)
    (V : ℝ≥0∞) (hV : volume (supGradSet w (ballZ0 (n : ℝ))) ≤ V) (hVt : V ≠ ⊤)
    (x : Site d) (hx : x ∈ ballZ0 (d := d) (n : ℝ)) :
    w x ≤ S + 3 * c * n * V.toReal ^ (1 / (d : ℝ)) := by
  have hpow : 0 ≤ V.toReal ^ (1 / (d : ℝ)) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  by_cases ha : w x ≤ S
  · have : 0 ≤ 3 * c * n * V.toReal ^ (1 / (d : ℝ)) := by positivity
    linarith
  rw [not_le] at ha
  have hn : (0 : ℝ) < n := lt_of_le_of_lt (norm_nonneg _) (mem_ballZ0.1 hx)
  set D : ℝ := 3 * n with hDdef
  have hDpos : 0 < D := by positivity
  set r : ℝ := (w x - S) / D with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hDpos.le
  have hball : Metric.ball (0 : Rd d) r ⊆ supGradSet w (ballZ0 (n : ℝ)) := by
    intro p hp
    rw [mem_ball_zero_iff] at hp
    have hpD : ‖p‖ * D < w x - S := by
      rw [hr, lt_div_iff₀ hDpos] at hp
      exact hp
    exact hS d w _ (ballZ0_finite _) x hx p
      (hT d w _ x hx S D p hSb (hD d n x hx) hpD)
  have hVle : (volume (supGradSet w (ballZ0 (n : ℝ)))).toReal ≤ V.toReal :=
    ENNReal.toReal_mono hVt hV
  have hrle := hrad r hr0 _ hball (ne_top_of_le_ne_top hVt hV)
  have hmono : (volume (supGradSet w (ballZ0 (n : ℝ)))).toReal ^ (1 / (d : ℝ)) ≤
      V.toReal ^ (1 / (d : ℝ)) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hVle (by positivity)
  have hrV : r ≤ c * V.toReal ^ (1 / (d : ℝ)) :=
    hrle.trans (mul_le_mul_of_nonneg_left hmono hc.le)
  have hwx : w x - S = r * D := by rw [hr]; field_simp
  have : r * D ≤ c * V.toReal ^ (1 / (d : ℝ)) * D := mul_le_mul_of_nonneg_right hrV hDpos.le
  rw [hDdef] at this
  nlinarith [this, hwx]

/-- Lemma 5.2 (`ABPStmt`) from its steps. -/
theorem abp_of_steps (hT : TiltedPlaneAboveStmt) (hS : SlidePlaneStmt)
    (hD : ClosureBallDiamStmt) (hB : BallVolumeRadiusStmt) (hN : SubGradNegVolumeStmt) :
    ABPStmt := by
  intro d hd
  obtain ⟨c, hc, hrad⟩ := hB d (by omega)
  refine ⟨3 * c, by positivity, fun n η l M _ => ⟨fun hμ w hw x hx => ?_, fun hμ w hw x hx => ?_⟩⟩
  · have hfin : (w '' bdry (ballZ0 (d := d) (n : ℝ))).Finite :=
      ((dClosure_finite (ballZ0_finite _)).subset (bdry_subset_dClosure _)).image w
    refine abp_supGrad_of_steps hT hS hD hc hrad n w _
      (fun z hz => le_csSup hfin.bddAbove (Set.mem_image_of_mem w hz)) _ ?_ hμ x hx
    exact le_iSup₂ (f := fun w _ => volume (supGradSet w (ballZ0 (d := d) (n : ℝ)))) w hw
  · have hfin : (w '' bdry (ballZ0 (d := d) (n : ℝ))).Finite :=
      ((dClosure_finite (ballZ0_finite _)).subset (bdry_subset_dClosure _)).image w
    have hV : volume (supGradSet (fun z => -w z) (ballZ0 (d := d) (n : ℝ))) ≤
        muStar (ballZ0 (n : ℝ)) η l M := by
      rw [← hN]
      exact le_iSup₂ (f := fun w _ => volume (subGradSet w (ballZ0 (d := d) (n : ℝ)))) w hw
    have := abp_supGrad_of_steps hT hS hD hc hrad n (fun z => -w z)
      (-sInf (w '' bdry (ballZ0 (n : ℝ))))
      (fun z hz => neg_le_neg (csInf_le hfin.bddBelow (Set.mem_image_of_mem w hz))) _ hV hμ x hx
    linarith

end RandomSandpile

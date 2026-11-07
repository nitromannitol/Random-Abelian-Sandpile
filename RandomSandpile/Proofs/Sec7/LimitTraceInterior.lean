import RandomSandpile.Proofs.Sec7.FreeOdometerLimitRegular
import RandomSandpile.Proofs.Sec7.LimitObstacle
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityHessianTrace
import RandomSandpile.Infra.SupConvolution

/-! # Theorem 1.1: the trace bound in `W` at quadratics touching from below

`limitTraceInterior_of_touching : PegdenSmartTouchingStmt → LimitTraceInteriorStmt`. Pegden-Smart's
Proposition 2.5 (`PegdenSmartTouchingStmt`, admitted verbatim) turns one-sided touching into
twice differentiability at nearby points, and the Peano form of the trace bound is proved
(`freeOdometerLimitHessianTrace`, Lemma 7.6(3)).

* `exists_taylor_of_touch_below`: if a quadratic with symmetric matrix `N` touches from below a
  continuous `v` with `|Δv| ≤ K` (viscosity) at `a`, then in every open `U ∋ a` and for every
  `σ > 0` there is `b ∈ U` where `v` has a second-order Peano expansion with symmetric `X'` and
  `q_{N - σI} ≤ q_{X'}`. Proof: the strict quadratic `P = v(a) + p·(· - a) + q_{N - σI}(· - a)`
  has `P - v ≤ -(σ/2) r²` on `∂B_r(a)` and `P - v = 0` at `a`; Proposition 2.5 for `P` and `v` on
  `B_r(a)` gives `b` with Peano expansions of `P` (matrix `X`) and `v` (matrix `X'`) and
  `X' - X ⪰ δI`; touching `P` from above by the paraboloid of `X + δI` gives
  `q_{N - σI} ≤ q_{X + δI} = q_X + (δ/2)|·|² ≤ q_{X'}` (`qM_le_hessian_of_isLocalMax`).
* `limitTraceInterior_of_touching`: with `U = W`, `tr X' ≥ tr N - dσ`, and
  `tr X' ≤ 2d - 1 - E η(0)` by `freeOdometerLimitHessianTrace`; let `σ → 0`. The viscosity
  bounds of the limits are `freeLimitRegular_of_bounded`.
-/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

namespace LimitTrace

variable {d : ℕ}

/-- The quadratic `c + p·(· - a) + q_N(· - a)` in the `innerSL` form of `contDiff_paraboloid`. -/
theorem quad_eq (c : ℝ) (p a : Rd d) (N : Matrix (Fin d) (Fin d) ℝ) :
    (fun y => c + inner ℝ p (y - a) + qM N (y - a)) =
      fun z => c + innerSL ℝ p (z - a) + qM N (z - a) := by
  funext z; simp [innerSL_apply_apply]

theorem continuous_quad (c : ℝ) (p a : Rd d) (N : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun y => c + inner ℝ p (y - a) + qM N (y - a)) := by
  rw [quad_eq]; exact (contDiff_paraboloid c p a N (n := 0)).continuous

/-- A quadratic satisfies `tr D² + K ≥ 0` tested from above once `K ≥ -tr N`. -/
theorem quad_viscAbove {c : ℝ} {p a : Rd d} {N : Matrix (Fin d) (Fin d) ℝ} {U : Set (Rd d)}
    {K : ℝ} (hK : -N.trace ≤ K) :
    ViscFromAboveGE (fun X => X.trace + K) U (fun y => c + inner ℝ p (y - a) + qM N (y - a)) := by
  intro x _ φ hφ hmax
  have h := trace_le_trace_of_qM_le (qM_le_hessian_of_isLocalMax hφ c p a N hmax)
  simp only
  linarith

/-- A quadratic satisfies `tr D² - K ≤ 0` tested from below once `K ≥ tr N + d`. -/
theorem quad_viscBelow {c : ℝ} {p a : Rd d} {N : Matrix (Fin d) (Fin d) ℝ} (hN : N.IsSymm)
    {U : Set (Rd d)} {K : ℝ} (hK : N.trace + d ≤ K) :
    ViscFromBelowLE (fun X => X.trace - K) U (fun y => c + inner ℝ p (y - a) + qM N (y - a)) := by
  intro x _ φ hφ hmin
  set g : Rd d := (InnerProductSpace.toDual ℝ (Rd d)).symm (fderiv ℝ φ x) with hg
  have ht := touch_below_of_isLocalMin hφ hmin one_pos
  have hmax : IsLocalMax (fun y => ((c + inner ℝ p (x - a) + qM N (x - a)) + inner ℝ g (y - x) +
      qM (hessian φ x - (1 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - x)) -
        (fun y => c + inner ℝ p (y - a) + qM N (y - a)) y) x := by
    filter_upwards [ht] with y hy
    simp only [sub_self, inner_zero_right, qM_zero_right, add_zero]
    linarith
  have hPc : ContDiffAt ℝ 2 (fun y => c + inner ℝ p (y - a) + qM N (y - a)) x := by
    rw [quad_eq]; exact (contDiff_paraboloid c p a N).contDiffAt
  have h := qM_le_hessian_of_isLocalMax hPc _ g x _ hmax
  have hH : hessian (fun y => c + inner ℝ p (y - a) + qM N (y - a)) x = N := by
    rw [quad_eq]; exact hessian_quadratic c p a hN x
  rw [hH] at h
  have htr := trace_le_trace_of_qM_le h
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    one_mul] at htr
  simp only
  linarith

/-- **One-sided touching gives nearby points of twice differentiability** (from Pegden-Smart's
Proposition 2.5). -/
theorem exists_taylor_of_touch_below (hT : PegdenSmartTouchingStmt) (hd : 2 ≤ d)
    {v : Rd d → ℝ} (hvc : Continuous v) {K : ℝ}
    (hA : ViscFromAboveGE (fun X => X.trace + K) Set.univ v)
    (hB : ViscFromBelowLE (fun X => X.trace - K) Set.univ v) {a p : Rd d}
    {N : Matrix (Fin d) (Fin d) ℝ} (hN : N.IsSymm)
    (htouch : ∀ᶠ y in 𝓝 a, v a + inner ℝ p (y - a) + qM N (y - a) ≤ v y)
    {U : Set (Rd d)} (hU : IsOpen U) (haU : a ∈ U) {σ : ℝ} (hσ : 0 < σ) :
    ∃ b ∈ U, ∃ (p' : Rd d) (X' : Matrix (Fin d) (Fin d) ℝ), X'.IsSymm ∧
      HasSecondOrderTaylorAt v b p' X' ∧
        ∀ h : Rd d, qM (N - σ • (1 : Matrix (Fin d) (Fin d) ℝ)) h ≤ qM X' h := by
  set N' : Matrix (Fin d) (Fin d) ℝ := N - σ • (1 : Matrix (Fin d) (Fin d) ℝ) with hN'
  have hN's : N'.IsSymm := PegdenSmartRegularity.isSymm_sub_smul_one hN σ
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU a haU
  obtain ⟨ρ', hρ', ht⟩ := Metric.eventually_nhds_iff.1 htouch
  set r : ℝ := min ρ ρ' / 2 with hr
  have hr0 : 0 < r := by positivity
  set K' : ℝ := max K (|N'.trace| + d) with hK'
  have hfront : ∀ y ∈ frontier (ball a r),
      (fun y => v a + inner ℝ p (y - a) + qM N' (y - a)) y - v y ≤ -(σ / 2 * r ^ 2) := by
    intro y hy
    rw [frontier_ball a hr0.ne'] at hy
    have hy' : dist y a = r := hy
    have h1 := ht (show dist y a < ρ' by rw [hy']; linarith [min_le_right ρ ρ'])
    have hn : ‖y - a‖ = r := by rw [← dist_eq_norm]; exact hy'
    simp only [hN', qM_sub_mat, qM_smul_one, hn]
    linarith
  have hpos : ∃ x ∈ ball a r,
      -(σ / 2 * r ^ 2) < (fun y => v a + inner ℝ p (y - a) + qM N' (y - a)) x - v x :=
    ⟨a, mem_ball_self hr0, by
      simp only [sub_self, inner_zero_right, qM_zero_right, add_zero]
      have : 0 < σ / 2 * r ^ 2 := by positivity
      linarith⟩
  have hvol := hT d hd (ball a r) isOpen_ball isBounded_ball K'
    (fun y => v a + inner ℝ p (y - a) + qM N' (y - a)) v
    (continuous_quad _ _ _ _).continuousOn hvc.continuousOn
    (quad_viscAbove (by have := neg_abs_le N'.trace; have : (0 : ℝ) ≤ d := by positivity
                        exact le_max_of_le_right (by linarith)))
    (quad_viscBelow hN's (le_max_of_le_right (by linarith [le_abs_self N'.trace])))
    (fun x _ φ hφ hm => (hA.trace_mono (le_max_left K _)) x trivial φ hφ hm)
    (fun x _ φ hφ hm => (hB.trace_mono (le_max_left K _)) x trivial φ hφ hm)
    _ hfront hpos
  obtain ⟨b, ⟨hbU, -, q, p', X, X', hX, hX', hTP, hTv, δ, hδ, hpd⟩⟩ :=
    nonempty_of_measure_ne_zero hvol.ne'
  refine ⟨b, hball (ball_subset_ball (by linarith [min_le_left ρ ρ']) hbU), p', X', hX', hTv,
    fun h => ?_⟩
  -- `q_{X'} ≥ q_X + (δ/2)|·|²`
  have hpd' : (X' - X - δ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
    have e : -(δ • (1 : Matrix (Fin d) (Fin d) ℝ)) - (X - X') =
        X' - X - δ • (1 : Matrix (Fin d) (Fin d) ℝ) := by abel
    rw [← e]; exact hpd.posSemidef
  have h2 := qM_sub_ge_of_psd hpd' h
  -- `q_{N'} ≤ q_{X + δI}`: the paraboloid of `X + δI` touches `P` from above at `b`
  have hXδ : (X + δ • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
    hX.add (Matrix.isSymm_one.smul δ)
  have hmax : IsLocalMax (fun y => (v a + inner ℝ p (y - a) + qM N' (y - a)) -
      (fun z => (fun y => v a + inner ℝ p (y - a) + qM N' (y - a)) b + innerSL ℝ q (z - b) +
        qM (X + δ • (1 : Matrix (Fin d) (Fin d) ℝ)) (z - b)) y) b := by
    filter_upwards [hTP.touch_above hδ] with y hy
    simp only [innerSL_apply_apply, sub_self, inner_zero_right, qM_zero_right, add_zero]
    linarith
  have h1 := qM_le_hessian_of_isLocalMax ((contDiff_paraboloid _ q b _ (n := 2)).contDiffAt)
    (v a) p a N' hmax h
  rw [hessian_quadratic _ q b hXδ, qM_add_mat, qM_smul_one] at h1
  linarith

end LimitTrace

open LimitTrace in
/-- **`Δv ≤ 2d - 1 - E η(0)` in `W`** at quadratics touching from below (`LimitTraceInteriorStmt`),
from Pegden-Smart's Proposition 2.5. -/
theorem limitTraceInterior_of_touching (hT : PegdenSmartTouchingStmt) : LimitTraceInteriorStmt := by
  intro d hd E W hW
  obtain ⟨Ω₂, hΩ₂, hTr⟩ := freeOdometerLimitHessianTrace d hd E W hW
  filter_upwards [ae_all_iff.2 E.bounded, mem_ae_iff.2 hΩ₂] with η hbd h2
  intro v hv a ha p N hN htouch
  obtain ⟨hvc, -, hA, hB⟩ := freeLimitRegular_of_bounded hd hW hbd hv
  obtain ⟨nk, hnk, hconv⟩ := hv
  have hdpos : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                                 linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨b, hbW, p', X', hX', hTv, hq⟩ := exists_taylor_of_touch_below hT hd hvc hA hB hN
    htouch hW.2.1 ha (σ := ε / d) (by positivity)
  have h1 := hTr η h2 nk hnk v hconv b hbW p' X' hX' hTv
  have h3 := trace_le_trace_of_qM_le hq
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul] at h3
  have h4 : ε / d * (d : ℝ) = ε := by field_simp
  linarith

end RandomSandpile

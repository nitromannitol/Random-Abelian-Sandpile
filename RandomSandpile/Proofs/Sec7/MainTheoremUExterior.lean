import RandomSandpile.Proofs.Sec7.LimitTraceInterior
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTranslates

/-! # Theorem 1.1, step: the supersolution property outside `W̄`

`exteriorSupersolution_of_touching : PegdenSmartTouchingStmt → ExteriorSupersolutionStmt`
(Pegden-Smart, Lemma 4.1, at quadratics touching from below; `paper/random_piles-corrected.tex` and 1388, repair 3 of `RandomSandpile/Steps/Sec7/MainTheorem.lean`).

If a quadratic with matrix `N` touches a subsequential limit `v` from below at `a ∉ W̄`, then
Pegden-Smart's Proposition 2.5 gives `b ∉ W̄` where `v` has a second-order Peano expansion with
matrix `X' ⪰ N - (ε/2) I` (`LimitTrace.exists_taylor_of_touch_below`, with the viscosity bounds of
`freeLimitRegular_of_bounded`). Near `n_k b` the pile `η 𝟙_{W_{n_k}}` vanishes, so
`Δ_{ℤ^d} v_{n_k} ≤ 2d - 1` there, and Pegden-Smart's Lemma 4.1 in the Peano form
(`pegdenSmartIntegerSuperharmonic`, proved) gives `u` with `Δ_{ℤ^d} u ≤ 2d - 1` and
`u ≥ q_{X' - (ε/2)I} ≥ q_{N - εI}`. The subsequence is shifted by one so that `n_k ≥ 1`. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

open LimitTrace in
/-- **Step** (`ExteriorSupersolutionStmt`) from Pegden-Smart's Proposition 2.5. -/
theorem exteriorSupersolution_of_touching (hT : PegdenSmartTouchingStmt) :
    ExteriorSupersolutionStmt := by
  intro d hd W hW ηmin ηmax η hbd v hv a p N ha hN htouch ε hε
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hvc, -, hA, hB⟩ := freeLimitRegular_of_bounded hd hW hbd hv
  obtain ⟨nk, hnk, hconv⟩ := hv
  obtain ⟨b, hb, p', X', hX', hTv, hq⟩ := exists_taylor_of_touch_below hT hd hvc hA hB hN
    htouch isClosed_closure.isOpen_compl ha (σ := ε / 2) (half_pos hε)
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl b hb
  -- the shifted subsequence `n_{k+1} ≥ 1`
  set mk : ℕ → ℕ := fun k => nk (k + 1) with hmk
  have hmono : StrictMono mk := fun i j h => hnk (Nat.succ_lt_succ h)
  have hconv' : TendstoUniformly
      (fun k => rescaleOdo (freeOdometer η (discretize W (mk k))) (mk k)) v atTop :=
    fun u hu => (tendsto_add_atTop_nat 1).eventually (hconv u hu)
  have hlap : ∀ k, ∀ z : Site d, ‖((mk k : ℝ))⁻¹ • toE z - b‖ < r →
      lap (freeOdometer η (discretize W (mk k))) z ≤ 2 * (d : ℤ) - 1 := by
    intro k z hz
    have hk : 1 ≤ mk k := by
      have : nk 0 < nk (k + 1) := hnk (show 0 < k + 1 by omega)
      show 1 ≤ nk (k + 1)
      omega
    have hn0 : (mk k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hzW : z ∉ discretize W (mk k) := by
      intro hzW
      have hmem : ((mk k : ℝ))⁻¹ • toE z ∈ W :=
        (Set.mem_smul_set_iff_inv_smul_mem₀ hn0 _ _).1 hzW
      exact hrb (by rw [mem_ball, dist_eq_norm]; exact hz) (subset_closure hmem)
    have h := PegdenSmartRegularity.lap_freeOdometer_add_indicator_le hd1 η hW.1 (mk k) z
    rw [Set.indicator_of_notMem hzW] at h
    linarith
  obtain ⟨u, hu⟩ := pegdenSmartIntegerSuperharmonic d hd mk hmono
    (fun k => freeOdometer η (discretize W (mk k))) v b r hr hlap hconv'.tendstoUniformlyOn
    p' X' hX' hTv (ε / 2) (half_pos hε)
  refine ⟨u, fun x => ⟨(hu x).1, le_trans ?_ (hu x).2⟩⟩
  have h1 := hq (toE x)
  simp only [qMZ]
  rw [qM_sub_mat, qM_smul_one] at h1 ⊢
  rw [qM_sub_mat, qM_smul_one]
  have : 0 ≤ ε * ‖toE x‖ ^ 2 := by positivity
  linarith

end RandomSandpile

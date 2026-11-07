import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessAA

/-! Local Arzelà–Ascoli for asymptotically equicontinuous sequences. -/

noncomputable section

open Filter Topology

namespace RandomSandpile

/-- Local boundedness and asymptotic equicontinuity give a locally uniformly
convergent subsequence with continuous limit. -/
theorem arzelaAscoli_locallyUniform_of_eventualBounds
    (d : ℕ) (F : ℕ → Rd d → ℝ)
    (hK : ∀ m : ℕ, ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖x‖ ≤ m → |F n x| ≤ K)
    (hE : ∀ m : ℕ, ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ,
      ∀ n ≥ N, ∀ x y, ‖x‖ ≤ m → ‖y‖ ≤ m → dist x y < δ →
        |F n x - F n y| < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : Rd d → ℝ, Continuous V ∧
      TendstoLocallyUniformly (fun j => F (φ j)) V atTop := by
  choose K N hK using hK
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rd d)
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_countable_of_bound D hDc F
    (fun x => |K ⌈‖x‖⌉₊| + ∑ i ∈ Finset.range (N ⌈‖x‖⌉₊), |F i x|) (by
      intro n x
      by_cases hn : N ⌈‖x‖⌉₊ ≤ n
      · have h := hK _ n hn x (Nat.le_ceil _)
        have hs : 0 ≤ ∑ i ∈ Finset.range (N ⌈‖x‖⌉₊), |F i x| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith [le_abs_self (K ⌈‖x‖⌉₊)]
      · have hs : |F n x| ≤ ∑ i ∈ Finset.range (N ⌈‖x‖⌉₊), |F i x| :=
          Finset.single_le_sum (s := Finset.range (N ⌈‖x‖⌉₊)) (f := fun i => |F i x|)
            (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_of_not_ge hn))
        linarith [abs_nonneg (K ⌈‖x‖⌉₊)])
  have hcauchy : ∀ q ∈ D, CauchySeq (fun j => F (φ j) q) := fun q hq =>
    (hlim q hq).choose_spec.cauchySeq
  have hunif : ∀ m : ℕ, ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, ∀ x, ‖x‖ ≤ m →
      |F (φ j) x - F (φ k) x| < ε := by
    intro m ε hε
    obtain ⟨δ, hδ, N, hN⟩ := hE (m + 1) (ε / 3) (by positivity)
    set r := min δ 1
    have hr : 0 < r := lt_min hδ one_pos
    have hcov : Metric.closedBall (0 : Rd d) m ⊆ ⋃ q : D, Metric.ball (q : Rd d) r := by
      intro x _
      obtain ⟨q, hq, hxq⟩ := hDd.exists_dist_lt x hr
      exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, Metric.mem_ball.2 hxq⟩
    obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : Rd d) m).elim_finite_subcover
      (fun q : D => Metric.ball (q : Rd d) r) (fun _ => Metric.isOpen_ball) hcov
    have hNq : ∀ q : D, ∃ Nq, ∀ j ≥ Nq, ∀ k ≥ Nq,
        dist (F (φ j) q) (F (φ k) q) < ε / 3 :=
      fun q => Metric.cauchySeq_iff.1 (hcauchy q q.2) _ (by positivity)
    choose Nq hNq using hNq
    refine ⟨max N (T.sup Nq), fun j hj k hk x hx => ?_⟩
    have hxb : x ∈ Metric.closedBall (0 : Rd d) m := mem_closedBall_zero_iff.2 hx
    obtain ⟨q, hqT, hxq⟩ := Set.mem_iUnion₂.1 (hT hxb)
    have hxq' : dist x q < r := Metric.mem_ball.1 hxq
    have hq : ‖(q : Rd d)‖ ≤ (m + 1 : ℕ) := by
      have h1 := norm_le_insert' (q : Rd d) x
      rw [← dist_eq_norm, dist_comm] at h1
      have hr1 : r ≤ 1 := min_le_right _ _
      push_cast
      linarith
    have hx1 : ‖x‖ ≤ (m + 1 : ℕ) := by push_cast; linarith
    have hjN : N ≤ φ j := le_trans (le_trans (le_max_left _ _) hj) (hφ.id_le j)
    have hkN : N ≤ φ k := le_trans (le_trans (le_max_left _ _) hk) (hφ.id_le k)
    have hjq : j ≥ Nq q := le_trans (Finset.le_sup hqT) (le_trans (le_max_right _ _) hj)
    have hkq : k ≥ Nq q := le_trans (Finset.le_sup hqT) (le_trans (le_max_right _ _) hk)
    have hdist : dist x q < δ := lt_of_lt_of_le hxq' (min_le_left _ _)
    have hA := hN (φ j) hjN x q hx1 hq hdist
    have hB := hN (φ k) hkN x q hx1 hq hdist
    have hC := hNq q j hjq k hkq
    rw [Real.dist_eq] at hC
    have htri : |F (φ j) x - F (φ k) x| ≤
        |F (φ j) x - F (φ j) q| + |F (φ j) q - F (φ k) q| +
          |F (φ k) x - F (φ k) q| := by
      have h1 := abs_sub_le (F (φ j) x) (F (φ j) q) (F (φ k) x)
      have h2 := abs_sub_le (F (φ j) q) (F (φ k) q) (F (φ k) x)
      rw [abs_sub_comm (F (φ k) q) (F (φ k) x)] at h2
      linarith
    linarith
  have hpt : ∀ x, ∃ v, Tendsto (fun j => F (φ j) x) atTop (𝓝 v) := fun x =>
    cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hunif ⌈‖x‖⌉₊ ε hε
      exact ⟨N, fun a ha b hb => by rw [Real.dist_eq]; exact hN a ha b hb x (Nat.le_ceil _)⟩)
  choose V hV using hpt
  have hTU : ∀ m : ℕ, TendstoUniformlyOn (fun j => F (φ j)) V atTop
      (Metric.closedBall (0 : Rd d) m) := by
    intro m
    have hUC : UniformCauchySeqOn (fun j => F (φ j)) atTop (Metric.closedBall (0 : Rd d) m) := by
      rw [Metric.uniformCauchySeqOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hunif m ε hε
      exact ⟨N, fun a ha b hb x hx => by
        rw [Real.dist_eq]; exact hN a ha b hb x (mem_closedBall_zero_iff.1 hx)⟩
    exact hUC.tendstoUniformlyOn_of_tendsto fun x _ => hV x
  have hcont : Continuous V := by
    rw [Metric.continuous_iff]
    intro x ε hε
    set m : ℕ := ⌈‖x‖⌉₊ + 1 with hm
    obtain ⟨δ, hδ, N, hN⟩ := hE m (ε / 2) (by positivity)
    refine ⟨min 1 δ, lt_min one_pos hδ, fun y hy => ?_⟩
    have hy1 : dist y x < 1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hyδ : dist y x < δ := lt_of_lt_of_le hy (min_le_right _ _)
    have hceil : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
    have hmR : (m : ℝ) = (⌈‖x‖⌉₊ : ℝ) + 1 := by rw [hm]; push_cast; ring
    have hxm : ‖x‖ ≤ m := by rw [hmR]; linarith
    have hym : ‖y‖ ≤ m := by
      have h1 := norm_le_insert' y x
      rw [← dist_eq_norm] at h1
      rw [hmR]; linarith
    have hbound : |V y - V x| ≤ ε / 2 := by
      apply le_of_tendsto ((hV y).sub (hV x)).abs
      filter_upwards [eventually_ge_atTop N] with j hj
      exact (hN (φ j) (le_trans hj (hφ.id_le j)) y x hym hxm hyδ).le
    rw [Real.dist_eq]
    linarith
  refine ⟨φ, hφ, V, hcont, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro C hC
  obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall (0 : Rd d)
  exact (hTU ⌈r⌉₊).mono (hr.trans (Metric.closedBall_subset_closedBall (Nat.le_ceil _)))

end RandomSandpile

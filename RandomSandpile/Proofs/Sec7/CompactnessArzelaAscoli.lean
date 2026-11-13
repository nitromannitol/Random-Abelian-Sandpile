import RandomSandpile.Defs.Lattice

/-!
# Arzelà–Ascoli for asymptotically equicontinuous sequences (Step S4 of Lemma 7.2)

A uniformly bounded sequence `F n : ℝ^d → ℝ`, supported in a fixed ball and satisfying the
asymptotic Lipschitz bound `|F n x - F n y| ≤ L |x - y| + e n` with `e n → 0`, has a subsequence
converging uniformly on `ℝ^d` to a continuous (indeed `max L 0`-Lipschitz) limit.

Proof (diagonal argument):
* `exists_subseq_tendsto_countable`: the product `D → [-K, K]` over a countable dense set `D` is
  compact and first countable, so a subsequence converges pointwise on `D`;
* `uniformCauchy_subseq`: a finite `δ`-net of the ball `B(0, ρ)` inside `D` (compactness and
  density) and the triangle inequality through the net make the subsequence uniformly Cauchy;
* the uniform limit is `max L 0`-Lipschitz, by passing to the limit in the Lipschitz bound.
-/

noncomputable section

open Filter Topology

namespace RandomSandpile

/-- A uniformly bounded sequence of real functions has a subsequence converging pointwise on a
given countable set (sequential compactness of the countable product `D → [-K, K]`). -/
theorem exists_subseq_tendsto_countable {α : Type*} (D : Set α) (hD : D.Countable)
    (G : ℕ → α → ℝ) (K : ℝ) (hK : ∀ n x, |G n x| ≤ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ q ∈ D, ∃ a, Tendsto (fun j => G (φ j) q) atTop (𝓝 a) := by
  have : Countable D := hD.to_subtype
  have hcomp : IsCompact (Set.univ.pi fun _ : D => Set.Icc (-K) K) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := fun n (q : D) => G n q)
    (fun n q _ => abs_le.1 (hK n q))
  exact ⟨φ, hφ, fun q hq => ⟨a ⟨q, hq⟩, tendsto_pi_nhds.1 hlim ⟨q, hq⟩⟩⟩

/-- Uniform Cauchy property of a subsequence which is pointwise Cauchy on a dense set, for an
asymptotically `M`-Lipschitz sequence supported in a ball. -/
theorem uniformCauchy_subseq (d : ℕ) (F : ℕ → Rd d → ℝ) (ρ M : ℝ)
    (hM : 0 ≤ M) (e : ℕ → ℝ)
    (hρ : ∀ n x, ρ < ‖x‖ → F n x = 0)
    (hL : ∀ n x y, |F n x - F n y| ≤ M * dist x y + e n) (he : Tendsto e atTop (𝓝 0))
    (D : Set (Rd d)) (hDd : Dense D) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hcauchy : ∀ q ∈ D, CauchySeq (fun j => F (φ j) q)) :
    ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, ∀ x, |F (φ j) x - F (φ k) x| < ε := by
  intro ε hε
  set δ : ℝ := ε / (6 * (M + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hMδ : M * δ < ε / 6 := by
    have h1 : (M + 1) * δ = ε / 6 := by rw [hδ]; field_simp
    have h2 : M * δ = (M + 1) * δ - δ := by ring
    linarith
  have hcov : Metric.closedBall (0 : Rd d) ρ ⊆
      ⋃ q : D, Metric.ball (q : Rd d) δ := by
    intro x _
    obtain ⟨q, hq, hxq⟩ := hDd.exists_dist_lt x hδpos
    exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, Metric.mem_ball.2 hxq⟩
  obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : Rd d) ρ).elim_finite_subcover
    (fun q : D => Metric.ball (q : Rd d) δ) (fun _ => Metric.isOpen_ball) hcov
  have hN : ∀ q : D, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (F (φ j) q) (F (φ k) q) < ε / 3 :=
    fun q => Metric.cauchySeq_iff.1 (hcauchy q q.2) _ (by positivity)
  choose Nq hNq using hN
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (he.comp hφ.tendsto_atTop) (ε / 6) (by positivity)
  have he6 : ∀ j ≥ N₁, e (φ j) < ε / 6 := fun j hj => by
    have := hN₁ j hj
    rw [Real.dist_eq, sub_zero] at this
    exact (abs_lt.1 this).2
  refine ⟨max N₁ (T.sup Nq), fun j hj k hk x => ?_⟩
  have hjN₁ : j ≥ N₁ := le_trans (le_max_left _ _) hj
  have hkN₁ : k ≥ N₁ := le_trans (le_max_left _ _) hk
  by_cases hx : ρ < ‖x‖
  · rw [hρ _ _ hx, hρ _ _ hx]
    simpa using hε
  · have hxb : x ∈ Metric.closedBall (0 : Rd d) ρ :=
      mem_closedBall_zero_iff.2 (not_lt.1 hx)
    obtain ⟨q, hqT, hxq⟩ := Set.mem_iUnion₂.1 (hT hxb)
    have hxq' : dist x q < δ := Metric.mem_ball.1 hxq
    have hjq : j ≥ Nq q := le_trans (Finset.le_sup hqT) (le_trans (le_max_right _ _) hj)
    have hkq : k ≥ Nq q := le_trans (Finset.le_sup hqT) (le_trans (le_max_right _ _) hk)
    have hA := hL (φ j) x q
    have hB := hL (φ k) x q
    have hC := hNq q j hjq k hkq
    rw [Real.dist_eq] at hC
    have hMd : M * dist x q ≤ M * δ := mul_le_mul_of_nonneg_left hxq'.le hM
    have hej := he6 j hjN₁
    have hek := he6 k hkN₁
    have htri : |F (φ j) x - F (φ k) x| ≤
        |F (φ j) x - F (φ j) q| + |F (φ j) q - F (φ k) q| + |F (φ k) x - F (φ k) q| := by
      have h1 := abs_sub_le (F (φ j) x) (F (φ j) q) (F (φ k) x)
      have h2 := abs_sub_le (F (φ j) q) (F (φ k) q) (F (φ k) x)
      rw [abs_sub_comm (F (φ k) q) (F (φ k) x)] at h2
      linarith
    linarith

/-- **Arzelà–Ascoli for asymptotically equicontinuous sequences** (Step S4 of Lemma 7.2): a
uniformly bounded sequence `F n` on `ℝ^d`, vanishing outside a fixed ball and satisfying
`|F n x - F n y| ≤ L |x - y| + e n` with `e n → 0`, has a subsequence converging uniformly on
`ℝ^d` to a continuous function. -/
theorem asymptoticArzelaAscoli_core (d : ℕ) (F : ℕ → Rd d → ℝ) (K L ρ : ℝ)
    (e : ℕ → ℝ)
    (hK : ∀ n x, |F n x| ≤ K) (hρ : ∀ n x, ρ < ‖x‖ → F n x = 0)
    (hL : ∀ n x y, |F n x - F n y| ≤ L * dist x y + e n) (he : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ vbar : Rd d → ℝ, Continuous vbar ∧
      TendstoUniformly (fun j => F (φ j)) vbar atTop := by
  set M : ℝ := max L 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hL' : ∀ n x y, |F n x - F n y| ≤ M * dist x y + e n := fun n x y =>
    (hL n x y).trans (by
      have : L * dist x y ≤ M * dist x y :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
      linarith)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rd d)
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_countable D hDc F K hK
  have hcauchy : ∀ q ∈ D, CauchySeq (fun j => F (φ j) q) := fun q hq =>
    (hlim q hq).choose_spec.cauchySeq
  have hunif := uniformCauchy_subseq d F ρ M hM e hρ hL' he D hDd φ hφ hcauchy
  have hUC : UniformCauchySeqOn (fun j => F (φ j)) atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif ε hε
    exact ⟨N, fun m hm n hn x _ => by rw [Real.dist_eq]; exact hN m hm n hn x⟩
  have hpt : ∀ x, ∃ v, Tendsto (fun j => F (φ j) x) atTop (𝓝 v) := fun x =>
    cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := hunif ε hε
      exact ⟨N, fun m hm n hn => by rw [Real.dist_eq]; exact hN m hm n hn x⟩)
  choose vbar hvbar using hpt
  have hTU : TendstoUniformly (fun j => F (φ j)) vbar atTop :=
    tendstoUniformlyOn_univ.1 (hUC.tendstoUniformlyOn_of_tendsto fun x _ => hvbar x)
  have hlip : ∀ x y, dist (vbar x) (vbar y) ≤ M * dist x y := by
    intro x y
    have h1 : Tendsto (fun j => |F (φ j) x - F (φ j) y|) atTop (𝓝 |vbar x - vbar y|) :=
      ((hvbar x).sub (hvbar y)).abs
    have h2 : Tendsto (fun j => M * dist x y + e (φ j)) atTop (𝓝 (M * dist x y + 0)) :=
      tendsto_const_nhds.add (he.comp hφ.tendsto_atTop)
    have := le_of_tendsto_of_tendsto' h1 h2 (fun j => hL' (φ j) x y)
    rw [Real.dist_eq]
    simpa using this
  have hcont : Continuous vbar :=
    (LipschitzWith.of_dist_le_mul (K := M.toNNReal) (fun x y => by
      rw [Real.coe_toNNReal M hM]; exact hlip x y)).continuous
  exact ⟨φ, hφ, vbar, hcont, hTU⟩

end RandomSandpile

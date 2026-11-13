import RandomSandpile.Defs.Lattice
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Arzelà-Ascoli on the exhaustion of the unit ball

A pure-analysis statement: a sequence of functions on `ℝ^d` that is eventually bounded and
equi-Lipschitz on every closed ball `B̄_δ`, `δ < 1`, has a subsequence converging uniformly on
every `B̄_δ`, `δ < 1`. The proof is the elementary one: diagonal extraction on a countable dense
subset of the open unit ball (via compactness of a countable product of intervals), followed by
the equi-Lipschitz uniform Cauchy estimate on `B̄_δ`.
-/

open Metric Filter Topology

namespace RandomSandpile
namespace StrictConcavityAscoli

variable {d : ℕ}

/-- Diagonal extraction: along a countable family of points where the sequence is eventually
bounded, some subsequence converges at every point of the family. -/
theorem pointwise_subseq (F : ℕ → Rd d → ℝ) (q : ℕ → Rd d)
    (hq : ∀ i, ∃ (M : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → |F k (q i)| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∃ a : ℝ, Tendsto (fun k => F (φ k) (q i)) atTop (𝓝 a) := by
  classical
  choose M k₀ hM using hq
  let G : ℕ → ℕ → ℝ := fun k i => if k₀ i ≤ k then F k (q i) else 0
  have hK : IsCompact (Set.pi Set.univ fun i => Set.Icc (-|M i|) |M i|) :=
    isCompact_univ_pi fun i => isCompact_Icc
  have hG : ∀ k, G k ∈ Set.pi Set.univ fun i => Set.Icc (-|M i|) |M i| := by
    intro k i _
    by_cases h : k₀ i ≤ k
    · have h1 := abs_le.mp ((hM i k h).trans (le_abs_self (M i)))
      simp only [G, ite_eq_left h]
      exact h1
    · simp only [G, ite_eq_right h]
      exact ⟨by linarith [abs_nonneg (M i)], abs_nonneg (M i)⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hG
  refine ⟨φ, hφ, fun i => ⟨a i, ?_⟩⟩
  have hi : Tendsto (fun k => G (φ k) i) atTop (𝓝 (a i)) :=
    (tendsto_pi_nhds.1 hlim) i
  refine hi.congr' ?_
  filter_upwards [eventually_ge_atTop (k₀ i)] with k hk
  have : k₀ i ≤ φ k := hk.trans (hφ.id_le k)
  simp only [G, ite_eq_left this]

/-- Equi-Lipschitz estimate: pointwise convergence on a dense family of points of the unit ball,
together with an equi-Lipschitz bound on `B̄_{δ'}`, makes the subsequence uniformly Cauchy on
`B̄_δ` for `δ < δ' < 1`. -/
theorem uniformCauchy (F : ℕ → Rd d → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ) (q : ℕ → Rd d)
    (hdense : ∀ X : Rd d, ‖X‖ < 1 → ∀ r : ℝ, 0 < r → ∃ i, dist X (q i) < r)
    (hconv : ∀ i, ∃ a : ℝ, Tendsto (fun k => F (φ k) (q i)) atTop (𝓝 a))
    (δ δ' : ℝ) (hδδ' : δ < δ') (hδ' : δ' < 1) (Λ : NNReal) (k₀ : ℕ)
    (hL : ∀ k, k₀ ≤ k → LipschitzOnWith Λ (F k) (closedBall (0 : Rd d) δ')) :
    UniformCauchySeqOn (fun k => F (φ k)) atTop (closedBall (0 : Rd d) δ) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hΛ : (0 : ℝ) ≤ (Λ : ℝ) := Λ.coe_nonneg
  have hΛ1 : (0 : ℝ) < (Λ : ℝ) + 1 := by linarith
  set r : ℝ := min (δ' - δ) (ε / (4 * ((Λ : ℝ) + 1))) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by positivity)
  have hr1 : r ≤ δ' - δ := min_le_left _ _
  have hΛr : (Λ : ℝ) * r < ε / 4 := by
    have h2 : r ≤ ε / (4 * ((Λ : ℝ) + 1)) := min_le_right _ _
    have h3 : (Λ : ℝ) * r ≤ (Λ : ℝ) * (ε / (4 * ((Λ : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left h2 hΛ
    have h4 : (Λ : ℝ) * (ε / (4 * ((Λ : ℝ) + 1))) < ε / 4 := by
      rw [show (Λ : ℝ) * (ε / (4 * ((Λ : ℝ) + 1))) = ε / 4 * ((Λ : ℝ) / ((Λ : ℝ) + 1)) by
        field_simp]
      have : (Λ : ℝ) / ((Λ : ℝ) + 1) < 1 := by
        rw [div_lt_one hΛ1]; linarith
      have hε4 : 0 < ε / 4 := by positivity
      nlinarith
    exact h3.trans_lt h4
  -- finite cover of `B̄_δ` by balls around the dense family
  have hcover : closedBall (0 : Rd d) δ ⊆ ⋃ i, ball (q i) r := by
    intro X hX
    have hX1 : ‖X‖ < 1 := by
      have : ‖X‖ ≤ δ := by simpa using hX
      linarith
    obtain ⟨i, hi⟩ := hdense X hX1 r hr0
    exact Set.mem_iUnion.2 ⟨i, by simpa [mem_ball, dist_comm] using hi⟩
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : Rd d) δ).elim_finite_subcover
    (fun i => ball (q i) r) (fun i => isOpen_ball) hcover
  choose a ha using hconv
  have hev : ∀ᶠ k in atTop, ∀ i ∈ t, dist (F (φ k) (q i)) (a i) < ε / 4 := by
    rw [Filter.eventually_all_finset]
    intro i _
    exact Metric.tendsto_nhds.1 (ha i) (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop k₀))
  refine ⟨N, fun m hm n hn X hX => ?_⟩
  have hX' := ht hX
  simp only [Set.mem_iUnion] at hX'
  obtain ⟨i, hit, hXi⟩ := hX'
  have hXi' : dist X (q i) < r := by simpa [mem_ball] using hXi
  have hXmem : X ∈ closedBall (0 : Rd d) δ' :=
    closedBall_subset_closedBall hδδ'.le hX
  have hqmem : q i ∈ closedBall (0 : Rd d) δ' := by
    rw [mem_closedBall]
    have h1 : dist (q i) X < r := by rwa [dist_comm]
    have h2 : dist X 0 ≤ δ := mem_closedBall.1 hX
    calc dist (q i) 0 ≤ dist (q i) X + dist X 0 := dist_triangle _ _ _
      _ ≤ δ' := by linarith
  have hm' : k₀ ≤ φ m := (hN m hm).2.trans (hφ.id_le m)
  have hn' : k₀ ≤ φ n := (hN n hn).2.trans (hφ.id_le n)
  have e1 : dist (F (φ m) X) (F (φ m) (q i)) ≤ Λ * dist X (q i) :=
    (hL _ hm').dist_le_mul X hXmem (q i) hqmem
  have e2 : dist (F (φ n) X) (F (φ n) (q i)) ≤ Λ * dist X (q i) :=
    (hL _ hn').dist_le_mul X hXmem (q i) hqmem
  have e3 : (Λ : ℝ) * dist X (q i) ≤ Λ * r := mul_le_mul_of_nonneg_left hXi'.le hΛ
  have e4 := (hN m hm).1 i hit
  have e5 := (hN n hn).1 i hit
  calc dist (F (φ m) X) (F (φ n) X)
      ≤ dist (F (φ m) X) (F (φ m) (q i)) + dist (F (φ m) (q i)) (a i)
        + dist (a i) (F (φ n) (q i)) + dist (F (φ n) (q i)) (F (φ n) X) := by
        calc dist (F (φ m) X) (F (φ n) X)
            ≤ dist (F (φ m) X) (F (φ m) (q i)) + dist (F (φ m) (q i)) (F (φ n) X) :=
              dist_triangle _ _ _
          _ ≤ dist (F (φ m) X) (F (φ m) (q i)) + (dist (F (φ m) (q i)) (a i)
              + dist (a i) (F (φ n) X)) := by
              gcongr; exact dist_triangle _ _ _
          _ ≤ dist (F (φ m) X) (F (φ m) (q i)) + (dist (F (φ m) (q i)) (a i)
              + (dist (a i) (F (φ n) (q i)) + dist (F (φ n) (q i)) (F (φ n) X))) := by
              gcongr; exact dist_triangle _ _ _
          _ = _ := by ring
    _ < ε := by
      rw [dist_comm (a i) (F (φ n) (q i)), dist_comm (F (φ n) (q i)) (F (φ n) X)]
      linarith

/-- Arzelà-Ascoli on the exhaustion `B̄_δ ↑ B_1`: a sequence of functions that are eventually
bounded and equi-Lipschitz on every `B̄_δ`, `δ < 1`, has a subsequence converging uniformly on
every `B̄_δ`. -/
theorem exists_subseq_tendstoUniformlyOn {d : ℕ} (F : ℕ → Rd d → ℝ)
    (hF : ∀ δ : ℝ, δ < 1 → ∃ (M L : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (∀ X ∈ closedBall (0 : Rd d) δ, |F k X| ≤ M) ∧
        LipschitzOnWith L.toNNReal (F k) (closedBall (0 : Rd d) δ)) :
    ∃ (φ : ℕ → ℕ) (V : Rd d → ℝ), StrictMono φ ∧
      ∀ δ : ℝ, δ < 1 → TendstoUniformlyOn (fun k => F (φ k)) V atTop
        (closedBall (0 : Rd d) δ) := by
  classical
  have : Nonempty (ball (0 : Rd d) 1) := ⟨⟨0, by simp⟩⟩
  let q : ℕ → ball (0 : Rd d) 1 := TopologicalSpace.denseSeq _
  have hqd : DenseRange q := TopologicalSpace.denseRange_denseSeq _
  have hq1 : ∀ i, ‖(q i : Rd d)‖ < 1 := fun i => mem_ball_zero_iff.1 (q i).2
  have hdense : ∀ X : Rd d, ‖X‖ < 1 → ∀ r : ℝ, 0 < r → ∃ i, dist X ((q i : ball (0 : Rd d) 1) : Rd d) < r := by
    intro X hX r hr
    obtain ⟨i, hi⟩ := denseRange_iff.1 hqd ⟨X, by simpa using hX⟩ r hr
    exact ⟨i, hi⟩
  have hbd : ∀ i, ∃ (M : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k → |F k (q i : Rd d)| ≤ M := by
    intro i
    obtain ⟨M, L, k₀, h⟩ := hF ‖(q i : Rd d)‖ (hq1 i)
    exact ⟨M, k₀, fun k hk => (h k hk).1 _ (by simp)⟩
  obtain ⟨φ, hφ, hconv⟩ := pointwise_subseq F (fun i => (q i : Rd d)) hbd
  refine ⟨φ, fun X => limUnder atTop (fun k => F (φ k) X), hφ, ?_⟩
  intro δ hδ
  have hδ' : (1 + δ) / 2 < 1 := by linarith
  have hδδ' : δ < (1 + δ) / 2 := by linarith
  obtain ⟨M, L, k₀, h⟩ := hF ((1 + δ) / 2) hδ'
  have hcau := uniformCauchy F φ hφ (fun i => (q i : Rd d)) hdense hconv δ ((1 + δ) / 2)
    hδδ' hδ' L.toNNReal k₀ (fun k hk => (h k hk).2)
  refine hcau.tendstoUniformlyOn_of_tendsto ?_
  intro X hX
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hcau.cauchySeq hX)
  exact tendsto_nhds_limUnder ⟨a, ha⟩

end StrictConcavityAscoli
end RandomSandpile

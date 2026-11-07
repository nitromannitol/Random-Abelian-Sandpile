import RandomSandpile.Proofs.Sec9.SingleSourceD2Approx

/-!
# Theorem 9.2 in dimension two: Arzelà-Ascoli off the origin

`localArzelaAscoli : LocalArzelaAscoliStmt`. As in `Proofs/Sec7/CompactnessArzelaAscoli.lean`
(the diagonal argument is a single extraction): along a countable dense set of points off the
origin, compactness of the product of the intervals `[-K_q, K_q]` gives a pointwise convergent
subsequence (`exists_subseq_tendsto_countable'`); on a compact `S` off the origin, equicontinuity on
a slightly larger closed annulus and a finite `δ`-net from the dense set make it uniformly Cauchy
(`uniformCauchy_on_compact`); the limit is continuous as a locally uniform limit of continuous
functions.
-/

noncomputable section

open Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceD2

/-- A sequence of real functions bounded at each point of a countable set has a subsequence
converging at every point of that set. -/
theorem exists_subseq_tendsto_countable' {α : Type*} (D : Set α) (hD : D.Countable)
    (G : ℕ → α → ℝ) (K : α → ℝ) (hK : ∀ n, ∀ x ∈ D, |G n x| ≤ K x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ q ∈ D, ∃ a, Tendsto (fun j => G (φ j) q) atTop (𝓝 a) := by
  haveI : Countable D := hD.to_subtype
  have hcomp : IsCompact (Set.univ.pi fun q : D => Set.Icc (-K q) (K q)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := fun n (q : D) => G n q)
    (fun n q _ => abs_le.1 (hK n q q.2))
  exact ⟨φ, hφ, fun q hq => ⟨a ⟨q, hq⟩, tendsto_pi_nhds.1 hlim ⟨q, hq⟩⟩⟩

/-- Uniform Cauchy property on a compact set off the origin. -/
theorem uniformCauchy_on_compact {u : ℕ → Rd 2 → ℝ} {φ : ℕ → ℕ} {D : Set (Rd 2)}
    (hDd : Dense D)
    (hequi : ∀ S : Set (Rd 2), IsCompact S → S ⊆ {x | x ≠ 0} → ∀ η : ℝ, 0 < η → ∃ δ : ℝ,
      0 < δ ∧ ∀ n, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → |u n x - u n y| < η)
    (hcauchy : ∀ q ∈ D, q ≠ 0 → CauchySeq (fun j => u (φ j) q))
    {S : Set (Rd 2)} (hS : IsCompact S) (hS0 : S ⊆ {x | x ≠ 0}) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ j ≥ N, ∀ k ≥ N, ∀ x ∈ S, |u (φ j) x - u (φ k) x| < ε := by
  intro ε hε
  obtain ⟨r, R, hr, hSA⟩ := exists_annulus hS hS0
  set S' := {x : Rd 2 | r / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ R + 1} with hS'
  have hS'c : IsCompact S' := isCompact_closedAnnulus _ _
  have hS'0 : S' ⊆ {x | x ≠ 0} := fun x hx => by
    simp only [hS', Set.mem_setOf_eq] at hx ⊢
    rintro rfl
    rw [norm_zero] at hx
    linarith [hx.1]
  obtain ⟨δ₀, hδ₀, hδu⟩ := hequi S' hS'c hS'0 (ε / 3) (by positivity)
  set δ := min δ₀ (min (r / 2) 1)
  have hδ0 : 0 < δ := lt_min hδ₀ (lt_min (half_pos hr) one_pos)
  have hδ1 : δ ≤ δ₀ := min_le_left _ _
  have hδ2 : δ ≤ r / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hSS' : S ⊆ S' := fun x hx => ⟨by linarith [(hSA hx).1], by linarith [(hSA hx).2]⟩
  have hnear : ∀ x ∈ S, ∀ q : Rd 2, dist x q < δ → q ∈ S' := by
    intro x hx q hq
    have h1 := hSA hx
    have h2 := norm_sub_norm_le x q
    have h3 := norm_sub_norm_le q x
    rw [dist_eq_norm] at hq
    have h4 : ‖q - x‖ = ‖x - q‖ := norm_sub_rev q x
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hcov : S ⊆ ⋃ q : D, ball (q : Rd 2) δ := by
    intro x _
    obtain ⟨q, hq, hxq⟩ := hDd.exists_dist_lt x hδ0
    exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, mem_ball.2 hxq⟩
  obtain ⟨T, hT⟩ := hS.elim_finite_subcover (fun q : D => ball (q : Rd 2) δ)
    (fun _ => isOpen_ball) hcov
  have hN : ∀ q : D, ∃ N, ∀ j ≥ N, ∀ k ≥ N, (q : Rd 2) ≠ 0 →
      |u (φ j) q - u (φ k) q| < ε / 3 := by
    intro q
    by_cases hq0 : (q : Rd 2) = 0
    · exact ⟨0, fun _ _ _ _ h => absurd hq0 h⟩
    · obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hcauchy q q.2 hq0) (ε / 3) (by positivity)
      exact ⟨N, fun j hj k hk _ => by have := hN j hj k hk; rwa [Real.dist_eq] at this⟩
  choose Nq hNq using hN
  refine ⟨T.sup Nq, fun j hj k hk x hx => ?_⟩
  obtain ⟨q, hqT, hxq⟩ := Set.mem_iUnion₂.1 (hT hx)
  have hxq' : dist x q < δ := mem_ball.1 hxq
  have hqS' := hnear x hx q hxq'
  have hq0 : (q : Rd 2) ≠ 0 := hS'0 hqS'
  have hjq : j ≥ Nq q := le_trans (Finset.le_sup hqT) hj
  have hkq : k ≥ Nq q := le_trans (Finset.le_sup hqT) hk
  have hA := hδu (φ j) x (hSS' hx) q hqS' (lt_of_lt_of_le hxq' hδ1)
  have hB := hδu (φ k) x (hSS' hx) q hqS' (lt_of_lt_of_le hxq' hδ1)
  have hC := hNq q j hjq k hkq hq0
  have htri : |u (φ j) x - u (φ k) x| ≤
      |u (φ j) x - u (φ j) q| + |u (φ j) q - u (φ k) q| + |u (φ k) x - u (φ k) q| := by
    have h1 := abs_sub_le (u (φ j) x) (u (φ j) q) (u (φ k) x)
    have h2 := abs_sub_le (u (φ j) q) (u (φ k) q) (u (φ k) x)
    rw [abs_sub_comm (u (φ k) q) (u (φ k) x)] at h2
    linarith
  linarith

/-- **Arzelà-Ascoli off the origin.** -/
theorem localArzelaAscoli : LocalArzelaAscoliStmt := by
  intro u huc hbd hequi
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rd 2)
  have hb : ∀ q : Rd 2, ∃ M : ℝ, q ≠ 0 → ∀ n, |u n q| ≤ M := by
    intro q
    by_cases hq : q = 0
    · exact ⟨0, fun h => absurd hq h⟩
    · obtain ⟨M, hM⟩ := hbd {q} isCompact_singleton (Set.singleton_subset_iff.2 hq)
      exact ⟨M, fun _ n => hM n q rfl⟩
  choose K hK using hb
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_countable' {q ∈ D | q ≠ 0}
    (hDc.mono (Set.sep_subset D _)) u K (fun n q hq => hK q hq.2 n)
  have hcauchy : ∀ q ∈ D, q ≠ 0 → CauchySeq (fun j => u (φ j) q) := fun q hq hq0 =>
    (hlim q ⟨hq, hq0⟩).choose_spec.cauchySeq
  have hunif := fun (S : Set (Rd 2)) (hS : IsCompact S) (hS0 : S ⊆ {x | x ≠ 0}) =>
    uniformCauchy_on_compact hDd hequi hcauchy hS hS0
  have hpt : ∀ x : Rd 2, ∃ v, x ≠ 0 → Tendsto (fun j => u (φ j) x) atTop (𝓝 v) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, fun h => absurd hx h⟩
    · obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => by
        obtain ⟨N, hN⟩ := hunif {x} isCompact_singleton (Set.singleton_subset_iff.2 hx) ε hε
        exact ⟨N, fun m hm n hn => by rw [Real.dist_eq]; exact hN m hm n hn x rfl⟩)
      exact ⟨v, fun _ => hv⟩
  choose w hw using hpt
  have hloc : TendstoLocallyUniformlyOn (fun j => u (φ j)) w atTop {x : Rd 2 | x ≠ 0} := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ne]
    intro S hSV hS
    have hUC : UniformCauchySeqOn (fun j => u (φ j)) atTop S := by
      rw [Metric.uniformCauchySeqOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hunif S hS hSV ε hε
      exact ⟨N, fun m hm n hn x hx => by rw [Real.dist_eq]; exact hN m hm n hn x hx⟩
    exact hUC.tendstoUniformlyOn_of_tendsto fun x hx => hw x (hSV hx)
  exact ⟨φ, hφ, w, hloc.continuousOn (Frequently.of_forall fun j => huc (φ j)), hloc⟩

end SingleSourceD2

end RandomSandpile

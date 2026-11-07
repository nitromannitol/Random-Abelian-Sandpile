import RandomSandpile.Proofs.Sec7.CompactnessArzelaAscoli

/-! # Theorem 9.2: Arzelà–Ascoli with bounds on every ball

A sequence `F n : ℝ^d → ℝ` that is bounded on every closed ball `B̄_m` and asymptotically
equi-Lipschitz there (`|F n x - F n y| ≤ L_m |x - y| + e_m(n)`, `e_m(n) → 0`) has a subsequence
converging locally uniformly on `ℝ^d` to a continuous function. This is the local form of
`asymptoticArzelaAscoli_core` (`Proofs/Sec7/CompactnessArzelaAscoli.lean`), which assumes a common
support ball; the diagonal argument is the same (pointwise convergence on a countable dense set,
uniform Cauchy property on each ball through a finite net).
-/

noncomputable section

open Filter Topology

namespace RandomSandpile

/-- A sequence bounded at each point by `B x` has a subsequence converging pointwise on a given
countable set (sequential compactness of `∏_{q ∈ D} [-B q, B q]`). -/
theorem exists_subseq_tendsto_countable_of_bound {α : Type*} (D : Set α) (hD : D.Countable)
    (G : ℕ → α → ℝ) (B : α → ℝ) (hB : ∀ n x, |G n x| ≤ B x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ q ∈ D, ∃ a, Tendsto (fun j => G (φ j) q) atTop (𝓝 a) := by
  haveI : Countable D := hD.to_subtype
  have hcomp : IsCompact (Set.univ.pi fun q : D => Set.Icc (-B q) (B q)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := fun n (q : D) => G n q)
    (fun n q _ => abs_le.1 (hB n q))
  exact ⟨φ, hφ, fun q hq => ⟨a ⟨q, hq⟩, tendsto_pi_nhds.1 hlim ⟨q, hq⟩⟩⟩

/-- Uniform Cauchy property on the closed ball `B̄_ρ` of a subsequence which is pointwise Cauchy
on a dense set, for a sequence asymptotically `M`-Lipschitz on `B̄_{ρ+1}`. -/
theorem uniformCauchy_closedBall_subseq (d : ℕ) (F : ℕ → Rd d → ℝ) (ρ M : ℝ)
    (hM : 0 ≤ M) (e : ℕ → ℝ)
    (hL : ∀ n x y, ‖x‖ ≤ ρ + 1 → ‖y‖ ≤ ρ + 1 → |F n x - F n y| ≤ M * dist x y + e n)
    (he : Tendsto e atTop (𝓝 0))
    (D : Set (Rd d)) (hDd : Dense D) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hcauchy : ∀ q ∈ D, CauchySeq (fun j => F (φ j) q)) :
    ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, ∀ x, ‖x‖ ≤ ρ → |F (φ j) x - F (φ k) x| < ε := by
  intro ε hε
  set δ : ℝ := min (ε / (6 * (M + 1))) 1 with hδ
  have hδ0 : 0 < ε / (6 * (M + 1)) := by positivity
  have hδpos : 0 < δ := lt_min hδ0 one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hMδ : M * δ < ε / 6 := by
    have h0 : δ ≤ ε / (6 * (M + 1)) := min_le_left _ _
    have h1 : (M + 1) * (ε / (6 * (M + 1))) = ε / 6 := by field_simp
    have h2 : M * δ ≤ M * (ε / (6 * (M + 1))) := mul_le_mul_of_nonneg_left h0 hM
    nlinarith
  have hcov : Metric.closedBall (0 : Rd d) ρ ⊆ ⋃ q : D, Metric.ball (q : Rd d) δ := by
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
  refine ⟨max N₁ (T.sup Nq), fun j hj k hk x hx => ?_⟩
  have hjN₁ : j ≥ N₁ := le_trans (le_max_left _ _) hj
  have hkN₁ : k ≥ N₁ := le_trans (le_max_left _ _) hk
  have hxb : x ∈ Metric.closedBall (0 : Rd d) ρ := mem_closedBall_zero_iff.2 hx
  obtain ⟨q, hqT, hxq⟩ := Set.mem_iUnion₂.1 (hT hxb)
  have hxq' : dist x q < δ := Metric.mem_ball.1 hxq
  have hq : ‖(q : Rd d)‖ ≤ ρ + 1 := by
    have h1 := norm_le_insert' (q : Rd d) x
    rw [← dist_eq_norm, dist_comm] at h1
    linarith
  have hx1 : ‖x‖ ≤ ρ + 1 := by linarith
  have hjq : j ≥ Nq q := le_trans (Finset.le_sup hqT) (le_trans (le_max_right _ _) hj)
  have hkq : k ≥ Nq q := le_trans (Finset.le_sup hqT) (le_trans (le_max_right _ _) hk)
  have hA := hL (φ j) x q hx1 hq
  have hB := hL (φ k) x q hx1 hq
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

/-- **Arzelà–Ascoli with bounds on every ball.** If `F n` is bounded on each closed ball `B̄_m`
and asymptotically equi-Lipschitz there, a subsequence converges locally uniformly on `ℝ^d` to a
continuous function. -/
theorem arzelaAscoli_locallyUniform (d : ℕ) (F : ℕ → Rd d → ℝ)
    (hK : ∀ m : ℕ, ∃ K : ℝ, ∀ n x, ‖x‖ ≤ m → |F n x| ≤ K)
    (hL : ∀ m : ℕ, ∃ L : ℝ, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ n x y, ‖x‖ ≤ m → ‖y‖ ≤ m → |F n x - F n y| ≤ L * dist x y + e n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : Rd d → ℝ, Continuous V ∧
      TendstoLocallyUniformly (fun j => F (φ j)) V atTop := by
  choose K hK using hK
  choose L e he hL using hL
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rd d)
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_countable_of_bound D hDc F
    (fun x => K ⌈‖x‖⌉₊) (fun n x => hK _ n x (Nat.le_ceil _))
  have hcauchy : ∀ q ∈ D, CauchySeq (fun j => F (φ j) q) := fun q hq =>
    (hlim q hq).choose_spec.cauchySeq
  have hLm : ∀ (m : ℕ) n x y, ‖x‖ ≤ m → ‖y‖ ≤ m →
      |F n x - F n y| ≤ max (L m) 0 * dist x y + e m n := by
    intro m n x y hx hy
    have h1 := hL m n x y hx hy
    have h2 : L m * dist x y ≤ max (L m) 0 * dist x y :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
    linarith
  have hunif : ∀ m : ℕ, ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, ∀ x, ‖x‖ ≤ m →
      |F (φ j) x - F (φ k) x| < ε := by
    intro m
    refine uniformCauchy_closedBall_subseq d F m (max (L (m + 1)) 0) (le_max_right _ _)
      (e (m + 1)) (fun n x y hx hy => hLm (m + 1) n x y (by push_cast; exact hx)
        (by push_cast; exact hy)) (he (m + 1)) D hDd φ hφ hcauchy
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
  have hlip : ∀ (m : ℕ) x y, ‖x‖ ≤ m → ‖y‖ ≤ m → |V x - V y| ≤ max (L m) 0 * dist x y := by
    intro m x y hx hy
    have h1 : Tendsto (fun j => |F (φ j) x - F (φ j) y|) atTop (𝓝 |V x - V y|) :=
      ((hV x).sub (hV y)).abs
    have h2 : Tendsto (fun j => max (L m) 0 * dist x y + e m (φ j)) atTop
        (𝓝 (max (L m) 0 * dist x y + 0)) :=
      tendsto_const_nhds.add ((he m).comp hφ.tendsto_atTop)
    have h3 := le_of_tendsto_of_tendsto' h1 h2 (fun j => hLm m (φ j) x y hx hy)
    simpa using h3
  have hcont : Continuous V := by
    rw [Metric.continuous_iff]
    intro x ε hε
    set m : ℕ := ⌈‖x‖⌉₊ + 1 with hm
    set M : ℝ := max (L m) 0 with hMdef
    have hM0 : 0 ≤ M := le_max_right _ _
    have hεM : 0 < ε / (M + 1) := div_pos hε (by linarith)
    refine ⟨min 1 (ε / (M + 1)), lt_min one_pos hεM, fun y hy => ?_⟩
    have hy1 : dist y x < 1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : dist y x < ε / (M + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    have hceil : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
    have hmR : (m : ℝ) = (⌈‖x‖⌉₊ : ℝ) + 1 := by rw [hm]; push_cast; ring
    have hxm : ‖x‖ ≤ m := by rw [hmR]; linarith
    have hym : ‖y‖ ≤ m := by
      have h1 := norm_le_insert' y x
      rw [← dist_eq_norm] at h1
      rw [hmR]; linarith
    rw [Real.dist_eq]
    have h1 := hlip m y x hym hxm
    have h2 : M * dist y x ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hy2.le hM0
    have h3 : M * (ε / (M + 1)) = ε - ε / (M + 1) := by field_simp; ring
    linarith
  refine ⟨φ, hφ, V, hcont, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro C hC
  obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall (0 : Rd d)
  refine (hTU ⌈r⌉₊).mono (hr.trans (Metric.closedBall_subset_closedBall (Nat.le_ceil _)))

end RandomSandpile

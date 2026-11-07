import RandomSandpile.Proofs.Sec9.SingleSourceD2Compare

/-!
# Theorem 9.2 in dimension two: Lemma 2.1, the component bound

`componentBound : ComponentBoundStmt`. For a source profile `u` and an
equation quadratic `Q` with positive definite Hessian:
* every component of `N_Q = {u < Q}` is unbounded (a bounded one contradicts the supersolution
  comparison `quadratic_le_of_super`), hence meets the exterior of a large ball, which is connected
  and contained in `N_Q`; so `N_Q` is preconnected;
* every component of `P_Q` other than the source component meets the convex set `{Q < 0}` (otherwise
  `u > Q ≥ 0` there and the subsolution comparison `le_quadratic_of_sub` is violated); `{Q < 0}` is
  convex and contained in `P_Q`, so all such components coincide.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

theorem convex_comb_lt {s t A B C : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (hA : A < C)
    (hB : B < C) : s * A + t * B < C := by
  have hC : s * C + t * C = C := by rw [← add_mul, hst, one_mul]
  rcases hs.eq_or_lt with h | h
  · have ht1 : t = 1 := by linarith
    rw [← h, ht1]
    linarith
  · have h1 := mul_lt_mul_of_pos_left hA h
    have h2 := mul_le_mul_of_nonneg_left hB.le ht
    linarith

theorem lt_convex_comb {s t A B C : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (hA : C < A)
    (hB : C < B) : C < s * A + t * B := by
  have h := convex_comb_lt hs ht hst (neg_lt_neg hA) (neg_lt_neg hB)
  linarith

theorem one_lt_rank_two : 1 < Module.rank ℝ (Rd 2) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (by norm_num : (1 : ℕ) < 2)

/-- Points outside a ball lie in one component of any set containing the exterior. -/
theorem mem_component_of_exterior {V : Set (Rd 2)} {R : ℝ} (_hR : 0 ≤ R)
    (hV : ∀ x : Rd 2, R < ‖x‖ → x ∈ V) {e e' : Rd 2} (he : R < ‖e‖) (he' : R < ‖e'‖) :
    e' ∈ connectedComponentIn V e := by
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : Rd 2, e₁ = EuclideanSpace.single 0 1 := ⟨_, rfl⟩
  have hn1 : ‖e₁‖ = 1 := by rw [he₁]; simp
  have hS : ∀ y : Rd 2, R < ‖y‖ → sphere (0 : Rd 2) ‖y‖ ⊆ V := fun y hy z hz =>
    hV z (by rw [mem_sphere_zero_iff_norm.1 hz]; exact hy)
  have hseg : segment ℝ (‖e‖ • e₁) (‖e'‖ • e₁) ⊆ V := by
    intro z hz
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
    apply hV
    rw [smul_smul, smul_smul, ← add_smul, norm_smul, hn1, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact lt_convex_comb hs ht hst he he'
  have hm : ∀ y : Rd 2, ‖y‖ • e₁ ∈ sphere (0 : Rd 2) ‖y‖ := fun y => by
    rw [mem_sphere_zero_iff_norm, norm_smul, hn1, mul_one, norm_norm]
  have h1 : IsPreconnected (sphere (0 : Rd 2) ‖e‖ ∪ segment ℝ (‖e‖ • e₁) (‖e'‖ • e₁)) :=
    IsPreconnected.union (‖e‖ • e₁) (hm e) (left_mem_segment ℝ _ _)
      (isPreconnected_sphere one_lt_rank_two 0 _) (convex_segment _ _).isPreconnected
  have h2 : IsPreconnected (sphere (0 : Rd 2) ‖e‖ ∪ segment ℝ (‖e‖ • e₁) (‖e'‖ • e₁) ∪
      sphere (0 : Rd 2) ‖e'‖) :=
    IsPreconnected.union (‖e'‖ • e₁) (Or.inr (right_mem_segment ℝ _ _)) (hm e') h1
      (isPreconnected_sphere one_lt_rank_two 0 _)
  have hsub : sphere (0 : Rd 2) ‖e‖ ∪ segment ℝ (‖e‖ • e₁) (‖e'‖ • e₁) ∪
      sphere (0 : Rd 2) ‖e'‖ ⊆ V := union_subset (union_subset (hS e he) hseg) (hS e' he')
  exact h2.subset_connectedComponentIn (Or.inl (Or.inl (mem_sphere_zero_iff_norm.2 rfl))) hsub
    (Or.inr (mem_sphere_zero_iff_norm.2 rfl))

/-- A positive definite quadratic is positive far away. -/
theorem quadratic_pos_far {c : ℝ} {p a : Rd 2} {N : Matrix (Fin 2) (Fin 2) ℝ} (hN : N.PosDef) :
    ∃ R > 0, ∀ x : Rd 2, R ≤ ‖x‖ → 0 < c + inner ℝ p (x - a) + qM N (x - a) := by
  obtain ⟨cN, hcN, hq⟩ := exists_qM_ge_of_posDef hN
  refine ⟨‖a‖ + (‖p‖ + |c|) / cN + 1, by positivity, fun x hx => ?_⟩
  have hs : (‖p‖ + |c|) / cN + 1 ≤ ‖x - a‖ := by
    have := norm_sub_norm_le x a
    linarith
  have h1 : ‖p‖ + |c| ≤ cN * (‖x - a‖ - 1) := by
    have : (‖p‖ + |c|) / cN ≤ ‖x - a‖ - 1 := by linarith
    rwa [div_le_iff₀ hcN, mul_comm] at this
  have hin : -(‖p‖ * ‖x - a‖) ≤ inner ℝ p (x - a) := by
    have := abs_real_inner_le_norm p (x - a)
    linarith [neg_abs_le (inner ℝ p (x - a))]
  have hq' := hq (x - a)
  have hc : -|c| ≤ c := neg_abs_le c
  have hs1 : 1 ≤ ‖x - a‖ := by
    have : 0 ≤ (‖p‖ + |c|) / cN := by positivity
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg (x - a)), abs_nonneg c, norm_nonneg p]

/-- The source ball: near the origin `Q < u`. -/
theorem exists_source_ball {u Q : Rd 2 → ℝ} (hu0 : Tendsto u (𝓝[≠] 0) atTop) (hQ : Continuous Q) :
    ∃ ρ > 0, ∀ x : Rd 2, x ≠ 0 → ‖x‖ < ρ → Q x < u x := by
  have hQ0 : ∀ᶠ y in 𝓝[≠] (0 : Rd 2), Q y < Q 0 + 1 :=
    nhdsWithin_le_nhds ((hQ.tendsto 0).eventually (gt_mem_nhds (by linarith)))
  have hu1 : ∀ᶠ y in 𝓝[≠] (0 : Rd 2), Q 0 + 1 < u y := hu0.eventually (eventually_gt_atTop _)
  have h := hQ0.and hu1
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨ρ, hρ, hρh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ρ, hρ, fun x hx0 hx => ?_⟩
  have := hρh (by rwa [dist_zero_right]) hx0
  linarith [this.1, this.2]

/-- A boundary point of a component of an open set is not in the set. -/
theorem not_mem_of_mem_frontier_component {V : Set (Rd 2)} (hV : IsOpen V) {x y : Rd 2}
    (hy : y ∈ frontier (connectedComponentIn V x)) : y ∉ V := by
  intro hyV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV y hyV
  obtain ⟨z, hzK, hzd⟩ := Metric.mem_closure_iff.1 hy.1 ε hε
  have hsub : ball y ε ⊆ connectedComponentIn V x := by
    rw [connectedComponentIn_eq hzK]
    exact (convex_ball y ε).isPreconnected.subset_connectedComponentIn
      (mem_ball.2 (by rwa [dist_comm])) hball
  exact hy.2 (mem_interior.2 ⟨ball y ε, hsub, isOpen_ball, mem_ball_self hε⟩)

/-- Convexity of a positive definite quadratic along a segment. -/
theorem quad_convex {c : ℝ} {p a₀ : Rd 2} {N : Matrix (Fin 2) (Fin 2) ℝ} (hNs : N.IsSymm)
    (hN : N.PosDef) (y₁ y₂ : Rd 2) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    c + inner ℝ p (s • y₁ + t • y₂ - a₀) + qM N (s • y₁ + t • y₂ - a₀) ≤
      s * (c + inner ℝ p (y₁ - a₀) + qM N (y₁ - a₀)) +
        t * (c + inner ℝ p (y₂ - a₀) + qM N (y₂ - a₀)) := by
  obtain ⟨cN, hcN, hq⟩ := exists_qM_ge_of_posDef hN
  have hnn : 0 ≤ qM N (y₁ - y₂) := le_trans (by positivity) (hq (y₁ - y₂))
  obtain rfl : t = 1 - s := by linarith
  have hsym : N 1 0 = N 0 1 := hNs.apply 0 1
  have key := mul_nonneg (mul_nonneg hs ht) hnn
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right, qM_two, PiLp.add_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hsym] at key ⊢
  nlinarith [key]

/-! ### Lemma 2.1 -/

/-- **(C2) SIMPLE-PROOF Lemma 2.1.** -/
theorem componentBound : ComponentBoundStmt := by
  intro F hshift hdeg u hu c p a N hNs hNpd hFN
  have hqc : Continuous fun x : Rd 2 => qM N (x - a) :=
    (contDiff_qM N (n := 0)).continuous.comp (continuous_id.sub continuous_const)
  have hQc : Continuous fun x : Rd 2 => c + inner ℝ p (x - a) + qM N (x - a) := by fun_prop
  set Q : Rd 2 → ℝ := fun x => c + inner ℝ p (x - a) + qM N (x - a)
  obtain ⟨ρ, hρ, hball⟩ := exists_source_ball hu.tendsto_atTop hQc
  obtain ⟨R₂, hR₂, hfar⟩ := quadratic_pos_far (c := c) (p := p) (a := a) hNpd
  obtain ⟨Ru, hRu⟩ := hu.eventually_zero
  obtain ⟨R₃, hR₃⟩ : ∃ R₃ : ℝ, R₃ = max R₂ Ru := ⟨_, rfl⟩
  have hR₃0 : 0 ≤ R₃ := by rw [hR₃]; exact le_trans hR₂.le (le_max_left _ _)
  have hext : ∀ x : Rd 2, R₃ < ‖x‖ → x ∈ negSet u Q := fun x hx => by
    have h1 : R₂ ≤ ‖x‖ := le_trans (by rw [hR₃]; exact le_max_left _ _) hx.le
    have h2 : Ru ≤ ‖x‖ := le_trans (by rw [hR₃]; exact le_max_right _ _) hx.le
    refine ⟨fun h0 => ?_, ?_⟩
    · rw [h0, norm_zero] at h1; linarith
    · rw [hRu x h2]; exact hfar x h1
  have hNo : IsOpen (negSet u Q) := isOpen_negSet hu.continuousOn hQc
  have hPo : IsOpen (posSet u Q) := isOpen_posSet hu.continuousOn hu.tendsto_atTop hQc
  have hNball : ∀ x ∈ negSet u Q, ρ ≤ ‖x‖ := fun x hx => by
    by_contra hlt
    exact absurd hx.2 (not_lt.2 (hball x hx.1 (not_le.mp hlt)).le)
  -- every component of `N_Q` reaches the exterior
  have hcomp_ext : ∀ x ∈ negSet u Q, ∃ e : Rd 2, R₃ < ‖e‖ ∧
      e ∈ connectedComponentIn (negSet u Q) x := by
    intro x hx
    by_contra hnone
    have hnone' : ∀ e ∈ connectedComponentIn (negSet u Q) x, ‖e‖ ≤ R₃ := fun e he => by
      by_contra h
      exact hnone ⟨e, not_le.mp h, he⟩
    have hKo : IsOpen (connectedComponentIn (negSet u Q) x) := hNo.connectedComponentIn
    have hKb : Bornology.IsBounded (connectedComponentIn (negSet u Q) x) :=
      isBounded_closedBall.subset fun e he => mem_closedBall_zero_iff.2 (hnone' e he)
    have hKsub : connectedComponentIn (negSet u Q) x ⊆ negSet u Q := connectedComponentIn_subset _ _
    have h0 : ∀ y ∈ closure (connectedComponentIn (negSet u Q) x), y ≠ 0 := by
      intro y hy hy0
      rw [hy0] at hy
      obtain ⟨z, hzK, hzd⟩ := Metric.mem_closure_iff.1 hy ρ hρ
      have := hNball z (hKsub hzK)
      rw [dist_zero_left] at hzd
      linarith
    have hbd : ∀ y ∈ frontier (connectedComponentIn (negSet u Q) x),
        c + inner ℝ p (y - a) + qM N (y - a) ≤ u y := fun y hy => by
      have hyn := not_mem_of_mem_frontier_component hNo hy
      by_contra hlt
      exact hyn ⟨h0 y hy.1, not_le.mp hlt⟩
    have := quadratic_le_of_super hshift hKo hKb (hu.continuousOn.mono h0)
      (hu.supersolution.mono fun y hy => (hKsub hy).1) hNs hFN hbd x (mem_connectedComponentIn hx)
    exact absurd hx.2 (not_lt.2 this)
  have hpre : IsPreconnected (negSet u Q) := by
    refine isPreconnected_of_forall_pair fun x hx y hy =>
      ⟨connectedComponentIn (negSet u Q) x, connectedComponentIn_subset _ _,
        mem_connectedComponentIn hx, ?_, isPreconnected_connectedComponentIn⟩
    obtain ⟨e, he, hex⟩ := hcomp_ext x hx
    obtain ⟨e', he', hey⟩ := hcomp_ext y hy
    have h1 : e' ∈ connectedComponentIn (negSet u Q) e := mem_component_of_exterior hR₃0 hext he he'
    rw [connectedComponentIn_eq hex, connectedComponentIn_eq h1, ← connectedComponentIn_eq hey]
    exact mem_connectedComponentIn hy
  -- components of `P_Q` other than the source component meet `{Q < 0}`
  have hsrc : ball (0 : Rd 2) ρ ⊆ connectedComponentIn (posSet u Q) 0 := by
    have hbP : ball (0 : Rd 2) ρ ⊆ posSet u Q := fun y hy => by
      by_cases hy0 : y = 0
      · exact Or.inr hy0
      · exact Or.inl ⟨hy0, hball y hy0 (mem_ball_zero_iff.1 hy)⟩
    exact (convex_ball (0 : Rd 2) ρ).isPreconnected.subset_connectedComponentIn
      (mem_ball_self hρ) hbP
  have hPb : ∀ y ∈ posSet u Q, ‖y‖ ≤ R₃ := fun y hy => by
    by_contra hlt
    have hN := hext y (not_le.mp hlt)
    rcases hy with hy | hy
    · exact absurd hN.2 (not_lt.2 hy.2.le)
    · exact hN.1 hy
  have hneg_pt : ∀ x ∈ posSet u Q, x ∉ connectedComponentIn (posSet u Q) 0 →
      ∃ y : Rd 2, Q y < 0 ∧ y ∈ connectedComponentIn (posSet u Q) x := by
    intro x hx hx0
    by_contra hnone
    have hnn : ∀ y ∈ connectedComponentIn (posSet u Q) x, 0 ≤ Q y := fun y hy => by
      by_contra h
      exact hnone ⟨y, not_le.mp h, hy⟩
    have hKo : IsOpen (connectedComponentIn (posSet u Q) x) := hPo.connectedComponentIn
    have hKsub : connectedComponentIn (posSet u Q) x ⊆ posSet u Q := connectedComponentIn_subset _ _
    have hKb : Bornology.IsBounded (connectedComponentIn (posSet u Q) x) :=
      isBounded_closedBall.subset fun e he => mem_closedBall_zero_iff.2 (hPb e (hKsub he))
    have hdisj : ∀ y ∈ connectedComponentIn (posSet u Q) x, y ∉ ball (0 : Rd 2) ρ := by
      intro y hy hyb
      apply hx0
      rw [connectedComponentIn_eq (hsrc hyb), ← connectedComponentIn_eq hy]
      exact mem_connectedComponentIn hx
    have h0 : ∀ y ∈ closure (connectedComponentIn (posSet u Q) x), y ≠ 0 := by
      intro y hy hy0
      rw [hy0] at hy
      obtain ⟨z, hzK, hzd⟩ := Metric.mem_closure_iff.1 hy ρ hρ
      exact hdisj z hzK (by rwa [mem_ball, dist_comm])
    have hKpos : ∀ y ∈ connectedComponentIn (posSet u Q) x, y ≠ 0 ∧ 0 < u y := by
      intro y hy
      have hy0 : y ≠ 0 := fun h => hdisj y hy (by rw [h]; exact mem_ball_self hρ)
      rcases hKsub hy with hyP | hyP
      · exact ⟨hy0, lt_of_le_of_lt (hnn y hy) hyP.2⟩
      · exact absurd hyP hy0
    have hbd : ∀ y ∈ frontier (connectedComponentIn (posSet u Q) x),
        u y ≤ c + inner ℝ p (y - a) + qM N (y - a) := fun y hy => by
      have hyn := not_mem_of_mem_frontier_component hPo hy
      by_contra hlt
      exact hyn (Or.inl ⟨h0 y hy.1, not_le.mp hlt⟩)
    have hx' := (hKpos x (mem_connectedComponentIn hx)).1
    have := le_quadratic_of_sub hshift hKo hKb (hu.continuousOn.mono h0)
      (hu.subsolution.mono fun y hy => hKpos y hy) hNs hFN hbd x (mem_connectedComponentIn hx)
    rcases hx with hxP | hxP
    · exact absurd hxP.2 (not_lt.2 this)
    · exact hx' hxP
  refine ⟨hpre, fun x hx y hy hx0 hy0 => ?_⟩
  obtain ⟨y₁, hq1, hy1⟩ := hneg_pt x hx hx0
  obtain ⟨y₂, hq2, hy2⟩ := hneg_pt y hy hy0
  have hseg : segment ℝ y₁ y₂ ⊆ posSet u Q := by
    intro z hz
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
    have hz := quad_convex (c := c) (p := p) (a₀ := a) hNs hNpd y₁ y₂ hs ht hst
    have hlt : Q (s • y₁ + t • y₂) < 0 := by
      have e1 : Q (s • y₁ + t • y₂) = c + inner ℝ p (s • y₁ + t • y₂ - a) +
          qM N (s • y₁ + t • y₂ - a) := rfl
      have e2 : Q y₁ = c + inner ℝ p (y₁ - a) + qM N (y₁ - a) := rfl
      have e3 : Q y₂ = c + inner ℝ p (y₂ - a) + qM N (y₂ - a) := rfl
      rw [e1]
      rw [e2] at hq1
      rw [e3] at hq2
      exact lt_of_le_of_lt hz (convex_comb_lt hs ht hst hq1 hq2)
    by_cases hz0 : s • y₁ + t • y₂ = 0
    · exact Or.inr hz0
    · exact Or.inl ⟨hz0, lt_of_lt_of_le hlt (hu.nonneg _ hz0)⟩
  have h12 : y₂ ∈ connectedComponentIn (posSet u Q) y₁ :=
    (convex_segment y₁ y₂).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ y₁ y₂)
      hseg (right_mem_segment ℝ y₁ y₂)
  rw [connectedComponentIn_eq hy1, connectedComponentIn_eq h12, ← connectedComponentIn_eq hy2]
  exact mem_connectedComponentIn hy

end SingleSourceD2

end RandomSandpile

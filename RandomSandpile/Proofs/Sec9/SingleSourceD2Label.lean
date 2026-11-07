import RandomSandpile.Proofs.Sec9.SingleSourceD2Component

/-!
# Theorem 9.2 in dimension two: the source label is open

`sourceLabelOpen : SourceLabelOpenStmt` (SIMPLE-PROOF Theorem 4.1, "being connected to the source
is an open condition"). At `θ₀`, join `x θ₀` to a point of a uniform source ball by a path in the
source component of `P_{θ₀}`; the part of its compact image outside half the source ball, together
with a small closed ball around `x θ₀`, stays in `P_θ` for `θ` near `θ₀` (tube lemma); the rest of
the path lies in the source ball, which is in `P_θ` for all nearby `θ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

/-- Positivity of `u - Q θ` on a compact set off the origin persists near `θ₀`. -/
theorem eventually_forall_lt_of_compact {u : Rd 2 → ℝ} (hu : ContinuousOn u {x | x ≠ 0})
    {Q : ℝ → Rd 2 → ℝ} (hQ : Continuous fun q : ℝ × Rd 2 => Q q.1 q.2) {θ₀ : ℝ}
    {K : Set (Rd 2)} (hK : IsCompact K) (hK0 : ∀ y ∈ K, y ≠ 0 ∧ Q θ₀ y < u y) :
    ∀ᶠ θ in 𝓝 θ₀, ∀ y ∈ K, Q θ y < u y := by
  refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
  have hcu : ContinuousAt (fun q : ℝ × Rd 2 => u q.2 - Q q.1 q.2) (θ₀, y) :=
    ((hu.continuousAt (isOpen_compl_singleton.mem_nhds (hK0 y hy).1)).comp
      continuous_snd.continuousAt).sub hQ.continuousAt
  have hpos : 0 < u y - Q θ₀ y := by linarith [(hK0 y hy).2]
  filter_upwards [hcu.eventually (lt_mem_nhds hpos)] with q hq
  linarith

/-- A uniform source ball for nearby parameters. -/
theorem eventually_source_ball {u : Rd 2 → ℝ} (hu0 : Tendsto u (𝓝[≠] 0) atTop)
    {Q : ℝ → Rd 2 → ℝ} (hQ : Continuous fun q : ℝ × Rd 2 => Q q.1 q.2) (θ₀ : ℝ) :
    ∃ ρ > 0, ∀ᶠ θ in 𝓝 θ₀, ∀ y : Rd 2, y ≠ 0 → ‖y‖ < ρ → Q θ y < u y := by
  have hQc : ∀ᶠ q in 𝓝 ((θ₀, (0 : Rd 2))), Q q.1 q.2 < Q θ₀ 0 + 1 :=
    hQ.continuousAt.eventually (gt_mem_nhds (by linarith))
  obtain ⟨S, hS, T, hT, hST⟩ := mem_nhds_prod_iff.1 hQc
  obtain ⟨ρ₁, hρ₁, hρ₁T⟩ := Metric.mem_nhds_iff.1 hT
  have hu1 : ∀ᶠ y in 𝓝[≠] (0 : Rd 2), Q θ₀ 0 + 1 < u y := hu0.eventually (eventually_gt_atTop _)
  rw [eventually_nhdsWithin_iff] at hu1
  obtain ⟨ρ₂, hρ₂, hρ₂u⟩ := Metric.eventually_nhds_iff.1 hu1
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  filter_upwards [hS] with θ hθ y hy0 hy
  have hy1 : y ∈ T := hρ₁T (mem_ball_zero_iff.2 (lt_of_lt_of_le hy (min_le_left _ _)))
  have h1 : Q θ y < Q θ₀ 0 + 1 := hST (mk_mem_prod hθ hy1)
  have h2 := hρ₂u (by rw [dist_zero_right]; exact lt_of_lt_of_le hy (min_le_right _ _)) hy0
  linarith

/-- **The source label is open. -/
theorem sourceLabelOpen : SourceLabelOpenStmt := by
  intro u hu hu0 Q hQ x hx hxP
  rw [isOpen_iff_mem_nhds]
  intro θ₀ hθ₀
  simp only [mem_setOf_eq] at hθ₀
  have hQθ : ∀ θ, Continuous (Q θ) := fun θ => hQ.comp (Continuous.prodMk_right θ)
  obtain ⟨ρ, hρ, hball⟩ := eventually_source_ball hu0 hQ θ₀
  -- the source ball lies in the source component for nearby parameters
  have hsrc : ∀ θ, (∀ y : Rd 2, y ≠ 0 → ‖y‖ < ρ → Q θ y < u y) →
      ball (0 : Rd 2) ρ ⊆ connectedComponentIn (posSet u (Q θ)) 0 := by
    intro θ hθ
    have hbP : ball (0 : Rd 2) ρ ⊆ posSet u (Q θ) := fun y hy => by
      by_cases hy0 : y = 0
      · exact Or.inr hy0
      · exact Or.inl ⟨hy0, hθ y hy0 (mem_ball_zero_iff.1 hy)⟩
    exact (convex_ball (0 : Rd 2) ρ).isPreconnected.subset_connectedComponentIn
      (mem_ball_self hρ) hbP
  have hball₀ := hball.self_of_nhds
  -- a path from `x θ₀` to a point of the source ball inside the source component
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Rd 2, z₀ = (ρ / 2) • EuclideanSpace.single 0 1 := ⟨_, rfl⟩
  have hn1 : ‖(EuclideanSpace.single 0 1 : Rd 2)‖ = 1 := by simp
  have hz₀b : z₀ ∈ ball (0 : Rd 2) ρ := by
    rw [mem_ball_zero_iff, hz₀, norm_smul, hn1, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hρ)]
    linarith
  set K₀ := connectedComponentIn (posSet u (Q θ₀)) 0
  have hK₀o : IsOpen K₀ := (isOpen_posSet hu hu0 (hQθ θ₀)).connectedComponentIn
  have hK₀c : IsConnected K₀ := isConnected_connectedComponentIn_iff.2 (Or.inr rfl)
  have hK₀p : IsPathConnected K₀ := (hK₀o.isConnected_iff_isPathConnected).1 hK₀c
  have hz₀K : z₀ ∈ K₀ := hsrc θ₀ hball₀ hz₀b
  have hj := hK₀p.joinedIn (x θ₀) hθ₀ z₀ hz₀K
  set γ := hj.somePath
  have hγK : ∀ t, γ t ∈ K₀ := hj.somePath_mem
  have hK₀sub : K₀ ⊆ posSet u (Q θ₀) := connectedComponentIn_subset _ _
  -- a closed ball around `x θ₀`
  have hx0 := hxP θ₀
  have hopen : IsOpen {y : Rd 2 | y ≠ 0 ∧ Q θ₀ y < u y} := by
    have h := ((hQθ θ₀).continuousOn.sub hu).isOpen_inter_preimage isOpen_compl_singleton
      (isOpen_Iio (a := (0 : ℝ)))
    convert h using 1
    ext y
    simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Iio, Pi.sub_apply, sub_neg]
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hopen (x θ₀) hx0
  -- the compact set where positivity must persist
  set Γ := range γ
  have hΓc : IsCompact Γ := isCompact_range γ.continuous
  set Kc := (Γ \ ball (0 : Rd 2) (ρ / 2)) ∪ closedBall (x θ₀) (ε / 2)
  have hKc : IsCompact Kc :=
    (hΓc.diff isOpen_ball).union (isCompact_closedBall _ _)
  have hKc0 : ∀ y ∈ Kc, y ≠ 0 ∧ Q θ₀ y < u y := by
    intro y hy
    rcases hy with ⟨⟨t, rfl⟩, hyb⟩ | hy
    · have hy0 : γ t ≠ 0 := fun h => hyb (by rw [h]; exact mem_ball_self (half_pos hρ))
      rcases hK₀sub (hγK t) with h | h
      · exact h
      · exact absurd h hy0
    · exact hεsub (lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hε))
  have hev := eventually_forall_lt_of_compact hu hQ hKc hKc0
  have hxev : ∀ᶠ θ in 𝓝 θ₀, x θ ∈ ball (x θ₀) (ε / 2) :=
    hx.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self (half_pos hε)))
  filter_upwards [hev, hball, hxev] with θ hθK hθb hθx
  show x θ ∈ connectedComponentIn (posSet u (Q θ)) 0
  have hsrcθ := hsrc θ hθb
  -- the path lies in `P_θ`
  have hΓP : Γ ⊆ posSet u (Q θ) := by
    rintro _ ⟨t, rfl⟩
    by_cases hb : γ t ∈ ball (0 : Rd 2) (ρ / 2)
    · have hb' : γ t ∈ ball (0 : Rd 2) ρ := ball_subset_ball (half_le_self hρ.le) hb
      exact connectedComponentIn_subset _ _ (hsrcθ hb')
    · have hy0 : γ t ≠ 0 := fun h => hb (by rw [h]; exact mem_ball_self (half_pos hρ))
      exact Or.inl ⟨hy0, hθK _ (Or.inl ⟨⟨t, rfl⟩, hb⟩)⟩
  have hΓsrc : Γ ⊆ connectedComponentIn (posSet u (Q θ)) 0 := by
    have hz : z₀ ∈ Γ := ⟨1, γ.target⟩
    have h := (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn hz hΓP
    rw [← connectedComponentIn_eq (hsrcθ hz₀b)] at h
    exact h
  have hxθ₀ : x θ₀ ∈ connectedComponentIn (posSet u (Q θ)) 0 := hΓsrc ⟨0, γ.source⟩
  -- the small ball around `x θ₀` lies in `P_θ`
  have hbP : ball (x θ₀) (ε / 2) ⊆ posSet u (Q θ) := fun y hy =>
    Or.inl ⟨(hKc0 y (Or.inr (ball_subset_closedBall hy))).1,
      hθK y (Or.inr (ball_subset_closedBall hy))⟩
  have h := (convex_ball (x θ₀) (ε / 2)).isPreconnected.subset_connectedComponentIn
    (mem_ball_self (half_pos hε)) hbP hθx
  rw [← connectedComponentIn_eq hxθ₀] at h
  exact h

end SingleSourceD2

end RandomSandpile

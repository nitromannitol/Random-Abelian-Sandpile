import RandomSandpile.Steps.Sec8.DivisibleHomogenizeDomain

/-!
# Uniform exterior ball condition for Lipschitz domains

Proof of `RandomSandpile.UniformExteriorBallStmt` (`uniformExteriorBall`), the geometric step of
Lemma 8.1 (`RandomSandpile/Steps/Sec8/DivisibleHomogenizeDomain.lean`).

Route. In a Lipschitz chart `(x₀, r, e, L, γ)` with `p` a boundary point within `r / 4` of `x₀`
(so `p ∉ W`, as `W` is open), the point `w = p - s e` has the ball `B(w, c s)` disjoint from `W`
as soon as `s ≤ r / 4` and `(2 Ls + 1) c ≤ 1` for any `Ls ≥ L`: a point `y` of this ball lies in
the chart and sits below the graph of `γ` (`local_exterior_ball`). The frontier of `W` is compact,
so finitely many charts of radius `r / 4` cover it, which makes the chart radius and the
Lipschitz constant uniform (`uniformExteriorBall`).
-/

noncomputable section

namespace RandomSandpile

variable {d : ℕ}

/-- Arithmetic core of `local_exterior_ball`: the contradiction obtained from the Lipschitz bound
`γ Y ≥ γ P - 2 L ‖v‖` and the chart inequalities. -/
theorem exteriorBall_arith {Ls c s nv L gY gP a b : ℝ} (hs : 0 < s) (hL0 : 0 ≤ L)
    (hLL : L ≤ Ls) (hcL : (2 * Ls + 1) * c ≤ 1) (hnv : nv < c * s) (hnv0 : 0 ≤ nv)
    (hb : b ≤ nv) (hLip : |gY - gP| ≤ L * (2 * nv)) (hP : a ≤ gP) (hY : gY < a - s + b) :
    False := by
  have hLs0 : 0 ≤ Ls := hL0.trans hLL
  have h1 : gP - gY ≤ L * (2 * nv) := by
    have := neg_abs_le (gY - gP)
    linarith
  have h2 : L * (2 * nv) ≤ Ls * (2 * nv) := mul_le_mul_of_nonneg_right hLL (by linarith)
  have h3 : Ls * (2 * nv) ≤ Ls * (2 * (c * s)) :=
    mul_le_mul_of_nonneg_left (by linarith) hLs0
  have h4 : (2 * Ls + 1) * c * s ≤ 1 * s := mul_le_mul_of_nonneg_right hcL hs.le
  nlinarith

/-- A finite family of positive numbers has a positive common lower bound. -/
theorem exists_pos_le_finset {ι : Type*} (f : ι → ℝ) (t : Finset ι) (h : ∀ x ∈ t, 0 < f x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ t, m ≤ f x := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a t hat ih =>
    obtain ⟨m, hm, hmt⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    refine ⟨min m (f a), lt_min hm (h a (Finset.mem_insert_self a t)), ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hmt x hx)

/-- Local form of the uniform exterior ball condition: in a Lipschitz chart at `x₀` of radius `r`
with direction `e` and Lipschitz constant `L ≤ Ls`, a boundary point `p ∉ W` within `r / 4` of
`x₀` has, for every `0 < s ≤ r / 4`, the ball `B(p - s e, c s)` disjoint from `W`, provided
`(2 Ls + 1) c ≤ 1`. -/
theorem local_exterior_ball {W : Set (Rd d)} {x₀ p e : Rd d} {r : ℝ} {L : NNReal}
    {γ : Rd d → ℝ} {Ls c s : ℝ} (he : ‖e‖ = 1) (hγ : LipschitzWith L γ)
    (hchart : ∀ y ∈ Metric.ball x₀ r,
      (y ∈ W ↔ γ ((y - x₀) - inner ℝ (y - x₀) e • e) < inner ℝ (y - x₀) e))
    (hp : p ∉ W) (hpx : ‖p - x₀‖ < r / 4) (hLs : (L : ℝ) ≤ Ls) (hc : 0 < c)
    (hcL : (2 * Ls + 1) * c ≤ 1) (hs : 0 < s) (hsr : s ≤ r / 4) :
    ∀ y ∈ Metric.ball (p - s • e) (c * s), y ∉ W := by
  intro y hy hyW
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hLs0 : 0 ≤ Ls := hL0.trans hLs
  have hc1 : c ≤ 1 := by nlinarith
  have hcs : c * s ≤ s := mul_le_of_le_one_left hs.le hc1
  have hr : 0 < r := by linarith [norm_nonneg (p - x₀)]
  obtain ⟨v, hv⟩ : ∃ v : Rd d, v = y - (p - s • e) := ⟨_, rfl⟩
  have hvn : ‖v‖ < c * s := by
    rw [hv, ← dist_eq_norm]
    exact Metric.mem_ball.1 hy
  have hyv : y - x₀ = (p - x₀) - s • e + v := by rw [hv]; abel
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hin : inner ℝ (y - x₀) e = inner ℝ (p - x₀) e - s + inner ℝ v e := by
    rw [hyv, inner_add_left, inner_sub_left, real_inner_smul_left, hee]
    ring
  have hY : (y - x₀) - inner ℝ (y - x₀) e • e
      = ((p - x₀) - inner ℝ (p - x₀) e • e) + (v - inner ℝ v e • e) := by
    rw [hin, hyv]
    module
  have hse : ‖s • e‖ = s := by rw [norm_smul, he, Real.norm_of_nonneg hs.le, mul_one]
  have hyx : ‖y - x₀‖ < r := by
    have h1 : ‖(p - x₀) - s • e + v‖ ≤ ‖(p - x₀) - s • e‖ + ‖v‖ := norm_add_le _ _
    have h2 : ‖(p - x₀) - s • e‖ ≤ ‖p - x₀‖ + ‖s • e‖ := norm_sub_le _ _
    rw [hyv]
    linarith
  have hyball : y ∈ Metric.ball x₀ r := by rw [Metric.mem_ball, dist_eq_norm]; exact hyx
  have hpball : p ∈ Metric.ball x₀ r := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hYlt := (hchart y hyball).1 hyW
  have hPge : inner ℝ (p - x₀) e ≤ γ ((p - x₀) - inner ℝ (p - x₀) e • e) :=
    not_lt.1 (fun h => hp ((hchart p hpball).2 h))
  have hbe : |inner ℝ v e| ≤ ‖v‖ := by
    have := abs_real_inner_le_norm v e
    rwa [he, mul_one] at this
  have hdiff : dist ((y - x₀) - inner ℝ (y - x₀) e • e)
      ((p - x₀) - inner ℝ (p - x₀) e • e) ≤ 2 * ‖v‖ := by
    rw [dist_eq_norm, hY, add_sub_cancel_left]
    calc ‖v - inner ℝ v e • e‖ ≤ ‖v‖ + ‖inner ℝ v e • e‖ := norm_sub_le _ _
      _ = ‖v‖ + |inner ℝ v e| := by rw [norm_smul, he, mul_one, Real.norm_eq_abs]
      _ ≤ 2 * ‖v‖ := by linarith
  have hLip : |γ ((y - x₀) - inner ℝ (y - x₀) e • e)
      - γ ((p - x₀) - inner ℝ (p - x₀) e • e)| ≤ (L : ℝ) * (2 * ‖v‖) := by
    have h1 := hγ.dist_le_mul ((y - x₀) - inner ℝ (y - x₀) e • e)
      ((p - x₀) - inner ℝ (p - x₀) e • e)
    rw [Real.dist_eq] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hdiff hL0)
  exact exteriorBall_arith hs hL0 hLs hcL hvn (norm_nonneg v) (le_trans (le_abs_self _) hbe)
    hLip hPge (lt_of_lt_of_eq hYlt hin)

/-- **Uniform exterior ball condition for Lipschitz domains** (`UniformExteriorBallStmt`). -/
theorem uniformExteriorBall : UniformExteriorBallStmt := by
  intro d W hW
  obtain ⟨hbd, hopen, -, hchart⟩ := hW
  have hK : IsCompact (frontier W) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hbd.closure.subset frontier_subset_closure)
  choose! r hr e he L γ hγ hch using hchart
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (r x / 4))
    (fun x hx => Metric.ball_mem_nhds x (by linarith [hr x hx]))
  obtain ⟨r₀, hr₀, hr₀t⟩ := exists_pos_le_finset (fun x => r x / 4) t
    (fun x hx => by have := hr x (htK x hx); positivity)
  set Ls : ℝ := ∑ x ∈ t, (L x : ℝ) with hLsdef
  have hLs0 : 0 ≤ Ls := Finset.sum_nonneg (fun x _ => NNReal.coe_nonneg _)
  have hLsL : ∀ x ∈ t, (L x : ℝ) ≤ Ls := fun x hx =>
    Finset.single_le_sum (f := fun x => (L x : ℝ)) (fun i _ => NNReal.coe_nonneg _) hx
  have hc0 : 0 < 1 / (2 * (Ls + 1)) := by positivity
  have hcL : (2 * Ls + 1) * (1 / (2 * (Ls + 1))) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  refine ⟨r₀, 1 / (2 * (Ls + 1)), hr₀, hc0, ?_⟩
  intro p hp s hs hsr
  obtain ⟨x₀, hx₀t, hpx⟩ := Set.mem_iUnion₂.1 (hcov hp)
  have hpW : p ∉ W := fun h => hp.2 (by rwa [hopen.interior_eq])
  have hpx' : ‖p - x₀‖ < r x₀ / 4 := by
    rw [← dist_eq_norm]; exact Metric.mem_ball.1 hpx
  have hsr' : s ≤ r x₀ / 4 := hsr.trans (hr₀t x₀ hx₀t)
  refine ⟨p - s • e x₀, ?_, ?_⟩
  · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, he x₀ (htK x₀ hx₀t),
      Real.norm_of_nonneg hs.le, mul_one]
  · exact local_exterior_ball (he x₀ (htK x₀ hx₀t)) (hγ x₀ (htK x₀ hx₀t))
      (hch x₀ (htK x₀ hx₀t)) hpW hpx' (hLsL x₀ hx₀t) hc0 hcL hs hsr'

end RandomSandpile

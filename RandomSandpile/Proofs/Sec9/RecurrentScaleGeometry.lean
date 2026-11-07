import RandomSandpile.Proofs.Sec9.RecurrentPositiveMass
import RandomSandpile.Proofs.Sec9.SingleSourceMinPrinciple

/-! # Integer-scale domains inside single-source positivity regions -/

open Filter LatticeProb Metric
open scoped Topology

namespace RandomSandpile

/-- If two positive spatial scales are asymptotic, the discrete ball at the
integer scale lies in any slightly larger ball at the other scale. -/
theorem eventually_discretize_ball_scaled_subset {d : ℕ} {a : Rd d} {r R : ℝ}
    (hrR : r < R) {m : ℕ → ℕ} {s : ℕ → ℝ}
    (hm : ∀ᶠ k in atTop, 1 ≤ m k) (hs : ∀ᶠ k in atTop, s k ≠ 0)
    (ht : Tendsto (fun k => (m k : ℝ) / s k) atTop (𝓝 1)) :
    ∀ᶠ k in atTop, ∀ z ∈ discretize (ball a r) (m k),
      (s k)⁻¹ • toE z ∈ closedBall a R := by
  let C : ℝ := ‖a‖ + |r| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have he : ∀ᶠ k in atTop, |(m k : ℝ) / s k - 1| * C < R - r := by
    have h := ((ht.sub_const 1).abs.mul_const C)
    rw [sub_self, abs_zero, zero_mul] at h
    exact h.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hm, hs, he] with k hmk hsk hk z hz
  have hm0 : (m k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hz' : (m k : ℝ)⁻¹ • toE z ∈ ball a r :=
    (OpenMaxPrinciple.mem_discretize_iff' (by omega)).1 hz
  let y : Rd d := (m k : ℝ)⁻¹ • toE z
  have hyn : ‖y‖ ≤ C := by
    have h1 : ‖y‖ ≤ ‖a‖ + dist y a := by
      rw [dist_eq_norm]
      calc ‖y‖ = ‖a + (y - a)‖ := by rw [add_sub_cancel]
        _ ≤ ‖a‖ + ‖y - a‖ := norm_add_le _ _
    have h2 : dist y a < r := hz'
    dsimp [C]
    linarith [le_abs_self r]
  have hdist : dist (((m k : ℝ) / s k) • y) y < R - r := by
    rw [dist_eq_norm, show ((m k : ℝ) / s k) • y - y =
      ((m k : ℝ) / s k - 1) • y by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hyn (abs_nonneg _)).trans_lt hk
  have heq : ((m k : ℝ) / s k) • y = (s k)⁻¹ • toE z := by
    dsimp [y]
    rw [smul_smul]
    congr 1
    field_simp
  rw [← heq, mem_closedBall]
  have htri := dist_triangle (((m k : ℝ) / s k) • y) y a
  have hya : dist y a < r := hz'
  linarith

/-- Recurrence holds eventually on integer-scale balls compactly contained in
the positivity region of a single-source subsequential limit. -/
theorem eventually_recurrent_discretize_ball {d : ℕ} (hd : 0 < d)
    {η : Site d → ℤ} (hfinite : SingleSourceFinite η) {u : Rd d → ℝ}
    {nk m : ℕ → ℕ} (hnk : StrictMono nk)
    (hconv : TendstoLocallyUniformlyOn
      (fun k => rescaleSingleSource (singleSourceOdometer η (nk k)) (nk k)) u atTop
      {x : Rd d | x ≠ 0})
    {a : Rd d} {r R : ℝ} (hrR : r < R)
    (hK0 : closedBall a R ⊆ {x : Rd d | x ≠ 0})
    (hcont : ContinuousOn u (closedBall a R))
    (hpos : ∀ x ∈ closedBall a R, 0 < u x)
    (hm : ∀ᶠ k in atTop, 1 ≤ m k)
    (ht : Tendsto (fun k => (m k : ℝ) / (nk k : ℝ) ^ (1 / (d : ℝ))) atTop (𝓝 1)) :
    ∀ᶠ k in atTop, IsRecurrentFunction η (discretize (ball a r) (m k))
      (singleSourceOdometer η (nk k)) := by
  have hs : ∀ᶠ k in atTop, (nk k : ℝ) ^ (1 / (d : ℝ)) ≠ 0 := by
    filter_upwards [hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hk) _).ne'
  filter_upwards [eventually_discretize_ball_scaled_subset hrR hm hs ht,
    recurrent_on_scaled_compact_of_positive_limit hd hfinite hnk hconv
      (isCompact_closedBall a R) hK0 hcont hpos] with k hk hrec
  exact hrec.mono hk

end RandomSandpile

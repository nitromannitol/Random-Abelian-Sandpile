import RandomSandpile.Steps.Sec6.StrictConcavity
import RandomSandpile.Proofs.Sec6.StrictConcavityHarnack
import RandomSandpile.Proofs.Sec6.StrictConcavityAscoli
import RandomSandpile.Proofs.Sec6.StrictConcavityCross
import RandomSandpile.Proofs.Sec6.StrictConcavityNearMax

/-! # Lemma 6.2', step N2a-1: compactness of the rescaled envelopes

`EnvelopeCompactnessStmt` (Steps/Sec6/StrictConcavity.lean) from:
* the Harnack chain `StrictConcavityHarnack.harnack_chain`;
* Arzelà-Ascoli on the exhaustion `B̄_δ ↑ B_1`, `StrictConcavityAscoli.exists_subseq_tendstoUniformlyOn`;
* the local convex-combination property `LocalConvexCombStmt`: every point of `ℝ^d` is a convex
  combination of lattice points at bounded distance.

Bounds on the normalized rescaled envelope `V_n`.
* Upper bound: `V_n ≤ 0`, because the envelope lies below its supporting plane at the contact
  point.
* Lower bound: write `nX` as a convex combination of nearby lattice points `z_i`. By concavity,
  `V_n(X) ≥ -max_i f(z_i)/n²`, where `f = w(x₀) + p·(· - x₀) - w ≥ 0`; the slopes cancel by
  linearity. The Harnack chain gives `f ≤ C K n²` on `B_{δ n}`.
* Concavity of `V_n` on `B_{δ}` and the bounds give equi-Lipschitz bounds
  (`ConcaveOn.lipschitzOnWith_of_abs_le`).
* Bolzano-Weierstrass for the rescaled contact points. -/

open MeasureTheory LatticeProb Filter Metric
open scoped Topology

namespace RandomSandpile

/-- Every point of `ℝ^d` is a convex combination of lattice points within distance `ρ = ρ(d)`. -/
def LocalConvexCombStmt : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x : Rd d, ∃ (ι : Type) (_ : Fintype ι) (z : ι → Site d)
    (lam : ι → ℝ), (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • toE (z i) = x ∧
      ∀ i, ‖toE (z i) - x‖ ≤ ρ

namespace EnvelopeCompactness

open MuLipschitz

variable {d : ℕ}

/-- The discrete Laplacian of an affine function vanishes. -/
theorem lapR_affine (c : ℝ) (p : Rd d) (x₀ x : Site d) :
    lapR (fun z => c + inner ℝ p (toE z - toE x₀)) x = 0 := by
  simp only [lapR, nbrSum]
  have h : ∀ i : Fin d, (c + inner ℝ p (toE (x + unit i) - toE x₀)) +
      (c + inner ℝ p (toE (x - unit i) - toE x₀)) = 2 * (c + inner ℝ p (toE x - toE x₀)) := by
    intro i
    have h1 : toE (x + unit i) - toE x₀ = (toE x - toE x₀) + toE (unit i) := by
      rw [toE_add]; abel
    have h2 : toE (x - unit i) - toE x₀ = (toE x - toE x₀) - toE (unit i) := by
      rw [toE_sub]; abel
    rw [h1, h2]
    simp only [inner_add_right, inner_sub_right]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- `V_n ≤ 0` where `nX` lies in the convex hull of `B̄_n`. -/
theorem rescaled_le_zero {w : Site d → ℝ} {n : ℕ} (hn : 1 ≤ n) {x₀ : Site d} {p : Rd d}
    (hx₀ : x₀ ∈ dClosure (ballZ0 (d := d) (n : ℝ))) (hp : p ∈ supGrad w x₀ (ballZ0 (n : ℝ)))
    {X : Rd d} (hX : (n : ℝ) • X ∈ convexHull ℝ (toE '' dClosure (ballZ0 (d := d) (n : ℝ)))) :
    rescaledEnvelope w n x₀ p X ≤ 0 := by
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  unfold rescaledEnvelope
  rw [div_le_iff₀ hn0, zero_mul]
  have := concaveEnvelopeOn_le_of_mem_supGrad (ballZ0_finite _) hx₀ hp hX
  linarith

/-- `V_n(X) ≥ -B/n²` when `nX` is a convex combination of points of `B̄_n` where the gap
`f = w(x₀) + p·(· - x₀) - w` is at most `B`. -/
theorem rescaled_ge {w : Site d → ℝ} {n : ℕ} (hn : 1 ≤ n) {x₀ : Site d} {p : Rd d} {X : Rd d}
    {ι : Type} [Fintype ι] {z : ι → Site d} {lam : ι → ℝ}
    (hz : ∀ i, z i ∈ dClosure (ballZ0 (d := d) (n : ℝ))) (h0 : ∀ i, 0 ≤ lam i)
    (h1 : ∑ i, lam i = 1) (hx : ∑ i, lam i • toE (z i) = (n : ℝ) • X) {B : ℝ}
    (hB : ∀ i, w x₀ + inner ℝ p (toE (z i) - toE x₀) - w (z i) ≤ B) :
    -B / (n : ℝ) ^ 2 ≤ rescaledEnvelope w n x₀ p X := by
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hsum := sum_le_concaveEnvelopeOver (w := w) (dClosure_finite (ballZ0_finite (n : ℝ))) hz
    h0 h1 hx
  unfold rescaledEnvelope
  rw [concaveEnvelopeOn_eq_concaveEnvelopeOver, div_le_div_iff_of_pos_right hn0]
  have hlin : ∑ i, lam i * (w x₀ + inner ℝ p (toE (z i) - toE x₀)) =
      w x₀ + inner ℝ p ((n : ℝ) • X - toE x₀) := by
    have hv : (n : ℝ) • X - toE x₀ = ∑ i, lam i • (toE (z i) - toE x₀) := by
      rw [← hx]
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
    rw [hv, inner_sum]
    simp only [inner_smul_right, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h1, one_mul]
  have hB' : ∑ i, lam i * (w x₀ + inner ℝ p (toE (z i) - toE x₀) - w (z i)) ≤ B := by
    calc _ ≤ ∑ i, lam i * B :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i) (h0 i)
      _ = B := by rw [← Finset.sum_mul, h1, one_mul]
  have hsplit : ∑ i, lam i * (w x₀ + inner ℝ p (toE (z i) - toE x₀) - w (z i)) =
      ∑ i, lam i * (w x₀ + inner ℝ p (toE (z i) - toE x₀)) - ∑ i, lam i * w (z i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- `V_n` is concave on `B_r` when `n B_r` lies in the convex hull of `B̄_n`. -/
theorem concaveOn_rescaled {w : Site d → ℝ} {n : ℕ} (hn : 1 ≤ n) {x₀ : Site d} {p : Rd d}
    {r : ℝ} (hsub : ∀ X ∈ ball (0 : Rd d) r,
      (n : ℝ) • X ∈ convexHull ℝ (toE '' dClosure (ballZ0 (d := d) (n : ℝ)))) :
    ConcaveOn ℝ (ball (0 : Rd d) r) (rescaledEnvelope w n x₀ p) := by
  refine ⟨convex_ball _ _, fun X hX Y hY a b ha hb hab => ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hc := (concaveOn_concaveEnvelopeOn (w := w) (ballZ0_finite (d := d) (n : ℝ))).2
    (hsub X hX) (hsub Y hY) ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  have hlin : (n : ℝ) • (a • X + b • Y) = a • ((n : ℝ) • X) + b • ((n : ℝ) • Y) := by
    rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm (n : ℝ) a,
      mul_comm (n : ℝ) b]
  have hinner : inner ℝ p (a • ((n : ℝ) • X) + b • ((n : ℝ) • Y) - toE x₀) =
      a * inner ℝ p ((n : ℝ) • X - toE x₀) + b * inner ℝ p ((n : ℝ) • Y - toE x₀) := by
    have : a • ((n : ℝ) • X) + b • ((n : ℝ) • Y) - toE x₀ =
        a • ((n : ℝ) • X - toE x₀) + b • ((n : ℝ) • Y - toE x₀) := by
      have hx0 : toE x₀ = a • toE x₀ + b • toE x₀ := by rw [← add_smul, hab, one_smul]
      rw [smul_sub, smul_sub]
      conv_lhs => rw [hx0]
      abel
    rw [this, inner_add_right, inner_smul_right, inner_smul_right]
  unfold rescaledEnvelope
  rw [hlin, hinner]
  have hw : a * w x₀ + b * w x₀ = w x₀ := by rw [← add_mul, hab, one_mul]
  rw [mul_div_assoc', mul_div_assoc', ← add_div, div_le_div_iff_of_pos_right hn0]
  nlinarith

end EnvelopeCompactness

open MuLipschitz EnvelopeCompactness in
/-- **Step N2a-1** (`EnvelopeCompactnessStmt`) from the local convex-combination property. -/
theorem envelopeCompactness_of_convexComb (hC : LocalConvexCombStmt) :
    EnvelopeCompactnessStmt := by
  intro d hd K hK w hlap β hβ0 hβ1 m hm x₀ p hx₀ hp
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ρ, hρ, hcomb⟩ := hC d hd1
  -- Bolzano-Weierstrass for the rescaled contact points
  have hmpos : ∀ k, (0 : ℝ) < m k := fun k => by
    have := mem_ballZ0.1 (hx₀ k)
    have := norm_nonneg (toE (x₀ k))
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hxb : ∀ k, ((m k : ℝ))⁻¹ • toE (x₀ k) ∈ closedBall (0 : Rd d) β := fun k => by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_natCast,
      inv_mul_le_iff₀ (hmpos k)]
    have := mem_ballZ0.1 (hx₀ k)
    linarith
  obtain ⟨z, -, ψ, hψ, hzlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hxb
  set F : ℕ → Rd d → ℝ := fun k =>
    rescaledEnvelope (w (m (ψ k))) (m (ψ k)) (x₀ (ψ k)) (p (ψ k))
  have hF : ∀ δ : ℝ, δ < 1 → ∃ (M L : ℝ) (k₀ : ℕ), ∀ k, k₀ ≤ k →
      (∀ X ∈ closedBall (0 : Rd d) δ, |F k X| ≤ M) ∧
        LipschitzOnWith L.toNNReal (F k) (closedBall (0 : Rd d) δ) := by
    intro δ hδ
    set δ₁ := max δ β
    have hδ₁ : δ₁ < 1 := max_lt hδ hβ1
    set δ₂ := (δ₁ + 1) / 2
    set δ₃ := (δ₂ + 1) / 2
    set δ₄ := (δ₃ + 1) / 2
    have hδ₂1 : δ₂ < 1 := by simp only [δ₂]; linarith
    have hδ₃1 : δ₃ < 1 := by simp only [δ₃]; linarith
    have hβδ₄ : β < δ₄ := by
      have := le_max_right δ β; simp only [δ₄, δ₃, δ₂]; linarith
    obtain ⟨C, hC0, n₀, hH⟩ := StrictConcavityHarnack.harnack_chain hd1 hβ0 hβδ₄
      (by simp only [δ₄, δ₃, δ₂]; linarith)
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (ρ / (δ₄ - δ₃))
    refine ⟨C * K, 2 * (C * K) / (δ₃ - δ₂), max n₀ (N₁ + 1), fun k hk => ?_⟩
    set n := m (ψ k)
    have hkn : max n₀ (N₁ + 1) ≤ n := hk.trans ((hψ.id_le k).trans (hm.id_le _))
    have hn1 : 1 ≤ n := le_trans (by omega) hkn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hρn : ρ ≤ (δ₄ - δ₃) * n := by
      have h1 : (N₁ : ℝ) + 1 ≤ n := by exact_mod_cast (le_max_right _ _).trans hkn
      have h2 := (div_lt_iff₀ (by simp only [δ₄]; linarith : (0 : ℝ) < δ₄ - δ₃)).1 hN₁
      nlinarith
    -- the gap `f` and the Harnack bound
    set f : Site d → ℝ := fun y =>
      w n (x₀ (ψ k)) + inner ℝ (p (ψ k)) (toE y - toE (x₀ (ψ k))) - w n y
    have hf0 : ∀ y ∈ dClosure (ballZ0 (d := d) (n : ℝ)), 0 ≤ f y := fun y hy => by
      have h : w n y ≤ w n (x₀ (ψ k)) + inner ℝ (p (ψ k)) (toE y - toE (x₀ (ψ k))) :=
        hp (ψ k) y hy
      simp only [f]; linarith
    have hflap : ∀ y ∈ ballZ0 (d := d) (n : ℝ), |lapR f y| ≤ K := fun y hy => by
      have : lapR f y = -lapR (w n) y := by
        simp only [f]
        rw [lapR_sub', lapR_affine]; ring
      rw [this, abs_neg]; exact hlap n y hy
    have hfx₀ : f (x₀ (ψ k)) = 0 := by simp only [f, sub_self, inner_zero_right]; ring
    have hHarn := hH n ((le_max_left _ _).trans hkn) K f hK hf0 hflap (x₀ (ψ k)) (hx₀ (ψ k)) hfx₀
    have hx₀c : x₀ (ψ k) ∈ dClosure (ballZ0 (d := d) (n : ℝ)) := by
      refine Or.inl (mem_ballZ0.2 ?_)
      have := mem_ballZ0.1 (hx₀ (ψ k)); nlinarith
    -- convex combinations for points of `n B_{δ₃}`
    have hcomb' : ∀ X ∈ ball (0 : Rd d) δ₃, ∃ (ι : Type) (_ : Fintype ι) (zz : ι → Site d)
        (lam : ι → ℝ), (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧
          ∑ i, lam i • toE (zz i) = (n : ℝ) • X ∧ ∀ i, zz i ∈ ballZ0 (d := d) (δ₄ * n) := by
      intro X hX
      obtain ⟨ι, hι, zz, lam, h0, h1, hs, hd⟩ := hcomb ((n : ℝ) • X)
      refine ⟨ι, hι, zz, lam, h0, h1, hs, fun i => mem_ballZ0.2 ?_⟩
      have hXn : ‖(n : ℝ) • X‖ < δ₃ * n := by
        rw [norm_smul, Real.norm_natCast, mul_comm]
        exact mul_lt_mul_of_pos_right (mem_ball_zero_iff.1 hX) hn0
      calc ‖toE (zz i)‖ = ‖(toE (zz i) - (n : ℝ) • X) + (n : ℝ) • X‖ := by rw [sub_add_cancel]
        _ ≤ ‖toE (zz i) - (n : ℝ) • X‖ + ‖(n : ℝ) • X‖ := norm_add_le _ _
        _ < δ₄ * n := by linarith [hd i]
    have hsubB : ∀ y ∈ ballZ0 (d := d) (δ₄ * n), y ∈ dClosure (ballZ0 (d := d) (n : ℝ)) :=
      fun y hy => Or.inl (mem_ballZ0.2 (by
        have := mem_ballZ0.1 hy
        have : δ₄ * n < n := by simp only [δ₄, δ₃, δ₂]; nlinarith
        linarith))
    have hhull : ∀ X ∈ ball (0 : Rd d) δ₃,
        (n : ℝ) • X ∈ convexHull ℝ (toE '' dClosure (ballZ0 (d := d) (n : ℝ))) := by
      intro X hX
      obtain ⟨ι, hι, zz, lam, h0, h1, hs, hz⟩ := hcomb' X hX
      rw [← hs]
      exact (convex_convexHull ℝ _).sum_mem (fun i _ => h0 i) h1
        (fun i _ => subset_convexHull ℝ _ ⟨zz i, hsubB _ (hz i), rfl⟩)
    have hbound : ∀ X ∈ ball (0 : Rd d) δ₃, |F k X| ≤ C * K := by
      intro X hX
      obtain ⟨ι, hι, zz, lam, h0, h1, hs, hz⟩ := hcomb' X hX
      have hup := rescaled_le_zero hn1 hx₀c (hp (ψ k)) (hhull X hX)
      have hlo := rescaled_ge (w := w n) hn1 (fun i => hsubB _ (hz i)) h0 h1 hs
        (B := C * K * (n : ℝ) ^ 2) (fun i => hHarn _ (hz i))
      rw [neg_div, mul_div_assoc, div_self (by positivity), mul_one] at hlo
      rw [abs_le]
      exact ⟨hlo, hup.trans (by positivity)⟩
    have hδle : δ ≤ δ₁ := le_max_left δ β
    have hδδ₃ : δ < δ₃ := by simp only [δ₃, δ₂]; linarith
    have hδδ₂ : δ < δ₂ := by simp only [δ₂]; linarith
    refine ⟨fun X hX => hbound X (closedBall_subset_ball hδδ₃ hX), ?_⟩
    have hconc : ConcaveOn ℝ (ball (0 : Rd d) δ₃) (F k) := concaveOn_rescaled hn1 hhull
    have hlip := hconc.lipschitzOnWith_of_abs_le (ε := δ₃ - δ₂) (by simp only [δ₃]; linarith)
      (M := C * K) (fun a ha => hbound a (mem_ball.2 ha))
    rw [sub_sub_cancel] at hlip
    exact hlip.mono (closedBall_subset_ball hδδ₂)
  obtain ⟨φ', V, hφ', hconv⟩ := StrictConcavityAscoli.exists_subseq_tendstoUniformlyOn F hF
  exact ⟨ψ ∘ φ', V, z, hψ.comp hφ', hzlim.comp hφ'.tendsto_atTop, hconv⟩

/-- **Local convex combinations**: `x` lies in the cross-polytope `conv{c ± d e_i}` around
`c = ⌊x⌋`, whose vertices are within `d + √d` of `x`. -/
theorem localConvexComb : LocalConvexCombStmt := by
  intro d hd
  refine ⟨d + √d, by positivity, fun x => ?_⟩
  set c : Site d := latticeRound x
  have hci : ∀ i, |x i - (c i : ℝ)| ≤ 1 := fun i => by
    have h1 := Int.floor_le (x i)
    have h2 := Int.lt_floor_add_one (x i)
    simp only [c, latticeRound]
    rw [abs_le]; constructor <;> linarith
  have hx : ∑ i, |x i - (c i : ℝ)| ≤ ((d : ℕ) : ℝ) := by
    calc ∑ i, |x i - (c i : ℝ)| ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => hci i
      _ = d := by simp
  obtain ⟨lam, h0, h1, hs⟩ := StrictConcavityCross.exists_crossPolytope_weights hd c hd x hx
  refine ⟨Fin d × Bool, inferInstance, StrictConcavityCross.crossVertex c d, lam, h0, h1, hs,
    fun j => ?_⟩
  have hc : ‖toE c - x‖ ≤ √d := by
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖(toE c - x) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs, sq_abs]
          have := hci i
          simp only [PiLp.sub_apply, toE_apply]
          rw [show (c i : ℝ) - x i = -(x i - c i) by ring, neg_sq]
          nlinarith [abs_le.1 this]
      _ = d := by simp
  calc ‖toE (StrictConcavityCross.crossVertex c d j) - x‖
      = ‖(toE (StrictConcavityCross.crossVertex c d j) - toE c) + (toE c - x)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖toE (StrictConcavityCross.crossVertex c d j) - toE c‖ + ‖toE c - x‖ := norm_add_le _ _
    _ ≤ d + √d := by rw [StrictConcavityCross.norm_crossVertex_sub]; linarith

/-- **Step N2a-1 of Lemma 6.2'** (`EnvelopeCompactnessStmt`), proved. -/
theorem envelopeCompactness : EnvelopeCompactnessStmt :=
  envelopeCompactness_of_convexComb localConvexComb

/-- **Lemma 6.2' with a locally legal and stabilizing witness** (consumed by Lemma 7.5) from
Lemma 5.5 and the uniform concavity of limits (`LimitUniformConcavityStmt`). -/
theorem nearMaxBendingStabilizing_of_uniformConcavity (hconv : MuConvergenceStmt)
    (hconc : LimitUniformConcavityStmt) : NearMaxBendingStabilizingStmt :=
  nearMaxBendingStabilizing_of_limit hconv (rescaledEnvelopeLimit_of_steps envelopeCompactness hconc)

/-- **Lemma 6.3** from Lemma 5.5 and the uniform concavity of limits. -/
theorem muLipschitz_of_uniformConcavity (hconv : MuConvergenceStmt)
    (hconc : LimitUniformConcavityStmt) : MuLipschitzStmt :=
  muLipschitz_of_limit hconv (rescaledEnvelopeLimit_of_steps envelopeCompactness hconc)

/-- **Lemma 6.2 with `C = C(β)`** from Lemma 5.5 and the uniform concavity of limits. -/
theorem strictConcavityBeta_of_uniformConcavity (hconv : MuConvergenceStmt)
    (hconc : LimitUniformConcavityStmt) : StrictConcavityBetaStmt :=
  strictConcavityBeta_of_limit hconv (rescaledEnvelopeLimit_of_steps envelopeCompactness hconc)

end RandomSandpile

import RandomSandpile.Proofs.Sec9.SingleSourceFstarLattice

/-!
# Theorem 9.2, `F*`-variant: the contradiction at one integer scale

 §4.3 at a fixed integer scale `m`, with the finite comparison of
`Proofs/Sec9/SingleSourceFstarLattice.lean`. Let `A = discretize (B_r(b)) m` (a ball of radius
`R = m r` around `z = m b` in `ℤ^d`, not containing the origin) and `I = discretize (B_{βr}(b)) m`.
If

* the single-source odometer `v_n` is within `e` of `T(y) = m² u₀ + m p₀·(y - z) + q_N(y - z)` on
  `Ā` and at least `Λ` on `A`,
* `μ*(A, η, 0, M')` exceeds the site bound of Lemma 5.4 times `|A ∖ I|`,
* `b₋/2 |h|² ≤ q_{M' - N}(h) ≤ b₊/2 |h|²`, and
* the quadratic gap `b₋ R²/2 - b₊ β² R²/2` and `Λ` dominate the errors,

then the contact point of a `μ*`-near-maximizer in `I` (`exists_contact_of_lt_muStar`) yields a
competitor below `v_n` (`false_of_contact`): impossible (`false_at_scale`).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceFstar

variable {d : ℕ}

theorem toE_zero' : toE (0 : Site d) = 0 := by
  ext1 i
  simp [toE]

/-- `|y - m b| = m |y/m - b|`. -/
theorem norm_toE_sub_smul {m : ℕ} (hm : m ≠ 0) (b : Rd d) (y : Site d) :
    ‖toE y - (m : ℝ) • b‖ = (m : ℝ) * ‖(m : ℝ)⁻¹ • toE y - b‖ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have e : toE y - (m : ℝ) • b = (m : ℝ) • ((m : ℝ)⁻¹ • toE y - b) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hmpos.ne', one_smul]
  rw [e, norm_smul, Real.norm_of_nonneg hmpos.le]

/-- **The contradiction at one integer scale**. -/
theorem false_at_scale (hd : 1 ≤ d) {η : Site d → ℤ} {ηmin : ℤ} (hη : ∀ x, ηmin ≤ η x) {n : ℕ}
    (hne : (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty)
    {m : ℕ} (hm : 1 ≤ m) {b : Rd d} {r β : ℝ} (hr : 0 < r) (hrb : r ≤ ‖b‖)
    {M' N : Matrix (Fin d) (Fin d) ℝ} (hM' : M'.IsSymm) {bm bp : ℝ} (hbm : 0 ≤ bm)
    (hbp : 0 ≤ bp)
    (hP : ∀ h : Rd d, bm / 2 * ‖h‖ ^ 2 ≤ qM (M' - N) h ∧ qM (M' - N) h ≤ bp / 2 * ‖h‖ ^ 2)
    {u₀ e Λ : ℝ} {p₀ : Rd d}
    (happ : ∀ y ∈ dClosure (discretize (ball b r) m),
      |(singleSourceOdometer η n y : ℝ) - ((m : ℝ) ^ 2 * u₀ +
        (m : ℝ) * inner ℝ p₀ (toE y - (m : ℝ) • b) + qM N (toE y - (m : ℝ) • b))| ≤ e)
    (hlow : ∀ y ∈ discretize (ball b r) m, Λ ≤ (singleSourceOdometer η n y : ℝ))
    (hmass : ENNReal.ofReal ((max ((2 * (d : ℝ) - 1) - (ηmin : ℝ) - 0 - M'.trace) 0 / d) ^ d *
        ((discretize (ball b r) m \ discretize (ball b (β * r)) m).ncard : ℝ)) <
        muStar (discretize (ball b r) m) η 0 M')
    (hgap : bp / 2 * (β * ((m : ℝ) * r)) ^ 2 + 2 * e +
        2 * (((d : ℝ) + 1) * ((m : ℝ) * r + 1) + 1) + 1 ≤ bm / 2 * ((m : ℝ) * r) ^ 2)
    (hpos : bp / 2 * (β * ((m : ℝ) * r)) ^ 2 + 2 * e +
        2 * (((d : ℝ) + 1) * ((m : ℝ) * r + 1) + 1) + 1 ≤ Λ) :
    False := by
  have hm0 : m ≠ 0 := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hAfin : (discretize (ball b r) m).Finite :=
    SubadditiveLipschitz.discretize_finite isBounded_ball m
  have h0 : (0 : Site d) ∉ discretize (ball b r) m := by
    intro h
    rw [OpenMaxPrinciple.mem_discretize_iff' hm0, toE_zero', smul_zero, mem_ball, dist_comm,
      dist_zero_right] at h
    linarith
  obtain ⟨X, hX, xc, ⟨hxcA, hxcI⟩, p, hp⟩ :=
    exists_contact_of_lt_muStar hd hAfin (fun x _ => hη x) 0 M' hmass
  -- geometry of the discretized balls
  have hA : ∀ y ∈ discretize (ball b r) m, ‖toE y - (m : ℝ) • b‖ < (m : ℝ) * r := by
    intro y hy
    have h := (OpenMaxPrinciple.mem_discretize_iff' hm0).1 hy
    rw [mem_ball, dist_eq_norm] at h
    rw [norm_toE_sub_smul hm0]
    exact mul_lt_mul_of_pos_left h hmpos
  have hI : ‖toE xc - (m : ℝ) • b‖ < β * ((m : ℝ) * r) := by
    have h := (OpenMaxPrinciple.mem_discretize_iff' hm0).1 hxcI
    rw [mem_ball, dist_eq_norm] at h
    rw [norm_toE_sub_smul hm0]
    have := mul_lt_mul_of_pos_left h hmpos
    linarith
  have hB : ∀ y ∈ bdry (discretize (ball b r) m),
      (m : ℝ) * r ≤ ‖toE y - (m : ℝ) • b‖ ∧ ‖toE y - (m : ℝ) • b‖ < (m : ℝ) * r + 1 := by
    intro y hy
    obtain ⟨h1, h2⟩ := OpenMaxPrinciple.bdry_rescaled hm hy
    rw [norm_toE_sub_smul hm0]
    constructor
    · exact mul_le_mul_of_nonneg_left h1 hmpos.le
    · have := mul_lt_mul_of_pos_left h2 hmpos
      rw [mul_add, mul_one_div_cancel hmpos.ne'] at this
      exact this
  have hD : ∀ y ∈ dClosure (discretize (ball b r) m),
      ‖toE y - (m : ℝ) • b‖ ≤ (m : ℝ) * r + 1 := by
    intro y hy
    rw [dClosure_eq] at hy
    rcases hy with hy | hy
    · linarith [hA y hy]
    · exact (hB y hy).2.le
  -- the splitting `q - T = G + affine`
  have hid : ∀ y ∈ dClosure (discretize (ball b r) m), (qlZ 0 y + qMZ M' y) -
      ((m : ℝ) ^ 2 * u₀ + (m : ℝ) * inner ℝ p₀ (toE y - (m : ℝ) • b) +
        qM N (toE y - (m : ℝ) • b)) =
      qM (M' - N) (toE y - (m : ℝ) • b) +
        ((-((m : ℝ) ^ 2 * u₀) + (m : ℝ) * inner ℝ p₀ ((m : ℝ) • b) - qM M' ((m : ℝ) • b)) +
          inner ℝ (WithLp.toLp 2 (M' *ᵥ WithLp.ofLp ((m : ℝ) • b)) - (m : ℝ) • p₀) (toE y)) := by
    intro y _
    have hq0 : qlZ 0 y = 0 := by simp [qlZ, ql]
    have h1 := OpenMaxPrinciple.qM_sub' hM' (toE y) ((m : ℝ) • b)
    have h2 : qMZ M' y = qM M' (toE y) := rfl
    rw [hq0, h2, qM_sub_mat, h1, inner_sub_left, real_inner_smul_left, inner_sub_right]
    ring
  have hG0 : ∀ y ∈ dClosure (discretize (ball b r) m), 0 ≤ qM (M' - N) (toE y - (m : ℝ) • b) :=
    fun y _ => le_trans (by positivity) (hP _).1
  have hGb : ∀ y ∈ bdry (discretize (ball b r) m),
      bm / 2 * ((m : ℝ) * r) ^ 2 ≤ qM (M' - N) (toE y - (m : ℝ) • b) := by
    intro y hy
    have h1 := (hP (toE y - (m : ℝ) • b)).1
    have h2 : ((m : ℝ) * r) ^ 2 ≤ ‖toE y - (m : ℝ) • b‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hB y hy).1 2
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ bm / 2)
    linarith
  have hGc : qM (M' - N) (toE xc - (m : ℝ) • b) ≤ bp / 2 * (β * ((m : ℝ) * r)) ^ 2 := by
    have h1 := (hP (toE xc - (m : ℝ) • b)).2
    have h2 : ‖toE xc - (m : ℝ) • b‖ ^ 2 ≤ (β * ((m : ℝ) * r)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hI.le 2
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ bp / 2)
    linarith
  exact false_of_contact hne h0 hX hxcA hp
    (T := fun y => (m : ℝ) ^ 2 * u₀ + (m : ℝ) * inner ℝ p₀ (toE y - (m : ℝ) • b) +
      qM N (toE y - (m : ℝ) • b))
    (G := fun y => qM (M' - N) (toE y - (m : ℝ) • b))
    (g := WithLp.toLp 2 (M' *ᵥ WithLp.ofLp ((m : ℝ) • b)) - (m : ℝ) • p₀)
    (c₀ := -((m : ℝ) ^ 2 * u₀) + (m : ℝ) * inner ℝ p₀ ((m : ℝ) • b) - qM M' ((m : ℝ) • b))
    (z0 := (m : ℝ) • b) (D := (m : ℝ) * r + 1)
    hid happ hG0 hGb hGc hD hgap fun y hy => hpos.trans (hlow y hy)

end SingleSourceFstar

end RandomSandpile

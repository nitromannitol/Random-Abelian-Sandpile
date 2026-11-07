import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatGeom3
import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlat

/-!
# Operator fact (11): the boundary minimum estimate

`boundaryMin : BoundaryMinStmt` (note §5, estimate (10)). Let `x` be a lattice minimizer of
`g = q_A + p·` over `B̄_R`. If `x ∈ ∂B_R` there is nothing to prove. Otherwise the comparisons at
`x ± e_i` give `|∇g(x)_i| ≤ A_ii/2`. Take a unit `e` with `eᵀAe ≤ 0`, follow `x + t e` to the sphere
(`t ≤ 2R`; `g` grows by at most `t |∇g(x)|`), then move to a boundary site within bounded distance
(`bdry_near`), where `∇g = ∇g(x) + t A e = O(R)`. Small `R` is bounded directly.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

theorem exit_point (u e : Fin d → ℝ) (hne : nv e = 1) {R : ℝ} (hR0 : 0 ≤ R) (hu : nv u < R) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 * R ∧ nv (u + t • e) = R := by
  have he : e ⬝ᵥ e = 1 := by rw [← nv_sq, hne]; norm_num
  have hBc : |u ⬝ᵥ e| ≤ nv u := by
    have := abs_dot_le u e; rw [hne, mul_one] at this; exact this
  have hu0 := nv_nonneg u
  have hD0 : 0 < R ^ 2 - nv u ^ 2 := by nlinarith
  have hsq : Real.sqrt ((u ⬝ᵥ e) ^ 2 + (R ^ 2 - nv u ^ 2)) ^ 2 = (u ⬝ᵥ e) ^ 2 + (R ^ 2 - nv u ^ 2) :=
    Real.sq_sqrt (by positivity)
  have hB2 : (u ⬝ᵥ e) ^ 2 ≤ nv u ^ 2 := by
    have := sq_abs (u ⬝ᵥ e); nlinarith [abs_nonneg (u ⬝ᵥ e)]
  have hsqabs : |u ⬝ᵥ e| ≤ Real.sqrt ((u ⬝ᵥ e) ^ 2 + (R ^ 2 - nv u ^ 2)) :=
    Real.abs_le_sqrt (by linarith)
  have hsqR : Real.sqrt ((u ⬝ᵥ e) ^ 2 + (R ^ 2 - nv u ^ 2)) ≤ R :=
    Real.sqrt_le_iff.2 ⟨hR0, by linarith⟩
  refine ⟨-(u ⬝ᵥ e) + Real.sqrt ((u ⬝ᵥ e) ^ 2 + (R ^ 2 - nv u ^ 2)), ?_, ?_, ?_⟩
  · linarith [neg_abs_le (u ⬝ᵥ e), le_abs_self (u ⬝ᵥ e)]
  · linarith [abs_le.1 hBc]
  · have h1 : nv (u + (-(u ⬝ᵥ e) + Real.sqrt ((u ⬝ᵥ e) ^ 2 + (R ^ 2 - nv u ^ 2))) • e) ^ 2 = R ^ 2 := by
      rw [nv_sq]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [he, dotProduct_comm e u, ← nv_sq u]
      linear_combination hsq
    have := nv_nonneg (u + (-(u ⬝ᵥ e) + Real.sqrt ((u ⬝ᵥ e) ^ 2 + (R ^ 2 - nv u ^ 2))) • e)
    nlinarith

theorem nv_xv_lt {R : ℝ} {y : Site d} (hy : y ∈ ballZ0 (d := d) R) : nv (xv y) < R := by
  have := MuLipschitz.mem_ballZ0.1 hy
  exact this

set_option maxHeartbeats 800000 in
theorem boundaryMin : BoundaryMinStmt := by
  intro d hd A hA hnot
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set M : ℝ := opC A with hM
  have hM0 : 0 ≤ M := opC_nonneg A
  set c₁ : ℝ := ∑ i, |A i i| with hc₁
  have hc₁0 : 0 ≤ c₁ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set lam : ℝ := Real.sqrt d + 1 with hlam
  have hlam0 : 0 < lam := by rw [hlam]; linarith
  set c₂ : ℝ := d * (2 * lam + 2 * Real.sqrt d) + Real.sqrt d + lam with hc₂
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  set c₃ : ℝ := 2 * d * (2 * lam + 1) with hc₃
  have hc₃0 : 0 ≤ c₃ := by rw [hc₃]; positivity
  set C : ℝ := 2 * c₁ + c₁ * c₂ + 2 * M * c₂ + M * c₂ ^ 2 / 2 + c₁ * c₃ + M * c₃ ^ 2 / 2 with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC0, fun R p y hy => ?_⟩
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  set B := ballZ0 (d := d) (R : ℝ) with hB
  set pv : Fin d → ℝ := WithLp.ofLp p with hpv
  have hfin : (dClosure B).Finite := dClosure_finite (MuLipschitz.ballZ0_finite _)
  suffices H : ∃ b ∈ bdry B, gq A pv (xv b) ≤ gq A pv (xv y) + C * ((R : ℝ) + 1) by
    obtain ⟨b, hb, h⟩ := H
    exact ⟨b, hb, by rw [gS_eq, gS_eq]; exact h⟩
  obtain ⟨x, hxcl, hxmin⟩ := Set.exists_min_image (dClosure B) (fun z => gq A pv (xv z)) hfin
    ⟨y, hy⟩
  have hCR : 0 ≤ C * ((R : ℝ) + 1) := by positivity
  rcases dClosure_union_bdry hxcl with hxB | hxb
  · -- interior minimizer
    set G : Fin d → ℝ := A *ᵥ xv x + pv with hG
    have hgrad : ∀ i, |G i| ≤ |A i i| := fun i => by
      have := grad_bound hA pv hxB (fun z hz => hxmin z hz) i
      have h2 : A i i / 2 ≤ |A i i| := by
        have := le_abs_self (A i i); have := abs_nonneg (A i i)
        have h3 : 0 ≤ A i i := by linarith [abs_nonneg (G i)]
        linarith
      exact this.trans h2
    have hnG : nv G ≤ c₁ := by
      have := norm_le_sum_abs (WithLp.toLp 2 G : Rd d)
      unfold nv
      refine this.trans ?_
      exact Finset.sum_le_sum fun i _ => hgrad i
    have hxlt : nv (xv x) < R := nv_xv_lt hxB
    by_cases hbig : 2 * lam ≤ (R : ℝ)
    · obtain ⟨e, hne, hAe⟩ := exists_unit_nonpos hA hnot
      obtain ⟨t, ht0, htR, hnq⟩ := exit_point (xv x) e hne hR0 hxlt
      set q : Fin d → ℝ := xv x + t • e with hq
      have hRl : 2 * (Real.sqrt d + 1) ≤ (R : ℝ) := hbig
      obtain ⟨b, hb, hbd⟩ := bdry_near (d := d) hRl (WithLp.toLp 2 q) (by simpa [nv] using hnq)
      set h : Fin d → ℝ := WithLp.ofLp (toE b - WithLp.toLp 2 q) with hh
      have hnh : nv h ≤ c₂ := by
        have : nv h = ‖toE b - WithLp.toLp 2 q‖ := by simp [nv, hh]
        rw [this]; exact hbd
      have hxb : xv b = q + h := by
        funext i; simp [hh, xv, toE]
      refine ⟨b, hb, ?_⟩
      have hmin' : gq A pv (xv x) ≤ gq A pv (xv y) := hxmin y hy
      rw [hxb, gq_add A hA]
      have hgq : gq A pv q = gq A pv (xv x) + t * (e ⬝ᵥ G) + t ^ 2 / 2 * (e ⬝ᵥ A *ᵥ e) := by
        rw [hq, gq_add A hA]
        simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, Matrix.mulVec_smul, hG]
        ring
      have hAq : A *ᵥ q + pv = G + t • (A *ᵥ e) := by
        rw [hq, Matrix.mulVec_add, Matrix.mulVec_smul, hG]
        abel
      rw [hAq, hgq]
      have b1 : e ⬝ᵥ G ≤ c₁ := by
        have := abs_dot_le e G; rw [hne, one_mul] at this
        exact (le_abs_self _).trans (this.trans hnG)
      have b2 : h ⬝ᵥ G ≤ c₂ * c₁ := by
        have := abs_dot_le h G
        exact (le_abs_self _).trans (this.trans (mul_le_mul hnh hnG (nv_nonneg _) hc₂0))
      have b3 : h ⬝ᵥ (A *ᵥ e) ≤ c₂ * M := by
        have := abs_dot_le h (A *ᵥ e)
        have h5 : nv (A *ᵥ e) ≤ M := by
          have := nv_mulVec_le A e; rw [hne, mul_one] at this; exact this
        exact (le_abs_self _).trans (this.trans (mul_le_mul hnh h5 (nv_nonneg _) hc₂0))
      have b4 : h ⬝ᵥ A *ᵥ h ≤ M * c₂ ^ 2 := by
        have := abs_quad_le A h
        refine (le_abs_self _).trans (this.trans ?_)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (nv_nonneg _) hnh 2) hM0
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have e1 : t * (e ⬝ᵥ G) ≤ 2 * R * c₁ := by
        calc t * (e ⬝ᵥ G) ≤ t * c₁ := mul_le_mul_of_nonneg_left b1 ht0
          _ ≤ 2 * R * c₁ := mul_le_mul_of_nonneg_right htR hc₁0
      have e2 : t * (h ⬝ᵥ A *ᵥ e) ≤ 2 * R * (c₂ * M) := by
        calc t * (h ⬝ᵥ A *ᵥ e) ≤ t * (c₂ * M) := mul_le_mul_of_nonneg_left b3 ht0
          _ ≤ 2 * R * (c₂ * M) := mul_le_mul_of_nonneg_right htR (by positivity)
      have e3 : t ^ 2 / 2 * (e ⬝ᵥ A *ᵥ e) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hAe
      have : C * ((R : ℝ) + 1) = C * R + C := by ring
      have hCge : C * R ≥ (2 * c₁ + 2 * M * c₂) * R := by
        apply mul_le_mul_of_nonneg_right _ hR0
        rw [hC]; nlinarith [mul_nonneg hc₁0 hc₂0, mul_nonneg hM0 (sq_nonneg c₂),
          mul_nonneg hc₁0 hc₃0, mul_nonneg hM0 (sq_nonneg c₃)]
      nlinarith [mul_nonneg hc₁0 hc₂0, mul_nonneg hM0 (sq_nonneg c₂), mul_nonneg hc₁0 hc₃0,
        mul_nonneg hM0 (sq_nonneg c₃), mul_nonneg hM0 hc₂0]
    · -- small radius
      push Not at hbig
      obtain ⟨b₀, hb₀⟩ := Burning.bdry_nonempty hd0 (MuLipschitz.ballZ0_finite (d := d) (R : ℝ))
        ⟨x, hxB⟩
      refine ⟨b₀, hb₀, ?_⟩
      set h : Fin d → ℝ := xv b₀ - xv x with hh
      have hcoord : ∀ i, |h i| ≤ 2 * ((R : ℝ) + 1) := fun i => by
        have a1 := abs_coord_le_dClosure (bdry_subset_dClosure _ hb₀) i
        have a2 := abs_coord_le_dClosure (mem_dClosure_of_mem hxB) i
        simp only [hh, Pi.sub_apply, xv]
        have := abs_sub (((b₀ i : ℤ) : ℝ)) (((x i : ℤ) : ℝ))
        linarith
      have hnh : nv h ≤ c₃ := by
        have := norm_le_sum_abs (WithLp.toLp 2 h : Rd d)
        unfold nv
        refine this.trans ?_
        calc ∑ i, |(WithLp.toLp 2 h : Rd d) i| ≤ ∑ _i : Fin d, 2 * ((R : ℝ) + 1) :=
              Finset.sum_le_sum fun i _ => hcoord i
          _ = d * (2 * ((R : ℝ) + 1)) := by simp
          _ ≤ c₃ := by rw [hc₃]; nlinarith
      have hxb : xv b₀ = xv x + h := by rw [hh]; abel
      have hmin' : gq A pv (xv x) ≤ gq A pv (xv y) := hxmin y hy
      rw [hxb, gq_add A hA]
      have b2 : h ⬝ᵥ G ≤ c₃ * c₁ := by
        have := abs_dot_le h G
        exact (le_abs_self _).trans (this.trans (mul_le_mul hnh hnG (nv_nonneg _) hc₃0))
      have b4 : h ⬝ᵥ A *ᵥ h ≤ M * c₃ ^ 2 := by
        have := abs_quad_le A h
        refine (le_abs_self _).trans (this.trans ?_)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (nv_nonneg _) hnh 2) hM0
      have hCge : C ≥ c₁ * c₃ + M * c₃ ^ 2 / 2 := by
        rw [hC]; nlinarith [mul_nonneg hc₁0 hc₂0, mul_nonneg hM0 (sq_nonneg c₂), hc₁0, hM0]
      nlinarith [mul_nonneg hC0 hR0]
  · exact ⟨x, hxb, by linarith [hxmin y hy]⟩

end SingleSourceH0

end RandomSandpile

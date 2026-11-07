import RandomSandpile.Proofs.Sec9.SingleSourceD2Algebra

/-!
# Theorem 9.2 in dimension two: trace-graph bounds for `F*`

SIMPLE-PROOF §6, (6.2). For a background with `η_max = 2`:
* `traceGraph_effOpStar_le`: `f(z) = F*(A_z) ≤ 3 - η_min` (site bound of Lemma 5.4,
  `muStarBar_eq_zero_of_ge`);
* `effOpStar_zero_nonneg`: `F*(0) ≥ 0`: the stabilizing function `0` and `-q_l`, `l < 0`, give
  subgradient balls of radius `-l/(2d)` at every site (`muStar_lower_zero`);
* `le_muStarBar_of_eventually`: the lower bound for `μ̄*` from large balls only;
* `effOpStarTraceBounds_of_lower`: from the lower bound `f ≥ -2`
  (`EffOpStarTraceLowerD2Stmt`, the ceiling-stabilizer argument of SIMPLE-PROOF §6).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal

namespace RandomSandpile

open EffectiveOperatorBasic MuLipschitz

namespace SingleSourceD2

variable {d : ℕ}

/-- **, upper half**: `f(z) ≤ 3 - η_min`. -/
theorem traceGraph_effOpStar_le (E : RandomEnvironment 2) (hE : E.ηmax ≤ 2 * ((2 : ℕ) : ℤ) - 1)
    (z : Rd 2) : traceGraph (effOpStar E) z ≤ ((3 - E.ηmin : ℤ) : ℝ) := by
  unfold traceGraph effOpStar
  refine csSup_le (effOpStar_set_nonempty (by norm_num) E hE (traceFreeMat_isSymm z))
    fun l hl => ?_
  by_contra hlt
  have h := muStarBar_eq_zero_of_ge (by norm_num) E (traceFreeMat z) (l := l) (by
    rw [trace_traceFreeMat]
    push_cast at hlt ⊢
    linarith [not_le.mp hlt])
  exact (ne_of_gt hl) h

/-- With the stabilizing function `0`, `-q_l` (`l < 0`) has subgradient balls of radius `-l/(2d)`
at every site. -/
theorem muStar_lower_zero (hd : 1 ≤ d) {l : ℝ} (hl : l < 0) {η : Site d → ℤ} {B : Set (Site d)}
    (hfin : B.Finite) (hη : ∀ x ∈ B, η x ≤ 2 * (d : ℤ) - 1) :
    ENNReal.ofReal ((volume (closedBall (0 : Rd d) (-l / (2 * d)))).toReal * (B.ncard : ℝ)) ≤
      muStar B η l 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = -l / (2 * d) := ⟨_, rfl⟩
  have hρ : 0 ≤ ρ := by rw [hρdef]; exact div_nonneg (by linarith) (by positivity)
  rw [← hρdef]
  set V := volume (closedBall (0 : Rd d) ρ)
  have hV : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have h0S : (0 : Site d → ℤ) ∈ stabilizing η B := by
    refine ⟨⟨fun _ => le_rfl, fun _ _ => rfl⟩, fun x hx => ?_⟩
    have : lap (0 : Site d → ℤ) x = 0 := by simp [lap, nbrSumZ]
    rw [this, zero_add]; exact hη x hx
  set w : Site d → ℝ := fun x => ((0 : Site d → ℤ) x : ℝ) -
    (qlZ l x + qMZ (0 : Matrix (Fin d) (Fin d) ℝ) x) with hw
  have hwS : w ∈ perturbedSuper B η l 0 := Set.mem_image_of_mem _ h0S
  have hq0 : ∀ z : Site d, qMZ (0 : Matrix (Fin d) (Fin d) ℝ) z = 0 := fun z => by
    simp [qMZ, qM]
  have hball : ∀ x : Site d, closedBall (-((l / d) • toE x)) ρ ⊆ subGrad w x B := by
    intro x p hp y _
    have he : ‖p + (l / d) • toE x‖ ≤ ρ := by
      rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add] at hp; exact hp
    have hcs := abs_real_inner_le_norm (p + (l / d) • toE x) (toE y - toE x)
    have hz := norm_le_sq_toE_sub x y
    have hql := qlZ_sub_eq_inner hd l x y
    have h1 : ‖p + (l / d) • toE x‖ * ‖toE y - toE x‖ ≤ ρ * ‖toE y - toE x‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg _)
    have h2 := mul_le_mul_of_nonneg_left hz hρ
    have hinner : inner ℝ (p + (l / d) • toE x) (toE y - toE x) =
        inner ℝ p (toE y - toE x) + inner ℝ ((l / d) • toE x) (toE y - toE x) :=
      inner_add_left _ _ _
    have hρl : l / (2 * d) = -ρ := by rw [hρdef]; ring
    rw [hρl] at hql
    simp only [w, Pi.zero_apply, Int.cast_zero, zero_sub, hq0, add_zero]
    linarith [le_abs_self (inner ℝ (p + (l / d) • toE x) (toE y - toE x))]
  calc ENNReal.ofReal (V.toReal * (B.ncard : ℝ))
      = (B.ncard : ℝ≥0∞) * V := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hV,
          ENNReal.ofReal_natCast, mul_comm]
    _ = ∑' _ : B, V := by
        rw [ENNReal.tsum_set_const, ← hfin.cast_ncard_eq]
        simp
    _ ≤ ∑' x : B, volume (subGrad w x B) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        calc V = volume (closedBall (-((l / d) • toE (x : Site d))) ρ) := by
              simp only [V, Measure.addHaar_closedBall _ _ hρ]
          _ ≤ _ := measure_mono (hball x)
    _ = volume (subGradSet w B) := ((supGradSetVolume d w B).2).symm
    _ ≤ muStar B η l 0 := le_iSup₂_of_le w hwS le_rfl

/-- `μ*(l, 0) > 0` for `l < 0` when `η_max ≤ 2d - 1`. -/
theorem muStarBar_zero_pos (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) {l : ℝ} (hl : l < 0) : 0 < muStarBar E l 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hρ : 0 < -l / (2 * d) := div_pos (by linarith) (by positivity)
  refine (volume_closedBall_toReal_pos (d := d) hρ).trans_le ?_
  refine le_muStarBar_of hd E ?_
  filter_upwards [ae_all_iff.2 E.bounded] with η hη
  exact fun n _ => muStar_lower_zero hd hl (ballZ0_finite _) fun x _ => (hη x).2.trans hE

/-- `F*(0) ≥ 0`. -/
theorem effOpStar_zero_nonneg (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hE : E.ηmax ≤ 2 * (d : ℤ) - 1) : 0 ≤ effOpStar E 0 :=
  (effOpStar_nonneg_iff hd E hE Matrix.isSymm_zero).2 fun _ hl => muStarBar_zero_pos hd E hE hl

/-- The lower bound for `μ̄*` from large balls only. -/
theorem le_muStarBar_of_eventually (hd : 1 ≤ d) (E : RandomEnvironment d) {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (h : ∀ᵐ η ∂E.P, ∀ n : ℕ, n₀ ≤ n →
      ENNReal.ofReal (c * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
        muStar (ballZ0 (n : ℝ)) η l M) :
    c ≤ muStarBar E l M := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (muStarBar_nonneg E l M)
  have hlim : ∀ᵐ η ∂E.P, ENNReal.ofReal c ≤
      limsup (fun n : ℕ => muStar (ballZ0 (n : ℝ)) η l M /
        ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop := by
    filter_upwards [h] with η hη
    exact le_limsup_of_frequently_le
      ((eventually_ge_atTop n₀).mono fun n hn =>
        ofReal_le_div_ncard hc.le (hn₀.trans hn) (hη n hn)).frequently
  unfold muStarBar
  calc c = (∫⁻ _, ENNReal.ofReal c ∂E.P).toReal := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.toReal_ofReal hc.le]
    _ ≤ _ := ENNReal.toReal_mono (lintegral_muStar_ne_top hd E l M) (lintegral_mono_ae hlim)

/-- **, lower half**: `f(z) ≥ -2`, i.e. `μ*(l, A_z) > 0` for `l < -2`. -/
def EffOpStarTraceLowerD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    ∀ z : Rd 2, -2 ≤ traceGraph (effOpStar E) z

/-- from its lower half. -/
theorem effOpStarTraceBounds_of_lower (h : EffOpStarTraceLowerD2Stmt) :
    EffOpStarTraceBoundsD2Stmt := by
  intro E hE
  have hE1 : E.ηmax ≤ 2 * ((2 : ℕ) : ℤ) - 1 := by rw [hE]; norm_num
  exact ⟨fun z => ⟨h E hE z, traceGraph_effOpStar_le E hE1 z⟩,
    effOpStar_zero_nonneg (by norm_num) E hE1⟩

end SingleSourceD2

end RandomSandpile

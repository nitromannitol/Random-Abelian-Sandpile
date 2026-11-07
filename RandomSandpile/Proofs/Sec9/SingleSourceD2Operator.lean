import RandomSandpile.Proofs.Sec9.SingleSourceD2Super
import RandomSandpile.Proofs.Sec9.SingleSourceD2TraceLower
import RandomSandpile.Proofs.Sec5.ABP
import RandomSandpile.Proofs.Sec6.StrictConcavityNearMax
import RandomSandpile.Proofs.Sec6.StrictConcavityBall
import RandomSandpile.Proofs.Sec3.Burning

/-!
# Theorem 9.2 in dimension two: `F̄ ≤ F*`

D2-PROOF §3.2 and (3.3). `noCommonZero`: there are no `l₁ < l₂` with `μ̄*(l₁, M) = 0` and
`μ̄(l₂, M) = 0`. On `B_n`, take `h` legal and stabilizing with boundary values
`⌈q_M + q_m⌉ + C₀`, `m = (l₁ + l₂)/2` (least action, `exists_locLegal_stabilizing`); the two ABP
bounds (Lemma 5.2) at `l₁` (stabilizing side) and `l₂` (legal side) give
`(l₂ - l₁) n²/4 ≤ 1 + C n (μ*(B_n)^{1/2} + μ(B_n)^{1/2})`, while the ergodic limits (Lemma 5.5) make
the right side `1 + o(n²)`. `effOpLeStar_of_noCommonZero`: from it, since `F̄(M)` lies in
`muEqSet` (`isGreatest_effOp`) and every `l > F*(M)` has `μ̄*(l, M) = 0`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter

namespace RandomSandpile

open EffectiveOperatorBasic MuLipschitz

namespace SingleSourceD2

/-- **No common-zero interval**. -/
def NoCommonZeroD2Stmt : Prop :=
  ∀ E : RandomEnvironment 2, E.ηmax = 2 * ((2 : ℕ) : ℤ) - 2 →
    ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm → ∀ l₁ l₂ : ℝ, l₁ < l₂ →
      muStarBar E l₁ M = 0 → muBar E l₂ M = 0 → False

/-- `μ̄*(l, M) = 0` above `F*(M)`. -/
theorem muStarBar_eq_zero_of_gt (E : RandomEnvironment 2) {M : Matrix (Fin 2) (Fin 2) ℝ}
    {l : ℝ} (hl : effOpStar E M < l) : muStarBar E l M = 0 := by
  by_contra hne
  have hpos : 0 < muStarBar E l M := lt_of_le_of_ne (muStarBar_nonneg E l M) (Ne.symm hne)
  have := le_csSup (effOpStar_set_bddAbove (by norm_num) E M) hpos
  exact absurd (lt_of_lt_of_le hl this) (lt_irrefl _)

/-- from the absence of a common zero. -/
theorem effOpLeStar_of_noCommonZero (h : NoCommonZeroD2Stmt) : EffOpLeStarD2Stmt := by
  intro E hE M hM
  have hG := isGreatest_effOp muConvergence_unconditional le_rfl E hM
  by_contra hlt
  have hlt' : effOpStar E M < effOp E M := not_le.mp hlt
  have h1 : muStarBar E ((effOpStar E M + effOp E M) / 2) M = 0 :=
    muStarBar_eq_zero_of_gt E (by linarith)
  have h2' : muStarBar E (effOp E M) M = 0 := muStarBar_eq_zero_of_gt E hlt'
  have h2 : muBar E (effOp E M) M = 0 := by
    have hmem : muBar E (effOp E M) M = muStarBar E (effOp E M) M := hG.1
    rw [hmem, h2']
  exact h E hE M hM _ _ (by linarith) h1 h2

/-! ### No common zero -/

theorem discretize_unitBall_eq {n : ℕ} (hn : 1 ≤ n) :
    discretize (Metric.ball (0 : Rd 2) 1) n = ballZ0 (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  ext x
  simp only [discretize, Set.mem_setOf_eq]
  rw [smul_ball hnp.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hnp, mul_one, Metric.mem_ball,
    dist_zero_right, mem_ballZ0]

theorem qlZ_two (l : ℝ) (y : Site 2) : qlZ l y = l / 4 * ‖toE y‖ ^ 2 := by
  simp only [qlZ, ql]; push_cast; ring

/-- Lower bound for the boundary values of `h - q_l - q_M` when `h = ⌈q_M + q_m⌉ + C₀` there. -/
theorem le_sInf_bdry {B : Set (Site 2)} (hne : (bdry B).Nonempty) {h : Site 2 → ℤ}
    {M : Matrix (Fin 2) (Fin 2) ℝ} {m l : ℝ} (hml : l ≤ m) {C₀ : ℤ} {n : ℝ}
    (hbd : ∀ y ∈ bdry B, (h y : ℝ) = ⌈qMZ M y + qlZ m y⌉ + C₀)
    (hfar : ∀ y ∈ bdry B, n ^ 2 ≤ ‖toE y‖ ^ 2) :
    (m - l) / 4 * n ^ 2 + C₀ ≤ sInf ((fun y => (h y : ℝ) - (qlZ l y + qMZ M y)) '' bdry B) := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hc := Int.le_ceil (qMZ M y + qlZ m y)
  have hfy := mul_le_mul_of_nonneg_left (hfar y hy) (by linarith : (0 : ℝ) ≤ (m - l) / 4)
  have hqm := qlZ_two m y
  have hql := qlZ_two l y
  show _ ≤ (h y : ℝ) - (qlZ l y + qMZ M y)
  rw [hbd y hy]
  linarith

/-- Upper bound for the boundary values of `h - q_l - q_M` when `h = ⌈q_M + q_m⌉ + C₀` there. -/
theorem sSup_bdry_le {B : Set (Site 2)} (hne : (bdry B).Nonempty) {h : Site 2 → ℤ}
    {M : Matrix (Fin 2) (Fin 2) ℝ} {m l : ℝ} (hml : m ≤ l) {C₀ : ℤ} {n : ℝ}
    (hbd : ∀ y ∈ bdry B, (h y : ℝ) = ⌈qMZ M y + qlZ m y⌉ + C₀)
    (hfar : ∀ y ∈ bdry B, n ^ 2 ≤ ‖toE y‖ ^ 2) :
    sSup ((fun y => (h y : ℝ) - (qlZ l y + qMZ M y)) '' bdry B) ≤ (m - l) / 4 * n ^ 2 + C₀ + 1 := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hc := Int.ceil_lt_add_one (qMZ M y + qlZ m y)
  have hfy := mul_le_mul_of_nonpos_left (hfar y hy) (by linarith : (m - l) / 4 ≤ 0)
  have hqm := qlZ_two m y
  have hql := qlZ_two l y
  show (h y : ℝ) - (qlZ l y + qMZ M y) ≤ _
  rw [hbd y hy]
  linarith

/-- The centre estimate: ABP on both sides for a legal stabilizer with ceiling boundary data. -/
theorem center_bound {C : ℝ}
    (hABP : ∀ (n : ℕ) (η : Site 2 → ℤ) (l : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ), M.IsSymm →
      (mu (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
        ∀ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
          w x ≤ sSup (w '' bdry (ballZ0 (n : ℝ))) +
            C * n * (mu (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / ((2 : ℕ) : ℝ))) ∧
      (muStar (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
        ∀ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
          sInf (w '' bdry (ballZ0 (n : ℝ))) ≤
            w x + C * n * (muStar (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / ((2 : ℕ) : ℝ))))
    {n : ℕ} (hn1 : 1 ≤ n) (η : Site 2 → ℤ) {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.IsSymm)
    {l₁ l₂ : ℝ} (hl : l₁ < l₂) (hf1 : muStar (ballZ0 (n : ℝ)) η l₁ M ≠ ⊤)
    (hf2 : mu (ballZ0 (n : ℝ)) η l₂ M ≠ ⊤) :
    (l₂ - l₁) / 4 * (n : ℝ) ^ 2 ≤
      1 + C * n * (muStar (ballZ0 (n : ℝ)) η l₁ M).toReal ^ (1 / ((2 : ℕ) : ℝ)) +
        C * n * (mu (ballZ0 (n : ℝ)) η l₂ M).toReal ^ (1 / ((2 : ℕ) : ℝ)) := by
  set B := ballZ0 (d := 2) (n : ℝ)
  have hfinB : B.Finite := ballZ0_finite _
  have hfinD : (dClosure B).Finite := dClosure_finite hfinB
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℤ, ∀ y ∈ dClosure B, -⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉ ≤ C₀ := by
    obtain ⟨C₀, hC₀⟩ := (hfinD.image fun y => -⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉).bddAbove
    exact ⟨C₀, fun y hy => hC₀ ⟨y, hy, rfl⟩⟩
  obtain ⟨u, hudef⟩ : ∃ u : Site 2 → ℤ,
      u = (dClosure B).indicator fun y => ⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉ + C₀ := ⟨_, rfl⟩
  have hu : IsTopplingFn B u := by
    rw [hudef]
    refine ⟨fun y => ?_, fun y hy => Set.indicator_of_notMem hy _⟩
    by_cases hy : y ∈ dClosure B
    · rw [Set.indicator_of_mem hy]; linarith [hC₀ y hy]
    · rw [Set.indicator_of_notMem hy]
  obtain ⟨h, ⟨hL, hS⟩, hbd⟩ :=
    NearMaxSequence.exists_locLegal_stabilizing (by norm_num) hfinB η hu
  have hbd' : ∀ y ∈ bdry B, (h y : ℝ) = ⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉ + C₀ := by
    intro y hy
    rw [hbd y hy, hudef, Set.indicator_of_mem (bdry_subset_dClosure B hy)]
    push_cast
    ring
  have hfar : ∀ y ∈ bdry B, (n : ℝ) ^ 2 ≤ ‖toE y‖ ^ 2 := by
    intro y hy
    have hyn : (n : ℝ) ≤ ‖toE y‖ := by
      by_contra hlt
      exact hy.1 (mem_ballZ0.2 (not_le.mp hlt))
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hne : (bdry B).Nonempty := Burning.bdry_nonempty (by norm_num) hfinB
    ⟨0, mem_ballZ0.2 (by rw [toE_zero, norm_zero]; exact_mod_cast hn1)⟩
  have h0B : (0 : Site 2) ∈ B := mem_ballZ0.2 (by rw [toE_zero, norm_zero]; exact_mod_cast hn1)
  have hw₁ : (fun y => (h y : ℝ) - (qlZ l₁ y + qMZ M y)) ∈ perturbedSuper B η l₁ M :=
    Set.mem_image_of_mem _ hS
  have hw₂ : (fun y => (h y : ℝ) - (qlZ l₂ y + qMZ M y)) ∈ perturbedSub B η l₂ M :=
    mem_perturbedSub.2 ⟨h, hL, rfl⟩
  have hA1 := (hABP n η l₁ M hM).2 hf1 _ hw₁ 0 h0B
  have hA2 := (hABP n η l₂ M hM).1 hf2 _ hw₂ 0 h0B
  have hq0 : ∀ l : ℝ, qlZ l (0 : Site 2) + qMZ M 0 = 0 := fun l => by
    simp [qlZ, ql, qMZ, qM, toE_zero]
  simp only [hq0, sub_zero] at hA1 hA2
  have hinf := le_sInf_bdry hne (h := h) (l := l₁) (by linarith) hbd' hfar
  have hsup := sSup_bdry_le hne (h := h) (l := l₂) (by linarith) hbd' hfar
  have e : ((l₁ + l₂) / 2 - l₁) / 4 * (n : ℝ) ^ 2 - ((l₁ + l₂) / 2 - l₂) / 4 * (n : ℝ) ^ 2 =
      (l₂ - l₁) / 4 * (n : ℝ) ^ 2 := by ring
  linarith

/-- **No common-zero interval**, proved from the ergodic limits (Lemma 5.5), the ABP bounds
(Lemma 5.2) and a legal stabilizer with ceiling boundary data (least action). -/
theorem noCommonZero : NoCommonZeroD2Stmt := by
  intro E hE M hM l₁ l₂ hl h1 h2
  obtain ⟨C, hC, hABP⟩ := abp 2 le_rfl
  have hconv := (muConvergence_unconditional 2 le_rfl).1
  obtain ⟨η, hη1, hη2⟩ := ((hconv E M hM l₁).and (hconv E M hM l₂)).exists
  have hW := StrictConcavityBall.isLipschitzDomain_ball (0 : Rd 2) one_pos
  obtain ⟨hfin1, -, hT1⟩ := hη1 _ hW
  obtain ⟨hfin2, hT2, -⟩ := hη2 _ hW
  rw [h1] at hT1
  rw [h2] at hT2
  have hD0 : 0 < l₂ - l₁ := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (l₂ - l₁) / (48 * C) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈8 / (l₂ - l₁)⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨n, hr1, hr2, hnN⟩ :=
    ((hT1.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ 2))).and
      ((hT2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ 2))).and
        (eventually_ge_atTop N))).exists
  have hn1 : 1 ≤ n := by rw [hN] at hnN; omega
  have hnD : 8 / (l₂ - l₁) < n := by
    have h1' : 8 / (l₂ - l₁) ≤ (⌈8 / (l₂ - l₁)⌉₊ : ℝ) := Nat.le_ceil _
    have h2' : ((⌈8 / (l₂ - l₁)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by rw [← hN]; exact_mod_cast hnN
    push_cast at h2'
    linarith
  simp only [discretize_unitBall_eq hn1] at hr1 hr2
  have hf1 := (hfin1 n).2
  have hf2 := (hfin2 n).1
  rw [discretize_unitBall_eq hn1] at hf1 hf2
  have hcard : (0 : ℝ) < ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ) := by
    exact_mod_cast ncard_ballZ0_pos hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hcard9 : ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ) ≤ 9 * (n : ℝ) ^ 2 :=
    (ncard_ballZ0_two_le n).trans (by nlinarith)
  have hs : ∀ t : ℝ, 0 ≤ t → t / ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ) < δ ^ 2 →
      t ^ (1 / ((2 : ℕ) : ℝ)) ≤ 3 * δ * n := by
    intro t ht htb
    rw [div_lt_iff₀ hcard] at htb
    have h3 : t ≤ (3 * δ * n) ^ 2 := by nlinarith
    have e : (1 / ((2 : ℕ) : ℝ)) = 1 / 2 := by norm_num
    rw [e, ← Real.sqrt_eq_rpow]
    calc Real.sqrt t ≤ Real.sqrt ((3 * δ * n) ^ 2) := Real.sqrt_le_sqrt h3
      _ = 3 * δ * n := Real.sqrt_sq (by positivity)
  have hs1 := hs _ ENNReal.toReal_nonneg hr1
  have hs2 := hs _ ENNReal.toReal_nonneg hr2
  have hkey := center_bound hABP hn1 η hM hl hf1 hf2
  have hCn : 0 ≤ C * n := by positivity
  have h3 := mul_le_mul_of_nonneg_left hs1 hCn
  have h4 := mul_le_mul_of_nonneg_left hs2 hCn
  have hδC : C * n * (3 * δ * n) = (l₂ - l₁) / 16 * (n : ℝ) ^ 2 := by
    rw [hδ]; field_simp; ring
  have hnD' : 8 < (l₂ - l₁) * n := by rwa [div_lt_iff₀ hD0, mul_comm] at hnD
  have h5 : 8 * n < (l₂ - l₁) * n * n := by nlinarith
  nlinarith

/-- `F̄_η ≤ F*_η`, proved. -/
theorem effOpLeStar : EffOpLeStarD2Stmt := effOpLeStar_of_noCommonZero noCommonZero

end SingleSourceD2

end RandomSandpile

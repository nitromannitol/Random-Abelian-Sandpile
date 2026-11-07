import RandomSandpile.Proofs.Sec9.SingleSourceD2Operator

/-!
# Theorem 9.2 for `d ≥ 3` with `H(0) = 0`: `F̄ ≤ F*` in every dimension

The proof of `SingleSourceD2.effOpLeStar` never used `d = 2`; this file
repeats it in dimension `d ≥ 2`. `noCommonZero`: there are no `l₁ < l₂` with `μ̄*(l₁, M) = 0` and
`μ̄(l₂, M) = 0`. On `B_n`, take `h` legal and stabilizing with boundary values
`⌈q_M + q_m⌉ + C₀`, `m = (l₁ + l₂)/2` (least action); the two ABP bounds (Lemma 5.2) give
`(l₂ - l₁) n²/(2d) ≤ 1 + C n (μ*(B_n)^{1/d} + μ(B_n)^{1/d})`, while the ergodic limits (Lemma 5.5)
make the right side `1 + o(n²)`. `effOpLeStar_gen`: `F̄(M) ≤ F*(M)` from it, since `F̄(M)` lies in
`muEqSet` and every `l > F*(M)` has `μ̄*(l, M) = 0`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter

namespace RandomSandpile

open EffectiveOperatorBasic MuLipschitz

namespace SingleSourceH0

variable {d : ℕ}

/-- `#B_n ≤ (3n)^d` (for `n ≥ 1`). -/
theorem ncard_ballZ0_le (n : ℕ) : ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) ≤ (2 * n + 1) ^ d := by
  classical
  set S : Finset (Site d) := Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) n
  have hsub : ballZ0 (d := d) (n : ℝ) ⊆ (S : Set (Site d)) := by
    intro x hx
    have hc := ABP.ballZ0_subset_cubeZ0 (d := d) (n : ℝ) hx
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hi := hc i
    simp only [Pi.zero_apply, sub_zero] at hi
    rw [abs_lt] at hi
    constructor
    · have : (-(n : ℝ)) < (x i : ℝ) := hi.1
      exact_mod_cast this.le
    · have : (x i : ℝ) < n := hi.2
      exact_mod_cast this.le
  have h1 : (ballZ0 (d := d) (n : ℝ)).ncard ≤ S.card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet S)
  have h2 : (S.card : ℝ) = (2 * n + 1) ^ d := by
    simp only [S, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    push_cast
    have : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
    rw [this]
    push_cast
    ring
  calc ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) ≤ S.card := by exact_mod_cast h1
    _ = _ := h2

/-- **No common-zero interval**, any dimension. -/
def NoCommonZeroStmt (d : ℕ) : Prop :=
  ∀ E : RandomEnvironment d, ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∀ l₁ l₂ : ℝ, l₁ < l₂ →
      muStarBar E l₁ M = 0 → muBar E l₂ M = 0 → False

theorem discretize_unitBall_eq' {n : ℕ} (hn : 1 ≤ n) :
    discretize (Metric.ball (0 : Rd d) 1) n = ballZ0 (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  ext x
  simp only [discretize, Set.mem_setOf_eq]
  rw [smul_ball hnp.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hnp, mul_one, Metric.mem_ball,
    dist_zero_right, mem_ballZ0]

theorem qlZ_gen (l : ℝ) (y : Site d) : qlZ l y = l / (2 * d) * ‖toE y‖ ^ 2 := by
  simp only [qlZ, ql]; ring

/-- Lower bound for the boundary values of `h - q_l - q_M` when `h = ⌈q_M + q_m⌉ + C₀` there. -/
theorem le_sInf_bdry_gen (hd : 0 < d) {B : Set (Site d)} (hne : (bdry B).Nonempty) {h : Site d → ℤ}
    {M : Matrix (Fin d) (Fin d) ℝ} {m l : ℝ} (hml : l ≤ m) {C₀ : ℤ} {n : ℝ}
    (hbd : ∀ y ∈ bdry B, (h y : ℝ) = ⌈qMZ M y + qlZ m y⌉ + C₀)
    (hfar : ∀ y ∈ bdry B, n ^ 2 ≤ ‖toE y‖ ^ 2) :
    (m - l) / (2 * d) * n ^ 2 + C₀ ≤ sInf ((fun y => (h y : ℝ) - (qlZ l y + qMZ M y)) '' bdry B) := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hc := Int.le_ceil (qMZ M y + qlZ m y)
  have hfy := mul_le_mul_of_nonneg_left (hfar y hy) (by
    have : (0 : ℝ) ≤ m - l := by linarith
    positivity : (0 : ℝ) ≤ (m - l) / (2 * d))
  have hqm := qlZ_gen m y
  have hql := qlZ_gen l y
  show _ ≤ (h y : ℝ) - (qlZ l y + qMZ M y)
  rw [hbd y hy]
  have e : (m - l) / (2 * d) * ‖toE y‖ ^ 2 = m / (2 * d) * ‖toE y‖ ^ 2 - l / (2 * d) * ‖toE y‖ ^ 2 := by
    ring
  linarith

/-- Upper bound for the boundary values of `h - q_l - q_M` when `h = ⌈q_M + q_m⌉ + C₀` there. -/
theorem sSup_bdry_le_gen (hd : 0 < d) {B : Set (Site d)} (hne : (bdry B).Nonempty) {h : Site d → ℤ}
    {M : Matrix (Fin d) (Fin d) ℝ} {m l : ℝ} (hml : m ≤ l) {C₀ : ℤ} {n : ℝ}
    (hbd : ∀ y ∈ bdry B, (h y : ℝ) = ⌈qMZ M y + qlZ m y⌉ + C₀)
    (hfar : ∀ y ∈ bdry B, n ^ 2 ≤ ‖toE y‖ ^ 2) :
    sSup ((fun y => (h y : ℝ) - (qlZ l y + qMZ M y)) '' bdry B) ≤
      (m - l) / (2 * d) * n ^ 2 + C₀ + 1 := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hc := Int.ceil_lt_add_one (qMZ M y + qlZ m y)
  have hfy := mul_le_mul_of_nonpos_left (hfar y hy) (by
    have : (m - l) ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg this (by positivity) : (m - l) / (2 * d) ≤ 0)
  have hqm := qlZ_gen m y
  have hql := qlZ_gen l y
  show (h y : ℝ) - (qlZ l y + qMZ M y) ≤ _
  rw [hbd y hy]
  have e : (m - l) / (2 * d) * ‖toE y‖ ^ 2 = m / (2 * d) * ‖toE y‖ ^ 2 - l / (2 * d) * ‖toE y‖ ^ 2 := by
    ring
  linarith

/-- The centre estimate: ABP on both sides for a legal stabilizer with ceiling boundary data. -/
theorem center_bound_gen (hd : 2 ≤ d) {C : ℝ}
    (hABP : ∀ (n : ℕ) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm →
      (mu (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
        ∀ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
          w x ≤ sSup (w '' bdry (ballZ0 (n : ℝ))) +
            C * n * (mu (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / (d : ℝ))) ∧
      (muStar (ballZ0 (n : ℝ)) η l M ≠ ⊤ →
        ∀ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M, ∀ x ∈ ballZ0 (n : ℝ),
          sInf (w '' bdry (ballZ0 (n : ℝ))) ≤
            w x + C * n * (muStar (ballZ0 (n : ℝ)) η l M).toReal ^ (1 / (d : ℝ))))
    {n : ℕ} (hn1 : 1 ≤ n) (η : Site d → ℤ) {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm)
    {l₁ l₂ : ℝ} (hl : l₁ < l₂) (hf1 : muStar (ballZ0 (n : ℝ)) η l₁ M ≠ ⊤)
    (hf2 : mu (ballZ0 (n : ℝ)) η l₂ M ≠ ⊤) :
    (l₂ - l₁) / (2 * d) * (n : ℝ) ^ 2 ≤
      1 + C * n * (muStar (ballZ0 (n : ℝ)) η l₁ M).toReal ^ (1 / (d : ℝ)) +
        C * n * (mu (ballZ0 (n : ℝ)) η l₂ M).toReal ^ (1 / (d : ℝ)) := by
  have hd0 : 0 < d := by omega
  set B := ballZ0 (d := d) (n : ℝ)
  have hfinB : B.Finite := ballZ0_finite _
  have hfinD : (dClosure B).Finite := dClosure_finite hfinB
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℤ, ∀ y ∈ dClosure B, -⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉ ≤ C₀ := by
    obtain ⟨C₀, hC₀⟩ := (hfinD.image fun y => -⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉).bddAbove
    exact ⟨C₀, fun y hy => hC₀ ⟨y, hy, rfl⟩⟩
  obtain ⟨u, hudef⟩ : ∃ u : Site d → ℤ,
      u = (dClosure B).indicator fun y => ⌈qMZ M y + qlZ ((l₁ + l₂) / 2) y⌉ + C₀ := ⟨_, rfl⟩
  have hu : IsTopplingFn B u := by
    rw [hudef]
    refine ⟨fun y => ?_, fun y hy => Set.indicator_of_notMem hy _⟩
    by_cases hy : y ∈ dClosure B
    · rw [Set.indicator_of_mem hy]; linarith [hC₀ y hy]
    · rw [Set.indicator_of_notMem hy]
  obtain ⟨h, ⟨hL, hS⟩, hbd⟩ :=
    NearMaxSequence.exists_locLegal_stabilizing hd0 hfinB η hu
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
  have hne : (bdry B).Nonempty := Burning.bdry_nonempty hd0 hfinB
    ⟨0, mem_ballZ0.2 (by rw [toE_zero, norm_zero]; exact_mod_cast hn1)⟩
  have h0B : (0 : Site d) ∈ B := mem_ballZ0.2 (by rw [toE_zero, norm_zero]; exact_mod_cast hn1)
  have hw₁ : (fun y => (h y : ℝ) - (qlZ l₁ y + qMZ M y)) ∈ perturbedSuper B η l₁ M :=
    Set.mem_image_of_mem _ hS
  have hw₂ : (fun y => (h y : ℝ) - (qlZ l₂ y + qMZ M y)) ∈ perturbedSub B η l₂ M :=
    mem_perturbedSub.2 ⟨h, hL, rfl⟩
  have hA1 := (hABP n η l₁ M hM).2 hf1 _ hw₁ 0 h0B
  have hA2 := (hABP n η l₂ M hM).1 hf2 _ hw₂ 0 h0B
  have hq0 : ∀ l : ℝ, qlZ l (0 : Site d) + qMZ M 0 = 0 := fun l => by
    simp [qlZ, ql, qMZ, qM, toE_zero]
  simp only [hq0, sub_zero] at hA1 hA2
  have hinf := le_sInf_bdry_gen hd0 hne (h := h) (l := l₁) (by linarith) hbd' hfar
  have hsup := sSup_bdry_le_gen hd0 hne (h := h) (l := l₂) (by linarith) hbd' hfar
  have e : ((l₁ + l₂) / 2 - l₁) / (2 * d) * (n : ℝ) ^ 2 -
      ((l₁ + l₂) / 2 - l₂) / (2 * d) * (n : ℝ) ^ 2 = (l₂ - l₁) / (2 * d) * (n : ℝ) ^ 2 := by
    ring
  linarith

/-- **No common-zero interval**, proved from the ergodic limits (Lemma 5.5), the ABP bounds
(Lemma 5.2) and a legal stabilizer with ceiling boundary data (least action). -/
theorem noCommonZero_gen (hd : 2 ≤ d) : NoCommonZeroStmt d := by
  intro E M hM l₁ l₂ hl h1 h2
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨C, hC, hABP⟩ := abp d hd
  have hconv := (muConvergence_unconditional d hd).1
  obtain ⟨η, hη1, hη2⟩ := ((hconv E M hM l₁).and (hconv E M hM l₂)).exists
  have hW := StrictConcavityBall.isLipschitzDomain_ball (0 : Rd d) one_pos
  obtain ⟨hfin1, -, hT1⟩ := hη1 _ hW
  obtain ⟨hfin2, hT2, -⟩ := hη2 _ hW
  rw [h1] at hT1
  rw [h2] at hT2
  have hD0 : 0 < l₂ - l₁ := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (l₂ - l₁) / (24 * d * C) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈4 * d / (l₂ - l₁)⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨n, hr1, hr2, hnN⟩ :=
    ((hT1.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ d))).and
      ((hT2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ d))).and
        (eventually_ge_atTop N))).exists
  have hn1 : 1 ≤ n := by rw [hN] at hnN; omega
  have hnD : 4 * d / (l₂ - l₁) < n := by
    have h1' : 4 * d / (l₂ - l₁) ≤ (⌈4 * d / (l₂ - l₁)⌉₊ : ℝ) := Nat.le_ceil _
    have h2' : ((⌈4 * d / (l₂ - l₁)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by rw [← hN]; exact_mod_cast hnN
    push_cast at h2'
    linarith
  simp only [discretize_unitBall_eq' hn1] at hr1 hr2
  have hf1 := (hfin1 n).2
  have hf2 := (hfin2 n).1
  rw [discretize_unitBall_eq' hn1] at hf1 hf2
  have hcard : (0 : ℝ) < ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
    exact_mod_cast ncard_ballZ0_pos hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hcard9 : ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) ≤ (3 * (n : ℝ)) ^ d :=
    (ncard_ballZ0_le n).trans (pow_le_pow_left₀ (by positivity) (by linarith) d)
  have hs : ∀ t : ℝ, 0 ≤ t → t / ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) < δ ^ d →
      t ^ (1 / (d : ℝ)) ≤ 3 * δ * n := by
    intro t ht htb
    rw [div_lt_iff₀ hcard] at htb
    have h3 : t ≤ (3 * δ * n) ^ d := by
      calc t ≤ δ ^ d * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := htb.le
        _ ≤ δ ^ d * (3 * (n : ℝ)) ^ d := by gcongr
        _ = (3 * δ * n) ^ d := by rw [← mul_pow]; ring_nf
    calc t ^ (1 / (d : ℝ)) ≤ ((3 * δ * n) ^ d) ^ (1 / (d : ℝ)) :=
          Real.rpow_le_rpow ht h3 (by positivity)
      _ = 3 * δ * n := by
          rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  have hs1 := hs _ ENNReal.toReal_nonneg hr1
  have hs2 := hs _ ENNReal.toReal_nonneg hr2
  have hkey := center_bound_gen hd hABP hn1 η hM hl hf1 hf2
  have hCn : 0 ≤ C * n := by positivity
  have h3 := mul_le_mul_of_nonneg_left hs1 hCn
  have h4 := mul_le_mul_of_nonneg_left hs2 hCn
  have hδC : C * n * (3 * δ * n) = (l₂ - l₁) / (8 * d) * (n : ℝ) ^ 2 := by
    rw [hδ]; field_simp; ring
  have hnD' : 4 * d < (l₂ - l₁) * n := by
    have := (div_lt_iff₀ hD0).1 hnD
    linarith
  have e1 : (l₂ - l₁) / (2 * d) * (n : ℝ) ^ 2 - 2 * ((l₂ - l₁) / (8 * d) * (n : ℝ) ^ 2) =
      (l₂ - l₁) / (4 * d) * (n : ℝ) ^ 2 := by field_simp; ring
  have h5 : 1 < (l₂ - l₁) / (4 * d) * (n : ℝ) ^ 2 := by
    have : (l₂ - l₁) / (4 * d) * (n : ℝ) ^ 2 = ((l₂ - l₁) * n) / (4 * d) * n := by
      field_simp
    rw [this]
    have hq : 1 < ((l₂ - l₁) * n) / (4 * d) := by rw [lt_div_iff₀ (by positivity)]; linarith
    nlinarith
  linarith

/-- **`F̄_η ≤ F*_η`** in every dimension `d ≥ 2`. -/
theorem effOpLeStar_gen (hd : 2 ≤ d) (E : RandomEnvironment d) {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.IsSymm) : effOp E M ≤ effOpStar E M := by
  have hG := isGreatest_effOp muConvergence_unconditional hd E hM
  by_contra hlt
  have hlt' : effOpStar E M < effOp E M := not_le.mp hlt
  have hz : ∀ {l : ℝ}, effOpStar E M < l → muStarBar E l M = 0 := fun {l} hl => by
    by_contra hne
    have hpos : 0 < muStarBar E l M :=
      lt_of_le_of_ne (EffectiveOperatorBasic.muStarBar_nonneg E l M) (Ne.symm hne)
    have := le_csSup (effOpStar_set_bddAbove (by omega) E M) hpos
    exact absurd (lt_of_lt_of_le hl this) (lt_irrefl _)
  have h1 : muStarBar E ((effOpStar E M + effOp E M) / 2) M = 0 := hz (by linarith)
  have h2' : muStarBar E (effOp E M) M = 0 := hz hlt'
  have h2 : muBar E (effOp E M) M = 0 := by
    have hmem : muBar E (effOp E M) M = muStarBar E (effOp E M) M := hG.1
    rw [hmem, h2']
  exact noCommonZero_gen hd E M hM _ _ (by linarith) h1 h2

end SingleSourceH0

end RandomSandpile

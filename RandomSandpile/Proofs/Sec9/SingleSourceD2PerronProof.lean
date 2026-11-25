import RandomSandpile.Proofs.Sec9.SingleSourceD2PerronEnvelope

/-!
# Theorem 9.2 in dimension two: Perron's method

`perron_exists_of_bounded`: Perron's method (Crandall-Ishii-Lions, *User's guide*, Theorem 4.1) on
an open set `Ω ⊆ ℝ²`, for a proper continuous `F` with comparison for (DP), between a subsolution
`u̲` and a supersolution `ū` of (DP), bounded on `Ω̄`, whose envelopes vanish on `∂Ω`.
The proof is that of CIL §4: the upper envelope `W^*` of the Perron function `W` is a subsolution
(`isSubsolution_uEnv`, CIL Lemma 4.2), hence lies below `ū` and belongs to the Perron family, so
`W = W^*`; the lower envelope `W_*` is a supersolution by the bump construction (CIL Lemma 4.4,
`isSupersolution_lEnv_perron`); comparison gives `W^* ≤ W_*`, so `W` is continuous on `Ω̄`.
-/

noncomputable section

open Filter Topology Metric Set
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

open CrandallIshiiLions

/-- A symmetric matrix inequality from the quadratic forms. -/
theorem posSemidef_sub_of_qM_le {M N : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.IsSymm) (hN : N.IsSymm)
    (h : ∀ ξ : Rd 2, qM N ξ ≤ qM M ξ) : (M - N).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hM.eq, hN.eq]
  · have hx := h (WithLp.toLp 2 x)
    simp only [qM] at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith

/-- The Perron family: subsolutions of (DP) between the barriers. -/
def perronSet (F : Rd 2 → ℝ → Rd 2 → Matrix (Fin 2) (Fin 2) ℝ → ℝ) (Ω : Set (Rd 2))
    (ul uu : Rd 2 → ℝ) : Set (Rd 2 → ℝ) :=
  {w | (∀ y ∈ closure Ω, ul y ≤ w y ∧ w y ≤ uu y) ∧ IsSubsolutionDP F Ω w}

/-- The Perron function. -/
def perronFun (F : Rd 2 → ℝ → Rd 2 → Matrix (Fin 2) (Fin 2) ℝ → ℝ) (Ω : Set (Rd 2))
    (ul uu : Rd 2 → ℝ) (x : Rd 2) : ℝ :=
  sSup ((fun w : Rd 2 → ℝ => w x) '' perronSet F Ω ul uu)

/-- Upper semicontinuity transfers along a local equality. -/
theorem upperSemicontinuousWithinAt_of_eventuallyEq {K : Set (Rd 2)} {f g : Rd 2 → ℝ}
    {x : Rd 2} (hfg : ∀ᶠ y in 𝓝 x, f y = g y) (hx : f x = g x)
    (hg : UpperSemicontinuousWithinAt g K x) : UpperSemicontinuousWithinAt f K x := by
  intro M hM
  rw [hx] at hM
  filter_upwards [hg M hM, mem_nhdsWithin_of_mem_nhds hfg] with y hy hyfg
  rw [hyfg]
  exact hy

/-- **The bump construction (CIL Lemma 4.4).** If the Perron function is a subsolution of (DP)
lying in the Perron family, its lower envelope is a supersolution. -/
theorem isSupersolution_lEnv_perron {F : Rd 2 → ℝ → Rd 2 → Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    {Ω : Set (Rd 2)} (hΩ : IsOpen Ω) (hprop : IsProper F)
    (hcont : Continuous (fun w : Rd 2 × ℝ × Rd 2 × Matrix (Fin 2) (Fin 2) ℝ =>
      F w.1 w.2.1 w.2.2.1 w.2.2.2))
    {ul uu : Rd 2 → ℝ} (huu : IsSupersolutionDP F Ω uu) {W : Rd 2 → ℝ} {C : ℝ}
    (hWC : ∀ y ∈ closure Ω, |W y| ≤ C)
    (hWsub : IsSubsolutionDP F Ω W) (hWb : ∀ y ∈ closure Ω, ul y ≤ W y ∧ W y ≤ uu y)
    (hmax : ∀ w ∈ perronSet F Ω ul uu, ∀ y ∈ closure Ω, w y ≤ W y) :
    IsSupersolution F Ω (lEnv (closure Ω) W) := by
  classical
  set K := closure Ω with hK
  set L := lEnv K W with hL
  refine ⟨(lowerSemicontinuousOn_lEnv hWC).mono subset_closure, fun z hz pX hpX => ?_⟩
  obtain ⟨p, X⟩ := pX
  have hX : X.IsSymm := hpX.1
  have hzK : z ∈ K := subset_closure hz
  show 0 ≤ F z (L z) p X
  by_contra hneg
  rw [not_le] at hneg
  set G : Rd 2 × ℝ × Rd 2 × Matrix (Fin 2) (Fin 2) ℝ → ℝ :=
    fun w => F w.1 w.2.1 w.2.2.1 w.2.2.2 with hG
  -- Step 1: `L z < uu z`
  have hLu : L z < uu z := by
    rcases lt_or_eq_of_le ((lEnv_le hWC hzK).trans (hWb z hzK).2) with h | h
    · exact h
    · exfalso
      have hj : (p, X) ∈ subJet2 Ω uu z :=
        mem_subJet2_of_le_on (fun y hy => (lEnv_le hWC (subset_closure hy)).trans
          (hWb y (subset_closure hy)).2) h hpX
      have h1 := huu.2.1.2 z hz _ hj
      rw [← h] at h1
      exact absurd h1 (not_le.2 hneg)
  -- Step 2: the bump family and the continuity of `F`
  set Ψ : Rd 2 × ℝ × ℝ → Rd 2 × ℝ × Rd 2 × Matrix (Fin 2) (Fin 2) ℝ := fun q =>
    (q.1, quadAt (L z + q.2.1) p z X (-q.2.2) q.1,
      p + matVec (X + (2 * -q.2.2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (q.1 - z),
      X + (2 * -q.2.2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) with hΨ
  have hΨc : Continuous Ψ := by
    have hmat : Continuous fun q : Rd 2 × ℝ × ℝ =>
        X + (2 * -q.2.2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by fun_prop
    have hvec : Continuous fun q : Rd 2 × ℝ × ℝ =>
        matVec (X + (2 * -q.2.2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (q.1 - z) :=
      (PiLp.continuous_toLp 2 _).comp (hmat.matrix_mulVec
        ((PiLp.continuous_ofLp 2 _).comp (continuous_fst.sub continuous_const)))
    rw [hΨ]
    refine continuous_fst.prodMk (Continuous.prodMk ?_ ((continuous_const.add hvec).prodMk hmat))
    unfold quadAt qM
    fun_prop
  have hΨ0 : Ψ (z, 0, 0) = (z, L z, p, X) := by
    simp [hΨ, quadAt, qM, matVec]
  have hev : ∀ᶠ q in 𝓝 ((z, 0, 0) : Rd 2 × ℝ × ℝ), G (Ψ q) < 0 := by
    have hca : ContinuousAt (fun q => G (Ψ q)) (z, 0, 0) := (hcont.comp hΨc).continuousAt
    have h0 : G (Ψ (z, 0, 0)) < 0 := by rw [hΨ0]; exact hneg
    exact hca.eventually (gt_mem_nhds h0)
  obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.1 hev
  have hneg' : ∀ x : Rd 2, ∀ γ δ : ℝ, dist x z < η → |γ| < η → |δ| < η → G (Ψ (x, γ, δ)) < 0 := by
    intro x γ δ hx hγ hδ
    refine hηball ?_
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt hx (max_lt hγ hδ)
  -- Step 3: choice of `δ`
  set M := (L z + uu z) / 2 with hM
  have hLM : L z < M := by rw [hM]; linarith
  have hMu : M < uu z := by rw [hM]; linarith
  set δ := min (η / 2) (M - L z) with hδ_def
  have hδ : 0 < δ := lt_min (half_pos hη) (by linarith)
  have hδη : δ < η := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
  have hδM : δ ≤ M - L z := min_le_right _ _
  -- the subjet inequality near `z`
  have hjet := hpX.2 (δ / 2) (half_pos hδ)
  rw [nhdsWithin_eq_nhds.2 (hΩ.mem_nhds hz)] at hjet
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.eventually_nhds_iff.1 (hjet.and (hΩ.mem_nhds hz))
  -- lower semicontinuity of `uu` at `z`
  obtain ⟨ρ₂, hρ₂, hball₂⟩ := Metric.mem_nhdsWithin_iff.1 (huu.1 z hzK M hMu)
  -- continuity of the base quadratic at `z`
  have hψ0c : Continuous (quadAt (L z) p z X (-δ)) := continuous_quadAt _ _ _ _ _
  have hψ0z : quadAt (L z) p z X (-δ) z = L z := quadAt_self _ _ _ _ _
  obtain ⟨ρ₃, hρ₃, hball₃⟩ := Metric.eventually_nhds_iff.1
    ((hψ0c.tendsto z).eventually (gt_mem_nhds (show quadAt (L z) p z X (-δ) z < L z + (M - L z) / 2
      by rw [hψ0z]; linarith)))
  -- Step 4: choice of `r` and `γ`
  set r := min 1 (min (η / 2) (min (ρ₁ / 2) (min ρ₂ ρ₃))) with hr_def
  have hr : 0 < r := lt_min one_pos (lt_min (half_pos hη) (lt_min (half_pos hρ₁) (lt_min hρ₂ hρ₃)))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrη : r < η := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hη)
  have hrρ₁ : r < ρ₁ := lt_of_le_of_lt ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _))) (half_lt_self hρ₁)
  have hrρ₂ : r ≤ ρ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hrρ₃ : r ≤ ρ₃ := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  set γ := δ * r ^ 2 / 16 with hγ_def
  have hγ : 0 < γ := by positivity
  have hγδ : γ ≤ δ / 16 := by
    rw [hγ_def]
    have : r ^ 2 ≤ 1 := by nlinarith
    have h16 : δ * r ^ 2 ≤ δ * 1 := mul_le_mul_of_nonneg_left this hδ.le
    linarith
  have hγη : γ < η := by linarith
  set ψ := quadAt (L z + γ) p z X (-δ) with hψ
  have hψ_eq : ∀ x, ψ x = quadAt (L z) p z X (-δ) x + γ := fun x => by
    simp only [hψ, quadAt]; ring
  -- facts on the ball
  have hballΩ : ∀ x ∈ ball z r, x ∈ Ω := fun x hx =>
    (hball₁ (lt_trans (mem_ball.1 hx) hrρ₁)).2
  have hψu : ∀ x ∈ K ∩ ball z r, ψ x < uu x := by
    rintro x ⟨hxK, hx⟩
    have h1 : quadAt (L z) p z X (-δ) x < L z + (M - L z) / 2 :=
      hball₃ (lt_of_lt_of_le (mem_ball.1 hx) hrρ₃)
    have h2 : M < uu x := hball₂ ⟨ball_subset_ball hrρ₂ hx, hxK⟩
    rw [hψ_eq]
    linarith
  have hψW : ∀ x : Rd 2, r / 2 < dist x z → dist x z < r → ψ x < W x := by
    intro x hx1 hx2
    have hxρ : dist x z < ρ₁ := lt_trans hx2 hrρ₁
    obtain ⟨hj, hxΩ⟩ := hball₁ hxρ
    have hLW : L x ≤ W x := lEnv_le hWC (subset_closure hxΩ)
    have hn : r ^ 2 / 4 < ‖x - z‖ ^ 2 := by
      rw [← dist_eq_norm]
      have : r / 2 < dist x z := hx1
      nlinarith [dist_nonneg (x := x) (y := z)]
    simp only [hψ, quadAt]
    have hj' : L z + inner ℝ p (x - z) + qM X (x - z) - δ / 2 * ‖x - z‖ ^ 2 ≤ L x := hj
    have hprod : δ * (r ^ 2 / 4) < δ * ‖x - z‖ ^ 2 := mul_lt_mul_of_pos_left hn hδ
    linarith
  -- Step 5: the bump
  set w : Rd 2 → ℝ := fun x => if x ∈ ball z r then max (W x) (ψ x) else W x with hw_def
  have hWw : ∀ x, W x ≤ w x := fun x => by
    simp only [hw_def]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hwfar : ∀ x : Rd 2, r / 2 < dist x z → w x = W x := by
    intro x hx
    simp only [hw_def]
    split_ifs with hxb
    · exact max_eq_left (hψW x hx (mem_ball.1 hxb)).le
    · rfl
  have hwnear : ∀ x ∈ ball z r, w x = max (W x) (ψ x) := fun x hx => by
    simp only [hw_def, hx, ↓reduceIte]
  have hψc : Continuous ψ := continuous_quadAt _ _ _ _ _
  -- the local forms of `w`
  have hfar_ev : ∀ x : Rd 2, r / 2 < dist x z → ∀ᶠ y in 𝓝 x, w y = W y := fun x hx => by
    filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hx]
      with y hy
    exact hwfar y hy
  have hnear_ev : ∀ x : Rd 2, ¬ r / 2 < dist x z →
      x ∈ ball z r ∧ ∀ᶠ y in 𝓝 x, w y = max (W y) (ψ y) := fun x hx => by
    have hxb : x ∈ ball z r := by
      rw [mem_ball]; linarith [not_lt.1 hx]
    refine ⟨hxb, ?_⟩
    filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
    exact hwnear y hy
  have husc : ∀ {S : Set (Rd 2)} {x : Rd 2}, UpperSemicontinuousWithinAt W S x →
      UpperSemicontinuousWithinAt w S x := by
    intro S x hWx
    by_cases hx : r / 2 < dist x z
    · exact upperSemicontinuousWithinAt_of_eventuallyEq (hfar_ev x hx)
        (hfar_ev x hx).self_of_nhds hWx
    · obtain ⟨-, h⟩ := hnear_ev x hx
      refine upperSemicontinuousWithinAt_of_eventuallyEq h h.self_of_nhds ?_
      intro M hM
      have h1 : W x < M := lt_of_le_of_lt (le_max_left _ _) hM
      have h2 : ψ x < M := lt_of_le_of_lt (le_max_right _ _) hM
      filter_upwards [hWx M h1, hψc.continuousWithinAt.upperSemicontinuousWithinAt M h2]
        with y hy1 hy2
      exact max_lt hy1 hy2
  have hwS : w ∈ perronSet F Ω ul uu := by
    refine ⟨fun y hy => ⟨(hWb y hy).1.trans (hWw y), ?_⟩, fun x hx => husc (hWsub.1 x hx),
      ⟨fun x hx => husc (hWsub.2.1.1 x hx), fun x hx pX hpX' => ?_⟩, ?_⟩
    · simp only [hw_def]
      split_ifs with hyb
      · exact max_le (hWb y hy).2 (hψu y ⟨hy, hyb⟩).le
      · exact (hWb y hy).2
    · obtain ⟨q, M'⟩ := pX
      show F x (w x) q M' ≤ 0
      by_cases hxf : r / 2 < dist x z
      · have h := hfar_ev x hxf
        have hj : (q, M') ∈ superJet2 Ω W x :=
          superJet2_congr (mem_nhdsWithin_of_mem_nhds (h.mono fun y hy => hy.symm))
            h.self_of_nhds.symm hpX'
        rw [h.self_of_nhds]
        exact hWsub.2.1.2 x hx _ hj
      · obtain ⟨hxb, h⟩ := hnear_ev x hxf
        have hjmax : (q, M') ∈ superJet2 Ω (fun y => max (W y) (ψ y)) x :=
          superJet2_congr (mem_nhdsWithin_of_mem_nhds (h.mono fun y hy => hy.symm))
            h.self_of_nhds.symm hpX'
        rw [h.self_of_nhds]
        rcases le_total (ψ x) (W x) with hle | hle
        · have hj : (q, M') ∈ superJet2 Ω W x :=
            mem_superJet2_of_le_on (fun y _ => le_max_left _ _) (max_eq_left hle).symm hjmax
          rw [max_eq_left hle]
          exact hWsub.2.1.2 x hx _ hj
        · have hj : (q, M') ∈ superJet2 Ω ψ x :=
            mem_superJet2_of_le_on (fun y _ => le_max_right _ _) (max_eq_right hle).symm hjmax
          rw [max_eq_right hle]
          have hshift : ∀ y, ψ y = ψ x + inner ℝ
              (p + matVec (X + (2 * -δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (x - z)) (y - x) +
              qM (X + (2 * -δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - x) := fun y =>
            quad_shift hX (L z + γ) (-δ) p z x y
          obtain ⟨hq, hqM⟩ := superJet2_quad hΩ hx hshift hj
          have hneg'' : F x (ψ x)
              (p + matVec (X + (2 * -δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (x - z))
              (X + (2 * -δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) < 0 :=
            hneg' x γ δ (lt_trans (mem_ball.1 hxb) hrη)
              (by rw [abs_of_pos hγ]; exact hγη) (by rw [abs_of_pos hδ]; exact hδη)
          rw [← hq] at hneg''
          have hN : (X + (2 * -δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm :=
            hX.add (Matrix.isSymm_one.smul _)
          have hpsd := posSemidef_sub_of_qM_le hpX'.1 hN hqM
          have hprop' := hprop x (ψ x) (ψ x) q M' (X + (2 * -δ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
            hpX'.1 hN le_rfl hpsd
          linarith
    · intro x hx
      have hxΩ : x ∉ Ω := by
        rw [hΩ.frontier_eq] at hx
        exact hx.2
      have hxb : x ∉ ball z r := fun h => hxΩ (hballΩ x h)
      simp only [hw_def, hxb, ↓reduceIte]
      exact hWsub.2.2 x hx
  -- Step 6: the contradiction
  have hwW := hmax w hwS
  obtain ⟨ρ₄, hρ₄, hball₄⟩ := Metric.eventually_nhds_iff.1
    ((hψ0c.tendsto z).eventually (lt_mem_nhds (show L z - γ / 2 < quadAt (L z) p z X (-δ) z
      by rw [hψ0z]; linarith)))
  obtain ⟨y, ⟨hyK, hyb⟩, hy⟩ := exists_lt_of_lEnv_lt hWC hzK (lt_min hr hρ₄) (by positivity :
    (0 : ℝ) < γ / 4)
  rw [mem_ball] at hyb
  have hyr : y ∈ ball z r := mem_ball.2 (lt_of_lt_of_le hyb (min_le_left _ _))
  have h1 : L z - γ / 2 < quadAt (L z) p z X (-δ) y :=
    hball₄ (lt_of_lt_of_le hyb (min_le_right _ _))
  have h2 : ψ y ≤ w y := by rw [hwnear y hyr]; exact le_max_right _ _
  have h3 := hwW y hyK
  rw [hψ_eq] at h2
  linarith

/-- **Perron's method** (CIL Theorem 4.1) on an open set of `ℝ²`, with barriers bounded on `Ω̄`. -/
theorem perron_exists_of_bounded {F : Rd 2 → ℝ → Rd 2 → Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    {Ω : Set (Rd 2)} (hΩ : IsOpen Ω) (hprop : IsProper F)
    (hcont : Continuous (fun w : Rd 2 × ℝ × Rd 2 × Matrix (Fin 2) (Fin 2) ℝ =>
      F w.1 w.2.1 w.2.2.1 w.2.2.2))
    (hcomp : ∀ w v : Rd 2 → ℝ, IsSubsolutionDP F Ω w → IsSupersolutionDP F Ω v →
      ∀ x ∈ closure Ω, w x ≤ v x)
    {ul uu : Rd 2 → ℝ} (hul : IsSubsolutionDP F Ω ul) (huu : IsSupersolutionDP F Ω uu)
    (henv : ∀ x ∈ frontier Ω, LowerEnvelopeZeroAt Ω ul x ∧ UpperEnvelopeZeroAt Ω uu x)
    (hle : ∀ y ∈ closure Ω, ul y ≤ uu y) {C : ℝ}
    (hC : ∀ y ∈ closure Ω, |ul y| ≤ C ∧ |uu y| ≤ C) :
    ∃ W : Rd 2 → ℝ, ContinuousOn W (closure Ω) ∧ IsSubsolution F Ω W ∧ IsSupersolution F Ω W ∧
      (∀ x ∈ frontier Ω, W x = 0) ∧ ∀ x ∈ closure Ω, ul x ≤ W x ∧ W x ≤ uu x := by
  set K := closure Ω with hK
  set S := perronSet F Ω ul uu with hS
  set W := perronFun F Ω ul uu with hW
  have hulS : ul ∈ S := ⟨fun y hy => ⟨le_rfl, hle y hy⟩, hul⟩
  have hbdd : ∀ y ∈ K, BddAbove ((fun w : Rd 2 → ℝ => w y) '' S) := fun y hy =>
    ⟨uu y, by rintro _ ⟨w, hw, rfl⟩; exact (hw.1 y hy).2⟩
  have hWb : ∀ y ∈ K, ul y ≤ W y ∧ W y ≤ uu y := fun y hy =>
    sSup_eval_bounds hulS fun w hw => (hw.1 y hy).2
  have hWC : ∀ y ∈ K, |W y| ≤ C := fun y hy => by
    obtain ⟨h1, h2⟩ := hWb y hy
    obtain ⟨h3, h4⟩ := hC y hy
    rw [abs_le] at h3 h4 ⊢
    constructor <;> linarith [h3.1, h4.2]
  have hSW : ∀ w ∈ S, ∀ y ∈ K, w y ≤ W y := fun w hw y hy => le_csSup (hbdd y hy) ⟨w, hw, rfl⟩
  have hWS : ∀ x ∈ K, ∀ θ : ℝ, 0 < θ → ∃ w ∈ S, W x - θ < w x := by
    intro x hx θ hθ
    obtain ⟨_, ⟨w, hw, rfl⟩, h⟩ := exists_lt_of_lt_csSup (s := (fun w : Rd 2 → ℝ => w x) '' S)
      ⟨ul x, ul, hulS, rfl⟩ (show W x - θ < W x by linarith)
    exact ⟨w, hw, h⟩
  -- the upper envelope is a subsolution of (DP), hence in the family, hence equal to `W`
  set U := uEnv K W with hU
  have hUsub : IsSubsolution F Ω U :=
    isSubsolution_uEnv hcont hΩ (fun w hw => hw.2.2.1) hSW hWS hWC
  have hUbd : ∀ x ∈ frontier Ω, U x ≤ 0 := by
    intro x hx
    have hxK : x ∈ K := frontier_subset_closure hx
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 ((henv x hx).2.1 ε hε)
    rw [zero_add]
    exact uEnv_le_of hWC hxK hρ fun y hy => (hWb y hy.1).2.trans (hball ⟨hy.2, hy.1⟩).le
  have hUDP : IsSubsolutionDP F Ω U := ⟨upperSemicontinuousOn_uEnv hWC, hUsub, hUbd⟩
  have hUuu : ∀ x ∈ K, U x ≤ uu x := hcomp U uu hUDP huu
  have hUS : U ∈ S := ⟨fun y hy => ⟨(hWb y hy).1.trans (le_uEnv hWC hy), hUuu y hy⟩, hUDP⟩
  have hWU : ∀ x ∈ K, W x = U x := fun x hx =>
    le_antisymm (le_uEnv hWC hx) (hSW U hUS x hx)
  have hWusc : UpperSemicontinuousOn W K := by
    intro x hx M hM
    rw [hWU x hx] at hM
    filter_upwards [upperSemicontinuousOn_uEnv hWC x hx M hM, self_mem_nhdsWithin] with y hy hyK
    rw [hWU y hyK]
    exact hy
  have hWsub : IsSubsolutionDP F Ω W := by
    refine ⟨hWusc, ⟨hWusc.mono subset_closure, fun x hx pX hpX => ?_⟩, fun x hx => ?_⟩
    · have hev : ∀ᶠ y in 𝓝[Ω] x, U y = W y := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hWU y (subset_closure hy)).symm
      have hj := superJet2_congr hev (hWU x (subset_closure hx)).symm hpX
      rw [hWU x (subset_closure hx)]
      exact hUsub.2 x hx pX hj
    · rw [hWU x (frontier_subset_closure hx)]
      exact hUbd x hx
  -- the lower envelope is a supersolution of (DP)
  set L := lEnv K W with hL
  have hLsup : IsSupersolution F Ω L :=
    isSupersolution_lEnv_perron hΩ hprop hcont huu hWC hWsub hWb hSW
  have hLbd : ∀ x ∈ frontier Ω, 0 ≤ L x := by
    intro x hx
    have hxK : x ∈ K := frontier_subset_closure hx
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 ((henv x hx).1.1 ε hε)
    have := le_lEnv_of hWC hxK hρ (M := -ε) fun y hy =>
      (le_of_lt (hball ⟨hy.2, hy.1⟩)).trans (hWb y hy.1).1
    linarith
  have hLDP : IsSupersolutionDP F Ω L := ⟨lowerSemicontinuousOn_lEnv hWC, hLsup, hLbd⟩
  -- comparison
  have hWLeq : ∀ x ∈ K, W x = L x := fun x hx => by
    refine le_antisymm ?_ (lEnv_le hWC hx)
    rw [hWU x hx]
    exact hcomp U L hUDP hLDP x hx
  have hWlsc : LowerSemicontinuousOn W K := by
    intro x hx M hM
    rw [hWLeq x hx] at hM
    filter_upwards [lowerSemicontinuousOn_lEnv hWC x hx M hM, self_mem_nhdsWithin] with y hy hyK
    rw [hWLeq y hyK]
    exact hy
  refine ⟨W, continuousOn_iff_lower_upperSemicontinuousOn.2 ⟨hWlsc, hWusc⟩, hWsub.2.1,
    ⟨hWlsc.mono subset_closure, fun x hx pX hpX => ?_⟩, fun x hx => ?_, hWb⟩
  · have hev : ∀ᶠ y in 𝓝[Ω] x, L y = W y := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hWLeq y (subset_closure hy)).symm
    have hj := subJet2_congr hev (hWLeq x (subset_closure hx)).symm hpX
    rw [hWLeq x (subset_closure hx)]
    exact hLsup.2 x hx pX hj
  · exact le_antisymm (hWsub.2.2 x hx)
      ((hLbd x hx).trans (hWLeq x (frontier_subset_closure hx)).symm.le)

end SingleSourceD2

end RandomSandpile

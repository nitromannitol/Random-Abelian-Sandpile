import RandomSandpile.Steps.Sec7.MainTheorem

/-!
# Theorem 1.1: the comparison of subsequential limits from its sub-steps

`limitComparison_of_steps` derives `LimitComparisonStmt` from Lemma 7.6(1)
(`PegdenSmartRegularityStmt`), the vanishing ranges of `μ`, `μ*` (`MuVanishStmt`), the exterior
steps of Pegden-Smart (`ExteriorSupersolutionStmt`, `ExteriorSubsolutionStmt`) and the interior
maximum and minimum principles (`InteriorMaxPrincipleStmt`, `InteriorMinPrincipleStmt`), following
the repaired proof (module docstring of `Steps/Sec7/MainTheorem.lean`).

The elementary ingredients: linearity of `q_M` in `M`, `q_{cI}(x) = c|x|²/2`, Taylor bounds from
the Peano expansion `HasSecondOrderTaylorAt`, and rational symmetric approximation of a symmetric
matrix (`symQ`), which makes the events of the interior steps countably many.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-! ### Quadratics -/

theorem qM_add_mat (A B : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) :
    qM (A + B) x = qM A x + qM B x := by
  simp only [qM, Matrix.add_mulVec, dotProduct_add]; ring

theorem qM_sub_mat (A B : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) :
    qM (A - B) x = qM A x - qM B x := by
  simp only [qM, Matrix.sub_mulVec, dotProduct_sub]; ring

theorem qM_neg_mat (A : Matrix (Fin d) (Fin d) ℝ) (x : Rd d) : qM (-A) x = -qM A x := by
  simp only [qM, Matrix.neg_mulVec, dotProduct_neg]; ring

theorem qM_smul_one (c : ℝ) (x : Rd d) :
    qM (c • (1 : Matrix (Fin d) (Fin d) ℝ)) x = c * ‖x‖ ^ 2 / 2 := by
  simp only [qM, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Real.norm_eq_abs, sq_abs, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem qM_zero_right (M : Matrix (Fin d) (Fin d) ℝ) : qM M (0 : Rd d) = 0 := by
  simp [qM]

theorem ql_zero_right (l : ℝ) : ql l (0 : Rd d) = 0 := by
  simp [ql]

theorem qM_nonneg_of_posSemidef {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) (x : Rd d) :
    0 ≤ qM A x := by
  have := hA.dotProduct_mulVec_nonneg (WithLp.ofLp x)
  simp only [star_trivial] at this
  unfold qM
  positivity

/-- `|q_N(x)| ≤ d² c |x|²` when all entries of `N` are bounded by `c`. -/
theorem abs_qM_le (N : Matrix (Fin d) (Fin d) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hN : ∀ i j, |N i j| ≤ c) (x : Rd d) : |qM N x| ≤ (d : ℝ) ^ 2 * c * ‖x‖ ^ 2 := by
  have hx : ∀ i, |WithLp.ofLp x i| ≤ ‖x‖ := fun i => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hterm : ∀ i j, |WithLp.ofLp x i * (N i j * WithLp.ofLp x j)| ≤ c * ‖x‖ ^ 2 :=
    fun i j => by
    rw [abs_mul, abs_mul]
    have h1 := hx i
    have h2 := hx j
    have h3 := hN i j
    calc |WithLp.ofLp x i| * (|N i j| * |WithLp.ofLp x j|) ≤ ‖x‖ * (c * ‖x‖) := by
          gcongr
      _ = c * ‖x‖ ^ 2 := by ring
  have hsum : |∑ i, WithLp.ofLp x i * ∑ j, N i j * WithLp.ofLp x j| ≤
      ∑ i : Fin d, ∑ j : Fin d, c * ‖x‖ ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold qM
  simp only [dotProduct, Matrix.mulVec]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h0 : 0 ≤ (d : ℝ) ^ 2 * c * ‖x‖ ^ 2 := by positivity
  nlinarith

/-! ### Rational symmetric matrices -/

/-- The symmetric real matrix `(A + Aᵀ)/2` of a rational array `A`. -/
def symQ (A : Fin d → Fin d → ℚ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ((A i j : ℝ) + (A j i : ℝ)) / 2

theorem symQ_isSymm (A : Fin d → Fin d → ℚ) : (symQ A).IsSymm := by
  ext i j
  simp [symQ, Matrix.transpose_apply, add_comm]

/-- Every symmetric matrix is approximated entrywise by some `symQ A`. -/
theorem exists_symQ_near (X : Matrix (Fin d) (Fin d) ℝ) (hX : X.IsSymm) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Fin d → Fin d → ℚ, ∀ i j, |(symQ A - X) i j| ≤ ε := by
  have hex : ∀ i j, ∃ q : ℚ, |(q : ℝ) - X i j| < ε := fun i j => by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show X i j - ε < X i j + ε by linarith)
    exact ⟨q, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩
  choose A hA using hex
  refine ⟨A, fun i j => ?_⟩
  have hXij : X j i = X i j := by
    have := congrFun (congrFun hX i) j
    simpa [Matrix.transpose_apply] using this
  have h1 := abs_lt.1 (hA i j)
  have h2 := abs_lt.1 (hA j i)
  rw [hXij] at h2
  simp only [symQ, Matrix.sub_apply, Matrix.of_apply]
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### Taylor bounds -/

theorem HasSecondOrderTaylorAt.bound {u : Rd d → ℝ} {a p : Rd d}
    {X : Matrix (Fin d) (Fin d) ℝ} (h : HasSecondOrderTaylorAt u a p X) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ρ > 0, ∀ y, ‖y - a‖ < ρ →
      |u y - u a - inner ℝ p (y - a) - qM X (y - a)| ≤ κ * ‖y - a‖ ^ 2 := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (h.def hκ)
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  have := hball (by rwa [dist_eq_norm])
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - a‖)] using this

theorem HasSecondOrderTaylorAt.touch_below {u : Rd d → ℝ} {a p : Rd d}
    {X : Matrix (Fin d) (Fin d) ℝ} (h : HasSecondOrderTaylorAt u a p X) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ y in 𝓝 a,
      u a + inner ℝ p (y - a) + qM (X - κ • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - a) ≤ u y := by
  filter_upwards [h.def (half_pos hκ)] with y hy
  rw [Real.norm_eq_abs, norm_pow, norm_norm, abs_le] at hy
  rw [qM_sub_mat, qM_smul_one]
  linarith [hy.1]

theorem HasSecondOrderTaylorAt.touch_above {u : Rd d → ℝ} {a p : Rd d}
    {X : Matrix (Fin d) (Fin d) ℝ} (h : HasSecondOrderTaylorAt u a p X) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ y in 𝓝 a,
      u y ≤ u a + inner ℝ p (y - a) + qM (X + κ • (1 : Matrix (Fin d) (Fin d) ℝ)) (y - a) := by
  filter_upwards [h.def (half_pos hκ)] with y hy
  rw [Real.norm_eq_abs, norm_pow, norm_norm, abs_le] at hy
  rw [qM_add_mat, qM_smul_one]
  linarith [hy.2]

/-! ### The reduction -/

/-- **Step** of Theorem 1.1 from its sub-steps (repaired). -/
theorem limitComparison_of_steps (h76 : PegdenSmartRegularityStmt) (hVan : MuVanishStmt)
    (hExtSup : ExteriorSupersolutionStmt) (hExtSub : ExteriorSubsolutionStmt)
    (hMax : InteriorMaxPrincipleStmt) (hMin : InteriorMinPrincipleStmt) :
    LimitComparisonStmt := by
  intro d hd E hHD W hW
  obtain ⟨Ω₁, hΩ₁, h76'⟩ := h76 d hd E hHD W hW
  have hΩ : ∀ᵐ η ∂E.P, η ∈ Ω₁ := ae_iff.2 hΩ₁
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  have hmaxae : ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), (q : ℝ) ≤ effOp E (symQ A) →
      ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) ≤
              v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro A
    by_cases hq : (q : ℝ) ≤ effOp E (symQ A)
    · filter_upwards [hMax d hd E W hW q (symQ A) (symQ_isSymm A)
        ((hVan d hd E hHD (symQ A) (symQ_isSymm A) q).1 hq)] with η hη
      exact fun _ => hη
    · exact Eventually.of_forall fun η h => absurd h hq
  have hminae : ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), effOp E (symQ A) ≤ (q : ℝ) →
      ∀ v : Rd d → ℝ, IsOdoSubseqLimit η W v →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ W →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            v y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) ≤
              v x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro A
    by_cases hq : effOp E (symQ A) ≤ (q : ℝ)
    · filter_upwards [hMin d hd E W hW q (symQ A) (symQ_isSymm A)
        ((hVan d hd E hHD (symQ A) (symQ_isSymm A) q).2 hq)] with η hη
      exact fun _ => hη
    · exact Eventually.of_forall fun η h => absurd h hq
  obtain ⟨Ω₀, hΩ₀ae, hΩ₀⟩ := (hΩ.and (hbdd.and (hmaxae.and hminae))).exists_mem
  refine ⟨Ω₀, mem_ae_iff.1 hΩ₀ae, ?_⟩
  intro η hη η' hη' v v' hv hv' x
  obtain ⟨hη1, hηb, hηmax, -⟩ := hΩ₀ η hη
  obtain ⟨hη1', hηb', -, hηmin'⟩ := hΩ₀ η' hη'
  by_contra hlt
  obtain ⟨nk, hnk, hconv⟩ := hv
  obtain ⟨nk', hnk', hconv'⟩ := hv'
  obtain ⟨a, p, p', X, X', haW, hva, hX, hX', hTv, hTv', ⟨δ, hδ, hPD⟩, -, -⟩ :=
    h76' η hη1 η' hη1' nk nk' hnk hnk' v v' hconv hconv' ⟨x, not_le.1 hlt⟩
  have hv : IsOdoSubseqLimit η W v := ⟨nk, hnk, hconv⟩
  have hv' : IsOdoSubseqLimit η' W v' := ⟨nk', hnk', hconv'⟩
  have hkey : ∀ h : Rd d, qM X h - qM X' h ≤ -(δ / 2) * ‖h‖ ^ 2 := fun h => by
    have := qM_nonneg_of_posSemidef hPD.posSemidef h
    rw [qM_sub_mat, qM_neg_mat, qM_smul_one, qM_sub_mat] at this
    linarith
  rcases haW with haW | haW
  · -- `a ∈ W`: the interior maximum and minimum principles
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW.2.1 a haW
    obtain ⟨A, hA⟩ := exists_symQ_near X' hX' (ε := δ / (16 * (d : ℝ) ^ 2)) (by positivity)
    have hMX' : ∀ h : Rd d, |qM (symQ A) h - qM X' h| ≤ δ / 16 * ‖h‖ ^ 2 := fun h => by
      rw [← qM_sub_mat]
      refine (abs_qM_le _ (by positivity) hA h).trans (le_of_eq ?_)
      field_simp
    obtain ⟨ρ₁, hρ₁, hT1⟩ := hTv.bound (κ := δ / 32) (by positivity)
    obtain ⟨ρ₂, hρ₂, hT2⟩ := hTv'.bound (κ := δ / 32) (by positivity)
    set r := min ρ (min ρ₁ ρ₂) / 2 with hr_def
    have hm : 0 < min ρ (min ρ₁ ρ₂) := lt_min hρ (lt_min hρ₁ hρ₂)
    have hr : 0 < r := half_pos hm
    have hrm : r < min ρ (min ρ₁ ρ₂) := half_lt_self hm
    have hrρ : r < ρ := hrm.trans_le (min_le_left _ _)
    have hr1 : r < ρ₁ := hrm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hr2 : r < ρ₂ := hrm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hrW : Metric.closedBall a r ⊆ W :=
      (Metric.closedBall_subset_ball hrρ).trans hρW
    have haC : a ∈ Metric.closedBall a r := Metric.mem_closedBall_self hr.le
    by_cases hl : -((d : ℝ) * δ / 2) < effOp E (symQ A)
    · -- the side of `η`: `v - φ - q_l` would have a strict local maximum at `a`
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hl
      obtain ⟨y, hy, hle⟩ := hηmax q A hq2.le v hv a p r hr hrW a haC
      simp only [sub_self, inner_zero_right, qM_zero_right, ql_zero_right, add_zero] at hle
      have hya : ‖y - a‖ = r := by rw [← dist_eq_norm]; exact Metric.mem_sphere.1 hy
      have h1 := abs_le.1 (hT1 y (by rw [hya]; exact hr1))
      have h2 := abs_le.1 (hMX' (y - a))
      have h3 := hkey (y - a)
      have hH : 0 < ‖y - a‖ ^ 2 := by rw [hya]; positivity
      have hq : -(δ / 4) * ‖y - a‖ ^ 2 < (q : ℝ) * ‖y - a‖ ^ 2 / (2 * d) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith [mul_lt_mul_of_pos_right hq1 hH]
      unfold ql at hle
      linarith [h1.2, h2.1]
    · -- the side of `η'`: `v' - φ - q_l` would have a strict local minimum at `a`
      have hl' : effOp E (symQ A) < -((d : ℝ) * δ / 4) := by
        have : -((d : ℝ) * δ / 2) < -((d : ℝ) * δ / 4) := by nlinarith
        linarith [not_lt.1 hl]
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hl'
      obtain ⟨y, hy, hle⟩ := hηmin' q A hq1.le v' hv' a p' r hr hrW a haC
      simp only [sub_self, inner_zero_right, qM_zero_right, ql_zero_right, add_zero] at hle
      have hya : ‖y - a‖ = r := by rw [← dist_eq_norm]; exact Metric.mem_sphere.1 hy
      have h1 := abs_le.1 (hT2 y (by rw [hya]; exact hr2))
      have h2 := abs_le.1 (hMX' (y - a))
      have hH : 0 < ‖y - a‖ ^ 2 := by rw [hya]; positivity
      have hq : (q : ℝ) * ‖y - a‖ ^ 2 / (2 * d) < -(δ / 8) * ‖y - a‖ ^ 2 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [mul_lt_mul_of_pos_right hq2 hH]
      unfold ql at hle
      linarith [h1.1, h2.2]
  · -- `a ∉ W̄`: Pegden-Smart's exterior argument
    have hκ : 0 < δ / 4 := by positivity
    obtain ⟨u, hu⟩ := hExtSup d hd W hW E.ηmin E.ηmax η' hηb' v' hv' a p'
      (X' - (δ / 4) • (1 : Matrix (Fin d) (Fin d) ℝ)) haW
      (hX'.sub (Matrix.isSymm_one.smul _)) (hTv'.touch_below hκ) (δ / 4) hκ
    refine hExtSub d hd W hW E.ηmin E.ηmax η hηb v hv a p
      (X + (δ / 4) • (1 : Matrix (Fin d) (Fin d) ℝ)) haW (hX.add (Matrix.isSymm_one.smul _))
      ((hv'.nonneg a).trans_lt hva) (hTv.touch_above hκ) (δ / 4) hκ
      ⟨u, fun z => ⟨(hu z).1, le_trans ?_ (hu z).2⟩⟩
    unfold qMZ
    simp only [qM_add_mat, qM_sub_mat, qM_smul_one]
    linarith [hkey (toE z)]

end RandomSandpile

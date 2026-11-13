import RandomSandpile.Proofs.Sec9.SingleSourceLimitMinimal
import RandomSandpile.Proofs.Sec9.SingleSourceMinPrinciple
import RandomSandpile.Proofs.Sec9.OpenBoundaryVisc
import RandomSandpile.Proofs.FinalSingleSource

/-!
# Theorem 9.2: the single-source limits are subsolutions

`ssLimitSubsolution_of_compactness : SSCompactnessStmt → SSLimitSubsolutionStmt`, hence
`ssLimitMinimal_of_compactness : SSCompactnessStmt → SSOuterBoundStmt → AlexandrovStmt →
SSLimitMinimalStmt` (with `ssLimitMinimal_of_outerBound`, `Proofs/Sec9/SingleSourceLimitMinimal.lean`).

* The single-source odometer `v_n` (least stabilizing toppling of `η + n δ_0` on `ℤ^d`,
  `η ≤ 2d - 2`) lies below each one-dimensional profile `y ↦ T(n + 1 - |y_i|)` of `ssNonempty`, so it
  vanishes off the cube `{|y_i| < n + 1}` (`singleSourceOdometer_eq_zero_of_coord`); by Theorem 1.1's
  `isLegal_of_isLeast_univ` (Proposition 3.1) it is legal there, and its restriction to a finite set
  avoiding the origin is locally legal for `η` (`singleSourceOdometer_restrict_locLegal`).
* **Maximum principle off the origin from `μ(l, M) = 0`** (`SSInteriorMaxPrincipleStmt`,
  `ssInteriorMaxPrinciple_of_compactness`): the argument of `ssInteriorMinPrinciple_of_compactness`
  with the locally legal restriction, Lemma 5.2's `μ`-bound (`volume_le_mu`) and Lemma 5.5.
* **Step** (`ssLimitSubsolution_of_maxPrinciple`): flatness (`muVanishFlat`) gives `μ(q, A) = 0`
  for `q ≤ F̄_η(A)`; the deterministic core `viscFromAboveLE_effOp_of_maxPrinciple` (Theorem 9.1,
  step) gives `F̄_η(D²u) ≤ 0` off the origin, tested from above, which contains.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

variable {d : ℕ}

namespace SingleSourceSub

/-- The one-dimensional profile `y ↦ T(n + 1 - |y_i|)` in the coordinate `i` stabilizes
`η + n δ_0` on `ℤ^d` when `η ≤ 2d - 2` (the proof of `ssNonempty`, any coordinate). -/
theorem ssG_coord_mem_stabilizing {η : Site d → ℤ} (hη : ∀ x, η x ≤ 2 * (d : ℤ) - 2) (n : ℕ)
    (i : Fin d) :
    (fun y : Site d => ssG ((n : ℤ) + 1) (y i)) ∈
      stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ := by
  set N : ℤ := (n : ℤ) + 1 with hN
  have hN1 : 1 ≤ N := by omega
  refine mem_stabilizing_univ.2 ⟨fun y => ssTri_nonneg _, fun x => ?_⟩
  rw [lap_comp_coord (fun t => ssG N t) i x]
  have hηx := hη x
  by_cases hx0 : x = 0
  · subst hx0
    simp only [Pi.zero_apply, dirac_self, mul_one]
    rw [ssG_secondDiff_zero hN1]
    omega
  · have hdx : dirac 0 x = 0 := by simp [dirac, hx0]
    rw [hdx, mul_zero, add_zero]
    have hlap : ssG N (x i + 1) + ssG N (x i - 1) - 2 * ssG N (x i) ≤ 1 := by
      by_cases hxi : x i = 0
      · rw [hxi, ssG_secondDiff_zero hN1]; omega
      · exact ssG_secondDiff_le N hxi
    omega

/-- The single-source odometer vanishes where some coordinate has `|y_i| ≥ n + 1`. -/
theorem singleSourceOdometer_eq_zero_of_coord {η : Site d → ℤ}
    (hη : ∀ x, η x ≤ 2 * (d : ℤ) - 2) (n : ℕ) {x : Site d} {i : Fin d}
    (hx : (n : ℤ) + 1 ≤ |x i|) : singleSourceOdometer η n x = 0 := by
  have hle := singleSourceOdometer_le (ssG_coord_mem_stabilizing hη n i) x
  have h0 : ssG ((n : ℤ) + 1) (x i) = 0 := ssProfile_of_nonpos (by linarith)
  have := singleSourceOdometer_nonneg η n x
  simp only at hle
  omega

/-- The restriction of the single-source odometer to a finite set avoiding the origin is locally
legal for the background `η` there. -/
theorem singleSourceOdometer_restrict_locLegal (hd : 1 ≤ d) {η : Site d → ℤ}
    (hη : ∀ x, η x ≤ 2 * (d : ℤ) - 2) (n : ℕ) {B : Set (Site d)} (hB : B.Finite)
    (h0 : ∀ z ∈ B, z ≠ 0) :
    (dClosure B).indicator (singleSourceOdometer η n) ∈ locLegal η B := by
  have hS : {x : Site d | ∀ i, |x i| < (n : ℤ) + 1}.Finite := by
    refine (Set.finite_Icc (fun _ : Fin d => -((n : ℤ) + 1)) (fun _ => (n : ℤ) + 1)).subset
      fun x hx => ?_
    exact ⟨fun i => (abs_lt.1 (hx i)).1.le, fun i => (abs_lt.1 (hx i)).2.le⟩
  have hv := isLeast_singleSourceOdometer (ssNonempty d hd η hη n)
  have hL := FreeMaxPrinciple.isLegal_of_isLeast_univ (by omega) (hS.union hB) hv
    (fun x hx => by
      have hx' : x ∉ {x : Site d | ∀ i, |x i| < (n : ℤ) + 1} := fun h => hx (Or.inl h)
      simp only [Set.mem_ofPred_eq, not_forall, not_lt] at hx'
      obtain ⟨i, hi⟩ := hx'
      exact singleSourceOdometer_eq_zero_of_coord hη n hi)
  have hR := locLegalRestrict d _ _ B _ Set.subset_union_right (mem_locLegal_of_isLegal hL)
  exact FreeMaxPrinciple.locLegal_congr (fun x hx => by simp [dirac, h0 x hx]) hR

end SingleSourceSub

/-! ### The maximum principle off the origin -/

/-- **Maximum principle off the origin from `μ(l, M) = 0`** for the single-source limits (the
`μ`-side of `SSInteriorMinPrincipleStmt`; Theorem 1.1's `InteriorMaxPrincipleStmt`). -/
def SSInteriorMaxPrincipleStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, E.ηmax = 2 * (d : ℤ) - 2 →
    ∀ (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), M.IsSymm → muBar E l M = 0 →
      ∀ᵐ η ∂E.P, ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ {x : Rd d | x ≠ 0} →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            u x - (inner ℝ p (x - a) + qM M (x - a) + ql l (x - a)) ≤
              u y - (inner ℝ p (y - a) + qM M (y - a) + ql l (y - a))

open SingleSourceMin OpenMaxPrinciple in
/-- `SSInteriorMaxPrincipleStmt` from Lemma 5.5 and step (the argument of
`ssInteriorMinPrinciple_of_compactness` with `μ` and the locally legal restriction). -/
theorem ssInteriorMaxPrinciple_of_compactness (hconv : MuConvergenceStmt)
    (hComp : SSCompactnessStmt) : SSInteriorMaxPrincipleStmt := by
  intro d hd E hE l M hM hμ
  have hd1 : 1 ≤ d := by omega
  filter_upwards [(hconv d hd).1 E M hM l, ae_all_iff.2 E.bounded] with η hη hbd
  rintro u ⟨nk, hnk, hconvu⟩ a p r hr hball x hx
  have hbd' : ∀ z, E.ηmin ≤ η z ∧ η z ≤ 2 * (d : ℤ) - 2 := fun z =>
    ⟨(hbd z).1, (hbd z).2.trans hE.le⟩
  obtain ⟨φ, hφ, v, hvc, hconvφ⟩ := hComp d hd E.ηmin η hbd' nk hnk
  have hopen : IsOpen {x : Rd d | x ≠ 0} := isOpen_ne
  have huv : Set.EqOn u (fun y => v y + fundamentalSolution d y) {x : Rd d | x ≠ 0} :=
    fun y hy =>
      tendsto_nhds_unique ((hconvu.tendsto_at hy).comp hφ.tendsto_atTop) (hconvφ.tendsto_at hy)
  have hucont : ContinuousOn u {x : Rd d | x ≠ 0} :=
    (hvc.continuousOn.add (continuousOn_fundamentalSolution d)).congr huv
  by_cases hxs : x ∈ sphere a r
  · exact ⟨x, hxs, le_rfl⟩
  have hxb : x ∈ ball a r := by
    rw [mem_closedBall] at hx; rw [mem_sphere] at hxs; rw [mem_ball]; exact lt_of_le_of_ne hx hxs
  -- radii `r < r₁ < r₂ < ‖a‖`
  have hra : r < ‖a‖ := by
    by_contra hcon
    have h0 : (0 : Rd d) ∈ closedBall a r := by
      rw [mem_closedBall, dist_comm, dist_zero_right]; linarith
    exact hball h0 rfl
  set r₂ := (r + ‖a‖) / 2 with hr₂
  set r₁ := (r + r₂) / 2 with hr₁
  have hball₂ : closedBall a r₂ ⊆ {x : Rd d | x ≠ 0} := by
    intro y hy hy0
    rw [hy0, mem_closedBall, dist_comm, dist_zero_right] at hy
    linarith
  have hFunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).1 hconvu _ hball₂
    (isCompact_closedBall a r₂)
  -- the integer scales `m_k = ⌊n_k^{1/d}⌋`
  have hdpos : (0 : ℝ) < 1 / (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    positivity
  set hk : ℕ → ℝ := fun k => (nk k : ℝ) ^ (1 / (d : ℝ)) with hhk_def
  set mk : ℕ → ℕ := fun k => ⌊hk k⌋₊ with hmk_def
  have hhk : Tendsto hk atTop atTop :=
    (tendsto_rpow_atTop hdpos).comp (tendsto_natCast_atTop_atTop.comp hnk.tendsto_atTop)
  have hmk : Tendsto mk atTop atTop := tendsto_nat_floor_atTop.comp hhk
  have ht : Tendsto (fun k => (mk k : ℝ) / hk k) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hhk
  have hc : Tendsto (fun k => (hk k / mk k) ^ 2) atTop (𝓝 1) := by
    have h := (ht.inv₀ one_ne_zero).pow 2
    simp only [inv_one, one_pow] at h
    exact h.congr fun k => by rw [inv_div]
  have hG : TendstoUniformlyOn (fun k => rescaleOdo (singleSourceOdometer η (nk k)) (mk k)) u
      atTop (closedBall a r₁) := by
    have h := tendstoUniformlyOn_rescale (by linarith : r₁ < r₂) (hucont.mono hball₂) hFunif hc ht
    refine h.congr ?_
    filter_upwards [hmk.eventually (eventually_ge_atTop 1),
      hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk1 hn1 y _
    exact (rescaleOdo_eq _ (by omega) (by omega) y).symm
  -- Lemma 5.5 on the ball: `μ / m^d → 0`
  obtain ⟨hfinμ, hlimμ, -⟩ := hη (ball a r) (StrictConcavityBall.isLipschitzDomain_ball a hr)
  rw [hμ] at hlimμ
  have hV : Tendsto (fun k => (mu (discretize (ball a r) (mk k)) η l M).toReal /
      (mk k : ℝ) ^ d) atTop (𝓝 0) :=
    (div_pow_tendsto_zero hd1 hr (fun A => mu A η l M) (mu_empty η l M) hlimμ
      strictMono_id).comp hmk
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (1 : ℝ) *
      ((singleSourceOdometer η (nk k) z : ℝ) - (mk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a))
          ((mk k : ℝ)⁻¹ • toE z))) (discretize (ball a r) (mk k))) ≤
        mu (discretize (ball a r) (mk k)) η l M ∧
      mu (discretize (ball a r) (mk k)) η l M ≠ ⊤ := by
    filter_upwards [hmk.eventually (eventually_ge_atTop 1)] with k hk1
    have hn0 : (mk k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨c, c0, hcq⟩ := rescaled_quad_affine hM p a l hn0
    have h0B : ∀ z ∈ discretize (ball a r) (mk k), z ≠ 0 := by
      intro z hz hz0
      rw [mem_discretize_iff' (by omega)] at hz
      rw [hz0, ABP.toE_zero, smul_zero] at hz
      exact hball (ball_subset_closedBall hz) rfl
    have hL := SingleSourceSub.singleSourceOdometer_restrict_locLegal hd1
      (fun z => (hbd' z).2) (nk k) (SubadditiveLipschitz.discretize_finite isBounded_ball (mk k))
      h0B
    refine ⟨volume_le_mu subset_rfl hL l M (-c) (-c0) (fun z hz => ?_), (hfinμ (mk k)).1⟩
    rw [Set.indicator_of_mem hz]
    have h1 := hcq (toE z)
    simp only [qlZ, qMZ, inner_neg_left]
    rw [h1]
    ring
  obtain ⟨y, hy, h⟩ := principle_generic_on hd1 (σ := 1) (continuous_quadratic p a M l) hr
    (by linarith : r < r₁)
    (hucont.mono ((closedBall_subset_closedBall (by linarith : r₁ ≤ r₂)).trans hball₂))
    hmk hG hvol hV hxb
  exact ⟨y, hy, by simpa using h⟩

/-! ### Step -/

/-- The maximum principle off the origin at all rational parameters with `q ≤ F̄_η(A)`, almost
surely (flatness: `μ(q, A) = 0` there, `muVanishFlat`). -/
theorem ae_ssInteriorMaxPrinciple_rat (hMax : SSInteriorMaxPrincipleStmt) (hd : 2 ≤ d)
    (E : RandomEnvironment d) (hE : E.ηmax = 2 * (d : ℤ) - 2) (hflat : FlatEff E) :
    ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), (q : ℝ) ≤ effOp E (symQ A) →
      ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ {x : Rd d | x ≠ 0} →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            u x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) ≤
              u y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) := by
  rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro A
  by_cases hq : (q : ℝ) ≤ effOp E (symQ A)
  · filter_upwards [hMax d hd E hE q (symQ A) (symQ_isSymm A)
      ((muVanishFlat d hd E hflat (symQ A) (symQ_isSymm A) q).1 hq)] with η hη
    exact fun _ => hη
  · exact Eventually.of_forall fun η h => absurd h hq

/-- **Step** from the maximum principle off the origin: the limits are viscosity subsolutions
of `F̄_η(D²u) ≤ 0` on `ℝ^d ∖ {0}` (in particular where they are positive). -/
theorem ssLimitSubsolution_of_maxPrinciple (hMax : SSInteriorMaxPrincipleStmt) :
    SSLimitSubsolutionStmt := by
  intro d hd E hE hflat
  have h64 := effectiveOperatorBasic_of_muConvergence muConvergence_unconditional
  filter_upwards [ae_ssInteriorMaxPrinciple_rat hMax hd E hE hflat] with η hη
  intro u hu
  have hW : ViscFromAboveLE (effOp E) {x : Rd d | x ≠ 0} u :=
    viscFromAboveLE_effOp_of_maxPrinciple h64 hd E isOpen_ne fun q A hq => hη q A hq u hu
  exact fun x hx => hW x hx.1

/-- **Step** from step (`SSCompactnessStmt`) and Lemma 5.5. -/
theorem ssLimitSubsolution_of_compactness (hComp : SSCompactnessStmt) : SSLimitSubsolutionStmt :=
  ssLimitSubsolution_of_maxPrinciple
    (ssInteriorMaxPrinciple_of_compactness muConvergence_unconditional hComp)

/-- **Step** (`SSLimitMinimalStmt`) from step, the outer bound `SSOuterBoundStmt`
and Alexandrov's theorem. -/
theorem ssLimitMinimal_of_compactness (hComp : SSCompactnessStmt) (hOB : SSOuterBoundStmt)
    (hA : AlexandrovStmt) : SSLimitMinimalStmt :=
  ssLimitMinimal_of_outerBound (ssLimitSubsolution_of_compactness hComp) hOB hA

end RandomSandpile

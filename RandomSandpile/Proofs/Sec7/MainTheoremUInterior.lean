import RandomSandpile.Proofs.Sec9.OpenBoundaryMaxPrinciple
import RandomSandpile.Proofs.Sec7.Compactness
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityFinite
import RandomSandpile.Steps.Sec7.MainTheorem

/-! # Theorem 1.1, steps and: interior maximum and minimum principles

`interiorMaxPrinciple_of_muConvergence : MuConvergenceStmt → InteriorMaxPrincipleStmt` and
`interiorMinPrinciple_of_muConvergence : MuConvergenceStmt → InteriorMinPrincipleStmt`
(`paper/random_piles-corrected.tex`, with the repairs of
`RandomSandpile/Steps/Sec7/MainTheorem.lean`). The route is that of Theorem 9.1's steps,
(`openInteriorMaxPrinciple_of_muConvergence`, `Proofs/Sec9/OpenBoundaryMaxPrinciple.lean`):
`principle_generic` (rescaled Lemma 5.2 on `nB_r(a) ∩ ℤ^d`) with Lemma 5.5 on the ball `B_r(a)`.
What changes is the toppling.

* The free odometer `v_n` of `η 𝟙_{W_n}` is the least stabilizing toppling on `ℤ^d`
  (`isLeast_freeOdometer`, finite by `freeOdometer_stabilizing_nonempty`) and vanishes off a box
  (Lemma 7.2's box, `freeOdometerUpperBound_of_oneDim`). Such a toppling is legal in every finite
  `A` off which it vanishes (`isLegal_of_isLeast_univ`: the legal stabilizing toppling `u` of
  Proposition 3.1 in `A` satisfies `u ≤ v_n`, and it is stabilizing on all of `ℤ^d` because
  `Δ_{ℤ^d} u ≤ Δ_{ℤ^d} v_n` off `A`). Its restriction to `B ⊆ W_n` is locally legal, resp.
  stabilizing, there (Lemma 5.5's restriction steps); since `η 𝟙_{W_n} = η` on `B`, for `η` itself
  (`locLegal_congr`, `stabilizing_congr`).
* The continuity of the limits comes from Lemma 7.2 (`compactness`): a further subsequence
  converges uniformly to a continuous function.
-/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped Topology ENNReal Matrix

namespace RandomSandpile

namespace FreeMaxPrinciple

variable {d : ℕ}

/-- Legality depends on the pile only in `A`. -/
theorem isLegal_congr {η η' : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (h : ∀ x ∈ A, η x = η' x) (hu : IsLegal η A u) : IsLegal η' A u := by
  obtain ⟨n, xs, hA, hleg, rfl⟩ := hu
  exact ⟨n, xs, hA, fun i => by rw [← h _ (hA i)]; exact hleg i, rfl⟩

/-- Local legality depends on the pile only in `A`. -/
theorem locLegal_congr {η η' : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (h : ∀ x ∈ A, η x = η' x) (hu : u ∈ locLegal η A) : u ∈ locLegal η' A := by
  obtain ⟨w, uh, hw, huh, rfl, hw0, huh0, hleg⟩ := hu
  exact ⟨w, uh, hw, huh, rfl, hw0, huh0, isLegal_congr (fun x hx => by rw [h x hx]) hleg⟩

/-- Stabilization depends on the pile only in `A`. -/
theorem stabilizing_congr {η η' : Site d → ℤ} {A : Set (Site d)} {v : Site d → ℤ}
    (h : ∀ x ∈ A, η x = η' x) (hv : v ∈ stabilizing η A) : v ∈ stabilizing η' A :=
  ⟨hv.1, fun x hx => by rw [← h x hx]; exact hv.2 x hx⟩

/-- The least stabilizing toppling on `ℤ^d`, if it vanishes off a finite set `A`, is legal in
`A` (Proposition 3.1 in `A`). -/
theorem isLegal_of_isLeast_univ (hd : 0 < d) {σ v : Site d → ℤ} {A : Set (Site d)}
    (hA : A.Finite) (hv : IsLeast (stabilizing σ Set.univ) v) (hvA : ∀ x ∉ A, v x = 0) :
    IsLegal σ A v := by
  obtain ⟨u, huL, huS⟩ := existsLegalStabilizing d hd A hA σ
  obtain ⟨hv0, hvlap⟩ := mem_stabilizing_univ.1 hv.1
  have hvS : v ∈ stabilizing σ A :=
    ⟨⟨hv0, fun x hx => hvA x fun h => hx (subset_dClosure A h)⟩, fun x _ => hvlap x⟩
  have huv : u ≤ v := legalLeStabilizing d A σ u v huL hvS
  have huU : u ∈ stabilizing σ Set.univ := by
    refine mem_stabilizing_univ.2 ⟨huS.1.1, fun x => ?_⟩
    by_cases hx : x ∈ A
    · exact huS.2 x hx
    · have hle : lap u x ≤ lap v x := by
        rw [lap_eq, lap_eq, huL.eq_zero_of_notMem hx, hvA x hx]
        have := nbrSumZ_mono huv x
        linarith
      linarith [hvlap x]
  rw [le_antisymm (hv.2 huU) huv]
  exact huL

/-- The free odometer of a bounded `η` on a bounded `W` vanishes off a finite set. -/
theorem freeOdometer_finite_support (hd : 2 ≤ d) {W : Set (Rd d)} (hW : Bornology.IsBounded W)
    (ηmax : ℤ) : ∀ n : ℕ, ∃ S : Set (Site d), S.Finite ∧ ∀ η : Site d → ℤ, (∀ x, η x ≤ ηmax) →
      ∀ x ∉ S, freeOdometer η (discretize W n) x = 0 := by
  obtain ⟨C, R₀, hUB⟩ := freeOdometerUpperBound_of_oneDim oneDimToppling d hd W hW ηmax
  intro n
  set N : ℤ := (R₀ : ℤ) * ((n : ℤ) + 1)
  refine ⟨{x : Site d | ∀ i, |x i| < N}, ?_, fun η hη x hx => (hUB η hη n).2.2 x ?_⟩
  · refine (Set.finite_Icc (fun _ : Fin d => -N) (fun _ => N)).subset fun x hx => ?_
    exact ⟨fun i => (abs_lt.1 (hx i)).1.le, fun i => (abs_lt.1 (hx i)).2.le⟩
  · simp only [Set.mem_setOf_eq, not_forall, not_lt] at hx
    exact hx

/-- The restriction to `B ⊆ W_n` of the free odometer of `η 𝟙_{W_n}` is locally legal for `η`
in `B`. -/
theorem freeOdometer_restrict_locLegal (hd : 2 ≤ d) {W : Set (Rd d)} (hW : Bornology.IsBounded W)
    {η : Site d → ℤ} {ηmax : ℤ} (hη : ∀ x, η x ≤ ηmax) (n : ℕ) {B : Set (Site d)}
    (hB : B ⊆ discretize W n) :
    (dClosure B).indicator (freeOdometer η (discretize W n)) ∈ locLegal η B := by
  obtain ⟨S, hS, hS0⟩ := freeOdometer_finite_support hd hW ηmax n
  have hv := isLeast_freeOdometer
    (PegdenSmartRegularity.freeOdometer_stabilizing_nonempty (by omega) η hW n)
  have hL := isLegal_of_isLeast_univ (by omega)
    (hS.union (SubadditiveLipschitz.discretize_finite hW n)) hv
    (fun x hx => hS0 η hη x fun h => hx (Or.inl h))
  have hR := locLegalRestrict d _ _ B _ (hB.trans Set.subset_union_right)
    (mem_locLegal_of_isLegal hL)
  exact locLegal_congr (fun x hx => Set.indicator_of_mem (hB hx) η) hR

/-- The restriction to `B ⊆ W_n` of the free odometer of `η 𝟙_{W_n}` is stabilizing for `η` in
`B`. -/
theorem freeOdometer_restrict_stabilizing (hd : 1 ≤ d) {W : Set (Rd d)}
    (hW : Bornology.IsBounded W) (η : Site d → ℤ) (n : ℕ) {B : Set (Site d)}
    (hB : B ⊆ discretize W n) :
    (dClosure B).indicator (freeOdometer η (discretize W n)) ∈ stabilizing η B := by
  have hv := isLeast_freeOdometer (PegdenSmartRegularity.freeOdometer_stabilizing_nonempty hd η hW n)
  exact stabilizing_congr (fun x hx => Set.indicator_of_mem (hB hx) η)
    (stabilizingRestrict d _ Set.univ B _ (Set.subset_univ B) hv.1)

/-- Subsequential limits of the rescaled free odometers of a bounded `η` are continuous
(Lemma 7.2). -/
theorem continuous_of_isOdoSubseqLimit (hd : 2 ≤ d) {W : Set (Rd d)} (hW : IsLipschitzDomain W)
    {ηmin ηmax : ℤ} {η : Site d → ℤ} (hbd : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) {v : Rd d → ℝ}
    (hv : IsOdoSubseqLimit η W v) : Continuous v := by
  obtain ⟨nk, hnk, hvconv⟩ := hv
  obtain ⟨φ, hφ, vbar, hvbar, hconvφ⟩ := (compactness d hd W hW ηmin ηmax η hbd).2 nk hnk
  have : v = vbar := funext fun X =>
    tendsto_nhds_unique ((hvconv.tendsto_at X).comp hφ.tendsto_atTop) (hconvφ.tendsto_at X)
  rw [this]
  exact hvbar

end FreeMaxPrinciple

open FreeMaxPrinciple OpenMaxPrinciple in
/-- **Step** (`InteriorMaxPrincipleStmt`) from Lemma 5.5. -/
theorem interiorMaxPrinciple_of_muConvergence (hconv : MuConvergenceStmt) :
    InteriorMaxPrincipleStmt := by
  intro d hd E W hW l M hM hμ
  have hd1 : 1 ≤ d := by omega
  filter_upwards [(hconv d hd).1 E M hM l, ae_all_iff.2 E.bounded] with η hη hbd
  intro v hv a p r hr hball x hx
  have hvc : Continuous v := continuous_of_isOdoSubseqLimit hd hW hbd hv
  obtain ⟨nk, hnk, hvconv⟩ := hv
  by_cases hxs : x ∈ sphere a r
  · exact ⟨x, hxs, le_rfl⟩
  have hxb : x ∈ ball a r := by
    rw [mem_closedBall] at hx; rw [mem_sphere] at hxs; rw [mem_ball]; exact lt_of_le_of_ne hx hxs
  obtain ⟨hfinμ, hlimμ, -⟩ := hη (ball a r) (StrictConcavityBall.isLipschitzDomain_ball a hr)
  rw [hμ] at hlimμ
  have hV := div_pow_tendsto_zero hd1 hr (fun A => mu A η l M) (mu_empty η l M) hlimμ hnk
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (1 : ℝ) *
      ((freeOdometer η (discretize W (nk k)) z : ℝ) - (nk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a))
          ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball a r) (nk k))) ≤
        mu (discretize (ball a r) (nk k)) η l M ∧
      mu (discretize (ball a r) (nk k)) η l M ≠ ⊤ := by
    filter_upwards [hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : (nk k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨c, c0, hcq⟩ := rescaled_quad_affine hM p a l hn0
    have hDW : discretize (ball a r) (nk k) ⊆ discretize W (nk k) :=
      fun z hz => Set.smul_set_mono (ball_subset_closedBall.trans hball) hz
    refine ⟨volume_le_mu subset_rfl
      (freeOdometer_restrict_locLegal hd hW.1 (fun y => (hbd y).2) (nk k) hDW)
      l M (-c) (-c0) (fun z hz => ?_), (hfinμ (nk k)).1⟩
    rw [Set.indicator_of_mem hz]
    have h1 := hcq (toE z)
    simp only [qlZ, qMZ, inner_neg_left]
    rw [h1]
    ring
  obtain ⟨y, hy, h⟩ := principle_generic hd1 (σ := 1) (continuous_quadratic p a M l) hvc hnk
    hvconv hr hvol hV hxb
  exact ⟨y, hy, by simpa using h⟩

open FreeMaxPrinciple OpenMaxPrinciple in
/-- **Step** (`InteriorMinPrincipleStmt`) from Lemma 5.5. -/
theorem interiorMinPrinciple_of_muConvergence (hconv : MuConvergenceStmt) :
    InteriorMinPrincipleStmt := by
  intro d hd E W hW l M hM hμ
  have hd1 : 1 ≤ d := by omega
  filter_upwards [(hconv d hd).1 E M hM l, ae_all_iff.2 E.bounded] with η hη hbd
  intro v hv a p r hr hball x hx
  have hvc : Continuous v := continuous_of_isOdoSubseqLimit hd hW hbd hv
  obtain ⟨nk, hnk, hvconv⟩ := hv
  by_cases hxs : x ∈ sphere a r
  · exact ⟨x, hxs, le_rfl⟩
  have hxb : x ∈ ball a r := by
    rw [mem_closedBall] at hx; rw [mem_sphere] at hxs; rw [mem_ball]; exact lt_of_le_of_ne hx hxs
  obtain ⟨hfinμ, -, hlimμ⟩ := hη (ball a r) (StrictConcavityBall.isLipschitzDomain_ball a hr)
  rw [hμ] at hlimμ
  have hV := div_pow_tendsto_zero hd1 hr (fun A => muStar A η l M) (muStar_empty η l M)
    hlimμ hnk
  have hvol : ∀ᶠ k in atTop, volume (supGradSet (fun z => (-1 : ℝ) *
      ((freeOdometer η (discretize W (nk k)) z : ℝ) - (nk k : ℝ) ^ 2 *
        (fun X : Rd d => inner ℝ p (X - a) + qM M (X - a) + ql l (X - a))
          ((nk k : ℝ)⁻¹ • toE z))) (discretize (ball a r) (nk k))) ≤
        muStar (discretize (ball a r) (nk k)) η l M ∧
      muStar (discretize (ball a r) (nk k)) η l M ≠ ⊤ := by
    filter_upwards [hnk.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    have hn0 : (nk k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨c, c0, hcq⟩ := rescaled_quad_affine hM p a l hn0
    have hDW : discretize (ball a r) (nk k) ⊆ discretize W (nk k) :=
      fun z hz => Set.smul_set_mono (ball_subset_closedBall.trans hball) hz
    refine ⟨volume_le_muStar subset_rfl
      (freeOdometer_restrict_stabilizing hd1 hW.1 η (nk k) hDW)
      l M c c0 (fun z hz => ?_), (hfinμ (nk k)).2⟩
    rw [Set.indicator_of_mem hz]
    have h1 := hcq (toE z)
    simp only [qlZ, qMZ]
    rw [h1]
    ring
  obtain ⟨y, hy, h⟩ := principle_generic hd1 (σ := -1) (continuous_quadratic p a M l) hvc hnk
    hvconv hr hvol hV hxb
  refine ⟨y, hy, ?_⟩
  simp only [neg_mul, one_mul, neg_le_neg_iff] at h
  exact h

end RandomSandpile

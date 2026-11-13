import RandomSandpile.Proofs.Sec9.SingleSourceD2Jets

/-!
# Theorem 9.2 in dimension two: comparison for the obstacle Dirichlet problem

`obsComparison`: for the obstacle operator `min{s + g(x), A(X)}` (`obsOp`), with `A` degenerate
elliptic, continuous on symmetric matrices and with the shift identity `A(M + tI) = A(M) - 2t`, and
`g` continuous, every upper semicontinuous subsolution of the Dirichlet problem (DP) on a bounded
open set lies below every lower semicontinuous supersolution (Crandall-Ishii-Lions, User's guide,
§3 and §5.C; this is the comparison hypothesis of their Theorem 4.1).

Proof: the strictified subsolution
`w_δ = w + δ(|x|²/2 - C₀)` satisfies `min{w_δ + g, A(X)} ≤ -δ` on its superjets (shift identity) and
`w_δ < 0` on `∂Ω`. If `w - v` were positive somewhere, the maxima of
`w_δ(x) - v(y) - (n+1)/2 |x - y|²` over `Ω̄ × Ω̄` have a subsequence converging to a diagonal point
`(x̄, x̄)` with `w_δ(x̄) - v(x̄) > 0`, so `x̄ ∈ Ω`; there the theorem of sums (CIL Theorem 3.2) gives
`X ≤ Y` with closed jets, hence `A(Y) ≤ A(X)`, and the two jet inequalities contradict
`|g(x̂) - g(ŷ)| < δ`.
-/

noncomputable section

open Filter Topology Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

open CrandallIshiiLions

/-- The obstacle operator `min{s + g(x), A(X)}` in Crandall-Ishii-Lions form. -/
def obsOp (g : Rd 2 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :
    Rd 2 → ℝ → Rd 2 → Matrix (Fin 2) (Fin 2) ℝ → ℝ :=
  fun x s _ X => min (s + g x) (A X)

/-- The strictified subsolution `w + δ(|x|²/2 - C₀)`. -/
def wStrict (w : Rd 2 → ℝ) (δ C0 : ℝ) (x : Rd 2) : ℝ := w x + δ * (‖x‖ ^ 2 / 2 - C0)

theorem wStrict_le {w : Rd 2 → ℝ} {δ C0 : ℝ} (hδ : 0 < δ) {x : Rd 2}
    (hxC : ‖x‖ ^ 2 / 2 ≤ C0 - 1) : wStrict w δ C0 x ≤ w x - δ := by
  have := mul_le_mul_of_nonneg_left hxC hδ.le
  unfold wStrict
  linarith

/-- The strictified subsolution satisfies `min{w_δ + g, A(X)} ≤ -δ` on its superjets. -/
theorem strict_superJet {Ω : Set (Rd 2)} {g : Rd 2 → ℝ} {A : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hA : HasTraceShift A) {w : Rd 2 → ℝ} (hw : IsSubsolution (obsOp g A) Ω w) {δ C0 : ℝ}
    (hδ : 0 < δ) {x : Rd 2} (hx : x ∈ Ω) (hxC : ‖x‖ ^ 2 / 2 ≤ C0 - 1) {p : Rd 2}
    {X : Matrix (Fin 2) (Fin 2) ℝ} (hj : (p, X) ∈ superJet2 Ω (wStrict w δ C0) x) :
    min (wStrict w δ C0 x + g x) (A X) ≤ -δ := by
  have hv : ∀ y, w y = wStrict w δ C0 y + (δ * C0 + (-(δ / 2)) * ‖y‖ ^ 2) := fun y => by
    unfold wStrict
    ring
  have hj' := mem_superJet2_add_quad hv hj
  have hXs : X.IsSymm := And.left hj
  have h : min (w x + g x) (A (X + (2 * -(δ / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) ≤ 0 :=
    hw.2 x hx _ hj'
  rw [hA X hXs (2 * -(δ / 2))] at h
  have hle := wStrict_le (w := w) hδ hxC
  rcases min_le_iff.1 h with h1 | h1
  · exact min_le_iff.2 (Or.inl (by linarith))
  · exact min_le_iff.2 (Or.inr (by linarith))

/-- The strict inequality passes to closed superjets. -/
theorem closedSuperJet_strict {Ω : Set (Rd 2)} {g : Rd 2 → ℝ} (hg : Continuous g)
    {A : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hA : HasTraceShift A)
    (hAc : ContinuousOn A {M | M.IsSymm}) {w : Rd 2 → ℝ} (hw : IsSubsolution (obsOp g A) Ω w)
    {δ C0 : ℝ} (hδ : 0 < δ) (hC : ∀ x ∈ Ω, ‖x‖ ^ 2 / 2 ≤ C0 - 1) {x p : Rd 2}
    {X : Matrix (Fin 2) (Fin 2) ℝ} (hXs : X.IsSymm)
    (hj : (p, X) ∈ closedSuperJet2 Ω (wStrict w δ C0) x) :
    min (wStrict w δ C0 x + g x) (A X) ≤ -δ := by
  obtain ⟨xs, qs, hxs, hqs, hxl, hul, hql⟩ := hj
  have hX : Tendsto (fun n => (qs n).2) atTop (𝓝 X) := (continuous_snd.tendsto _).comp hql
  have hAl : Tendsto (fun n => A (qs n).2) atTop (𝓝 (A X)) :=
    (hAc X hXs).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hX, Eventually.of_forall fun n => And.left (hqs n)⟩)
  have hlim : Tendsto (fun n => min (wStrict w δ C0 (xs n) + g (xs n)) (A (qs n).2)) atTop
      (𝓝 (min (wStrict w δ C0 x + g x) (A X))) :=
    (hul.add ((hg.tendsto x).comp hxl)).min hAl
  exact le_of_tendsto' hlim fun n =>
    strict_superJet (p := (qs n).1) (X := (qs n).2) hA hw hδ (hxs n) (hC _ (hxs n)) (hqs n)

/-- The supersolution inequality passes to closed subjets. -/
theorem closedSubJet_super {Ω : Set (Rd 2)} {g : Rd 2 → ℝ} (hg : Continuous g)
    {A : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hAc : ContinuousOn A {M | M.IsSymm})
    {v : Rd 2 → ℝ} (hv : IsSupersolution (obsOp g A) Ω v) {x p : Rd 2}
    {Y : Matrix (Fin 2) (Fin 2) ℝ} (hYs : Y.IsSymm) (hj : (p, Y) ∈ closedSubJet2 Ω v x) :
    0 ≤ min (v x + g x) (A Y) := by
  obtain ⟨xs, qs, hxs, hqs, hxl, hvl, hql⟩ := hj
  have hY : Tendsto (fun n => (qs n).2) atTop (𝓝 Y) := (continuous_snd.tendsto _).comp hql
  have hAl : Tendsto (fun n => A (qs n).2) atTop (𝓝 (A Y)) :=
    (hAc Y hYs).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hY, Eventually.of_forall fun n => And.left (hqs n)⟩)
  have hlim : Tendsto (fun n => min (v (xs n) + g (xs n)) (A (qs n).2)) atTop
      (𝓝 (min (v x + g x) (A Y))) :=
    (hvl.add ((hg.tendsto x).comp hxl)).min hAl
  exact ge_of_tendsto' hlim fun n => hv.2 (xs n) (hxs n) (qs n) (hqs n)

/-- Upper semicontinuity of the doubled function on `s × s`. -/
theorem usc_doubling {s : Set (Rd 2)} {u v : Rd 2 → ℝ} (hu : UpperSemicontinuousOn u s)
    (hv : LowerSemicontinuousOn v s) (α : ℝ) :
    UpperSemicontinuousOn (fun z : Rd 2 × Rd 2 => u z.1 - v z.2 - α / 2 * ‖z.1 - z.2‖ ^ 2)
      (s ×ˢ s) := by
  intro z hz y hy
  have hy' : u z.1 - v z.2 - α / 2 * ‖z.1 - z.2‖ ^ 2 < y := hy
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (y - (u z.1 - v z.2 - α / 2 * ‖z.1 - z.2‖ ^ 2)) / 3 :=
    ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; linarith
  have h1 : Tendsto Prod.fst (𝓝[s ×ˢ s] z) (𝓝[s] z.1) :=
    continuous_fst.continuousWithinAt.tendsto_nhdsWithin fun z hz => hz.1
  have h2 : Tendsto Prod.snd (𝓝[s ×ˢ s] z) (𝓝[s] z.2) :=
    continuous_snd.continuousWithinAt.tendsto_nhdsWithin fun z hz => hz.2
  have hq : Continuous fun z : Rd 2 × Rd 2 => α / 2 * ‖z.1 - z.2‖ ^ 2 := by fun_prop
  have e1 := h1.eventually (hu z.1 hz.1 (u z.1 + e) (by linarith))
  have e2 := h2.eventually (hv z.2 hz.2 (v z.2 - e) (by linarith))
  have e3 : ∀ᶠ z' in 𝓝[s ×ˢ s] z, α / 2 * ‖z.1 - z.2‖ ^ 2 - e < α / 2 * ‖z'.1 - z'.2‖ ^ 2 :=
    ((hq.tendsto z).eventually (lt_mem_nhds (by linarith))).filter_mono nhdsWithin_le_nhds
  filter_upwards [e1, e2, e3] with z' h1' h2' h3'
  show u z'.1 - v z'.2 - α / 2 * ‖z'.1 - z'.2‖ ^ 2 < y
  linarith

/-- `Y - X` is positive semidefinite when `ξᵀXξ ≤ ξᵀYξ` for all `ξ`. -/
theorem posSemidef_of_bilin_le {X Y : Matrix (Fin 2) (Fin 2) ℝ} (hX : X.IsSymm) (hY : Y.IsSymm)
    (h : ∀ ξ : Rd 2, matrixBilin X ξ ξ ≤ matrixBilin Y ξ ξ) : (Y - X).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hX.eq, hY.eq]
  · have hx := h (WithLp.toLp 2 x)
    change x ⬝ᵥ X *ᵥ x ≤ x ⬝ᵥ Y *ᵥ x at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith

/-- **Comparison for the obstacle Dirichlet problem** (semicontinuous sub- and supersolutions),
from the theorem of sums. -/
theorem obsComparison (hTS : CILTheoremOfSumsStmt) {Ω : Set (Rd 2)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {g : Rd 2 → ℝ} (hg : Continuous g)
    {A : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hA : HasTraceShift A) (hAd : DegenerateElliptic A)
    (hAc : ContinuousOn A {M | M.IsSymm}) {w v : Rd 2 → ℝ}
    (hw : IsSubsolutionDP (obsOp g A) Ω w) (hv : IsSupersolutionDP (obsOp g A) Ω v) :
    ∀ x ∈ closure Ω, w x ≤ v x := by
  intro x0 hx0
  by_contra hlt
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = w x0 - v x0 := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hm_def]; linarith [not_le.1 hlt]
  obtain ⟨R, hR⟩ := hΩb.closure.exists_norm_le
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = R ^ 2 / 2 + 1 := ⟨_, rfl⟩
  have hC : ∀ x ∈ closure Ω, ‖x‖ ^ 2 / 2 ≤ C0 - 1 := fun x hx => by
    have h2 : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) (hR x hx) 2
    rw [hC0]
    linarith
  have hC0pos : 0 < C0 := by rw [hC0]; positivity
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = m / (2 * C0) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδ_def]; positivity
  have hδC : δ * C0 = m / 2 := by
    rw [hδ_def, div_mul_eq_mul_div, mul_div_mul_right _ _ hC0pos.ne']
  have hux0 : m / 2 ≤ wStrict w δ C0 x0 - v x0 := by
    have h1 : 0 ≤ δ * (‖x0‖ ^ 2 / 2) := mul_nonneg hδ.le (by positivity)
    show m / 2 ≤ w x0 + δ * (‖x0‖ ^ 2 / 2 - C0) - v x0
    nlinarith
  -- semicontinuity and bounds
  have hK1 : IsCompact (closure Ω) := hΩb.isCompact_closure
  have huu : UpperSemicontinuousOn (wStrict w δ C0) (closure Ω) := by
    have hc : ContinuousOn (fun x : Rd 2 => δ * (‖x‖ ^ 2 / 2 - C0)) (closure Ω) :=
      (by fun_prop : Continuous fun x : Rd 2 => δ * (‖x‖ ^ 2 / 2 - C0)).continuousOn
    exact hw.1.add hc.upperSemicontinuousOn
  have hvl : LowerSemicontinuousOn v (closure Ω) := hv.1
  obtain ⟨Bu, hBu⟩ := huu.bddAbove_of_isCompact hK1
  obtain ⟨Bv, hBv⟩ := hvl.bddBelow_of_isCompact hK1
  -- maximizers of the doubled functions
  have hK : IsCompact (closure Ω ×ˢ closure Ω) := hK1.prod hK1
  have hne : (closure Ω ×ˢ closure Ω).Nonempty := ⟨(x0, x0), hx0, hx0⟩
  have hmax : ∀ n : ℕ, ∃ z ∈ closure Ω ×ˢ closure Ω, IsMaxOn (fun z : Rd 2 × Rd 2 =>
      wStrict w δ C0 z.1 - v z.2 - ((n : ℝ) + 1) / 2 * ‖z.1 - z.2‖ ^ 2)
      (closure Ω ×ˢ closure Ω) z :=
    fun n => (usc_doubling huu hvl ((n : ℝ) + 1)).exists_isMaxOn hne hK
  choose zs hzK hzmax using hmax
  have hΦn : ∀ n : ℕ, m / 2 ≤ wStrict w δ C0 (zs n).1 - v (zs n).2 -
      ((n : ℝ) + 1) / 2 * ‖(zs n).1 - (zs n).2‖ ^ 2 := by
    intro n
    have h := isMaxOn_iff.1 (hzmax n) (x0, x0) ⟨hx0, hx0⟩
    have h0 : wStrict w δ C0 x0 - v x0 - ((n : ℝ) + 1) / 2 * ‖x0 - x0‖ ^ 2 =
        wStrict w δ C0 x0 - v x0 := by simp
    have h' : wStrict w δ C0 x0 - v x0 - ((n : ℝ) + 1) / 2 * ‖x0 - x0‖ ^ 2 ≤
        wStrict w δ C0 (zs n).1 - v (zs n).2 - ((n : ℝ) + 1) / 2 * ‖(zs n).1 - (zs n).2‖ ^ 2 :=
      h
    linarith
  have hdist : ∀ n : ℕ, ‖(zs n).1 - (zs n).2‖ ^ 2 ≤ 2 * (Bu - Bv) * (1 / ((n : ℝ) + 1)) := by
    intro n
    have h1 := hΦn n
    have h2 : wStrict w δ C0 (zs n).1 ≤ Bu := hBu (Set.mem_image_of_mem _ (hzK n).1)
    have h3 : Bv ≤ v (zs n).2 := hBv (Set.mem_image_of_mem _ (hzK n).2)
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [mul_one_div, le_div_iff₀ hn]
    linarith
  -- a convergent subsequence, on the diagonal
  obtain ⟨zbar, hzbar, φ, hφ, hlim⟩ := hK.tendsto_subseq hzK
  have hlim1 : Tendsto (fun k => (zs (φ k)).1) atTop (𝓝 zbar.1) :=
    (continuous_fst.tendsto _).comp hlim
  have hlim2 : Tendsto (fun k => (zs (φ k)).2) atTop (𝓝 zbar.2) :=
    (continuous_snd.tendsto _).comp hlim
  have hd0 : Tendsto (fun k => ‖(zs (φ k)).1 - (zs (φ k)).2‖ ^ 2) atTop (𝓝 0) := by
    have ha : Tendsto (fun n : ℕ => 2 * (Bu - Bv) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * (Bu - Bv))
      rwa [mul_zero] at this
    exact squeeze_zero (fun k => sq_nonneg _) (fun k => hdist (φ k)) (ha.comp hφ.tendsto_atTop)
  have hdl : Tendsto (fun k => ‖(zs (φ k)).1 - (zs (φ k)).2‖ ^ 2) atTop
      (𝓝 (‖zbar.1 - zbar.2‖ ^ 2)) := ((hlim1.sub hlim2).norm).pow 2
  have heq : zbar.1 = zbar.2 := by
    have h := tendsto_nhds_unique hdl hd0
    exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h))
  have hlim2' : Tendsto (fun k => (zs (φ k)).2) atTop (𝓝 zbar.1) := by
    rw [heq]
    exact hlim2
  have hxbar : zbar.1 ∈ closure Ω := hzbar.1
  -- the limit point carries the positive gap
  have hval : m / 2 ≤ wStrict w δ C0 zbar.1 - v zbar.1 := by
    by_contra hc
    have hc' := not_le.1 hc
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = (m / 2 - (wStrict w δ C0 zbar.1 - v zbar.1)) / 3 :=
      ⟨_, rfl⟩
    have he0 : 0 < e := by rw [he]; linarith
    have hT1 : Tendsto (fun k => (zs (φ k)).1) atTop (𝓝[closure Ω] zbar.1) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim1, Eventually.of_forall fun k => (hzK (φ k)).1⟩
    have hT2 : Tendsto (fun k => (zs (φ k)).2) atTop (𝓝[closure Ω] zbar.1) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim2', Eventually.of_forall fun k => (hzK (φ k)).2⟩
    have e1 := hT1.eventually (huu zbar.1 hxbar (wStrict w δ C0 zbar.1 + e) (by linarith))
    have e2 := hT2.eventually (hvl zbar.1 hxbar (v zbar.1 - e) (by linarith))
    obtain ⟨k, hk1, hk2⟩ := (e1.and e2).exists
    have h1 := hΦn (φ k)
    have h2 : 0 ≤ ((φ k : ℝ) + 1) / 2 * ‖(zs (φ k)).1 - (zs (φ k)).2‖ ^ 2 := by positivity
    linarith
  -- the limit point is interior
  have hxΩ : zbar.1 ∈ Ω := by
    by_contra hn
    have hfr : zbar.1 ∈ frontier Ω := by
      rw [hΩ.frontier_eq]
      exact ⟨hxbar, hn⟩
    have h1 := hw.2.2 _ hfr
    have h2 := hv.2.2 _ hfr
    have h3 := wStrict_le (w := w) hδ (hC _ hxbar)
    linarith
  -- a good index
  have hev1 : ∀ᶠ k in atTop, (zs (φ k)).1 ∈ Ω := hlim1.eventually (hΩ.mem_nhds hxΩ)
  have hev2 : ∀ᶠ k in atTop, (zs (φ k)).2 ∈ Ω := hlim2'.eventually (hΩ.mem_nhds hxΩ)
  have hgl : Tendsto (fun k => g (zs (φ k)).1 - g (zs (φ k)).2) atTop
      (𝓝 (g zbar.1 - g zbar.1)) :=
    ((hg.tendsto _).comp hlim1).sub ((hg.tendsto _).comp hlim2')
  rw [sub_self] at hgl
  have hev3 : ∀ᶠ k in atTop, |g (zs (φ k)).1 - g (zs (φ k)).2| < δ := by
    filter_upwards [Metric.tendsto_nhds.1 hgl δ hδ] with k hk
    rwa [Real.dist_eq, sub_zero] at hk
  obtain ⟨k, hk1, hk2, hk3⟩ := (hev1.and (hev2.and hev3)).exists
  -- the theorem of sums at the maximum
  have hloc : IsLocalMaxOn (fun z : Rd 2 × Rd 2 => wStrict w δ C0 z.1 - v z.2 -
      ((φ k : ℝ) + 1) / 2 * ‖z.1 - z.2‖ ^ 2) (Ω ×ˢ Ω) ((zs (φ k)).1, (zs (φ k)).2) :=
    ((hzmax (φ k)).of_subset (Set.prod_mono subset_closure subset_closure)).isLocalMaxOn
  obtain ⟨X, Y, hXs, hYs, hX, hY, _, hup⟩ := hTS 2 Ω hΩ (wStrict w δ C0) v
    (huu.mono subset_closure) (hvl.mono subset_closure) ((φ k : ℝ) + 1) (by positivity) _ _
    hk1 hk2 hloc
  have hPSD : (Y - X).PosSemidef := posSemidef_of_bilin_le hXs hYs fun ξ => by
    have h := hup ξ ξ
    rw [sub_self, norm_zero, zero_pow two_ne_zero, mul_zero] at h
    linarith
  have hAXY := hAd X Y hXs hYs hPSD
  have hsub := closedSuperJet_strict hg hA hAc hw.2.1 hδ (fun x hx => hC x (subset_closure hx))
    hXs hX
  have hsup := closedSubJet_super hg hAc hv.2.1 hYs hY
  have hAY : 0 ≤ A Y := (le_min_iff.1 hsup).2
  have hvy : 0 ≤ v (zs (φ k)).2 + g (zs (φ k)).2 := (le_min_iff.1 hsup).1
  have hux : wStrict w δ C0 (zs (φ k)).1 + g (zs (φ k)).1 ≤ -δ := by
    rcases min_le_iff.1 hsub with h | h
    · exact h
    · linarith
  have hΦk := hΦn (φ k)
  have hq : 0 ≤ ((φ k : ℝ) + 1) / 2 * ‖(zs (φ k)).1 - (zs (φ k)).2‖ ^ 2 := by positivity
  have habs := abs_lt.1 hk3
  linarith

end SingleSourceD2

end RandomSandpile

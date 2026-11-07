import RandomSandpile.Draft.Section5
import RandomSandpile.Proofs.Sec5.MuBounded

/-! # Lemma 5.5 (almost sure convergence of `μ` and `μ*`): proof steps

The printed proof of Lemma 5.5 (`MuConvergenceStmt`, `paper/random_piles-corrected.tex`)
applies the multiparameter subadditive ergodic theorem (Proposition 5.3, `SubadditiveErgodicStmt`,
cited; an explicit hypothesis of the reduction) to `f(A, η) = μ(A, η, l, M)` and to `μ*`. The steps:

* `LocLegalRestrictStmt`: for `B ⊆ A`, the restriction to `B̄` of a locally legal
  toppling `u ∈ 𝓛(η, A)` is locally legal in `B`: the topplings of `u` on `∂B` are performed first
  (they are arbitrary boundary topplings for `B`), and the legal topplings of `u` at sites of `B`
  remain legal, since the boundary `∂B` has already received all its topplings;
* `StabilizingRestrictStmt`: the restriction to `B̄` of `v ∈ 𝓢(η, A)` lies in
  `𝓢(η, B)`;
* `MuSubadditiveStmt`: `μ(A) ≤ ∑_j μ(A_j)` and `μ*(A) ≤ ∑_j μ*(A_j)` whenever
  `A = ⋃_j A_j`, deduced from the two restriction steps by `muSubadditive_of_steps`. Only the
  inclusion `∂⁺(w, A) ⊆ ⋃_j ∂⁺(w, A_j)` and the subadditivity of Lebesgue measure are used, so
  neither disjointness nor Lemma 5.3 (invoked) is needed;
* `MuStationaryStmt` (the stationarity of the process, which the printed proof leaves implicit; see
  `IsSubadditiveProcess`): `μ(A, T_y η) = μ(y + A, η)`, because translating a toppling translates
  its supergradient sets and `q_l + q_M` changes by an affine function under translation;
* `LocLegalLocalStmt` (measurability, left implicit in the paper): `𝓛(η, A)` and `𝓢(η, A)`
  depend on `η` only through its restriction to `A`; for finite `A` this makes `η ↦ μ(A, η)`
  measurable for the product σ-algebra (`measurable_of_locLegal_local`);
* `UnitBallLipschitzStmt`: the open unit ball is a bounded Lipschitz domain, so the balls
  `B_n = nB ∩ ℤ^d` defining `muBar` (`Defs/Effective.lean`) are covered by Proposition 5.3;
* `DiscretizeFiniteStmt`: `nW ∩ ℤ^d` is finite for bounded `W`.

The bounds `0 ≤ μ(A, η) ≤ C |A|` of Lemma 5.4 hold only when `η ≤ η_max` (`mu_le_ncard`), an event
of full probability, while `IsSubadditiveProcess` asks them for every configuration; the process
used in `muConvergence_of_steps` is `μ` on the event `{η_min ≤ η ≤ η_max}` and `0` off it. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped ENNReal Pointwise

namespace RandomSandpile

/-- Step 1a. For `B ⊆ A`, the restriction to `B̄` (extended by `0`) of a locally
legal toppling `u ∈ 𝓛(η, A)` lies in `𝓛(η, B)`. -/
def LocLegalRestrictStmt : Prop :=
  ∀ (d : ℕ) (η : Site d → ℤ) (A B : Set (Site d)) (u : Site d → ℤ), B ⊆ A → u ∈ locLegal η A →
    (dClosure B).indicator u ∈ locLegal η B

/-- Step 1b. For `B ⊆ A`, the restriction to `B̄` (extended by `0`) of a stabilizing
toppling `v ∈ 𝓢(η, A)` lies in `𝓢(η, B)`. -/
def StabilizingRestrictStmt : Prop :=
  ∀ (d : ℕ) (η : Site d → ℤ) (A B : Set (Site d)) (v : Site d → ℤ), B ⊆ A →
    v ∈ stabilizing η A → (dClosure B).indicator v ∈ stabilizing η B

/-- Step 1. Subadditivity of `A ↦ μ(A, η, l, M)` and `A ↦ μ*(A, η, l, M)` over finite
covers `A = A_1 ∪ ⋯ ∪ A_k`, in `[0, ∞]`. -/
def MuSubadditiveStmt : Prop :=
  ∀ (d : ℕ) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (A : Set (Site d))
    (B : Fin k → Set (Site d)), A = ⋃ j, B j →
      mu A η l M ≤ ∑ j, mu (B j) η l M ∧ muStar A η l M ≤ ∑ j, muStar (B j) η l M

/-- Step 2 (stationarity, implicit). `μ(A, T_y η, l, M) = μ(y + A, η, l, M)` and
`μ*(A, T_y η, l, M) = μ*(y + A, η, l, M)`, where `T_y η(z) = η(y + z)`. -/
def MuStationaryStmt : Prop :=
  ∀ (d : ℕ) (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (y : Site d)
    (A : Set (Site d)),
      mu A (shift y η) l M = mu (y +ᵥ A) η l M ∧ muStar A (shift y η) l M = muStar (y +ᵥ A) η l M

/-- Step 3 (locality, the source of measurability). `𝓛(η, A)` and `𝓢(η, A)` depend on `η` only
through its restriction to `A`. -/
def LocLegalLocalStmt : Prop :=
  ∀ (d : ℕ) (η η' : Site d → ℤ) (A : Set (Site d)), (∀ x ∈ A, η x = η' x) →
    locLegal η A = locLegal η' A ∧ stabilizing η A = stabilizing η' A

/-- Step 4. The open unit ball of `ℝ^d` is a bounded Lipschitz domain. -/
def UnitBallLipschitzStmt : Prop :=
  ∀ d : ℕ, IsLipschitzDomain (Metric.ball (0 : Rd d) 1)

/-- Step 5. For bounded `W ⊆ ℝ^d`, `nW ∩ ℤ^d` is finite. -/
def DiscretizeFiniteStmt : Prop :=
  ∀ (d : ℕ) (W : Set (Rd d)), Bornology.IsBounded W → ∀ n : ℕ, (discretize W n).Finite

/-! ### Subadditivity from the restriction steps -/

section Reductions

variable {d : ℕ}

/-- `B ⊆ A` implies `B̄ ⊆ Ā`. -/
theorem dClosure_mono {A B : Set (Site d)} (h : B ⊆ A) : dClosure B ⊆ dClosure A := by
  intro y hy
  rw [dClosure_eq] at hy ⊢
  rcases hy with hy | hy
  · exact Or.inl (h hy)
  · by_cases hyA : y ∈ A
    · exact Or.inl hyA
    · obtain ⟨-, x, hx, hxy⟩ := mem_bdry.1 hy
      exact Or.inr (mem_bdry.2 ⟨hyA, x, h hx, hxy⟩)

/-- **Reduction of Step 1**: subadditivity of `μ` and `μ*` from the two restriction
steps. For `x ∈ A_j` the test set `Ā_j` of `∂⁺(w, x, A_j)` is contained in `Ā`, so
`∂⁺(w, x, A) ⊆ ∂⁺(w, x, A_j)`; hence `∂⁺(w, A) ⊆ ⋃_j ∂⁺(w_j, A_j)`, where `w_j` is the restriction
of `w = u - q_l - q_M` to `Ā_j`, which lies in `S(A_j, η, l, M)` by Step 1a. -/
theorem muSubadditive_of_steps (h1 : LocLegalRestrictStmt) (h2 : StabilizingRestrictStmt) :
    MuSubadditiveStmt := by
  intro d η l M k A B hAB
  have hBA : ∀ j, B j ⊆ A := fun j => hAB ▸ Set.subset_iUnion B j
  have hx : ∀ x ∈ A, ∃ j, x ∈ B j := fun x hx => Set.mem_iUnion.1 (hAB ▸ hx)
  constructor
  · refine iSup₂_le fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.1 hw
    let wj : Fin k → Site d → ℝ := fun j x =>
      (((dClosure (B j)).indicator u x : ℤ) : ℝ) - (qlZ l x + qMZ M x)
    have hwj : ∀ j, wj j ∈ perturbedSub (B j) η l M := fun j =>
      mem_perturbedSub.2 ⟨_, h1 d η A (B j) u (hBA j) hu, rfl⟩
    have hsub : supGradSet (fun x => (u x : ℝ) - (qlZ l x + qMZ M x)) A ⊆
        ⋃ j, supGradSet (wj j) (B j) := by
      intro p hp
      obtain ⟨x, hxA, hp⟩ := Set.mem_iUnion₂.1 hp
      obtain ⟨j, hxj⟩ := hx x hxA
      refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion₂.2 ⟨x, hxj, fun y hy => ?_⟩⟩
      have := hp y (dClosure_mono (hBA j) hy)
      simpa [wj, Set.indicator_of_mem hy, Set.indicator_of_mem (subset_dClosure _ hxj)] using this
    calc volume (supGradSet (fun x => (u x : ℝ) - (qlZ l x + qMZ M x)) A)
        ≤ volume (⋃ j, supGradSet (wj j) (B j)) := measure_mono hsub
      _ ≤ ∑ j, volume (supGradSet (wj j) (B j)) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ j, mu (B j) η l M := Finset.sum_le_sum fun j _ =>
          le_iSup₂ (f := fun w (_ : w ∈ perturbedSub (B j) η l M) =>
            volume (supGradSet w (B j))) (wj j) (hwj j)
  · refine iSup₂_le fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := mem_perturbedSuper.1 hw
    let wj : Fin k → Site d → ℝ := fun j x =>
      (((dClosure (B j)).indicator v x : ℤ) : ℝ) - (qlZ l x + qMZ M x)
    have hwj : ∀ j, wj j ∈ perturbedSuper (B j) η l M := fun j =>
      mem_perturbedSuper.2 ⟨_, h2 d η A (B j) v (hBA j) hv, rfl⟩
    have hsub : subGradSet (fun x => (v x : ℝ) - (qlZ l x + qMZ M x)) A ⊆
        ⋃ j, subGradSet (wj j) (B j) := by
      intro p hp
      obtain ⟨x, hxA, hp⟩ := Set.mem_iUnion₂.1 hp
      obtain ⟨j, hxj⟩ := hx x hxA
      refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion₂.2 ⟨x, hxj, fun y hy => ?_⟩⟩
      have := hp y (dClosure_mono (hBA j) hy)
      simpa [wj, Set.indicator_of_mem hy, Set.indicator_of_mem (subset_dClosure _ hxj)] using this
    calc volume (subGradSet (fun x => (v x : ℝ) - (qlZ l x + qMZ M x)) A)
        ≤ volume (⋃ j, subGradSet (wj j) (B j)) := measure_mono hsub
      _ ≤ ∑ j, volume (subGradSet (wj j) (B j)) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ j, muStar (B j) η l M := Finset.sum_le_sum fun j _ =>
          le_iSup₂ (f := fun w (_ : w ∈ perturbedSuper (B j) η l M) =>
            volume (subGradSet w (B j))) (wj j) (hwj j)

/-! ### Measurability from locality -/

/-- A function of the configuration that only depends on its restriction to a finite set `A` is
measurable for the product σ-algebra: it factors through the restriction `Config d → (A → ℤ)`,
whose target is countable with measurable singletons. -/
theorem measurable_of_eqOn_finite {β : Type*} [MeasurableSpace β] {A : Set (Site d)}
    (hA : A.Finite) {F : Config d → β}
    (hF : ∀ η η' : Config d, (∀ x ∈ A, η x = η' x) → F η = F η') : Measurable F := by
  classical
  haveI : Finite A := hA.to_subtype
  let r : Config d → (A → ℤ) := fun η a => η a
  let e : (A → ℤ) → Config d := fun ξ x => if h : x ∈ A then ξ ⟨x, h⟩ else 0
  have hr : Measurable r := measurable_pi_lambda _ fun a => measurable_pi_apply (a : Site d)
  have hFe : F = (F ∘ e) ∘ r := by
    funext η
    exact hF _ _ fun x hx => by simp [r, e, hx]
  rw [hFe]
  exact (measurable_of_countable _).comp hr

/-- Under Step 3, `η ↦ μ(A, η, l, M)` and `η ↦ μ*(A, η, l, M)` are measurable for finite `A`. -/
theorem measurable_mu_of_local (hloc : LocLegalLocalStmt) {A : Set (Site d)} (hA : A.Finite)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (fun η : Config d => mu A η l M) ∧
      Measurable (fun η : Config d => muStar A η l M) :=
  ⟨measurable_of_eqOn_finite hA fun η η' h => by
      simp only [mu, perturbedSub, (hloc d η η' A h).1],
    measurable_of_eqOn_finite hA fun η η' h => by
      simp only [muStar, perturbedSuper, (hloc d η η' A h).2]⟩

/-! ### The discrete balls `B_n = nB ∩ ℤ^d` -/

theorem toE_zero' : toE (0 : Site d) = 0 := by
  ext i; simp

/-- For `n ≥ 1`, `nB ∩ ℤ^d = B_n`, where `B` is the open unit ball of `ℝ^d`. -/
theorem discretize_unitBall {n : ℕ} (hn : 1 ≤ n) :
    discretize (Metric.ball (0 : Rd d) 1) n = ballZ0 (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  ext x
  simp only [discretize, Set.mem_setOf_eq, smul_unitBall hn', Real.norm_natCast,
    mem_ball_zero_iff, ballZ0, ballZ, toE_zero', sub_zero]

/-! ### The abstract reduction: a subadditive quantity of the environment -/

/-- The core of `muConvergence_of_steps`, for a set function `m(A, η) ∈ [0, ∞]` that is local in
the sense of being measurable on finite sets, stationary, subadditive over finite covers, and
bounded by `K |A|` on a shift-invariant event `G` of full probability. The process
`f(A, η) = 1_G(η) m(A, η)` (in `ℝ`) is a subadditive process in `𝓜_K`, so Proposition 5.3 gives a
deterministic limit `a ∈ [0, K]` along `nW ∩ ℤ^d` for every bounded Lipschitz domain `W`; along the
balls (Step 4) this identifies `a` with the `P`-average of `limsup_n m(B_n) / |B_n|`. -/
theorem subadditive_limit_of_steps (hSE : SubadditiveErgodicStmt)
    (hball : UnitBallLipschitzStmt) (hfin : DiscretizeFiniteStmt) (hd : 2 ≤ d)
    (E : RandomEnvironment d) (m : Set (Site d) → Config d → ℝ≥0∞) (G : Set (Config d))
    (K : ℝ) (hK : 0 ≤ K) (hG : MeasurableSet G) (hGfull : ∀ᵐ η ∂E.P, η ∈ G)
    (hGshift : ∀ (y : Site d) (η : Config d), shift y η ∈ G ↔ η ∈ G)
    (hmeas : ∀ A : Set (Site d), A.Finite → Measurable (m A))
    (hstat : ∀ (y : Site d) (A : Set (Site d)) (η : Config d), m A (shift y η) = m (y +ᵥ A) η)
    (hsub : ∀ (η : Config d) (k : ℕ) (A : Set (Site d)) (B : Fin k → Set (Site d)),
      A = ⋃ j, B j → m A η ≤ ∑ j, m (B j) η)
    (hbd : ∀ η ∈ G, ∀ A : Set (Site d), A.Finite → m A η ≤ ENNReal.ofReal (K * (A.ncard : ℝ))) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ K ∧
      (∫⁻ η, limsup (fun n : ℕ => m (ballZ0 (n : ℝ)) η /
        ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P).toReal = a ∧
      ∀ᵐ η ∂E.P, ∀ W : Set (Rd d), IsLipschitzDomain W →
        (∀ n : ℕ, m (discretize W n) η ≠ ⊤) ∧
        Tendsto (fun n : ℕ => (m (discretize W n) η).toReal / ((discretize W n).ncard : ℝ))
          atTop (𝓝 a) := by
  let f : Config d → Set (Site d) → ℝ := fun η A => G.indicator (fun η => (m A η).toReal) η
  have hne : ∀ η ∈ G, ∀ A : Set (Site d), A.Finite → m A η ≠ ⊤ := fun η hη A hA =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbd η hη A hA)
  have hfG : ∀ η ∈ G, ∀ A, f η A = (m A η).toReal := fun η hη A => Set.indicator_of_mem hη _
  have hfG' : ∀ η ∉ G, ∀ A, f η A = 0 := fun η hη A => Set.indicator_of_notMem hη _
  have hproc : IsSubadditiveProcess K f := by
    refine ⟨fun η => ⟨?_, fun A hA => ?_⟩, fun A hA => ?_, fun y A _ η => ?_⟩
    · intro k A B hA hB _ hAB
      by_cases hη : η ∈ G
      · simp only [hfG η hη]
        rw [← ENNReal.toReal_sum fun j _ => hne η hη _ (hB j)]
        exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun j _ => hne η hη _ (hB j))
          (hsub η k A B hAB)
      · simp [hfG' η hη]
    · by_cases hη : η ∈ G
      · rw [hfG η hη]
        exact ⟨ENNReal.toReal_nonneg,
          ENNReal.toReal_le_of_le_ofReal (by positivity) (hbd η hη A hA)⟩
      · rw [hfG' η hη]
        exact ⟨le_rfl, by positivity⟩
    · exact (hmeas A hA).ennreal_toReal.indicator hG
    · by_cases hη : η ∈ G
      · rw [hfG η hη, hfG _ ((hGshift y η).2 hη), hstat]
      · rw [hfG' η hη, hfG' _ fun h => hη ((hGshift y η).1 h)]
  obtain ⟨a, ha0, haK, hae⟩ := hSE d hd E K f hproc
  have hgood := hGfull.and hae
  have hlim : ∀ᵐ η ∂E.P, limsup (fun n : ℕ => m (ballZ0 (n : ℝ)) η /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop = ENNReal.ofReal a := by
    filter_upwards [hgood] with η hη
    refine Tendsto.limsup_eq ((ENNReal.tendsto_ofReal (hη.2 _ (hball d))).congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [discretize_unitBall hn, hfG η hη.1]
    have hBfin : (ballZ0 (d := d) (n : ℝ)).Finite := by
      rw [← discretize_unitBall hn]; exact hfin d _ Metric.isBounded_ball n
    have hpos : 0 < (ballZ0 (d := d) (n : ℝ)).ncard :=
      (Set.ncard_pos hBfin).2 ⟨0, by
        simp only [ballZ0, ballZ, Set.mem_setOf_eq, sub_self, norm_zero]
        exact_mod_cast hn⟩
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hpos),
      ENNReal.ofReal_toReal (hne η hη.1 _ hBfin), ENNReal.ofReal_natCast]
  refine ⟨a, ha0, haK, ?_, ?_⟩
  · rw [lintegral_congr_ae hlim, lintegral_const, measure_univ, mul_one,
      ENNReal.toReal_ofReal ha0]
  · filter_upwards [hgood] with η hη W hW
    refine ⟨fun n => hne η hη.1 _ (hfin d W hW.1 n), ?_⟩
    simpa only [hfG η hη.1] using hη.2 W hW

/-- The event `{η ≤ η_max everywhere}` is measurable, shift invariant and of full probability. -/
theorem le_ηmax_event (E : RandomEnvironment d) :
    MeasurableSet {η : Config d | ∀ x, η x ≤ E.ηmax} ∧
      (∀ᵐ η ∂E.P, η ∈ {η : Config d | ∀ x, η x ≤ E.ηmax}) ∧
      ∀ (y : Site d) (η : Config d), shift y η ∈ {η : Config d | ∀ x, η x ≤ E.ηmax} ↔
        η ∈ {η : Config d | ∀ x, η x ≤ E.ηmax} := by
  refine ⟨?_, ae_all_iff.2 fun x => (E.bounded x).mono fun _ h => h.2, fun y η => ⟨fun h x => ?_,
    fun h x => h (y + x)⟩⟩
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun x => measurableSet_setOf.2
      ((measurable_of_countable (fun z : ℤ => z ≤ E.ηmax)).comp
        (@measurable_pi_apply (Site d) (fun _ => ℤ) _ x))
  · simpa [add_neg_cancel_left] using h (-y + x)

/-- The event `{η ≥ η_min everywhere}` is measurable, shift invariant and of full probability. -/
theorem ηmin_le_event (E : RandomEnvironment d) :
    MeasurableSet {η : Config d | ∀ x, E.ηmin ≤ η x} ∧
      (∀ᵐ η ∂E.P, η ∈ {η : Config d | ∀ x, E.ηmin ≤ η x}) ∧
      ∀ (y : Site d) (η : Config d), shift y η ∈ {η : Config d | ∀ x, E.ηmin ≤ η x} ↔
        η ∈ {η : Config d | ∀ x, E.ηmin ≤ η x} := by
  refine ⟨?_, ae_all_iff.2 fun x => (E.bounded x).mono fun _ h => h.1, fun y η => ⟨fun h x => ?_,
    fun h x => h (y + x)⟩⟩
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun x => measurableSet_setOf.2
      ((measurable_of_countable (fun z : ℤ => E.ηmin ≤ z)).comp
        (@measurable_pi_apply (Site d) (fun _ => ℤ) _ x))
  · simpa [add_neg_cancel_left] using h (-y + x)

end Reductions

/-- **Reduction of Lemma 5.5** to Proposition 5.3 (`SubadditiveErgodicStmt`, cited)
and Steps 1-5. The constants are those of Lemma 5.4 on every finite set (`mu_le_ncard`,
`muStar_le_ncard`): `C = d^{-d} ((max(η_max, 0) + l + Tr M)⁺)^d` and
`C* = d^{-d} (((2d - 1) - η_min - l - Tr M)⁺)^d`. -/
theorem muConvergence_of_steps (hSE : SubadditiveErgodicStmt) (hsub : MuSubadditiveStmt)
    (hstat : MuStationaryStmt) (hloc : LocLegalLocalStmt) (hball : UnitBallLipschitzStmt)
    (hfin : DiscretizeFiniteStmt) : MuConvergenceStmt := by
  intro d hd
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hmu : ∀ (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), ∃ a : ℝ,
      0 ≤ a ∧ a ≤ (max (((max E.ηmax 0 : ℤ) : ℝ) + l + M.trace) 0 / d) ^ d ∧ muBar E l M = a ∧
      ∀ᵐ η ∂E.P, ∀ W : Set (Rd d), IsLipschitzDomain W →
        (∀ n : ℕ, mu (discretize W n) η l M ≠ ⊤) ∧
        Tendsto (fun n : ℕ => (mu (discretize W n) η l M).toReal / ((discretize W n).ncard : ℝ))
          atTop (𝓝 a) := fun E l M =>
    subadditive_limit_of_steps hSE hball hfin hd E (fun A η => mu A η l M) _ _ (by positivity)
      (le_ηmax_event E).1 (le_ηmax_event E).2.1 (le_ηmax_event E).2.2
      (fun A hA => (measurable_mu_of_local hloc hA l M).1) (fun y A η => (hstat d η l M y A).1)
      (fun η k A B h => (hsub d η l M k A B h).1)
      (fun η hη A hA => mu_le_ncard hd1 hA (fun x _ => hη x) l M)
  have hmus : ∀ (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ), ∃ a : ℝ,
      0 ≤ a ∧ a ≤ (max ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - l - M.trace) 0 / d) ^ d ∧
      muStarBar E l M = a ∧
      ∀ᵐ η ∂E.P, ∀ W : Set (Rd d), IsLipschitzDomain W →
        (∀ n : ℕ, muStar (discretize W n) η l M ≠ ⊤) ∧
        Tendsto (fun n : ℕ => (muStar (discretize W n) η l M).toReal /
          ((discretize W n).ncard : ℝ)) atTop (𝓝 a) := fun E l M =>
    subadditive_limit_of_steps hSE hball hfin hd E (fun A η => muStar A η l M) _ _
      (by positivity) (ηmin_le_event E).1 (ηmin_le_event E).2.1 (ηmin_le_event E).2.2
      (fun A hA => (measurable_mu_of_local hloc hA l M).2) (fun y A η => (hstat d η l M y A).2)
      (fun η k A B h => (hsub d η l M k A B h).2)
      (fun η hη A hA => muStar_le_ncard hd1 hA (fun x _ => hη x) l M)
  refine ⟨fun E M _ l => ?_,
    fun ηmax l M _ => ⟨(max (((max ηmax 0 : ℤ) : ℝ) + l + M.trace) 0 / d) ^ d, fun E hE => ?_⟩,
    fun ηmin l M _ =>
      ⟨(max ((2 * (d : ℝ) - 1) - (ηmin : ℝ) - l - M.trace) 0 / d) ^ d, fun E hE => ?_⟩⟩
  · obtain ⟨a, -, -, ha, hae⟩ := hmu E l M
    obtain ⟨b, -, -, hb, hbe⟩ := hmus E l M
    filter_upwards [hae, hbe] with η h1 h2 W hW
    rw [ha, hb]
    exact ⟨fun n => ⟨(h1 W hW).1 n, (h2 W hW).1 n⟩, (h1 W hW).2, (h2 W hW).2⟩
  · obtain ⟨a, ha0, haK, ha, -⟩ := hmu E l M
    rw [ha]
    exact ⟨ha0, hE ▸ haK⟩
  · obtain ⟨a, ha0, haK, ha, -⟩ := hmus E l M
    rw [ha]
    exact ⟨ha0, hE ▸ haK⟩

end RandomSandpile

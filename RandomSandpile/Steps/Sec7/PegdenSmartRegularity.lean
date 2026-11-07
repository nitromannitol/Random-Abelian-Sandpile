import RandomSandpile.Draft.Section7
import RandomSandpile.Inputs.Proposed

/-!
# Steps of Lemma 7.6 (regularity of the limits; Pegden-Smart)

Carving of `RandomSandpile.PegdenSmartRegularityStmt` (Lemma 7.6, `regularity`,
`paper/random_piles-corrected.tex`) into steps and the reduction
`pegdenSmartRegularity_of_steps`, which takes Pegden-Smart's Proposition 2.5
(`PegdenSmartTouchingStmt`, part 1, a literature input) as an explicit hypothesis.

* **Part 1** (Prop 2.5). Touching at a point of twice differentiability, applied to
  `v`, `v'` on a ball `U ⊇ B_R` outside of which `v = v' = 0`, with boundary maximum `m = 0`. Its
  hypotheses on the limits (continuity, compact support, `|Δ v| ≤ K` in the viscosity sense) are
  step `FreeOdometerLimitRegularStmt`. Its conclusion is a set of positive measure, which meets the
  complement of `∂W` because `∂W` is Lebesgue-null (step `LipschitzDomainFrontierNullStmt`); a point
  off `∂W` is in `W` (open) or outside `W̄`.
* **Part 2** (Lemma 4.1). For `a ∉ W̄` and `n` large, the sites `z` with
  `z / n` near `a` lie outside `W_n`, where the free sandpile is stable with no initial chips:
  `Δ_{ℤ^d} v_n(z) ≤ 2d - 1` (also for the junk value `v_n = 0`). Pegden-Smart's construction
  (the integer-corrected minimum of translates, `PegdenSmartIntegerSuperharmonicStmt`) then gives
  `u` (`pegdenSmart_part2_of_steps`).
* **Part 3** (sketched in the paper). The printed sketch (periodic tiling `η̃`, the
  ergodic average of `η` over `B_{rn}`, Rossin's observation for `Δ_{ℤ^d} u`) is replaced by two
  steps that isolate its content. (a) In `W` the limit satisfies `Δ v ≤ 2d - 1 - E(η(0))` at
  points of second-order Peano expansion (step `FreeOdometerLimitHessianTraceStmt`, the
  homogenized form of `Δ_{ℤ^d} v_n + η ≤ 2d - 1` in `W_n`, by the ergodic theorem for `η`); under
  high density this is `tr D²v(a) < 0`. (b) Every symmetric `B` with `tr B < d` is an integer
  superharmonic matrix: some `u : ℤ^d → ℤ` has `Δ_{ℤ^d} u ≤ 2d - 1` and `u ≥ q_B` (step
  `IntegerSuperharmonicOfTraceStmt`; proof: `⌊q_A⌋` for a rational `A ≥ B` with `tr A < d` has a
  periodic Laplacian whose average over a period is `tr A`, and Rossin's observation stabilizes
  it with a bounded periodic odometer, `RandomSandpile/Infra/Rossin.lean`). Part 3 follows with
  `B = D²v(a) - εI`, even without the `o(|x|²)` term (`pegdenSmart_part3_of_steps`).

Parts 2 and 3 are proved below for an arbitrary uniform limit of rescaled free odometers, so they
apply to `v'` as well as to `v``).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

/-! ### Step statements -/

/-- **Step (part 1): regularity of limits of rescaled free odometers** (and inside
 Prop 2.5; cf. the proof of Lemma 7.2). Almost surely, every uniform limit `v` of a
subsequence of the rescaled free odometers `v̄_n` of `η` on `W` is continuous, vanishes outside a
ball, and satisfies `|Δ v| ≤ K` in `ℝ^d` in the viscosity sense: `v` is a viscosity subsolution of
`-Δ v - K = 0` and a viscosity supersolution of `-Δ v + K = 0` (Crandall-Ishii-Lions). The constant
`K` depends only on `d` and the bounds `η_min, η_max` (it comes from `|Δ_{ℤ^d} v_n| ≤ K`). -/
def FreeOdometerLimitRegularStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∃ Ω₁ : Set (Config d), E.P Ω₁ᶜ = 0 ∧ ∃ K : ℝ, ∀ η ∈ Ω₁, ∀ nk : ℕ → ℕ, StrictMono nk →
      ∀ v : Rd d → ℝ,
        TendstoUniformly
          (fun k => rescaleOdo (freeOdometer η (discretize W (nk k))) (nk k)) v atTop →
        Continuous v ∧ (∃ R : ℝ, ∀ x : Rd d, R ≤ ‖x‖ → v x = 0) ∧
          ViscFromAboveGE (fun X => X.trace + K) Set.univ v ∧
          ViscFromBelowLE (fun X => X.trace - K) Set.univ v

/-- **Step (part 1): the boundary of a Lipschitz domain is Lebesgue-null** (needed to choose
`a ∉ ∂W`). Locally `∂W` is the graph of a Lipschitz function over a hyperplane. -/
def LipschitzDomainFrontierNullStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), IsLipschitzDomain W → volume (frontier W) = 0

/-- **Step (part 3): the Hessian of a limit in `W` has trace at most `2d - 1 - E(η(0))`**
(the content). Almost surely, if a uniform limit `v` of a subsequence of the
rescaled free odometers of `η` on `W` has a second-order Peano expansion at `a ∈ W` with symmetric
matrix `X = D²v(a)`, then `tr X ≤ 2d - 1 - E(η(0))`. This is the pointwise form, at points of
twice differentiability, of the viscosity inequality `Δ v ≤ 2d - 1 - E(η(0))` in `W`, the
homogenized limit of `Δ_{ℤ^d} v_n + η ≤ 2d - 1` in `W_n` (ergodic theorem for `η` on balls). -/
def FreeOdometerLimitHessianTraceStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ E : RandomEnvironment d, ∀ W : Set (Rd d), IsLipschitzDomain W →
    ∃ Ω₁ : Set (Config d), E.P Ω₁ᶜ = 0 ∧ ∀ η ∈ Ω₁, ∀ nk : ℕ → ℕ, StrictMono nk →
      ∀ v : Rd d → ℝ,
        TendstoUniformly
          (fun k => rescaleOdo (freeOdometer η (discretize W (nk k))) (nk k)) v atTop →
        ∀ a ∈ W, ∀ (p : Rd d) (X : Matrix (Fin d) (Fin d) ℝ), X.IsSymm →
          HasSecondOrderTaylorAt v a p X → X.trace ≤ 2 * (d : ℝ) - 1 - meanEta E.P

/-- **Step (part 3): matrices of trace less than `d` are integer superharmonic** (the role of
Rossin's observation; [LPS16] Fact 3.5 and the remark after it). For a symmetric `B`
with `tr B < d` there is `u : ℤ^d → ℤ` with `Δ_{ℤ^d} u ≤ 2d - 1` and `u ≥ q_B` on `ℤ^d`. -/
def IntegerSuperharmonicOfTraceStmt : Prop :=
  ∀ (d : ℕ) (B : Matrix (Fin d) (Fin d) ℝ), B.IsSymm → B.trace < d →
    ∃ u : Site d → ℤ, (∀ x : Site d, lap u x ≤ 2 * (d : ℤ) - 1) ∧ ∀ x : Site d, qMZ B x ≤ u x

/-! ### Elementary facts -/

namespace PegdenSmartRegularity

variable {d : ℕ}

theorem pointwiseInf_empty : pointwiseInf (∅ : Set (Site d → ℤ)) = 0 := by
  funext x
  simp [pointwiseInf]

theorem lap_zero (x : Site d) : lap (0 : Site d → ℤ) x = 0 := by
  simp [lap, nbrSumZ]

/-- Outside `W_n` the free odometer satisfies `Δ_{ℤ^d} v_n ≤ 2d - 1` (also for the junk value). -/
theorem lap_freeOdometer_le_of_not_mem (hd : 1 ≤ d) (η : Site d → ℤ) {Wn : Set (Site d)}
    {z : Site d} (hz : z ∉ Wn) : lap (freeOdometer η Wn) z ≤ 2 * (d : ℤ) - 1 := by
  by_cases hne : (stabilizing (Wn.indicator η) Set.univ).Nonempty
  · have h := (mem_stabilizing_univ.1 (isLeast_freeOdometer hne).1).2 z
    rw [Set.indicator_of_notMem hz] at h
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [freeOdometer, hne, pointwiseInf_empty, lap_zero]
    have : (1 : ℤ) ≤ d := by exact_mod_cast hd
    linarith

theorem mem_discretize_iff {W : Set (Rd d)} {n : ℕ} (hn : n ≠ 0) (z : Site d) :
    z ∈ discretize W n ↔ (n : ℝ)⁻¹ • toE z ∈ W := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [discretize, Set.mem_setOf_eq]
  exact Set.mem_smul_set_iff_inv_smul_mem₀ hn' W (toE z)

theorem trace_sub_smul_one (X : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) :
    (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)).trace = X.trace - ε * d := by
  simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]

theorem isSymm_sub_smul_one {X : Matrix (Fin d) (Fin d) ℝ} (hX : X.IsSymm) (ε : ℝ) :
    (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm :=
  hX.sub ((Matrix.isSymm_one).smul ε)

end PegdenSmartRegularity

open PegdenSmartRegularity

/-! ### Parts 2 and 3 for an arbitrary limit of rescaled free odometers -/

/-- **Lemma 7.6(2)** for any uniform limit `v` of rescaled free odometers of any `η` on an open
`W`, at any `a ∉ W̄` where `v` is twice differentiable (applies to `v` and to `v'`). -/
theorem pegdenSmart_part2_of_steps (hIS : PegdenSmartIntegerSuperharmonicStmt) {d : ℕ}
    (hd : 2 ≤ d) {W : Set (Rd d)} (η : Config d) {nk : ℕ → ℕ} (hnk : StrictMono nk)
    {v : Rd d → ℝ}
    (hv : TendstoUniformly
      (fun k => rescaleOdo (freeOdometer η (discretize W (nk k))) (nk k)) v atTop)
    {a : Rd d} (ha : a ∉ closure W) {p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ} (hX : X.IsSymm)
    (hTay : HasSecondOrderTaylorAt v a p X) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : Site d → ℤ, ∀ x : Site d, lap u x ≤ 2 * (d : ℤ) - 1 ∧
      qMZ (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ (u x : ℝ) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl a ha
  set n : ℕ → ℕ := fun k => nk (k + 1) with hn_def
  have hn : StrictMono n := fun i j hij => hnk (Nat.add_lt_add_right hij 1)
  have hnpos : ∀ k, n k ≠ 0 := fun k =>
    Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le (Nat.succ_pos k) (hnk.id_le (k + 1)))
  have hv' : TendstoUniformly
      (fun k => rescaleOdo (freeOdometer η (discretize W (n k))) (n k)) v atTop := by
    rw [Metric.tendstoUniformly_iff] at hv ⊢
    exact fun e he => (tendsto_add_atTop_nat 1).eventually (hv e he)
  refine hIS d hd n hn (fun k => freeOdometer η (discretize W (n k))) v a r hr ?_
    (hv'.tendstoUniformlyOn) p X hX hTay ε hε
  intro k z hz
  apply lap_freeOdometer_le_of_not_mem (by omega)
  rw [mem_discretize_iff (hnpos k)]
  intro hW
  exact hball (Metric.mem_ball.2 (by rwa [dist_eq_norm])) (subset_closure hW)

/-- **Lemma 7.6(3)** for any uniform limit `v` of rescaled free odometers whose Hessian at `a` has
trace `< d`: `u ≥ q_{D²v(a) - εI}` holds on all of `ℤ^d` (no `o(|x|²)` term is needed). -/
theorem pegdenSmart_part3_of_trace (hTr : IntegerSuperharmonicOfTraceStmt) {d : ℕ}
    {X : Matrix (Fin d) (Fin d) ℝ} (hX : X.IsSymm) (htr : X.trace < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : Site d → ℤ, ∀ x : Site d, lap u x ≤ 2 * (d : ℤ) - 1 ∧
      qMZ (X - ε • (1 : Matrix (Fin d) (Fin d) ℝ)) x ≤ (u x : ℝ) := by
  obtain ⟨u, hu1, hu2⟩ := hTr d _ (isSymm_sub_smul_one hX ε) (by
    rw [trace_sub_smul_one]
    have : 0 ≤ ε * d := by positivity
    linarith)
  exact ⟨u, fun x => ⟨hu1 x, hu2 x⟩⟩

/-! ### The reduction -/

/-- **Lemma 7.6 from its steps.** `PegdenSmartTouchingStmt` (Prop 2.5) is a literature
input; `PegdenSmartIntegerSuperharmonicStmt` (Lemma 4.1) and
`IntegerSuperharmonicOfTraceStmt` (Rossin) are proved in
`RandomSandpile/Proofs/Sec7/PegdenSmartRegularity*.lean`. -/
theorem pegdenSmartRegularity_of_steps (hT : PegdenSmartTouchingStmt)
    (hreg : FreeOdometerLimitRegularStmt) (hnull : LipschitzDomainFrontierNullStmt)
    (htrace : FreeOdometerLimitHessianTraceStmt) (hIS : PegdenSmartIntegerSuperharmonicStmt)
    (hTr : IntegerSuperharmonicOfTraceStmt) : PegdenSmartRegularityStmt := by
  intro d hd E hHD W hW
  obtain ⟨Ω₁, hΩ₁, K, hK⟩ := hreg d hd E W hW
  obtain ⟨Ω₂, hΩ₂, htr⟩ := htrace d hd E W hW
  refine ⟨Ω₁ ∩ Ω₂, ?_, ?_⟩
  · rw [Set.compl_inter]
    exact measure_union_null hΩ₁ hΩ₂
  intro η hη η' hη' nk nk' hnk hnk' v v' hv hv' hpos
  obtain ⟨hvc, ⟨R, hR⟩, hv1, hv2⟩ := hK η hη.1 nk hnk v hv
  obtain ⟨hvc', ⟨R', hR'⟩, hv1', hv2'⟩ := hK η' hη'.1 nk' hnk' v' hv'
  set ρ : ℝ := max (max R R') 0 + 1 with hρ
  have hρpos : 0 < ρ := by positivity
  have hzero : ∀ x : Rd d, ρ - 1 ≤ ‖x‖ → v x = 0 ∧ v' x = 0 := fun x hx =>
    ⟨hR x (by simp only [hρ] at hx; linarith [le_max_left R R', le_max_left (max R R') 0]),
      hR' x (by simp only [hρ] at hx; linarith [le_max_right R R', le_max_left (max R R') 0])⟩
  set U : Set (Rd d) := Metric.ball 0 ρ with hU
  have hfront : ∀ x ∈ frontier U, v x - v' x ≤ 0 := by
    intro x hx
    rw [hU, frontier_ball 0 hρpos.ne'] at hx
    have : ‖x‖ = ρ := by simpa using hx
    obtain ⟨h1, h2⟩ := hzero x (by linarith)
    rw [h1, h2]; simp
  obtain ⟨x₀, hx₀⟩ := hpos
  have hx₀U : x₀ ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right]
    by_contra hc
    obtain ⟨h1, h2⟩ := hzero x₀ (by linarith)
    rw [h1, h2] at hx₀; exact lt_irrefl _ hx₀
  have hmeas := hT d hd U Metric.isOpen_ball Metric.isBounded_ball K v v'
    hvc.continuousOn hvc'.continuousOn (fun x _ => hv1 x trivial) (fun x _ => hv2 x trivial)
    (fun x _ => hv1' x trivial) (fun x _ => hv2' x trivial) 0 hfront ⟨x₀, hx₀U, by linarith⟩
  set S := {a : Rd d | a ∈ U ∧ 0 < v a - v' a ∧
          ∃ (p p' : Rd d) (X X' : Matrix (Fin d) (Fin d) ℝ),
            X.IsSymm ∧ X'.IsSymm ∧ HasSecondOrderTaylorAt v a p X ∧
            HasSecondOrderTaylorAt v' a p' X' ∧
            ∃ δ : ℝ, 0 < δ ∧ (-(δ • (1 : Matrix (Fin d) (Fin d) ℝ)) - (X - X')).PosDef} with hS
  have hnot : ¬ S ⊆ frontier W := by
    intro hsub
    have := measure_mono_null hsub (hnull d hd W hW)
    rw [this] at hmeas; exact lt_irrefl _ hmeas
  obtain ⟨a, haS, haW⟩ := Set.not_subset.1 hnot
  obtain ⟨-, hva, p, p', X, X', hX, hX', hT1, hT2, hδ⟩ := haS
  have hWa : a ∈ W ∨ a ∉ closure W := by
    by_cases hc : a ∈ closure W
    · left
      have : a ∈ interior W := by
        by_contra hi; exact haW ⟨hc, hi⟩
      exact interior_subset this
    · exact Or.inr hc
  refine ⟨a, p, p', X, X', hWa, by linarith, hX, hX', hT1, hT2, hδ, ?_, ?_⟩
  · intro ha ε hε
    exact pegdenSmart_part2_of_steps hIS hd η hnk hv ha hX hT1 ε hε
  · intro ha ε hε
    have htrX := htr η hη.2 nk hnk v hv a ha p X hX hT1
    have hHD' : 2 * (d : ℝ) - 1 < meanEta E.P := hHD
    obtain ⟨u, hu⟩ := pegdenSmart_part3_of_trace hTr hX
      (by have : (0 : ℝ) ≤ d := by positivity
          linarith) ε hε
    refine ⟨u, fun x => (hu x).1, fun κ hκ => ⟨0, fun x _ => ?_⟩⟩
    have := (hu x).2
    have : 0 ≤ κ * ‖toE x‖ ^ 2 := by positivity
    linarith

end RandomSandpile

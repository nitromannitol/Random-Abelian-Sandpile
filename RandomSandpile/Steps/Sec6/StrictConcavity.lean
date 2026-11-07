import RandomSandpile.Steps.Sec6.MuLipschitz
import RandomSandpile.Steps.Sec7.Flat
import RandomSandpile.Infra.ConcaveEnvelope

/-! # Lemma 6.2 (strict concavity of near-maximizers): proof steps

Carving of `StrictConcavityStmt` (Lemma 6.2, with [C2] and the proposed [C4]) along its
printed proof, as repaired in .

**What the printed proof gives.** The proof passes to a limit `φ̄` of the rescaled
concave envelopes. It shows `D²φ̄ ≤ -λ` with `λ ≍ α`, then transfers this back to `w_n`. Uniform
concavity bends the supporting plane at a contact point `x₀ ∈ B_{βn}` by `≍ α (1-β) n |y - x₀|` at
`y ∈ ∂B_n`. Since `|y - x₀| ≥ (1-β) n`, the bending is at least `≍ (1-β)² α n²`, and the Hessian
bound `|D²φ̄| ≤ Λ` shows that this order cannot be improved by the argument. So the printed proof
gives the drafted conclusion with a constant `C(β) = c (1-β)²`, not with `C` uniform in `β`.

This file contains:
* `BallCountStmt` (lattice-point counting): `|B_{βn}| / |B_n| → β^d`;
* `StrictConcavityBetaStmt`: the drafted statement with the drop `C (1-β)² α n²` in place of
  `C α n²`. It is weaker than `StrictConcavityStmt` (`strictConcavityBeta_of_strictConcavity`);
* the reduction `strictConcavityBeta_of_steps`. It derives `StrictConcavityBetaStmt` from Lemma 6.2'
  (`NearMaxBendingStmt`), the shell estimate (`ShellBoundStmt`, Lemma 5.5) and `BallCountStmt`.

**No reduction of the drafted `StrictConcavityStmt`.** The drafted constant is uniform in `β`.
No step supported by the printed proof gives it. A step "near-maximizers bend uniformly in `β`"
would make `μ(·, M)` constant to the left of every level where it is positive (E8, consistency
remark), so it is not a usable step. The drafted statement is reported as [C9 proposed]. The
recommendation is to replace Lemma 6.2 by Lemma 6.2' (`NearMaxBendingStmt`), which is exactly what
Lemma 6.3 consumes (`muLipschitz_of_steps`). The minimal alternative is `C = C(β)`, which is
`StrictConcavityBetaStmt`. -/

open MeasureTheory LatticeProb Filter
open scoped ENNReal

namespace RandomSandpile

/-- Step (lattice-point counting). For `d ≥ 1` and `β > 0`, `|B_{βn}| / |B_n| → β^d`. Both
cardinalities are `≍ ω_d (βn)^d`, `ω_d n^d` by `tendsto_card_div_pow_atTop_volume'`; the sphere is
Lebesgue-null. -/
def BallCountStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ β : ℝ, 0 < β →
    Tendsto (fun n : ℕ => ((ballZ0 (d := d) (β * n)).ncard : ℝ) / (ballZ0 (d := d) (n : ℝ)).ncard)
      atTop (nhds (β ^ d))

/-- Lemma 6.2 with a constant depending on `β`: `StrictConcavityStmt` with the drop
`C (1-β)² α n²` in place of `C α n²`. Every other part is as drafted: the conjunct
`α/2 ≤ |∂⁺(w_n, B_{βn})| / |B_{βn}|`, the contact hypothesis, and the dual half for `μ*`. -/
def StrictConcavityBetaStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
      (0 < muBar E l M →
        ∀ᵐ η ∂E.P, ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∃ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M,
            ENNReal.ofReal (muBar E l M / 2 * ((ballZ0 (d := d) (β * n)).ncard : ℝ)) ≤
                volume (⋃ x ∈ ballZ0 (β * n), supGrad w x (ballZ0 (n : ℝ))) ∧
              ∀ x₀ ∈ ballZ0 (β * n), concaveEnvelopeOn (ballZ0 (n : ℝ)) w (toE x₀) = w x₀ →
                ∀ p₀ ∈ supGrad w x₀ (ballZ0 (n : ℝ)), ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                  w y ≤ w x₀ + inner ℝ p₀ (toE y - toE x₀) -
                    C * (1 - β) ^ 2 * muBar E l M * (n : ℝ) ^ 2) ∧
      (0 < muStarBar E l M →
        ∀ᵐ η ∂E.P, ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∃ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M,
            ENNReal.ofReal (muStarBar E l M / 2 * ((ballZ0 (d := d) (β * n)).ncard : ℝ)) ≤
                volume (⋃ x ∈ ballZ0 (β * n), subGrad w x (ballZ0 (n : ℝ))) ∧
              ∀ x₀ ∈ ballZ0 (β * n), convexEnvelopeOn (ballZ0 (n : ℝ)) w (toE x₀) = w x₀ →
                ∀ p₀ ∈ subGrad w x₀ (ballZ0 (n : ℝ)), ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                  w x₀ + inner ℝ p₀ (toE y - toE x₀) +
                    C * (1 - β) ^ 2 * muStarBar E l M * (n : ℝ) ^ 2 ≤ w y)

/-- The drafted Lemma 6.2 implies its `β`-dependent form, since `(1-β)² ≤ 1`. -/
theorem strictConcavityBeta_of_strictConcavity (h : StrictConcavityStmt) :
    StrictConcavityBetaStmt := by
  intro d hd ηmin ηmax l M
  obtain ⟨C, hC, hCE⟩ := h d hd ηmin ηmax l M
  refine ⟨C, hC, fun E hmin hmax => ⟨fun hα => ?_, fun hα => ?_⟩⟩
  · filter_upwards [(hCE E hmin hmax).1 hα] with η hη
    intro β hβ0 hβ1
    obtain ⟨n₀, hn₀⟩ := hη β hβ0 hβ1
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨w, hw, h1, h2⟩ := hn₀ n hn
    refine ⟨w, hw, h1, fun x₀ hx₀ hc p₀ hp₀ y hy => (h2 x₀ hx₀ hc p₀ hp₀ y hy).trans ?_⟩
    have : (1 - β) ^ 2 ≤ 1 := by nlinarith
    have : C * (1 - β) ^ 2 * muBar E l M * (n : ℝ) ^ 2 ≤ C * muBar E l M * (n : ℝ) ^ 2 := by
      have h0 : 0 ≤ C * muBar E l M * (n : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  · filter_upwards [(hCE E hmin hmax).2 hα] with η hη
    intro β hβ0 hβ1
    obtain ⟨n₀, hn₀⟩ := hη β hβ0 hβ1
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨w, hw, h1, h2⟩ := hn₀ n hn
    refine ⟨w, hw, h1, fun x₀ hx₀ hc p₀ hp₀ y hy => le_trans ?_ (h2 x₀ hx₀ hc p₀ hp₀ y hy)⟩
    have : (1 - β) ^ 2 ≤ 1 := by nlinarith
    have : C * (1 - β) ^ 2 * muStarBar E l M * (n : ℝ) ^ 2 ≤
        C * muStarBar E l M * (n : ℝ) ^ 2 := by
      have h0 : 0 ≤ C * muStarBar E l M * (n : ℝ) ^ 2 := by positivity
      nlinarith
    linarith

namespace StrictConcavity

open MuLipschitz

variable {d : ℕ}

/-- For `x₀ ∈ B_{βn}` and `y ∈ ∂B_n`: `|y - x₀| ≥ (1-β) n`. -/
theorem sub_le_norm_sub {β : ℝ} {n : ℕ} {x₀ y : Site d} (hx₀ : x₀ ∈ ballZ0 (β * n))
    (hy : y ∈ bdry (ballZ0 (d := d) (n : ℝ))) : (1 - β) * n ≤ ‖toE y - toE x₀‖ := by
  have h1 := mem_ballZ0.1 hx₀
  have h2 := le_norm_of_mem_bdry_ballZ0 hy
  have h3 : ‖toE y‖ - ‖toE x₀‖ ≤ ‖toE y - toE x₀‖ := norm_sub_norm_le _ _
  nlinarith

/-- The linear bending of Lemma 6.2' gives the quadratic drop `c (1-β)² α n²`. -/
theorem drop_le_bend {c α β : ℝ} {n : ℕ} {x₀ y : Site d} (hc : 0 < c) (hα : 0 ≤ α)
    (hβ1 : β < 1) (hx₀ : x₀ ∈ ballZ0 (β * n)) (hy : y ∈ bdry (ballZ0 (d := d) (n : ℝ))) :
    c * (1 - β) ^ 2 * α * (n : ℝ) ^ 2 ≤ c * α * ((1 - β) * n) * ‖toE y - toE x₀‖ := by
  have h0 : 0 ≤ c * α * ((1 - β) * n) := by
    have : 0 ≤ 1 - β := by linarith
    positivity
  calc c * (1 - β) ^ 2 * α * (n : ℝ) ^ 2 = c * α * ((1 - β) * n) * ((1 - β) * n) := by ring
    _ ≤ c * α * ((1 - β) * n) * ‖toE y - toE x₀‖ :=
        mul_le_mul_of_nonneg_left (sub_le_norm_sub hx₀ hy) h0

/-- `B_n` is the union of `B_{βn}` and the shell `B_n \ B_{βn}`, at the level of supergradient
sets. -/
theorem supGradSet_subset_union (w : Site d → ℝ) (β : ℝ) (n : ℕ) :
    supGradSet w (ballZ0 (n : ℝ)) ⊆ (⋃ x ∈ ballZ0 (d := d) (β * n), supGrad w x (ballZ0 (n : ℝ))) ∪
      ⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 (β * n), supGrad w x (ballZ0 (n : ℝ)) := by
  intro p hp
  simp only [supGradSet, Set.mem_iUnion] at hp
  obtain ⟨x, hx, hp⟩ := hp
  by_cases hx' : x ∈ ballZ0 (β * n)
  · exact Or.inl (Set.mem_biUnion hx' hp)
  · exact Or.inr (Set.mem_biUnion ⟨hx, hx'⟩ hp)

/-- Dual of `supGradSet_subset_union`. -/
theorem subGradSet_subset_union (w : Site d → ℝ) (β : ℝ) (n : ℕ) :
    subGradSet w (ballZ0 (n : ℝ)) ⊆ (⋃ x ∈ ballZ0 (d := d) (β * n), subGrad w x (ballZ0 (n : ℝ))) ∪
      ⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 (β * n), subGrad w x (ballZ0 (n : ℝ)) := by
  intro p hp
  simp only [subGradSet, Set.mem_iUnion] at hp
  obtain ⟨x, hx, hp⟩ := hp
  by_cases hx' : x ∈ ballZ0 (β * n)
  · exact Or.inl (Set.mem_biUnion hx' hp)
  · exact Or.inr (Set.mem_biUnion ⟨hx, hx'⟩ hp)

/-- The spreadout conjunct of Lemma 6.2. A near-maximizer (`(α - ε) N` with `ε = α β^d / 8`) with a
small shell (`((1 - β^d) α + ε) N`) has mass `≥ (α/2) |B_{βn}|` in `B_{βn}`, once
`|B_{βn}| ≤ (3/2) β^d |B_n|`. -/
theorem half_le_inner {α β : ℝ} {n : ℕ} {S T U : ℝ≥0∞} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hcnt : ((ballZ0 (d := d) (β * n)).ncard : ℝ) ≤
      (β ^ d + β ^ d / 2) * (ballZ0 (d := d) (n : ℝ)).ncard)
    (hN : ENNReal.ofReal ((α - α * β ^ d / 8) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ S)
    (hsplit : S ≤ T + U)
    (hS : U ≤ ENNReal.ofReal (((1 - β ^ d) * α + α * β ^ d / 8) *
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) :
    ENNReal.ofReal (α / 2 * ((ballZ0 (d := d) (β * n)).ncard : ℝ)) ≤ T := by
  set N : ℝ := ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hβd : 0 < β ^ d := pow_pos hβ d
  have hnn : 0 ≤ ((1 - β ^ d) * α + α * β ^ d / 8) * N := by
    have : 0 ≤ (1 - β ^ d) * α := mul_nonneg (by linarith [pow_le_one₀ hβ.le hβ1.le (n := d)]) hα.le
    positivity
  have htot : ENNReal.ofReal ((α - α * β ^ d / 8) * N) ≤
      T + ENNReal.ofReal (((1 - β ^ d) * α + α * β ^ d / 8) * N) :=
    hN.trans (hsplit.trans (add_le_add le_rfl hS))
  calc ENNReal.ofReal (α / 2 * ((ballZ0 (d := d) (β * n)).ncard : ℝ))
      ≤ ENNReal.ofReal ((α - α * β ^ d / 8) * N - ((1 - β ^ d) * α + α * β ^ d / 8) * N) :=
        ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = ENNReal.ofReal ((α - α * β ^ d / 8) * N) -
          ENNReal.ofReal (((1 - β ^ d) * α + α * β ^ d / 8) * N) := ENNReal.ofReal_sub _ hnn
    _ ≤ T := tsub_le_iff_right.2 htot

end StrictConcavity

open MuLipschitz StrictConcavity in
/-- **Reduction for the `β`-dependent Lemma 6.2.** Lemma 6.2' (`NearMaxBendingStmt`), the shell
estimate (`ShellBoundStmt`) and lattice-point counting (`BallCountStmt`) give
`StrictConcavityBetaStmt`, with the constant `c` of Lemma 6.2'. -/
theorem strictConcavityBeta_of_steps (hbend : NearMaxBendingStmt) (hshell : ShellBoundStmt)
    (hcount : BallCountStmt) : StrictConcavityBetaStmt := by
  intro d hd ηmin ηmax l M
  obtain ⟨c, hc, hcE⟩ := hbend d hd ηmin ηmax l M
  refine ⟨c, hc, fun E hmin hmax => ⟨fun hα => ?_, fun hα => ?_⟩⟩
  · filter_upwards [(hcE E hmin hmax).1 hα, hshell d hd E l M] with η hb hsh
    intro β hβ0 hβ1
    have hβd : 0 < β ^ d := pow_pos hβ0 d
    obtain ⟨n₀, hn₀⟩ := hb (muBar E l M * β ^ d / 8) (by positivity) β hβ0 hβ1
    obtain ⟨n₁, hn₁⟩ := hsh (1 - β) (by linarith) (by linarith) (muBar E l M * β ^ d / 8)
      (by positivity)
    obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 ((hcount d (by omega) β hβ0).eventually
      (gt_mem_nhds (show β ^ d < β ^ d + β ^ d / 2 by linarith)))
    refine ⟨max (max n₀ n₁) (max n₂ 1), fun n hn => ?_⟩
    have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hn3 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    obtain ⟨w, hw, hN, hB⟩ := hn₀ n hn0
    refine ⟨w, hw, ?_, fun x₀ hx₀ _ p₀ hp₀ y hy => ?_⟩
    · have hS := (hn₁ n hn1).1 w hw
      rw [sub_sub_cancel] at hS
      have hNpos : (0 : ℝ) < (ballZ0 (d := d) (n : ℝ)).ncard := by
        exact_mod_cast ncard_ballZ0_pos hn3
      have hcnt := (div_lt_iff₀ hNpos).1 (hn₂ n hn2)
      exact half_le_inner hα hβ0 hβ1 hcnt.le hN
        ((measure_mono (supGradSet_subset_union w β n)).trans (measure_union_le _ _)) hS
    · have h1 := hB x₀ hx₀ p₀ hp₀ y hy
      have h2 := drop_le_bend (α := muBar E l M) hc hα.le hβ1 hx₀ hy
      linarith
  · filter_upwards [(hcE E hmin hmax).2 hα, hshell d hd E l M] with η hb hsh
    intro β hβ0 hβ1
    have hβd : 0 < β ^ d := pow_pos hβ0 d
    obtain ⟨n₀, hn₀⟩ := hb (muStarBar E l M * β ^ d / 8) (by positivity) β hβ0 hβ1
    obtain ⟨n₁, hn₁⟩ := hsh (1 - β) (by linarith) (by linarith) (muStarBar E l M * β ^ d / 8)
      (by positivity)
    obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 ((hcount d (by omega) β hβ0).eventually
      (gt_mem_nhds (show β ^ d < β ^ d + β ^ d / 2 by linarith)))
    refine ⟨max (max n₀ n₁) (max n₂ 1), fun n hn => ?_⟩
    have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hn3 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    obtain ⟨w, hw, hN, hB⟩ := hn₀ n hn0
    refine ⟨w, hw, ?_, fun x₀ hx₀ _ p₀ hp₀ y hy => ?_⟩
    · have hS := (hn₁ n hn1).2 w hw
      rw [sub_sub_cancel] at hS
      have hNpos : (0 : ℝ) < (ballZ0 (d := d) (n : ℝ)).ncard := by
        exact_mod_cast ncard_ballZ0_pos hn3
      have hcnt := (div_lt_iff₀ hNpos).1 (hn₂ n hn2)
      exact half_le_inner hα hβ0 hβ1 hcnt.le hN
        ((measure_mono (subGradSet_subset_union w β n)).trans (measure_union_le _ _)) hS
    · have h1 := hB x₀ hx₀ p₀ hp₀ y hy
      have h2 := drop_le_bend (α := muStarBar E l M) hc hα.le hβ1 hx₀ hy
      linarith

/-! ### Lemma 6.2' (`NearMaxBendingStmt`): decomposition along the printed limit argument

The printed proof of Lemma 6.2 splits into a probabilistic part and a deterministic
analytic core.

* `NearMaxSequenceStmt` (probabilistic; Lemma 5.5, Lemma 5.3, the restriction lemma). For a.e. `η`
  there is a sequence `w_n ∈ S(B_n, η, l, M)` with three properties:
  - the toppling is locally legal *and* stabilizing (Lemma 5.3), so `|Δ_{ℤ^d} w_n| ≤ K`;
  - it is near-maximizing, `|∂⁺(w_n, B_n)| / |B_n| → α`;
  - its Monge-Ampère mass is at most `α × volume` on every sub-ball `B_{rn}(nz)` and every centred
    annulus. These are the upper bounds of Lemma 5.5 on sub-domains, through the restriction lemma.
* `AlmostMaximalBendingStmt` (deterministic). Every sequence with these properties bends for large
  `n`, with a constant `c = c(d, K)`. Its proof is the limit argument:
  - Harnack bounds;
  - compactness of the rescaled concave envelopes;
  - weak continuity of Monge-Ampère measures (`GutierrezWeakContinuityStmt`, proposed input);
  - the limit has Monge-Ampère measure `α · Lebesgue` (upper bounds on balls, lower bounds from
    near-maximality and the annuli);
  - the `C^{1,1}` bound at contact points (`CaffarelliCabreContactStmt`), hence uniform concavity
    `D²φ̄ ≤ -α / Λ^{d-1}`;
  - transfer back to `w_n` along rays. -/

/-- Step N1 (probabilistic part of Lemma 6.2'). There is `K = K(ηmin, ηmax, l, M, d) ≥ 0` such that,
if `α = μ(l, M) > 0`, then for a.e. `η` there is a sequence
`w_n ∈ S(B_n, η, l, M) ∩ S*(B_n, η, l, M)` (the toppling is locally legal and stabilizing) with
`|Δ_{ℤ^d} w_n| ≤ K` on `B_n`, which is near-maximizing and whose supergradient mass is at most
`α r^d |B_n| + o(|B_n|)` on every sub-ball `B_{rn}(nz) ⊆ B_n` and at most
`α (1 - ρ^d) |B_n| + o(|B_n|)` on every annulus `n(B_1 \ B̄_ρ(c))`. Dually for `μ*`. -/
def NearMaxSequenceStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
      (0 < muBar E l M → ∀ᵐ η ∂E.P, ∃ w : ℕ → Site d → ℝ,
        (∀ n : ℕ, w n ∈ perturbedSub (ballZ0 (n : ℝ)) η l M ∩ perturbedSuper (ballZ0 (n : ℝ)) η l M) ∧
        (∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal ((muBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
            volume (supGradSet (w n) (ballZ0 (n : ℝ)))) ∧
        (∀ (z : Rd d) (r : ℝ), 0 < r → Metric.ball z r ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
            volume (⋃ x ∈ discretize (Metric.ball z r) n, supGrad (w n) x (ballZ0 (n : ℝ))) ≤
              ENNReal.ofReal ((muBar E l M * r ^ d + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) ∧
        (∀ (c : Rd d) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
            volume (⋃ x ∈ discretize (Metric.ball (0 : Rd d) 1 \ Metric.closedBall c ρ) n,
                supGrad (w n) x (ballZ0 (n : ℝ))) ≤
              ENNReal.ofReal ((muBar E l M * (1 - ρ ^ d) + ε) *
                ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)))) ∧
      (0 < muStarBar E l M → ∀ᵐ η ∂E.P, ∃ w : ℕ → Site d → ℝ,
        (∀ n : ℕ, w n ∈ perturbedSub (ballZ0 (n : ℝ)) η l M ∩ perturbedSuper (ballZ0 (n : ℝ)) η l M) ∧
        (∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal ((muStarBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
            volume (subGradSet (w n) (ballZ0 (n : ℝ)))) ∧
        (∀ (z : Rd d) (r : ℝ), 0 < r → Metric.ball z r ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
            volume (⋃ x ∈ discretize (Metric.ball z r) n, subGrad (w n) x (ballZ0 (n : ℝ))) ≤
              ENNReal.ofReal ((muStarBar E l M * r ^ d + ε) *
                ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) ∧
        (∀ (c : Rd d) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
            volume (⋃ x ∈ discretize (Metric.ball (0 : Rd d) 1 \ Metric.closedBall c ρ) n,
                subGrad (w n) x (ballZ0 (n : ℝ))) ≤
              ENNReal.ofReal ((muStarBar E l M * (1 - ρ ^ d) + ε) *
                ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))))

/-- Step N2 (deterministic analytic core of Lemma 6.2'). For `d ≥ 2` and `K ≥ 0` there
is `c = c(d, K) > 0` with the following property. Let `α > 0` and `w_n : ℤ^d → ℝ` satisfy:
* `|Δ_{ℤ^d} w_n| ≤ K` on `B_n`;
* `w_n` is near-maximizing at density `α`: `|∂⁺(w_n, B_n)| ≥ (α - ε)|B_n|` eventually;
* the supergradient mass is at most `α r^d |B_n| + o(|B_n|)` on every sub-ball `B_{rn}(nz)` and at
  most `α (1-ρ^d) |B_n| + o(|B_n|)` on every complement `B_1 \ B̄_ρ(c)` of a closed sub-ball.

Then for every `0 < β < 1` and all large `n`, `w_n` bends:
`w_n(y) ≤ w_n(x₀) + p₀·(y - x₀) - c α (1-β) n |y - x₀|` for `x₀ ∈ B_{βn}`,
`p₀ ∈ ∂⁺(w_n, x₀, B_n)` and `y ∈ ∂B_n`.

The mass bounds force the limit of the rescaled envelopes to have Monge-Ampère measure
`α · Lebesgue` in `B_1`; with `|D²φ̄| ≤ Λ = Λ(d, K)` this gives `D²φ̄ ≤ -α/Λ^{d-1}`, and
`c = 1/(16 Λ^{d-1})`. -/
def AlmostMaximalBendingStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 0 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 0 < α →
    ∀ w : ℕ → Site d → ℝ,
      (∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (supGradSet (w n) (ballZ0 (n : ℝ)))) →
      (∀ (z : Rd d) (r : ℝ), 0 < r → Metric.ball z r ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball z r) n, supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * r ^ d + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      (∀ (c : Rd d) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball (0 : Rd d) 1 \ Metric.closedBall c ρ) n,
              supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * (1 - ρ ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      ∀ β : ℝ, 0 < β → β < 1 → ∀ᶠ n : ℕ in atTop,
        ∀ x₀ ∈ ballZ0 (β * n), ∀ p₀ ∈ supGrad (w n) x₀ (ballZ0 (n : ℝ)),
          ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
            w n y ≤ w n x₀ + inner ℝ p₀ (toE y - toE x₀) - c * α * ((1 - β) * n) * ‖toE y - toE x₀‖

namespace NearMaxBending

variable {d : ℕ}

theorem lapR_neg (f : Site d → ℝ) (x : Site d) : lapR (fun y => -f y) x = -lapR f x := by
  simp only [lapR, nbrSum]
  rw [Finset.sum_congr rfl (fun i _ => show -f (x + unit i) + -f (x - unit i) =
    -(f (x + unit i) + f (x - unit i)) by ring), Finset.sum_neg_distrib]
  ring

/-- `p ∈ ∂⁺(-w, x, A)` iff `-p ∈ ∂⁻(w, x, A)`. -/
theorem mem_supGrad_neg_iff {w : Site d → ℝ} {x : Site d} {A : Set (Site d)} {p : Rd d} :
    p ∈ supGrad (fun y => -w y) x A ↔ -p ∈ subGrad w x A := by
  simp only [supGrad, subGrad, Set.mem_setOf_eq, inner_neg_left]
  constructor <;> intro h y hy <;> linarith [h y hy]

/-- Negation preserves Lebesgue measure on `ℝ^d`. -/
theorem volume_preimage_neg (S : Set (Rd d)) :
    volume ((fun p : Rd d => -p) ⁻¹' S) = volume S := by
  have h := Measure.addHaar_preimage_smul (volume : Measure (Rd d)) (r := -1) (by norm_num) S
  simp only [neg_smul, one_smul] at h
  rw [h, finrank_euclideanSpace_fin]
  simp

theorem volume_biUnion_supGrad_neg (w : Site d → ℝ) (A S : Set (Site d)) :
    volume (⋃ x ∈ S, supGrad (fun y => -w y) x A) = volume (⋃ x ∈ S, subGrad w x A) := by
  rw [← volume_preimage_neg]
  congr 1
  ext p
  simp only [Set.mem_iUnion, Set.mem_preimage, mem_supGrad_neg_iff, neg_neg]

end NearMaxBending

open NearMaxBending in
/-- **Reduction for Lemma 6.2'**: `NearMaxSequenceStmt` (probabilistic part) and
`AlmostMaximalBendingStmt` (deterministic core) give `NearMaxBendingStmt`, with the constant
`c(d, K)` of the core. The `μ*` half applies the core to `-w_n`. -/
theorem nearMaxBending_of_steps (hseq : NearMaxSequenceStmt) (hcore : AlmostMaximalBendingStmt) :
    NearMaxBendingStmt := by
  intro d hd ηmin ηmax l M
  obtain ⟨K, hK, hKE⟩ := hseq d hd ηmin ηmax l M
  obtain ⟨c, hc, hcore'⟩ := hcore d hd K hK
  refine ⟨c, hc, fun E hmin hmax => ⟨fun hα => ?_, fun hα => ?_⟩⟩
  · filter_upwards [(hKE E hmin hmax).1 hα] with η hη
    obtain ⟨w, hwS, hlap, hnear, hballs, hann⟩ := hη
    intro ε hε β hβ0 hβ1
    have hb := hcore' _ hα w hlap hnear hballs hann β hβ0 hβ1
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hb.and (hnear ε hε))
    exact ⟨n₀, fun n hn => ⟨w n, (hwS n).1, (hn₀ n hn).2, (hn₀ n hn).1⟩⟩
  · filter_upwards [(hKE E hmin hmax).2 hα] with η hη
    obtain ⟨w, hwS, hlap, hnear, hballs, hann⟩ := hη
    intro ε hε β hβ0 hβ1
    set v : ℕ → Site d → ℝ := fun n y => -w n y
    have hb := hcore' _ hα v
      (fun n x hx => by simp only [v, lapR_neg, abs_neg]; exact hlap n x hx)
      (fun ε hε => (hnear ε hε).mono fun n h => by
        simp only [v, supGradSet]; rw [volume_biUnion_supGrad_neg]; exact h)
      (fun z r hr hzr ε hε => (hballs z r hr hzr ε hε).mono fun n h => by
        simp only [v]; rw [volume_biUnion_supGrad_neg]; exact h)
      (fun c ρ hρ0 hcρ ε hε => (hann c ρ hρ0 hcρ ε hε).mono fun n h => by
        simp only [v]; rw [volume_biUnion_supGrad_neg]; exact h)
      β hβ0 hβ1
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hb.and (hnear ε hε))
    refine ⟨n₀, fun n hn => ⟨w n, (hwS n).2, (hn₀ n hn).2, fun x₀ hx₀ p₀ hp₀ y hy => ?_⟩⟩
    have hp : -p₀ ∈ supGrad (v n) x₀ (ballZ0 (n : ℝ)) := by
      rw [mem_supGrad_neg_iff, neg_neg]; exact hp₀
    have h := (hn₀ n hn).1 x₀ hx₀ (-p₀) hp y hy
    simp only [v, inner_neg_left] at h
    linarith

open NearMaxBending in
/-- **Reduction for Lemma 6.2' with a locally legal and stabilizing witness** (the form consumed by
Lemma 7.5, `Flat.NearMaxBendingStabilizingStmt`). Same proof as
`nearMaxBending_of_steps`: the sequence of `NearMaxSequenceStmt` already lies in
`S(B_n, η, l, M) ∩ S*(B_n, η, l, M)`. -/
theorem nearMaxBendingStabilizing_of_steps (hseq : NearMaxSequenceStmt)
    (hcore : AlmostMaximalBendingStmt) : NearMaxBendingStabilizingStmt := by
  intro d hd ηmin ηmax l M
  obtain ⟨K, hK, hKE⟩ := hseq d hd ηmin ηmax l M
  obtain ⟨c, hc, hcore'⟩ := hcore d hd K hK
  refine ⟨c, hc, fun E hmin hmax => ⟨fun hα => ?_, fun hα => ?_⟩⟩
  · filter_upwards [(hKE E hmin hmax).1 hα] with η hη
    obtain ⟨w, hwS, hlap, hnear, hballs, hann⟩ := hη
    intro ε hε β hβ0 hβ1
    have hb := hcore' _ hα w hlap hnear hballs hann β hβ0 hβ1
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hb.and (hnear ε hε))
    exact ⟨n₀, fun n hn => ⟨w n, hwS n, (hn₀ n hn).2, (hn₀ n hn).1⟩⟩
  · filter_upwards [(hKE E hmin hmax).2 hα] with η hη
    obtain ⟨w, hwS, hlap, hnear, hballs, hann⟩ := hη
    intro ε hε β hβ0 hβ1
    set v : ℕ → Site d → ℝ := fun n y => -w n y
    have hb := hcore' _ hα v
      (fun n x hx => by simp only [v, lapR_neg, abs_neg]; exact hlap n x hx)
      (fun ε hε => (hnear ε hε).mono fun n h => by
        simp only [v, supGradSet]; rw [volume_biUnion_supGrad_neg]; exact h)
      (fun z r hr hzr ε hε => (hballs z r hr hzr ε hε).mono fun n h => by
        simp only [v]; rw [volume_biUnion_supGrad_neg]; exact h)
      (fun c ρ hρ0 hcρ ε hε => (hann c ρ hρ0 hcρ ε hε).mono fun n h => by
        simp only [v]; rw [volume_biUnion_supGrad_neg]; exact h)
      β hβ0 hβ1
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hb.and (hnear ε hε))
    refine ⟨n₀, fun n hn => ⟨w n, hwS n, (hn₀ n hn).2, fun x₀ hx₀ p₀ hp₀ y hy => ?_⟩⟩
    have hp : -p₀ ∈ supGrad (v n) x₀ (ballZ0 (n : ℝ)) := by
      rw [mem_supGrad_neg_iff, neg_neg]; exact hp₀
    have h := (hn₀ n hn).1 x₀ hx₀ (-p₀) hp y hy
    simp only [v, inner_neg_left] at h
    linarith

/-! ### The deterministic core N2: the limit of rescaled envelopes and the transfer -/

/-- The normalized rescaled concave envelope of `w` at the contact datum `(x₀, p)`:
`X ↦ (Γ_w(nX) - w(x₀) - p · (nX - x₀)) / n²`, where `Γ_w = concaveEnvelopeOn B_n w` (
`φ̄_n` after the normalization `Γ(x₀) = 0`, `p₀ = 0`, made). -/
noncomputable def rescaledEnvelope {d : ℕ} (w : Site d → ℝ) (n : ℕ) (x₀ : Site d) (p : Rd d)
    (X : Rd d) : ℝ :=
  (concaveEnvelopeOn (ballZ0 (n : ℝ)) w ((n : ℝ) • X) - w x₀ -
    inner ℝ p ((n : ℝ) • X - toE x₀)) / (n : ℝ) ^ 2

/-- Step N2a (the limit object). Under the hypotheses of `AlmostMaximalBendingStmt`
there is `κ = κ(d, K) > 0` with the following property. Take contact data `x₀(k) ∈ B_{β m_k}` and
`p(k) ∈ ∂⁺(w_{m_k}, x₀(k), B_{m_k})` along any subsequence `m_k`. A further subsequence of the
normalized rescaled envelopes converges uniformly on every `B̄_δ`, `δ < 1`, to a limit `V`. The
rescaled contact points converge to some `z`, and `V` is uniformly concave at `z`:
`V(Y) ≤ -(κα/2)|Y - z|²` on `B_1`.

This is the analytic content of the printed proof ("Plan for N2"):
* the Harnack chain bounds the envelopes on each `B_δ`;
* compactness;
* the limit has Monge-Ampère measure `α · Lebesgue` (weak continuity, `GutierrezWeakContinuityStmt`);
* the `C^{1,1}` bound `Λ = Λ(d, K)` at contact points (`CaffarelliCabreContactStmt`), with the contact
  set of full measure;
* uniform concavity `D²V ≤ -α/Λ^{d-1}` (Alexandrov second differentiability, `AlexandrovStmt`).

Since `V ≤ 0 = V(z)`, uniform concavity at `z` is the inequality stated. -/
def RescaledEnvelopeLimitStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 0 ≤ K → ∃ κ : ℝ, 0 < κ ∧ ∀ α : ℝ, 0 < α →
    ∀ w : ℕ → Site d → ℝ,
      (∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (supGradSet (w n) (ballZ0 (n : ℝ)))) →
      (∀ (z : Rd d) (r : ℝ), 0 < r → Metric.ball z r ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball z r) n, supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * r ^ d + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      (∀ (c : Rd d) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball (0 : Rd d) 1 \ Metric.closedBall c ρ) n,
              supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * (1 - ρ ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      ∀ β : ℝ, 0 < β → β < 1 → ∀ m : ℕ → ℕ, StrictMono m →
      ∀ (x₀ : ℕ → Site d) (p : ℕ → Rd d), (∀ k, x₀ k ∈ ballZ0 (β * m k)) →
        (∀ k, p k ∈ supGrad (w (m k)) (x₀ k) (ballZ0 (m k : ℝ))) →
        ∃ (φ : ℕ → ℕ) (V : Rd d → ℝ) (z : Rd d), StrictMono φ ∧
          Tendsto (fun k => ((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k))) atTop (nhds z) ∧
          (∀ δ : ℝ, δ < 1 → TendstoUniformlyOn
            (fun k => rescaledEnvelope (w (m (φ k))) (m (φ k)) (x₀ (φ k)) (p (φ k))) V atTop
            (Metric.closedBall 0 δ)) ∧
          ∀ Y ∈ Metric.ball (0 : Rd d) 1, V Y ≤ -(κ * α / 2) * ‖Y - z‖ ^ 2

namespace AlmostMaximalBending

open MuLipschitz StrictConcavity

variable {d : ℕ}

/-- The transfer along a ray. Let `x₀ ∈ B_{βn}` be a contact point with slope `p`, let
`y ∈ ∂B_n`, and let `X = (x₀ + t(y - x₀))/n` with `t |y - x₀| = (1-β)n/2`. If the rescaled envelope
satisfies `V_n(X) ≤ -μ (1-β)²`, then the gap at `y` is at least `2 μ (1-β) n |y - x₀|`. -/
theorem gap_ge_of_rescaled {w : Site d → ℝ} {n : ℕ} (hn : 1 ≤ n) {β μ : ℝ} (hβ1 : β < 1)
    {x₀ y : Site d} (hx₀ : x₀ ∈ ballZ0 (β * n)) {p : Rd d}
    (hp : p ∈ supGrad w x₀ (ballZ0 (n : ℝ))) (hy : y ∈ bdry (ballZ0 (d := d) (n : ℝ)))
    (hV : rescaledEnvelope w n x₀ p ((n : ℝ)⁻¹ • (toE x₀ + ((1 - β) * n / 2 /
      ‖toE y - toE x₀‖) • (toE y - toE x₀))) ≤ -μ * (1 - β) ^ 2) :
    2 * μ * (1 - β) * n * ‖toE y - toE x₀‖ ≤ w x₀ + inner ℝ p (toE y - toE x₀) - w y := by
  have hA := ballZ0_finite (d := d) (n : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hxA : x₀ ∈ ballZ0 (d := d) (n : ℝ) := by
    have h1 := mem_ballZ0.1 hx₀
    have h2 : ‖toE x₀‖ < n := by
      have := norm_nonneg (toE x₀); nlinarith
    exact mem_ballZ0.2 h2
  have hxc : x₀ ∈ dClosure (ballZ0 (d := d) (n : ℝ)) := Or.inl hxA
  have hyc : y ∈ dClosure (ballZ0 (d := d) (n : ℝ)) := Or.inr hy
  set D := ‖toE y - toE x₀‖ with hD
  have hDge : (1 - β) * n ≤ D := sub_le_norm_sub hx₀ hy
  have hDpos : 0 < D := lt_of_lt_of_le (by nlinarith) hDge
  set t := (1 - β) * n / 2 / D with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hDpos]; nlinarith
  have htD : t * D = (1 - β) * n / 2 := by rw [ht]; field_simp
  -- concavity of the envelope on the segment `[x₀, y]`
  have hconc := (concaveOn_concaveEnvelopeOn (w := w) hA).2 (toE_mem_convexHull_dClosure hxc)
    (toE_mem_convexHull_dClosure hyc) (sub_nonneg.2 ht1) ht0 (by ring)
  rw [concaveEnvelopeOn_eq_of_mem_supGrad hA hxc hp] at hconc
  simp only [smul_eq_mul] at hconc
  have hwy := le_concaveEnvelopeOn (w := w) hA hyc
  have hpoint : (n : ℝ) • ((n : ℝ)⁻¹ • (toE x₀ + t • (toE y - toE x₀))) =
      (1 - t) • toE x₀ + t • toE y := by
    rw [smul_smul, mul_inv_cancel₀ hn0.ne', one_smul, smul_sub, sub_smul, one_smul]
    abel
  unfold rescaledEnvelope at hV
  rw [hpoint, div_le_iff₀ (by positivity)] at hV
  have hin : inner ℝ p ((1 - t) • toE x₀ + t • toE y - toE x₀) = t * inner ℝ p (toE y - toE x₀) := by
    rw [show (1 - t) • toE x₀ + t • toE y - toE x₀ = t • (toE y - toE x₀) by
      rw [smul_sub, sub_smul, one_smul]; abel, inner_smul_right]
  rw [hin] at hV
  -- `t (w x₀ + p·(y - x₀) - w y) ≥ μ (1-β)² n²`
  have hkey : μ * (1 - β) ^ 2 * (n : ℝ) ^ 2 ≤
      t * (w x₀ + inner ℝ p (toE y - toE x₀) - w y) := by
    have : t * w y ≤ t * concaveEnvelopeOn (ballZ0 (n : ℝ)) w (toE y) :=
      mul_le_mul_of_nonneg_left hwy ht0
    nlinarith
  -- divide by `t = (1-β)n/(2D)`
  have htpos : 0 < t := div_pos (div_pos (mul_pos (by linarith) hn0) two_pos) hDpos
  have hgap : μ * (1 - β) ^ 2 * (n : ℝ) ^ 2 / t ≤ w x₀ + inner ℝ p (toE y - toE x₀) - w y := by
    rw [div_le_iff₀ htpos]; linarith
  have heq : μ * (1 - β) ^ 2 * (n : ℝ) ^ 2 / t = 2 * μ * (1 - β) * n * D := by
    have h1β : (1 - β) ≠ 0 := by linarith
    rw [ht]; field_simp
  linarith

end AlmostMaximalBending

open MuLipschitz StrictConcavity AlmostMaximalBending in
/-- **Reduction of the deterministic core N2** to the limit object `RescaledEnvelopeLimitStmt`,
with `c = κ/16`. Suppose the bending fails for infinitely many `n`. Extract the violating contact
data and pass to the limit along a further subsequence. At the point `X` of the segment
`[x₀, y]` at distance `(1-β)n/2` from `x₀`, the limit gives `V_n(X) ≤ -(κα/16)(1-β)²` for large `n`.
The transfer along the ray (`gap_ge_of_rescaled`) then gives the bending with `2c`. -/
theorem almostMaximalBending_of_limit (hlim : RescaledEnvelopeLimitStmt) :
    AlmostMaximalBendingStmt := by
  intro d hd K hK
  obtain ⟨κ, hκ, hlim'⟩ := hlim d hd K hK
  refine ⟨κ / 16, by positivity, fun α hα w hlap hnear hballs hann β hβ0 hβ1 => ?_⟩
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨m, hm, hmP⟩ := Filter.extraction_of_frequently_atTop hcon
  simp only [not_forall, not_le, exists_prop] at hmP
  choose x₀ hx₀ p hp y hy hviol using hmP
  obtain ⟨φ, V, z, hφ, hz, hconv, hconc⟩ := hlim' α hα w hlap hnear hballs hann β hβ0 hβ1 m hm
    x₀ p hx₀ hp
  set δ := (1 + β) / 2 with hδ
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  have h1β : 0 < 1 - β := by linarith
  set ε := κ * α * (1 - β) ^ 2 / 128 with hε
  have hεpos : 0 < ε := by positivity
  have e1 := Metric.tendstoUniformlyOn_iff.1 (hconv δ hδ1) ε hεpos
  have e2 := (Metric.tendsto_atTop.1 hz) ((1 - β) / 8) (by positivity)
  obtain ⟨k₂, hk₂⟩ := e2
  obtain ⟨k, hk⟩ := (e1.and (eventually_ge_atTop (max k₂ 1))).exists
  obtain ⟨hk1, hkge⟩ := hk
  set n := m (φ k)
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) hkge)
    ((hφ.id_le k).trans (hm.id_le (φ k)))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hzk := hk₂ k (le_trans (le_max_left _ _) hkge)
  set a := toE (x₀ (φ k))
  set b := toE (y (φ k))
  set D := ‖b - a‖
  have hDge : (1 - β) * n ≤ D := sub_le_norm_sub (hx₀ (φ k)) (hy (φ k))
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDge
  set t := (1 - β) * n / 2 / D
  set X := (n : ℝ)⁻¹ • (a + t • (b - a))
  have htD : t * D = (1 - β) * n / 2 := by simp only [t]; field_simp
  have ht0 : 0 ≤ t := by positivity
  -- `X ∈ B̄_δ` and `|X - z| ≥ 3(1-β)/8`
  have hXa : ‖X - (n : ℝ)⁻¹ • a‖ = (1 - β) / 2 := by
    simp only [X]
    rw [← smul_sub, add_sub_cancel_left, norm_smul, norm_smul, norm_inv, Real.norm_natCast,
      Real.norm_of_nonneg ht0]
    rw [show (n : ℝ)⁻¹ * (t * D) = (1 - β) / 2 by rw [htD]; field_simp]
  have ha : ‖(n : ℝ)⁻¹ • a‖ < β := by
    have := mem_ballZ0.1 (hx₀ (φ k))
    rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hn0]
    linarith
  have hXδ : X ∈ Metric.closedBall (0 : Rd d) δ := by
    rw [mem_closedBall_zero_iff]
    calc ‖X‖ = ‖(X - (n : ℝ)⁻¹ • a) + (n : ℝ)⁻¹ • a‖ := by rw [sub_add_cancel]
      _ ≤ ‖X - (n : ℝ)⁻¹ • a‖ + ‖(n : ℝ)⁻¹ • a‖ := norm_add_le _ _
      _ ≤ δ := by rw [hXa, hδ]; linarith
  have hXz : 3 * (1 - β) / 8 ≤ ‖X - z‖ := by
    have h1 : ‖X - (n : ℝ)⁻¹ • a‖ ≤ ‖X - z‖ + ‖(n : ℝ)⁻¹ • a - z‖ := by
      calc ‖X - (n : ℝ)⁻¹ • a‖ = ‖(X - z) - ((n : ℝ)⁻¹ • a - z)‖ := by congr 1; abel
        _ ≤ ‖X - z‖ + ‖(n : ℝ)⁻¹ • a - z‖ := norm_sub_le _ _
    rw [hXa] at h1
    have h2 : ‖(n : ℝ)⁻¹ • a - z‖ < (1 - β) / 8 := by rw [← dist_eq_norm]; exact hzk
    linarith
  -- the rescaled envelope at `X`
  have hVX : V X ≤ -(κ * α / 2) * ‖X - z‖ ^ 2 :=
    hconc X (Metric.closedBall_subset_ball hδ1 hXδ)
  have hclose := hk1 X hXδ
  rw [Real.dist_eq] at hclose
  have hVk : rescaledEnvelope (w n) n (x₀ (φ k)) (p (φ k)) X ≤
      -(κ / 16 * α) * (1 - β) ^ 2 := by
    have hsq : (3 * (1 - β) / 8) ^ 2 ≤ ‖X - z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hXz 2
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ κ * α / 2)
    have hcl := (abs_lt.1 hclose).1
    rw [hε] at hcl
    linarith
  have hgap := gap_ge_of_rescaled hn1 hβ1 (hx₀ (φ k)) (hp (φ k)) (hy (φ k))
    (μ := κ / 16 * α) hVk
  have hv := hviol (φ k)
  have hc0 : 0 ≤ κ / 16 * α * ((1 - β) * n) * D := by positivity
  nlinarith

/-- Step N2a-1 (compactness). Along any subsequence
of contact data `x₀(k) ∈ B_{β m_k}`, `p(k) ∈ ∂⁺(w_{m_k}, x₀(k), B_{m_k})`, a further subsequence of
the normalized rescaled envelopes converges uniformly on every `B̄_δ`, `δ < 1`, and the rescaled
contact points converge. Proof plan:
* Harnack chain (`BoxHarnackBddLapStmt`) for `f = w(x₀) + p·(· - x₀) - w ≥ 0`, `f(x₀) = 0`,
  `|Δ_{ℤ^d} f| ≤ K`, giving `-C(β, δ) ≤ V_n ≤ 0` on `B_δ`;
* concavity, giving equi-Lipschitz bounds on `B_δ`;
* Arzelà-Ascoli, with a diagonal argument over `δ_j ↑ 1`. -/
def EnvelopeCompactnessStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 0 ≤ K → ∀ w : ℕ → Site d → ℝ,
    (∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K) →
    ∀ β : ℝ, 0 < β → β < 1 → ∀ m : ℕ → ℕ, StrictMono m →
    ∀ (x₀ : ℕ → Site d) (p : ℕ → Rd d), (∀ k, x₀ k ∈ ballZ0 (β * m k)) →
      (∀ k, p k ∈ supGrad (w (m k)) (x₀ k) (ballZ0 (m k : ℝ))) →
      ∃ (φ : ℕ → ℕ) (V : Rd d → ℝ) (z : Rd d), StrictMono φ ∧
        Tendsto (fun k => ((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k))) atTop (nhds z) ∧
        ∀ δ : ℝ, δ < 1 → TendstoUniformlyOn
          (fun k => rescaledEnvelope (w (m (φ k))) (m (φ k)) (x₀ (φ k)) (p (φ k))) V atTop
          (Metric.closedBall 0 δ)

/-- Step N2a-2 (the limit is uniformly concave). There is `κ = κ(d, K) > 0` with the
following property. Under the hypotheses of `AlmostMaximalBendingStmt`, every locally uniform limit
`V` of normalized rescaled envelopes along contact data satisfies `V(Y) ≤ -(κα/2)|Y - z|²` on `B_1`,
where `z` is the limit of the rescaled contact points.

Content ("Plan for N2", items 3-5):
* the Monge-Ampère measure of `V` is `α · Lebesgue` on `B_1`: discrete-to-continuum
  identification for the polyhedral envelopes, plus `GutierrezWeakContinuityStmt`;
* it is supported on the contact set of the limit of `w_n(n·)/n²`;
* the `C^{1,1}` bound at contact points (`CaffarelliCabreContactStmt`);
* uniform concavity (`AlexandrovStmt`). -/
def LimitUniformConcavityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 0 ≤ K → ∃ κ : ℝ, 0 < κ ∧ ∀ α : ℝ, 0 < α →
    ∀ w : ℕ → Site d → ℝ,
      (∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (supGradSet (w n) (ballZ0 (n : ℝ)))) →
      (∀ (z : Rd d) (r : ℝ), 0 < r → Metric.ball z r ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball z r) n, supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * r ^ d + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      (∀ (c : Rd d) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball (0 : Rd d) 1 \ Metric.closedBall c ρ) n,
              supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * (1 - ρ ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      ∀ β : ℝ, 0 < β → β < 1 → ∀ m : ℕ → ℕ, StrictMono m →
      ∀ (x₀ : ℕ → Site d) (p : ℕ → Rd d), (∀ k, x₀ k ∈ ballZ0 (β * m k)) →
        (∀ k, p k ∈ supGrad (w (m k)) (x₀ k) (ballZ0 (m k : ℝ))) →
        ∀ (φ : ℕ → ℕ) (V : Rd d → ℝ) (z : Rd d), StrictMono φ →
          Tendsto (fun k => ((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k))) atTop (nhds z) →
          (∀ δ : ℝ, δ < 1 → TendstoUniformlyOn
            (fun k => rescaledEnvelope (w (m (φ k))) (m (φ k)) (x₀ (φ k)) (p (φ k))) V atTop
            (Metric.closedBall 0 δ)) →
          ∀ Y ∈ Metric.ball (0 : Rd d) 1, V Y ≤ -(κ * α / 2) * ‖Y - z‖ ^ 2

/-- **Reduction of the limit object**: compactness (`EnvelopeCompactnessStmt`) and uniform concavity
of limits (`LimitUniformConcavityStmt`) give `RescaledEnvelopeLimitStmt`. -/
theorem rescaledEnvelopeLimit_of_steps (hcpt : EnvelopeCompactnessStmt)
    (hconc : LimitUniformConcavityStmt) : RescaledEnvelopeLimitStmt := by
  intro d hd K hK
  obtain ⟨κ, hκ, hconc'⟩ := hconc d hd K hK
  refine ⟨κ, hκ, fun α hα w hlap hnear hballs hann β hβ0 hβ1 m hm x₀ p hx₀ hp => ?_⟩
  obtain ⟨φ, V, z, hφ, hz, hconv⟩ := hcpt d hd K hK w hlap β hβ0 hβ1 m hm x₀ p hx₀ hp
  exact ⟨φ, V, z, hφ, hz, hconv,
    hconc' α hα w hlap hnear hballs hann β hβ0 hβ1 m hm x₀ p hx₀ hp φ V z hφ hz hconv⟩

/-! ### Carving of `LimitUniformConcavityStmt` (no literature input)

The limit `V` is concave and `C^{1,1}` (two-sided paraboloid bounds), and its slope image has mass
`≥ α |K|` on closed sub-balls `K`. Elementary real analysis then gives uniform concavity:
* Rademacher and the area formula give `|det D∇V| ≥ α` a.e.;
* `second_derivative_symmetric` gives symmetry;
* the eigenvalues lie in `[-2Λ, 0]`, so `D²V ≤ -α/(2Λ)^{d-1}`;
* integration along segments.

The discrete Harnack quadratic bound replaces the `C^{1,1}` estimate of Caffarelli-Cabré, and reverse
Fatou for slope sets replaces the weak continuity of Monge-Ampère measures. -/

/-- The normal mapping of `V` over `K`, relative to `B_1`: the slopes `q` of affine functions
touching `V` from above on `B_1` at a point of `K`. -/
def slopeSet {d : ℕ} (V : Rd d → ℝ) (K : Set (Rd d)) : Set (Rd d) :=
  {q | ∃ X ∈ K, ∀ Y ∈ Metric.ball (0 : Rd d) 1, V Y ≤ V X + inner ℝ q (Y - X)}

/-- Step L2-0. A limit of normalized rescaled envelopes is concave on `B_1`, nonpositive, and
vanishes at the limit `z` of the rescaled contact points. -/
def LimitBasicStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 0 ≤ K → ∀ α : ℝ, 0 < α →
    ∀ w : ℕ → Site d → ℝ,
      (∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (supGradSet (w n) (ballZ0 (n : ℝ)))) →
      (∀ (z : Rd d) (r : ℝ), 0 < r → Metric.ball z r ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball z r) n, supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * r ^ d + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      (∀ (c : Rd d) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball (0 : Rd d) 1 \ Metric.closedBall c ρ) n,
              supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * (1 - ρ ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      ∀ β : ℝ, 0 < β → β < 1 → ∀ m : ℕ → ℕ, StrictMono m →
      ∀ (x₀ : ℕ → Site d) (p : ℕ → Rd d), (∀ k, x₀ k ∈ ballZ0 (β * m k)) →
        (∀ k, p k ∈ supGrad (w (m k)) (x₀ k) (ballZ0 (m k : ℝ))) →
        ∀ (φ : ℕ → ℕ) (V : Rd d → ℝ) (z : Rd d), StrictMono φ →
          Tendsto (fun k => ((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k))) atTop (nhds z) →
          (∀ δ : ℝ, δ < 1 → TendstoUniformlyOn
            (fun k => rescaledEnvelope (w (m (φ k))) (m (φ k)) (x₀ (φ k)) (p (φ k))) V atTop
            (Metric.closedBall 0 δ)) →
          ConcaveOn ℝ (Metric.ball (0 : Rd d) 1) V ∧
            (∀ Y ∈ Metric.ball (0 : Rd d) 1, V Y ≤ 0) ∧ V z = 0

/-- Step L2-A (`C^{1,1}` from the discrete Harnack quadratic bound). There is
`Λ = Λ(d, K) ≥ 0`, uniform in `δ`, such that on every `B̄_δ` the limit is touched from below by
paraboloids of opening `Λ` at scale `r₀(δ)`. Contact points of `w_n` carry the discrete bound
(`HarnackQuadraticStmt`). Limit contact points are dense, since each sub-ball carries mass `≥ α|K|`,
and the bound is closed under limits. -/
def LimitSemiconvexStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 0 ≤ K → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ α : ℝ, 0 < α →
    ∀ w : ℕ → Site d → ℝ,
      (∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (supGradSet (w n) (ballZ0 (n : ℝ)))) →
      (∀ (z : Rd d) (r : ℝ), 0 < r → Metric.ball z r ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball z r) n, supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * r ^ d + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      (∀ (c : Rd d) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball (0 : Rd d) 1 \ Metric.closedBall c ρ) n,
              supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * (1 - ρ ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      ∀ β : ℝ, 0 < β → β < 1 → ∀ m : ℕ → ℕ, StrictMono m →
      ∀ (x₀ : ℕ → Site d) (p : ℕ → Rd d), (∀ k, x₀ k ∈ ballZ0 (β * m k)) →
        (∀ k, p k ∈ supGrad (w (m k)) (x₀ k) (ballZ0 (m k : ℝ))) →
        ∀ (φ : ℕ → ℕ) (V : Rd d → ℝ) (z : Rd d), StrictMono φ →
          Tendsto (fun k => ((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k))) atTop (nhds z) →
          (∀ δ : ℝ, δ < 1 → TendstoUniformlyOn
            (fun k => rescaledEnvelope (w (m (φ k))) (m (φ k)) (x₀ (φ k)) (p (φ k))) V atTop
            (Metric.closedBall 0 δ)) →
          ∀ δ : ℝ, δ < 1 → ∃ r₀ : ℝ, 0 < r₀ ∧
            ∀ X ∈ Metric.closedBall (0 : Rd d) δ, ∀ q : Rd d,
              (∀ Y ∈ Metric.ball (0 : Rd d) 1, V Y ≤ V X + inner ℝ q (Y - X)) →
              ∀ Y ∈ Metric.ball X r₀, V X + inner ℝ q (Y - X) - Λ * ‖Y - X‖ ^ 2 ≤ V Y

/-- Step L2-B (slope mass of the limit). For every closed sub-ball `K ⊆ B_1`,
`|slopes of V over K| ≥ α |K|`. The discrete mass of `nK` is at least `α |K| n^d (1 - o(1))`, by
near-maximality and the bound on the complement `B_1 \ K`. The rescaled discrete slopes are
supergradients of `V_n`, and every limit point of them is a slope of `V` over `K`; reverse Fatou
for sets concludes. -/
def LimitSlopeMassStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ K : ℝ, 0 ≤ K → ∀ α : ℝ, 0 < α →
    ∀ w : ℕ → Site d → ℝ,
      (∀ n : ℕ, ∀ x ∈ ballZ0 (d := d) (n : ℝ), |lapR (w n) x| ≤ K) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
          volume (supGradSet (w n) (ballZ0 (n : ℝ)))) →
      (∀ (z : Rd d) (r : ℝ), 0 < r → Metric.ball z r ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball z r) n, supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * r ^ d + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      (∀ (c : Rd d) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ Metric.ball 0 1 → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop,
          volume (⋃ x ∈ discretize (Metric.ball (0 : Rd d) 1 \ Metric.closedBall c ρ) n,
              supGrad (w n) x (ballZ0 (n : ℝ))) ≤
            ENNReal.ofReal ((α * (1 - ρ ^ d) + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) →
      ∀ β : ℝ, 0 < β → β < 1 → ∀ m : ℕ → ℕ, StrictMono m →
      ∀ (x₀ : ℕ → Site d) (p : ℕ → Rd d), (∀ k, x₀ k ∈ ballZ0 (β * m k)) →
        (∀ k, p k ∈ supGrad (w (m k)) (x₀ k) (ballZ0 (m k : ℝ))) →
        ∀ (φ : ℕ → ℕ) (V : Rd d → ℝ) (z : Rd d), StrictMono φ →
          Tendsto (fun k => ((m (φ k) : ℝ))⁻¹ • toE (x₀ (φ k))) atTop (nhds z) →
          (∀ δ : ℝ, δ < 1 → TendstoUniformlyOn
            (fun k => rescaledEnvelope (w (m (φ k))) (m (φ k)) (x₀ (φ k)) (p (φ k))) V atTop
            (Metric.closedBall 0 δ)) →
          ∀ (c : Rd d) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Metric.ball 0 1 →
            ENNReal.ofReal α * volume (Metric.closedBall c r) ≤
              volume (slopeSet V (Metric.closedBall c r))

/-- Step L2-C (pure real analysis). Let `V` be concave on `B_1`, touched from below by paraboloids
of opening `Λ` locally uniformly on every `B̄_δ`, with slope mass `≥ α |K|` on closed sub-balls. Then
`V` is uniformly concave with modulus `κα`, `κ = κ(d, Λ)`. Route: `V` is `C^{1,1}`; Rademacher and
the area formula give `|det D∇V| ≥ α` a.e.; `second_derivative_symmetric` gives symmetry; then
eigenvalue bounds and integration along segments. -/
def ConcaveUniformConcavityStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ Λ : ℝ, 0 ≤ Λ → ∃ κ : ℝ, 0 < κ ∧ ∀ α : ℝ, 0 < α → ∀ V : Rd d → ℝ,
    ConcaveOn ℝ (Metric.ball (0 : Rd d) 1) V →
    (∀ δ : ℝ, δ < 1 → ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ X ∈ Metric.closedBall (0 : Rd d) δ, ∀ q : Rd d,
        (∀ Y ∈ Metric.ball (0 : Rd d) 1, V Y ≤ V X + inner ℝ q (Y - X)) →
        ∀ Y ∈ Metric.ball X r₀, V X + inner ℝ q (Y - X) - Λ * ‖Y - X‖ ^ 2 ≤ V Y) →
    (∀ (c : Rd d) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Metric.ball 0 1 →
      ENNReal.ofReal α * volume (Metric.closedBall c r) ≤
        volume (slopeSet V (Metric.closedBall c r))) →
    ∀ X ∈ Metric.ball (0 : Rd d) 1, ∀ q : Rd d,
      (∀ Y ∈ Metric.ball (0 : Rd d) 1, V Y ≤ V X + inner ℝ q (Y - X)) →
      ∀ Y ∈ Metric.ball (0 : Rd d) 1, V Y ≤ V X + inner ℝ q (Y - X) - (κ * α / 2) * ‖Y - X‖ ^ 2

/-- **Reduction of `LimitUniformConcavityStmt`** to L2-0, L2-A, L2-B and L2-C. Apply L2-C at
`X = z` with slope `0`: `V ≤ 0 = V(z)`, so `0` touches `V` from above at `z`. -/
theorem limitUniformConcavity_of_steps (h0 : LimitBasicStmt) (hA : LimitSemiconvexStmt)
    (hB : LimitSlopeMassStmt) (hC : ConcaveUniformConcavityStmt) : LimitUniformConcavityStmt := by
  intro d hd K hK
  obtain ⟨Λ, hΛ, hA'⟩ := hA d hd K hK
  obtain ⟨κ, hκ, hC'⟩ := hC d hd Λ hΛ
  refine ⟨κ, hκ, fun α hα w hlap hnear hballs hann β hβ0 hβ1 m hm x₀ p hx₀ hp φ V z hφ hz
    hconv Y hY => ?_⟩
  obtain ⟨hconc, hle, hz0⟩ :=
    h0 d hd K hK α hα w hlap hnear hballs hann β hβ0 hβ1 m hm x₀ p hx₀ hp φ V z hφ hz hconv
  have hzb : z ∈ Metric.ball (0 : Rd d) 1 := by
    have hzc : z ∈ Metric.closedBall (0 : Rd d) β := by
      refine Metric.isClosed_closedBall.mem_of_tendsto hz (Eventually.of_forall fun k => ?_)
      have hk := hx₀ (φ k)
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_natCast]
      have h1 : ‖toE (x₀ (φ k))‖ < β * (m (φ k) : ℝ) := MuLipschitz.mem_ballZ0.1 hk
      have hm0 : (0 : ℝ) < m (φ k) := by
        by_contra h; rw [not_lt] at h
        have : β * (m (φ k) : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ0.le h
        linarith [norm_nonneg (toE (x₀ (φ k)))]
      rw [inv_mul_le_iff₀ hm0]; linarith
    exact Metric.closedBall_subset_ball hβ1 hzc
  have hsup : ∀ Y ∈ Metric.ball (0 : Rd d) 1, V Y ≤ V z + inner ℝ (0 : Rd d) (Y - z) := by
    intro Y hY; rw [hz0, inner_zero_left, add_zero]; exact hle Y hY
  have := hC' α hα V hconc
    (hA' α hα w hlap hnear hballs hann β hβ0 hβ1 m hm x₀ p hx₀ hp φ V z hφ hz hconv)
    (hB d hd K hK α hα w hlap hnear hballs hann β hβ0 hβ1 m hm x₀ p hx₀ hp φ V z hφ hz hconv)
    z hzb 0 hsup Y hY
  simp only [hz0, inner_zero_left, zero_add] at this
  linarith

end RandomSandpile

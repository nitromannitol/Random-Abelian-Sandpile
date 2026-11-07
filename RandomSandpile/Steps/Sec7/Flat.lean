import RandomSandpile.Draft.Section7
import RandomSandpile.Steps.Sec6.MuLipschitz

/-! # Lemma 7.5 (`flat`): proof steps

The proof of Lemma 7.5 (`FlatStmt`), decomposed into step statements, and the reduction
`flat_of_steps` concluding exactly `FlatStmt` from them.

The printed argument. Let `l = l_M`, so `μ(l, M) = μ*(l, M) =: α ≥ 0` (Lemma 6.4(3)). If `α > 0`,
pick `u, v ∈ 𝓛(η, B_n) ∩ 𝒮(η, B_n)` such that `u - q` (resp. `v - q`), `q = q_l + q_M`, has a
supergradient `p₀` at some `x₀ ∈ B_{βn}` (resp. a subgradient `p₀*` at some `x₀* ∈ B_{βn}`) and
bends by `≍ α n²` on `∂B_n` (Lemma 6.2, with Lemma 5.1 and the even convergence of `μ`). The gaps
`g_u = (u - q)(x₀) + p₀ · (· - x₀) - (u - q) ≥ 0` and `g_v = (v - q) - (v - q)(x₀*) - p₀* · (· - x₀*) ≥ 0`
on `B̄_n` vanish at `x₀`, `x₀*` and have bounded Laplacian, so the Harnack inequality (Prop 5.2) gives
`(g_u + g_v)(0) ≤ C β² n²`. On the other side, `g_u + g_v = v - u - P · (·) + const` with
`P = p₀* - p₀`, and the comparison principle of Prop 3.3 for the stable recurrent
sandpile `Δ w + η` (Prop 3.2, Lemma 7.4, Prop 3.4), with the integer harmonic rounding of `P · x`,
gives `(g_u + g_v)(0) ≥ inf_{∂A} (g_u + g_v) - O(n) ≳ α n²`. Contradiction for `β` small.

Steps.
* `NearMaxBendingStabilizingStmt` (input; what the proof of Lemma 6.2 gives). It is
  Lemma 6.2' (`NearMaxBendingStmt`, the E8 form of Lemma 6.2) with the witness in
  `S(B_n, η, l, M) ∩ S*(B_n, η, l, M)`, i.e. `w_n = h - q_l - q_M` with `h` locally legal *and*
  stabilizing. The printed proof of Lemma 6.2 makes this assumption explicitly ("In light of Lemma
  5.1, we can assume `w_n ∈ S ∩ S*`") and so does the proof of Lemma 7.5.
  It is needed: the Harnack step requires `|Δ_{ℤ^d} w_n| ≤ C` near `x₀`, which fails for a merely
  locally legal `u` (its final configuration is unbounded above) and for a merely stabilizing `v`.
  Lemma 5.1 alone does not transfer the bending of Lemma 6.2 from `u` to its legal stabilization
  `h`: the inclusion `∂⁺(u, A) ⊆ ∂⁺(h, A)` does not keep the contact points in `B_{βn}`.
  `nearMaxBending_of_stabilizing` shows that this step implies `NearMaxBendingStmt`.
* `ShellBoundStmt` (Lemma 5.5 on the annulus `B_1 \ B̄_β`, `Steps/Sec6/MuLipschitz.lean`). With the
  near-maximizing property it gives the even convergence of `μ` over the unit ball
  ([AS14c] Lemma 3.2): `w_n` has supergradient mass `≥ (β^d α / 2) |B_n|` at the points
  of `B_{βn}` (`exists_mem_supGrad_of_mass`).
* `NoOppositeBendingStmt` (deterministic;): for `β`, `ε` small and `n` large, no
  pair `u, v ∈ S(B_n) ∩ S*(B_n)` bends in opposite directions by `c n²` on `∂B_n` from contact points
  in `B_{βn}`, when every legal stabilizing `w` with `w = 0` on `∂B_n` satisfies `w ≥ 1` on
  `B_{(1-ε)n}` (the conclusion of Lemma 7.4). Proved in `Proofs/Sec7/Flat.lean` from Props 3.1,
  3.2, 3.3, 3.4 and 5.2 and a barrier argument.
* Lemma 7.4 (`OdometerLowerBoundStmt`) and Lemma 6.4(3) (`EffectiveOperatorBasicStmt`, attainment
  of `l_M`) enter as Draft statements.

Issue N9 is resolved without strengthening Lemma 6.2: is applied on
`A = B_{(1-ε)n}`, and the drop on `∂A` follows from the drop on `∂B_n` by the minimum principle
applied to `g_u - λ |x|² / (2d)`, which is superharmonic in `B_n` (`|Δ g_u| ≤ λ`). The loss
`λ ((n+1)² - (1-ε)² n²) / (2d) ≤ λ (2 ε n² + 2n + 1) / (2d)` is small for `ε` small.
The constant of Lemma 6.2' degenerates only as `β → 1`; here `β ≤ 1/2`, and on `∂B_n`
`(1-β) n |y - x₀| ≥ n² / 4`.

Reading. `B_r = ballZ0 r`, `∂B_n = bdry (ballZ0 n)`. The near-maximizing property is stated against
the deterministic limit, as in `NearMaxBendingStmt`. -/

open MeasureTheory LatticeProb Filter
open scoped ENNReal

namespace RandomSandpile

/-- Step 1 (Lemma 6.2' with a legal stabilizing witness; the proof of Lemma 6.2, with
Lemma 5.1). There is `c = c(ηmin, ηmax, l, M, d) > 0`
such that, if `α := μ(l, M) > 0`, then for a.e. `η`, every `ε > 0` and every `0 < β < 1`, for all
large `n` some `w_n ∈ S(B_n, η, l, M) ∩ S*(B_n, η, l, M)` is near-maximizing,
`|∂⁺(w_n, B_n)| ≥ (α - ε) |B_n|`, and bends: for `x₀ ∈ B_{βn}`, `p₀ ∈ ∂⁺(w_n, x₀, B_n)` and
`y ∈ ∂B_n`, `w_n(y) ≤ w_n(x₀) + p₀ · (y - x₀) - c α (1-β) n |y - x₀|`. Dually for `μ*`, with
`∂⁻` and the reversed inequality. -/
def NearMaxBendingStabilizingStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
    ∃ c : ℝ, 0 < c ∧ ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
      (0 < muBar E l M →
        ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∃ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M ∩ perturbedSuper (ballZ0 (n : ℝ)) η l M,
            ENNReal.ofReal ((muBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
                volume (supGradSet w (ballZ0 (n : ℝ))) ∧
              ∀ x₀ ∈ ballZ0 (β * n), ∀ p₀ ∈ supGrad w x₀ (ballZ0 (n : ℝ)),
                ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                  w y ≤ w x₀ + inner ℝ p₀ (toE y - toE x₀) -
                    c * muBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖) ∧
      (0 < muStarBar E l M →
        ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∃ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M ∩ perturbedSuper (ballZ0 (n : ℝ)) η l M,
            ENNReal.ofReal ((muStarBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
                volume (subGradSet w (ballZ0 (n : ℝ))) ∧
              ∀ x₀ ∈ ballZ0 (β * n), ∀ p₀ ∈ subGrad w x₀ (ballZ0 (n : ℝ)),
                ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                  w x₀ + inner ℝ p₀ (toE y - toE x₀) +
                    c * muStarBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖ ≤ w y)

/-- Step 2 (deterministic;). Given `c > 0` and bounds `ηmin ≤ η ≤ ηmax`, there are
`0 < β ≤ 1/2`, `0 < ε < 1` and `n₀` such that for `n ≥ n₀` the following configuration is
impossible: every `w ∈ 𝓛(η, B_n) ∩ 𝒮(η, B_n)` with `w = 0` on `∂B_n` is `≥ 1` on `B_{(1-ε)n}`;
`u, v ∈ S(B_n, η, l, M) ∩ S*(B_n, η, l, M)`; `p₀ ∈ ∂⁺(u, x₀, B_n)` and `p₀* ∈ ∂⁻(v, x₀*, B_n)` with
`x₀, x₀* ∈ B_{βn}`; and on `∂B_n`, `u ≤ u(x₀) + p₀ · (· - x₀) - c n²` and
`v ≥ v(x₀*) + p₀* · (· - x₀*) + c n²`. -/
def NoOppositeBendingStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ), 0 < c →
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 2 ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ η : Site d → ℤ, (∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) →
      (∀ w ∈ locLegal η (ballZ0 (n : ℝ)) ∩ stabilizing η (ballZ0 (n : ℝ)),
          (∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)), w y = 0) →
          ∀ x ∈ ballZ0 (d := d) ((1 - ε) * n), 1 ≤ w x) →
      ∀ u ∈ perturbedSub (ballZ0 (n : ℝ)) η l M ∩ perturbedSuper (ballZ0 (n : ℝ)) η l M,
      ∀ v ∈ perturbedSub (ballZ0 (n : ℝ)) η l M ∩ perturbedSuper (ballZ0 (n : ℝ)) η l M,
      ∀ x₀ ∈ ballZ0 (d := d) (β * n), ∀ p₀ ∈ supGrad u x₀ (ballZ0 (n : ℝ)),
      ∀ x₀' ∈ ballZ0 (d := d) (β * n), ∀ p₀' ∈ subGrad v x₀' (ballZ0 (n : ℝ)),
      (∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
          u y ≤ u x₀ + inner ℝ p₀ (toE y - toE x₀) - c * (n : ℝ) ^ 2) →
      (∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
          v x₀' + inner ℝ p₀' (toE y - toE x₀') + c * (n : ℝ) ^ 2 ≤ v y) →
      False

namespace Flat

variable {d : ℕ}

/-- The legal stabilizing form of Lemma 6.2' implies Lemma 6.2' (`NearMaxBendingStmt`):
`S ∩ S* ⊆ S` and `S ∩ S* ⊆ S*`. -/
theorem nearMaxBending_of_stabilizing (h : NearMaxBendingStabilizingStmt) :
    NearMaxBendingStmt := by
  intro d hd ηmin ηmax l M
  obtain ⟨c, hc, hE⟩ := h d hd ηmin ηmax l M
  refine ⟨c, hc, fun E h1 h2 => ⟨fun hα => ?_, fun hα => ?_⟩⟩
  · filter_upwards [(hE E h1 h2).1 hα] with η hη ε hε β hβ0 hβ1
    obtain ⟨n₀, hn₀⟩ := hη ε hε β hβ0 hβ1
    exact ⟨n₀, fun n hn => let ⟨w, hw, hw'⟩ := hn₀ n hn; ⟨w, hw.1, hw'⟩⟩
  · filter_upwards [(hE E h1 h2).2 hα] with η hη ε hε β hβ0 hβ1
    obtain ⟨n₀, hn₀⟩ := hη ε hε β hβ0 hβ1
    exact ⟨n₀, fun n hn => let ⟨w, hw, hw'⟩ := hn₀ n hn; ⟨w, hw.2, hw'⟩⟩

/-- Even convergence (the localization of the supergradient mass): if `|∂⁺(w, B)| ≥ a` and the
supergradients at the points of `B \ B'` have measure `≤ b < a`, then some `x ∈ B'` carries a
supergradient. -/
theorem exists_mem_supGrad_of_mass {B B' : Set (Site d)} {w : Site d → ℝ} {a b : ℝ}
    (hb : 0 ≤ b) (hab : b < a) (hN : ENNReal.ofReal a ≤ volume (supGradSet w B))
    (hS : volume (⋃ x ∈ B \ B', supGrad w x B) ≤ ENNReal.ofReal b) :
    ∃ x ∈ B', (supGrad w x B).Nonempty := by
  by_contra hne
  simp only [not_exists, not_and, Set.not_nonempty_iff_eq_empty] at hne
  have hsub : supGradSet w B ⊆ ⋃ x ∈ B \ B', supGrad w x B := by
    intro p hp
    simp only [supGradSet, Set.mem_iUnion] at hp ⊢
    obtain ⟨x, hx, hpx⟩ := hp
    by_cases hx' : x ∈ B'
    · rw [hne x hx'] at hpx; exact absurd hpx (Set.notMem_empty _)
    · exact ⟨x, ⟨hx, hx'⟩, hpx⟩
  have := (hN.trans (measure_mono hsub)).trans hS
  rw [ENNReal.ofReal_le_ofReal_iff hb] at this
  linarith

/-- The dual of `exists_mem_supGrad_of_mass` for subgradients. -/
theorem exists_mem_subGrad_of_mass {B B' : Set (Site d)} {w : Site d → ℝ} {a b : ℝ}
    (hb : 0 ≤ b) (hab : b < a) (hN : ENNReal.ofReal a ≤ volume (subGradSet w B))
    (hS : volume (⋃ x ∈ B \ B', subGrad w x B) ≤ ENNReal.ofReal b) :
    ∃ x ∈ B', (subGrad w x B).Nonempty := by
  by_contra hne
  simp only [not_exists, not_and, Set.not_nonempty_iff_eq_empty] at hne
  have hsub : subGradSet w B ⊆ ⋃ x ∈ B \ B', subGrad w x B := by
    intro p hp
    simp only [subGradSet, Set.mem_iUnion] at hp ⊢
    obtain ⟨x, hx, hpx⟩ := hp
    by_cases hx' : x ∈ B'
    · rw [hne x hx'] at hpx; exact absurd hpx (Set.notMem_empty _)
    · exact ⟨x, ⟨hx, hx'⟩, hpx⟩
  have := (hN.trans (measure_mono hsub)).trans hS
  rw [ENNReal.ofReal_le_ofReal_iff hb] at this
  linarith

/-- On `∂B_n`, seen from `x₀ ∈ B_{βn}` with `β ≤ 1/2`, the bending of Lemma 6.2' is at least
`n² / 4` times `c α`: `(1-β) n |y - x₀| ≥ n² / 4`. -/
theorem quarter_le_bend {n : ℕ} {β : ℝ} (hβ : β ≤ 1 / 2) {x₀ y : Site d}
    (hx₀ : x₀ ∈ ballZ0 (β * n)) (hy : y ∈ bdry (ballZ0 (d := d) (n : ℝ))) :
    (n : ℝ) ^ 2 / 4 ≤ (1 - β) * n * ‖toE y - toE x₀‖ := by
  have h1 := MuLipschitz.le_norm_of_mem_bdry_ballZ0 hy
  have h2 := MuLipschitz.mem_ballZ0.1 hx₀
  have h3 : ‖toE y‖ - ‖toE x₀‖ ≤ ‖toE y - toE x₀‖ := norm_sub_norm_le _ _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : (n : ℝ) / 2 ≤ ‖toE y - toE x₀‖ := by nlinarith
  have h5 : (n : ℝ) / 2 ≤ (1 - β) * n := by nlinarith
  calc (n : ℝ) ^ 2 / 4 = (n / 2) * (n / 2) := by ring
    _ ≤ ((1 - β) * n) * ‖toE y - toE x₀‖ :=
        mul_le_mul h5 h4 (by positivity) (by nlinarith)

end Flat

open Flat in
/-- **Lemma 7.5** (`flat`) from its steps: `μ(l_M, M) = μ*(l_M, M) = 0`. -/
theorem flat_of_steps (hbend : NearMaxBendingStabilizingStmt) (hshell : ShellBoundStmt)
    (hlow : OdometerLowerBoundStmt) (heff : EffectiveOperatorBasicStmt)
    (hcomp : NoOppositeBendingStmt) : FlatStmt := by
  intro d hd E hE M hM
  obtain ⟨_, _, hC⟩ := heff d hd E.ηmin E.ηmax
  have hEq : muBar E (effOp E M) M = muStarBar E (effOp E M) M :=
    ((hC E rfl rfl M M hM hM).2.2).1
  set l := effOp E M with hl
  have h0 : 0 ≤ muBar E l M := ENNReal.toReal_nonneg
  rcases h0.lt_or_eq with hpos | hzero
  swap
  · exact ⟨hzero.symm, by rw [← hEq]; exact hzero.symm⟩
  exfalso
  have hpos' : 0 < muStarBar E l M := hEq ▸ hpos
  set α := muBar E l M with hα
  obtain ⟨c, hc, hcE⟩ := hbend d hd E.ηmin E.ηmax l M
  obtain ⟨hsub, hsup⟩ := hcE E rfl rfl
  have hc0 : 0 < c * α / 4 := by positivity
  obtain ⟨β, hβ0, hβ, ε, hε0, -, n₁, hn₁⟩ := hcomp d hd E.ηmin E.ηmax l M (c * α / 4) hc0
  have hβ1 : β < 1 := by linarith
  set δ := β ^ d * α / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  obtain ⟨η, h1, h2, h3, h4, h5⟩ := ((hsub hpos).and ((hsup hpos').and
    ((hshell d hd E l M).and ((hlow d hd E hE).and hbdd)))).exists
  obtain ⟨na, hna⟩ := h1 δ hδ0 β hβ0 hβ1
  obtain ⟨nb, hnb⟩ := h2 δ hδ0 β hβ0 hβ1
  obtain ⟨nc, hnc⟩ := h3 (1 - β) (by linarith) (by linarith) δ hδ0
  obtain ⟨ne, hne⟩ := h4 ε hε0
  set n := max (max n₁ (max na nb)) (max nc (max ne 1)) with hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨u, hu, hNu, hBu⟩ := hna n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _))
  obtain ⟨v, hv, hNv, hBv⟩ := hnb n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _))
  obtain ⟨hSu, hSv⟩ := hnc n (le_trans (le_max_left _ _) (le_max_right _ _))
  have hlowN := (hne n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _))).2
  have hsimp : 1 - (1 - β) = β := sub_sub_cancel 1 β
  rw [hsimp] at hSu hSv
  have hN : (0 : ℝ) < ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
    exact_mod_cast MuLipschitz.ncard_ballZ0_pos hn1
  have hβd : β ^ d ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  -- the even convergence: contact points in `B_{βn}`
  obtain ⟨x₀, hx₀, p₀, hp₀⟩ := exists_mem_supGrad_of_mass (B' := ballZ0 (β * n))
    (a := (α - δ) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))
    (b := ((1 - β ^ d) * α + δ) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))
    (by have : 0 ≤ (1 - β ^ d) * α := mul_nonneg (by linarith) hpos.le; positivity)
    (by apply mul_lt_mul_of_pos_right _ hN; rw [hδ]; nlinarith)
    hNu (hSu u hu.1)
  obtain ⟨x₀', hx₀', p₀', hp₀'⟩ := exists_mem_subGrad_of_mass (B' := ballZ0 (β * n))
    (a := (α - δ) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))
    (b := ((1 - β ^ d) * α + δ) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))
    (by have : 0 ≤ (1 - β ^ d) * α := mul_nonneg (by linarith) hpos.le; positivity)
    (by apply mul_lt_mul_of_pos_right _ hN; rw [hδ]; nlinarith)
    (by rw [hEq]; exact hNv) (by rw [← hEq] at hSv; exact hSv v hv.2)
  refine hn₁ n (le_trans (le_max_left _ _) (le_max_left _ _)) η h5 hlowN u hu v hv x₀ hx₀ p₀ hp₀
    x₀' hx₀' p₀' hp₀' (fun y hy => ?_) (fun y hy => ?_)
  · have hb := hBu x₀ hx₀ p₀ hp₀ y hy
    have hq := quarter_le_bend hβ hx₀ hy
    have hcα : 0 ≤ c * α := by positivity
    have : c * α / 4 * (n : ℝ) ^ 2 ≤ c * α * ((1 - β) * n) * ‖toE y - toE x₀‖ := by
      calc c * α / 4 * (n : ℝ) ^ 2 = c * α * ((n : ℝ) ^ 2 / 4) := by ring
        _ ≤ c * α * ((1 - β) * n * ‖toE y - toE x₀‖) := mul_le_mul_of_nonneg_left hq hcα
        _ = _ := by ring
    linarith
  · have hb := hBv x₀' hx₀' p₀' hp₀' y hy
    have hq := quarter_le_bend hβ hx₀' hy
    have hcα : 0 ≤ c * α := by positivity
    have : c * α / 4 * (n : ℝ) ^ 2 ≤ c * muStarBar E l M * ((1 - β) * n) * ‖toE y - toE x₀'‖ := by
      rw [← hEq]
      calc c * α / 4 * (n : ℝ) ^ 2 = c * α * ((n : ℝ) ^ 2 / 4) := by ring
        _ ≤ c * α * ((1 - β) * n * ‖toE y - toE x₀'‖) := mul_le_mul_of_nonneg_left hq hcα
        _ = _ := by ring
    linarith

end RandomSandpile

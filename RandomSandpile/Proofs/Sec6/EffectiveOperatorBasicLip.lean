import RandomSandpile.Proofs.Sec6.StrictConcavityFinal
import RandomSandpile.Steps.Sec6.EffectiveOperatorBasic

/-! # Lemma 6.3 with a constant uniform for `l` in bounded sets (`MuLipschitzLocStmt`)

The proof of Lemma 6.3 (`muLipschitz_of_steps`, constant `3/(2c)`) and of Lemma 6.2'
(`nearMaxBending_of_steps`, constant `c = c(d, K)` of `AlmostMaximalBendingStmt`) are per level
`l`. Their constants depend on `l` only through the Laplacian bound of the near-maximizing
sequences, which is `lapBound d ηmin ηmax l M = K₀ + |l + Tr M| ≤ K₀ + |R| + |Tr M|` for
`|l| ≤ R`. Here the two reductions are repeated with explicit constants:
* `NearMaxSequenceAt`, `NearMaxBendingAt`: the bodies of `NearMaxSequenceStmt` and
  `NearMaxBendingStmt` at a fixed level with a fixed constant;
* `nearMaxSequenceAt_lapBound`: the near-maximizing sequences of `nearMaxSequence_of_muConvergence`
  have `|Δ w_n| ≤ lapBound d ηmin ηmax l M` (they lie in `𝓛 ∩ 𝒮` minus the parabola,
  `abs_lapR_le`);
* `nearMaxBendingAt_of` (body copied from `nearMaxBending_of_steps`);
* `muLipschitzAt` (body copied from `muLipschitz_of_steps`);
* `muLipschitzLoc_of_muConvergence : MuConvergenceStmt → MuLipschitzLocStmt`. -/

open MeasureTheory LatticeProb Filter
open scoped ENNReal

namespace RandomSandpile

/-- The body of `NearMaxSequenceStmt` at the level `l` with the Laplacian bound `K`. -/
def NearMaxSequenceAt (d : ℕ) (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (K : ℝ) :
    Prop :=
  ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
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

/-- The body of `NearMaxBendingStmt` at the level `l` with the constant `c`. -/
def NearMaxBendingAt (d : ℕ) (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) :
    Prop :=
  ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
    (0 < muBar E l M →
      ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M,
          ENNReal.ofReal ((muBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
              volume (supGradSet w (ballZ0 (n : ℝ))) ∧
            ∀ x₀ ∈ ballZ0 (β * n), ∀ p₀ ∈ supGrad w x₀ (ballZ0 (n : ℝ)),
              ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                w y ≤ w x₀ + inner ℝ p₀ (toE y - toE x₀) -
                  c * muBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖) ∧
    (0 < muStarBar E l M →
      ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M,
          ENNReal.ofReal ((muStarBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
              volume (subGradSet w (ballZ0 (n : ℝ))) ∧
            ∀ x₀ ∈ ballZ0 (β * n), ∀ p₀ ∈ subGrad w x₀ (ballZ0 (n : ℝ)),
              ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                w x₀ + inner ℝ p₀ (toE y - toE x₀) +
                  c * muStarBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖ ≤ w y)

namespace MuLipschitzLoc

variable {d : ℕ}

/-- A function of `S(A) ∩ S*(A)` is `h - (q_l + q_M)` for one `h ∈ 𝓛(η, A) ∩ 𝒮(η, A)`. -/
theorem exists_mem_inter {A : Set (Site d)} {η : Site d → ℤ} {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {w : Site d → ℝ}
    (hw : w ∈ perturbedSub A η l M ∩ perturbedSuper A η l M) :
    ∃ h ∈ locLegal η A ∩ stabilizing η A, w = fun x => (h x : ℝ) - (qlZ l x + qMZ M x) := by
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.1 hw.1
  obtain ⟨v, hv, hvw⟩ := mem_perturbedSuper.1 hw.2
  have huv : u = v := by
    funext y
    have := congrFun hvw y
    simp only [sub_left_inj, Int.cast_inj] at this
    exact this
  exact ⟨u, ⟨hu, huv ▸ hv⟩, rfl⟩

/-- Monotonicity of `NearMaxSequenceAt` in the Laplacian bound. -/
theorem nearMaxSequenceAt_mono {ηmin ηmax : ℤ} {l : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {K K' : ℝ}
    (h : NearMaxSequenceAt d ηmin ηmax l M K) (hK : K ≤ K') :
    NearMaxSequenceAt d ηmin ηmax l M K' := by
  intro E hmin hmax
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · filter_upwards [(h E hmin hmax).1 hα] with η hη
    obtain ⟨w, hwS, hlap, hrest⟩ := hη
    exact ⟨w, hwS, fun n x hx => (hlap n x hx).trans hK, hrest⟩
  · filter_upwards [(h E hmin hmax).2 hα] with η hη
    obtain ⟨w, hwS, hlap, hrest⟩ := hη
    exact ⟨w, hwS, fun n x hx => (hlap n x hx).trans hK, hrest⟩

open NearMaxSequence in
/-- The near-maximizing sequences of Lemma 5.5 have `|Δ w_n| ≤ lapBound d ηmin ηmax l M`. -/
theorem nearMaxSequenceAt_lapBound (hconv : MuConvergenceStmt) (hd : 2 ≤ d) (ηmin ηmax : ℤ)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    NearMaxSequenceAt d ηmin ηmax l M (lapBound d ηmin ηmax l M) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨K, -, hKE⟩ := nearMaxSequence_of_muConvergence hconv d hd ηmin ηmax l M
  intro E hmin hmax
  have hηae : ∀ᵐ η ∂E.P, ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax := by
    rw [← hmin, ← hmax]; exact ae_all_iff.2 E.bounded
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · filter_upwards [(hKE E hmin hmax).1 hα, hηae] with η hη hb
    obtain ⟨w, hwS, -, hrest⟩ := hη
    refine ⟨w, hwS, fun n x hx => ?_, hrest⟩
    obtain ⟨h, hh, hw⟩ := exists_mem_inter (hwS n)
    rw [hw]
    exact abs_lapR_le hd1 hb hh l M hx
  · filter_upwards [(hKE E hmin hmax).2 hα, hηae] with η hη hb
    obtain ⟨w, hwS, -, hrest⟩ := hη
    refine ⟨w, hwS, fun n x hx => ?_, hrest⟩
    obtain ⟨h, hh, hw⟩ := exists_mem_inter (hwS n)
    rw [hw]
    exact abs_lapR_le hd1 hb hh l M hx

theorem lapBound_le {ηmin ηmax : ℤ} {l R : ℝ} (M : Matrix (Fin d) (Fin d) ℝ) (hl : |l| ≤ R) :
    NearMaxSequence.lapBound d ηmin ηmax l M ≤
      ((|max ηmax 0| + |2 * (d : ℤ) - 1 - ηmin| : ℤ) : ℝ) + (|R| + |M.trace|) := by
  unfold NearMaxSequence.lapBound
  have h1 := abs_add_le l M.trace
  have h2 := le_abs_self R
  linarith

open NearMaxBending in
/-- `nearMaxBending_of_steps` (Steps/Sec6/StrictConcavity.lean) with explicit constants: a
near-maximizing sequence with Laplacian bound `K` and the core constant `c` for `K` give the bending
at the level `l` with constant `c`. Body copied from `nearMaxBending_of_steps`. -/
theorem nearMaxBendingAt_of {ηmin ηmax : ℤ} {l : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {K c : ℝ}
    (hKE : NearMaxSequenceAt d ηmin ηmax l M K)
    (hcore' : ∀ α : ℝ, 0 < α → ∀ w : ℕ → Site d → ℝ,
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
            w n y ≤ w n x₀ + inner ℝ p₀ (toE y - toE x₀) -
              c * α * ((1 - β) * n) * ‖toE y - toE x₀‖) :
    NearMaxBendingAt d ηmin ηmax l M c := by
  refine fun E hmin hmax => ⟨fun hα => ?_, fun hα => ?_⟩
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

open MuLipschitz in
/-- `muLipschitz_of_steps` (Steps/Sec6/MuLipschitz.lean) with an explicit bending constant: the
bending at the level `l` with constant `c` gives Lemma 6.3 at `l` with `C = 3/(2c)`. Body copied
from `muLipschitz_of_steps`. -/
theorem muLipschitzAt (hshift : PerturbedShiftStmt) (hABP : BoundaryGapStmt)
    (hshell : ShellBoundStmt) (hd : 2 ≤ d) {ηmin ηmax : ℤ} {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} (hc : 0 < c) (hcE : NearMaxBendingAt d ηmin ηmax l M c)
    (E : RandomEnvironment d) (hmin : E.ηmin = ηmin) (hmax : E.ηmax = ηmax) (s : ℝ) (hs0 : 0 < s) :
    muBar E l M ≤ muBar E (l - s) M + s * (3 / (2 * c)) ∧
      muStarBar E l M ≤ muStarBar E (l + s) M + s * (3 / (2 * c)) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine ⟨?_, ?_⟩
  · -- `μ(l) ≤ μ(l - s) + s C`
    set α := muBar E l M with hαdef
    have hnn : 0 ≤ muBar E (l - s) M := ENNReal.toReal_nonneg
    by_cases hα : α ≤ 3 / (2 * c) * s
    · linarith
    rw [not_le] at hα
    have hαpos : 0 < α := lt_of_le_of_lt (by positivity) hα
    set τ := 3 * s / (2 * d * c * α) with hτ
    have hτpos : 0 < τ := by positivity
    have hτ1 : τ < 1 := by
      rw [hτ, div_lt_one (by positivity)]
      have : 3 / (2 * c) * s * 1 ≤ 3 / (2 * c) * s * d := by
        gcongr; exact_mod_cast hd1
      have h2 : 3 / (2 * c) * s * d < α * d := by nlinarith
      calc 3 * s = 3 / (2 * c) * s * (2 * c) := by field_simp
        _ < α * d * (2 * c) := by nlinarith
        _ = 2 * d * c * α := by ring
    have hdτα : d * τ * α = 3 / (2 * c) * s := by
      rw [hτ]; field_simp
    have hκ : ∀ n : ℕ, 3 * s * n / (2 * d) ≤ c * α * ((1 - (1 - τ)) * n) := by
      intro n
      rw [sub_sub_cancel, hτ]
      apply le_of_eq
      field_simp
    suffices h : α - 3 / (2 * c) * s ≤ muBar E (l - s) M by linarith
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ᵐ η ∂E.P, ∀ n : ℕ,
        mu (ballZ0 (n : ℝ)) η (l - s) M ≤
          ENNReal.ofReal (K * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
      refine ⟨_, (ae_all_iff.2 fun x => (E.bounded x).mono fun _ h => h.2).mono
        fun η hη n => mu_le_ncard hd1 (ballZ0_finite _) (fun x _ => hη x) (l - s) M⟩
    refine le_toReal_lintegral_limsup (K := K)
      (hK.mono fun η h => Eventually.of_forall fun n => div_ncard_le_ofReal (h n)) ?_
    filter_upwards [(hcE E hmin hmax).1 hαpos, hshell d hd E l M] with η hb hsh
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hb (ε / 2) (by positivity) (1 - τ) (by linarith) (by linarith)
    obtain ⟨n₁, hn₁⟩ := hsh τ hτpos hτ1 (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop (max (max n₀ n₁) 1)] with n hn
    have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn2 : 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨w, hw, hN, hB⟩ := hn₀ n hn0
    have hS := (hn₁ n hn1).1 w hw
    have hbern : 1 - d * τ ≤ (1 - τ) ^ d := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -τ by linarith) d
      rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
      exact this
    have hcoef : (1 - (1 - τ) ^ d) * α ≤ 3 / (2 * c) * s := by
      rw [← hdτα]; nlinarith
    have := ofReal_le_mu_sub (Cs := 3 / (2 * c) * s) hshift hABP hd1 hs0 (by positivity) (hκ n)
      hw hN hB (hS.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by rw [hαdef] at hcoef; linarith) (Nat.cast_nonneg _))))
    refine ofReal_le_div_ncard hn2 (le_trans (le_of_eq ?_) this)
    congr 1
    rw [hαdef]
    ring
  · -- `μ*(l) ≤ μ*(l + s) + s C`
    set α := muStarBar E l M with hαdef
    have hnn : 0 ≤ muStarBar E (l + s) M := ENNReal.toReal_nonneg
    by_cases hα : α ≤ 3 / (2 * c) * s
    · linarith
    rw [not_le] at hα
    have hαpos : 0 < α := lt_of_le_of_lt (by positivity) hα
    set τ := 3 * s / (2 * d * c * α) with hτ
    have hτpos : 0 < τ := by positivity
    have hτ1 : τ < 1 := by
      rw [hτ, div_lt_one (by positivity)]
      have : 3 / (2 * c) * s * 1 ≤ 3 / (2 * c) * s * d := by
        gcongr; exact_mod_cast hd1
      have h2 : 3 / (2 * c) * s * d < α * d := by nlinarith
      calc 3 * s = 3 / (2 * c) * s * (2 * c) := by field_simp
        _ < α * d * (2 * c) := by nlinarith
        _ = 2 * d * c * α := by ring
    have hdτα : d * τ * α = 3 / (2 * c) * s := by
      rw [hτ]; field_simp
    have hκ : ∀ n : ℕ, 3 * s * n / (2 * d) ≤ c * α * ((1 - (1 - τ)) * n) := by
      intro n
      rw [sub_sub_cancel, hτ]
      apply le_of_eq
      field_simp
    suffices h : α - 3 / (2 * c) * s ≤ muStarBar E (l + s) M by linarith
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ᵐ η ∂E.P, ∀ n : ℕ,
        muStar (ballZ0 (n : ℝ)) η (l + s) M ≤
          ENNReal.ofReal (K * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
      refine ⟨_, (ae_all_iff.2 fun x => (E.bounded x).mono fun _ h => h.1).mono
        fun η hη n => muStar_le_ncard hd1 (ballZ0_finite _) (fun x _ => hη x) (l + s) M⟩
    refine le_toReal_lintegral_limsup (K := K)
      (hK.mono fun η h => Eventually.of_forall fun n => div_ncard_le_ofReal (h n)) ?_
    filter_upwards [(hcE E hmin hmax).2 hαpos, hshell d hd E l M] with η hb hsh
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hb (ε / 2) (by positivity) (1 - τ) (by linarith) (by linarith)
    obtain ⟨n₁, hn₁⟩ := hsh τ hτpos hτ1 (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop (max (max n₀ n₁) 1)] with n hn
    have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn2 : 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨w, hw, hN, hB⟩ := hn₀ n hn0
    have hS := (hn₁ n hn1).2 w hw
    have hbern : 1 - d * τ ≤ (1 - τ) ^ d := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -τ by linarith) d
      rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
      exact this
    have hcoef : (1 - (1 - τ) ^ d) * α ≤ 3 / (2 * c) * s := by
      rw [← hdτα]; nlinarith
    have := ofReal_le_muStar_add (Cs := 3 / (2 * c) * s) hshift hABP hd1 hs0 (by positivity) (hκ n)
      hw hN hB (hS.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by rw [hαdef] at hcoef; linarith) (Nat.cast_nonneg _))))
    refine ofReal_le_div_ncard hn2 (le_trans (le_of_eq ?_) this)
    congr 1
    rw [hαdef]
    ring

end MuLipschitzLoc

open MuLipschitzLoc in
/-- **Lemma 6.3, locally uniform in `l`** (`MuLipschitzLocStmt`) from Lemma 5.5: for `|l| ≤ R` the
constant is `3/(2c)`, `c = c(d, K_R)` the core constant of `AlmostMaximalBendingStmt` for the
Laplacian bound `K_R = K₀ + |R| + |Tr M| ≥ lapBound d ηmin ηmax l M`. -/
theorem muLipschitzLoc_of_muConvergence (hconv : MuConvergenceStmt) : MuLipschitzLocStmt := by
  intro d hd ηmin ηmax M R
  set KR : ℝ := ((|max ηmax 0| + |2 * (d : ℤ) - 1 - ηmin| : ℤ) : ℝ) + (|R| + |M.trace|) with hKR
  have hKR0 : 0 ≤ KR := by
    have : (0 : ℤ) ≤ |max ηmax 0| + |2 * (d : ℤ) - 1 - ηmin| := by positivity
    have : (0 : ℝ) ≤ ((|max ηmax 0| + |2 * (d : ℤ) - 1 - ηmin| : ℤ) : ℝ) := by exact_mod_cast this
    positivity
  have hcore : AlmostMaximalBendingStmt :=
    almostMaximalBending_of_limit (rescaledEnvelopeLimit_of_steps envelopeCompactness
      limitUniformConcavity)
  obtain ⟨c, hc, hcore'⟩ := hcore d hd KR hKR0
  refine ⟨3 / (2 * c), by positivity, fun E hmin hmax l hl s hs0 _ => ?_⟩
  have hseq : NearMaxSequenceAt d ηmin ηmax l M KR :=
    nearMaxSequenceAt_mono (nearMaxSequenceAt_lapBound hconv hd ηmin ηmax l M) (lapBound_le M hl)
  have hbend : NearMaxBendingAt d ηmin ηmax l M c := nearMaxBendingAt_of hseq (hcore' )
  exact muLipschitzAt perturbedShift boundaryGap (shellBound_of_muConvergence hconv) hd hc hbend
    E hmin hmax s hs0

end RandomSandpile

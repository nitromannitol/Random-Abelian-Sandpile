import RandomSandpile.Draft.Section6
import RandomSandpile.Steps.Sec6.MuMonotone
import RandomSandpile.Steps.Sec6.MuLipschitz
import RandomSandpile.Proofs.Sec5.MuBounded

/-! # Carving of Lemma 6.4 (`EffectiveOperatorBasicStmt`)

`effectiveOperatorBasic_of_steps` derives the drafted statement, with `C = d`, from Lemma 6.1
(`MuMonotoneStmt`), Lemma 5.4 (the support lemmas `mu_le_ncard`, `muStar_le_ncard`, proved) and
four steps:
* `MuMatrixMonotoneStmt`: Lemma 6.1 with `q_A`, `A ≥ 0`, in place of `q_s`;
* `MuShiftStmt`: `q_{M + tI} = q_M + q_{dt}`, so `μ(l, M + tI) = μ(l + dt, M)`. Hence the
  constant of the Lipschitz bound is `d` with the normalization `q_l = l|x|²/(2d)`; the
  printed `|M - N|_2` is `d |M - N|_2` here;
* `MuLipschitzLocStmt`: Lemma 6.3 with a constant uniform for `l` in bounded sets;
* `MuPositiveStmt`: for symmetric `M` and `l` large, `μ(B_n, η, l, M) ≥ c |B_n|`.

**Why `MuLipschitzLocStmt` and not `MuLipschitzStmt`.** The definition of `F̄_η` and
Lemma 6.4(3) need the intermediate value theorem for `l ↦ μ(l, M) - μ*(l, M)`, hence continuity in
`l`. Lemma 6.3 as printed (and drafted, `C = C_{ηmin, ηmax, l, M, d}`) together with Lemma 6.1
gives only one-sided continuity: `μ(·, M)` is left-continuous and `μ*(·, M)` right-continuous at
every `l`. A jump of `μ` to the right of `l₀` is compatible with it, because the constants at
`l₀ + s` may blow up as `s → 0`. The printed proof of 6.3 gives a constant depending on `l` only
through the Laplacian bound `K(l) = K₀ + |l + Tr M|`, which is locally bounded. That is
`MuLipschitzLocStmt`, proved from Lemma 5.5 in `Proofs/Sec6/EffectiveOperatorBasicLip.lean`.
It is a proof-level gap, not a statement change.

`effOp_add_smul_one_of_isGreatest`: `F̄_η(M + tI) = F̄_η(M) - d t`. -/

open MeasureTheory LatticeProb Filter Set
open scoped ENNReal Topology Matrix

namespace RandomSandpile

/-- Step 1: Lemma 6.1 with `q_A`, `A ≥ 0`, in place of `q_s`:
`μ(B_n, η, l, M + A) ≥ μ(B_n, η, l, M)` and `μ*(B_n, η, l, M + A) ≤ μ*(B_n, η, l, M)`. -/
def MuMatrixMonotoneStmt : Prop :=
  ∀ (d : ℕ) (η : Site d → ℤ) (n : ℕ) (l : ℝ) (M A : Matrix (Fin d) (Fin d) ℝ), A.PosSemidef →
    mu (ballZ0 (n : ℝ)) η l M ≤ mu (ballZ0 (n : ℝ)) η l (M + A) ∧
      muStar (ballZ0 (n : ℝ)) η l (M + A) ≤ muStar (ballZ0 (n : ℝ)) η l M

/-- Step 2: `q_l + q_{M + tI} = q_{l + dt} + q_M`, hence
`μ(B_n, η, l, M + tI) = μ(B_n, η, l + dt, M)`, and likewise for `μ*`. -/
def MuShiftStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (η : Site d → ℤ) (n : ℕ) (l t : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
    mu (ballZ0 (n : ℝ)) η l (M + t • 1) = mu (ballZ0 (n : ℝ)) η (l + d * t) M ∧
      muStar (ballZ0 (n : ℝ)) η l (M + t • 1) = muStar (ballZ0 (n : ℝ)) η (l + d * t) M

/-- Step 3: Lemma 6.3 (with [C1]) with a constant uniform for `|l| ≤ R`. -/
def MuLipschitzLocStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin ηmax : ℤ) (M : Matrix (Fin d) (Fin d) ℝ) (R : ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
      ∀ l : ℝ, |l| ≤ R → ∀ s : ℝ, 0 < s → s < 1 →
        muBar E l M ≤ muBar E (l - s) M + s * C ∧
          muStarBar E l M ≤ muStarBar E (l + s) M + s * C

/-- Step 4 (positivity, used for `|F̄_η(M)| < ∞`): for symmetric `M` and large `l`,
`μ(B_n, η, l, M) ≥ c |B_n|`, deterministically. -/
def MuPositiveStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsSymm → ∃ l₁ c : ℝ, 0 < c ∧
    ∀ l : ℝ, l₁ ≤ l → ∀ n : ℕ, 1 ≤ n → ∀ η : Site d → ℤ,
      ENNReal.ofReal (c * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ mu (ballZ0 (n : ℝ)) η l M

namespace EffectiveOperatorBasic

open MuLipschitz

variable {d : ℕ}

theorem lintegral_mu_ne_top (hd : 1 ≤ d) (E : RandomEnvironment d) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    ∫⁻ η, limsup (fun n : ℕ => mu (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal
    ((max (((max E.ηmax 0 : ℤ) : ℝ) + l + M.trace) 0 / d) ^ d) ∂E.P) (by simp) ?_
  refine lintegral_mono_ae ((ae_all_iff.2 E.bounded).mono fun η hη => ?_)
  refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => ?_)
  exact div_ncard_le_ofReal (mu_le_ncard hd (ballZ0_finite _) (fun x _ => (hη x).2) l M)

theorem lintegral_muStar_ne_top (hd : 1 ≤ d) (E : RandomEnvironment d) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    ∫⁻ η, limsup (fun n : ℕ => muStar (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop ∂E.P ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal
    ((max ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - l - M.trace) 0 / d) ^ d) ∂E.P) (by simp) ?_
  refine lintegral_mono_ae ((ae_all_iff.2 E.bounded).mono fun η hη => ?_)
  refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => ?_)
  exact div_ncard_le_ofReal (muStar_le_ncard hd (ballZ0_finite _) (fun x _ => (hη x).1) l M)

theorem muBar_le_of (hd : 1 ≤ d) {E : RandomEnvironment d} {l l' : ℝ}
    {M M' : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ (η : Site d → ℤ) (n : ℕ), mu (ballZ0 (n : ℝ)) η l M ≤ mu (ballZ0 (n : ℝ)) η l' M') :
    muBar E l M ≤ muBar E l' M' := by
  unfold muBar
  refine ENNReal.toReal_mono (lintegral_mu_ne_top hd E l' M') (lintegral_mono fun η => ?_)
  exact limsup_le_limsup (Eventually.of_forall fun n => ENNReal.div_le_div_right (h η n) _)

theorem muStarBar_le_of (hd : 1 ≤ d) {E : RandomEnvironment d} {l l' : ℝ}
    {M M' : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ (η : Site d → ℤ) (n : ℕ),
      muStar (ballZ0 (n : ℝ)) η l M ≤ muStar (ballZ0 (n : ℝ)) η l' M') :
    muStarBar E l M ≤ muStarBar E l' M' := by
  unfold muStarBar
  refine ENNReal.toReal_mono (lintegral_muStar_ne_top hd E l' M') (lintegral_mono fun η => ?_)
  exact limsup_le_limsup (Eventually.of_forall fun n => ENNReal.div_le_div_right (h η n) _)

theorem muBar_nonneg (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    0 ≤ muBar E l M := ENNReal.toReal_nonneg

theorem muStarBar_nonneg (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    0 ≤ muStarBar E l M := ENNReal.toReal_nonneg

/-- Lemma 5.4, vanishing range of `μ`, for the deterministic limit. -/
theorem muBar_eq_zero (hd : 1 ≤ d) (E : RandomEnvironment d) {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hl : l ≤ -((max E.ηmax 0 : ℤ) : ℝ) - M.trace) :
    muBar E l M = 0 := by
  unfold muBar
  have h : ∀ᵐ η ∂E.P, limsup (fun n : ℕ => mu (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop = 0 := by
    filter_upwards [ae_all_iff.2 E.bounded] with η hη
    have h0 : ∀ n : ℕ, mu (ballZ0 (n : ℝ)) η l M = 0 := fun n => by
      refine le_antisymm ((mu_le_ncard hd (ballZ0_finite _) (fun x _ => (hη x).2) l M).trans
        (le_of_eq ?_)) bot_le
      rw [max_eq_right (by linarith), zero_div, zero_pow (by omega), zero_mul,
        ENNReal.ofReal_zero]
    simp [h0]
  rw [lintegral_congr_ae h, lintegral_zero, ENNReal.toReal_zero]

/-- Lemma 5.4, vanishing range of `μ*`, for the deterministic limit. -/
theorem muStarBar_eq_zero (hd : 1 ≤ d) (E : RandomEnvironment d) {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hl : (2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - M.trace ≤ l) :
    muStarBar E l M = 0 := by
  unfold muStarBar
  have h : ∀ᵐ η ∂E.P, limsup (fun n : ℕ => muStar (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) atTop = 0 := by
    filter_upwards [ae_all_iff.2 E.bounded] with η hη
    have h0 : ∀ n : ℕ, muStar (ballZ0 (n : ℝ)) η l M = 0 := fun n => by
      refine le_antisymm ((muStar_le_ncard hd (ballZ0_finite _) (fun x _ => (hη x).1) l M).trans
        (le_of_eq ?_)) bot_le
      rw [max_eq_right (by linarith), zero_div, zero_pow (by omega), zero_mul,
        ENNReal.ofReal_zero]
    simp [h0]
  rw [lintegral_congr_ae h, lintegral_zero, ENNReal.toReal_zero]

theorem muBar_mono (hmono : MuMonotoneStmt) (hd : 1 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) : Monotone (fun l => muBar E l M) := by
  intro a b hab
  have h := fun (η : Site d → ℤ) (n : ℕ) => (hmono d η n a (b - a) M (sub_nonneg.2 hab)).1
  simp only [add_sub_cancel] at h
  exact muBar_le_of hd h

theorem muStarBar_anti (hmono : MuMonotoneStmt) (hd : 1 ≤ d) (E : RandomEnvironment d)
    (M : Matrix (Fin d) (Fin d) ℝ) : Antitone (fun l => muStarBar E l M) := by
  intro a b hab
  have h := fun (η : Site d → ℤ) (n : ℕ) => (hmono d η n b (b - a) M (sub_nonneg.2 hab)).2
  simp only [sub_sub_cancel] at h
  exact muStarBar_le_of hd h

/-- Local Lipschitz bound of `μ(·, M)` from `MuLipschitzLocStmt` and Lemma 6.1. -/
theorem abs_muBar_sub_le (hmono : MuMonotoneStmt) (hlip : MuLipschitzLocStmt) (hd : 2 ≤ d)
    (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) (l₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℝ, |l - l₀| < 1 →
      |muBar E l M - muBar E l₀ M| ≤ C * |l - l₀| ∧
        |muStarBar E l M - muStarBar E l₀ M| ≤ C * |l - l₀| := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC, hCE⟩ := hlip d hd E.ηmin E.ηmax M (|l₀| + 1)
  refine ⟨C, hC, fun l hl => ?_⟩
  rcases lt_trichotomy l l₀ with h | h | h
  · have hs0 : 0 < l₀ - l := by linarith
    have hs1 : l₀ - l < 1 := by rw [abs_sub_comm, abs_of_pos hs0] at hl; exact hl
    obtain ⟨h1, -⟩ := hCE E rfl rfl l₀ (by linarith [le_abs_self l₀]) (l₀ - l) hs0 hs1
    rw [sub_sub_cancel] at h1
    have hm := muBar_mono hmono hd1 E M h.le
    have ha := muStarBar_anti hmono hd1 E M h.le
    simp only at hm ha
    rw [abs_of_neg (by linarith : l - l₀ < 0)]
    refine ⟨?_, ?_⟩
    · rw [abs_of_nonpos (by linarith)]; nlinarith
    · -- `μ*(l) - μ*(l₀) ≤ (l₀ - l) C`: Lemma 6.3 at the base point `l`
      have hl' : |l| ≤ |l₀| + 1 := by
        have : |l| ≤ |l - l₀| + |l₀| := by
          calc |l| = |(l - l₀) + l₀| := by rw [sub_add_cancel]
            _ ≤ |l - l₀| + |l₀| := abs_add_le _ _
        linarith
      obtain ⟨-, h3⟩ := hCE E rfl rfl l hl' (l₀ - l) hs0 hs1
      rw [add_sub_cancel] at h3
      rw [abs_of_nonneg (by linarith)]; nlinarith
  · subst h; simp
  · have hs0 : 0 < l - l₀ := by linarith
    have hs1 : l - l₀ < 1 := by rw [abs_of_pos hs0] at hl; exact hl
    have hl' : |l| ≤ |l₀| + 1 := by
      have : |l| ≤ |l - l₀| + |l₀| := by
        calc |l| = |(l - l₀) + l₀| := by rw [sub_add_cancel]
          _ ≤ |l - l₀| + |l₀| := abs_add_le _ _
      linarith
    obtain ⟨h1, -⟩ := hCE E rfl rfl l hl' (l - l₀) hs0 hs1
    rw [sub_sub_cancel] at h1
    obtain ⟨-, h2⟩ := hCE E rfl rfl l₀ (by linarith [le_abs_self l₀]) (l - l₀) hs0 hs1
    rw [add_sub_cancel] at h2
    have hm := muBar_mono hmono hd1 E M h.le
    have ha := muStarBar_anti hmono hd1 E M h.le
    simp only at hm ha
    rw [abs_of_pos hs0]
    refine ⟨?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)]; nlinarith
    · rw [abs_of_nonpos (by linarith)]; nlinarith

theorem continuous_of_local {f : ℝ → ℝ} (h : ∀ l₀ : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ l : ℝ, |l - l₀| < 1 →
    |f l - f l₀| ≤ C * |l - l₀|) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro l₀
  obtain ⟨C, hC, hloc⟩ := h l₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min 1 (ε / (C + 1)), by positivity, fun l hl => ?_⟩
  rw [Real.dist_eq] at hl ⊢
  have h1 : |l - l₀| < 1 := lt_of_lt_of_le hl (min_le_left _ _)
  have h2 : |l - l₀| < ε / (C + 1) := lt_of_lt_of_le hl (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at h2
  calc |f l - f l₀| ≤ C * |l - l₀| := hloc l h1
    _ ≤ |l - l₀| * (C + 1) := by nlinarith [abs_nonneg (l - l₀)]
    _ < ε := h2

theorem continuous_muBar (hmono : MuMonotoneStmt) (hlip : MuLipschitzLocStmt) (hd : 2 ≤ d)
    (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun l => muBar E l M) :=
  continuous_of_local fun l₀ => by
    obtain ⟨C, hC, h⟩ := abs_muBar_sub_le hmono hlip hd E M l₀
    exact ⟨C, hC, fun l hl => (h l hl).1⟩

theorem continuous_muStarBar (hmono : MuMonotoneStmt) (hlip : MuLipschitzLocStmt) (hd : 2 ≤ d)
    (E : RandomEnvironment d) (M : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun l => muStarBar E l M) :=
  continuous_of_local fun l₀ => by
    obtain ⟨C, hC, h⟩ := abs_muBar_sub_le hmono hlip hd E M l₀
    exact ⟨C, hC, fun l hl => (h l hl).2⟩

/-- Positivity of the deterministic limit `μ(l, M)` for large `l`. -/
theorem muBar_pos (hpos : MuPositiveStmt) (hd : 2 ≤ d) (E : RandomEnvironment d)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) :
    ∃ l₁ : ℝ, ∀ l : ℝ, l₁ ≤ l → 0 < muBar E l M := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨l₁, c, hc, h⟩ := hpos d hd M hM
  refine ⟨l₁, fun l hl => lt_of_lt_of_le hc ?_⟩
  unfold muBar
  refine le_toReal_lintegral_limsup (F := fun η n => mu (ballZ0 (n : ℝ)) η l M /
      ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞)) (K := (max (((max E.ηmax 0 : ℤ) : ℝ) + l + M.trace) 0 / d) ^ d)
    ((ae_all_iff.2 E.bounded).mono fun η hη => Eventually.of_forall fun n =>
      div_ncard_le_ofReal (mu_le_ncard hd1 (ballZ0_finite _) (fun x _ => (hη x).2) l M))
    (Eventually.of_forall fun η ε hε => (eventually_ge_atTop 1).mono fun n hn =>
      (ENNReal.ofReal_le_ofReal (by linarith)).trans (ofReal_le_div_ncard hn (h l hl n hn η)))

/-- `B + |B|₂ I ≥ 0` for symmetric `B`. -/
theorem posSemidef_add_smul_one {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.IsSymm) :
    (B + ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B‖ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  set t := ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B‖ with ht
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    exact hB.add (Matrix.isSymm_one.smul t)
  · set T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B
    set v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
    have h1 : star x ⬝ᵥ (B *ᵥ x) = inner ℝ v (T v) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [T, v, Matrix.toEuclideanCLM_toLp, WithLp.ofLp_toLp, star_trivial]
      exact dotProduct_comm _ _
    have h2 : star x ⬝ᵥ x = ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [v, star_trivial]
    have h3 : |inner ℝ v (T v)| ≤ t * ‖v‖ ^ 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖v‖ * ‖T v‖ ≤ ‖v‖ * (t * ‖v‖) :=
            mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _)
        _ = t * ‖v‖ ^ 2 := by ring
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, h1, h2]
    linarith [neg_abs_le (inner ℝ v (T v))]

theorem muBar_le_add (hmat : MuMatrixMonotoneStmt) (hd : 1 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    muBar E l M ≤ muBar E l (M + A) ∧ muStarBar E l (M + A) ≤ muStarBar E l M :=
  ⟨muBar_le_of hd fun η n => (hmat d η n l M A hA).1,
    muStarBar_le_of hd fun η n => (hmat d η n l M A hA).2⟩

theorem muBar_shift (hshift : MuShiftStmt) (hd : 1 ≤ d) (E : RandomEnvironment d)
    (l t : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muBar E l (M + t • 1) = muBar E (l + d * t) M ∧
      muStarBar E l (M + t • 1) = muStarBar E (l + d * t) M := by
  have h1 := fun (η : Site d → ℤ) (n : ℕ) => (hshift d hd η n l t M).1
  have h2 := fun (η : Site d → ℤ) (n : ℕ) => (hshift d hd η n l t M).2
  exact ⟨by simp only [muBar, h1], by simp only [muStarBar, h2]⟩

/-- **Lemma 6.4(3)**: the largest `l` with `μ(l, M) = μ*(l, M)` exists. -/
theorem isGreatest_muEqSet (hmono : MuMonotoneStmt) (hlip : MuLipschitzLocStmt)
    (hpos : MuPositiveStmt) (hd : 2 ≤ d) (E : RandomEnvironment d)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) :
    IsGreatest (muEqSet E M) (effOp E M) := by
  have hd1 : 1 ≤ d := by omega
  set f : ℝ → ℝ := fun l => muBar E l M - muStarBar E l M with hf
  have hfc : Continuous f :=
    (continuous_muBar hmono hlip hd E M).sub (continuous_muStarBar hmono hlip hd E M)
  have hfm : Monotone f := fun a b hab =>
    sub_le_sub (muBar_mono hmono hd1 E M hab) (muStarBar_anti hmono hd1 E M hab)
  have hset : muEqSet E M = f ⁻¹' {0} := by
    ext l; simp [muEqSet, f, sub_eq_zero]
  obtain ⟨l₁, hl₁⟩ := muBar_pos hpos hd E hM
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = -((max E.ηmax 0 : ℤ) : ℝ) - M.trace := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = max l₁ ((2 * (d : ℝ) - 1) - (E.ηmin : ℝ) - M.trace) :=
    ⟨_, rfl⟩
  have hfa : f a ≤ 0 := by
    simp only [f]
    rw [muBar_eq_zero hd1 E (le_of_eq ha)]
    linarith [muStarBar_nonneg E a M]
  have hfb : 0 < f b := by
    simp only [f]
    rw [muStarBar_eq_zero hd1 E (by rw [hb]; exact le_max_right _ _), sub_zero]
    exact hl₁ b (by rw [hb]; exact le_max_left _ _)
  have hab : a ≤ b := by
    by_contra h
    have := hfm (le_of_lt (not_le.1 h))
    linarith
  obtain ⟨l₀, -, hfl₀⟩ := intermediate_value_Icc hab hfc.continuousOn ⟨hfa, hfb.le⟩
  have hne : (muEqSet E M).Nonempty := ⟨l₀, by rw [hset]; exact hfl₀⟩
  have hbdd : BddAbove (muEqSet E M) := by
    refine ⟨b, fun l hl => ?_⟩
    rw [hset] at hl
    have hl0 : f l = 0 := hl
    by_contra h
    have := hfm (le_of_lt (not_le.1 h))
    linarith
  have hclosed : IsClosed (muEqSet E M) := by
    rw [hset]; exact isClosed_singleton.preimage hfc
  exact ⟨hclosed.csSup_mem hne hbdd, fun l hl => le_csSup hbdd hl⟩

/-- **Lemma 6.4(1)** (degenerate ellipticity), given 6.4(3) for `M` and `N`. -/
theorem effOp_anti_of_isGreatest (hmono : MuMonotoneStmt) (hmat : MuMatrixMonotoneStmt)
    (hd : 1 ≤ d) (E : RandomEnvironment d) {M N : Matrix (Fin d) (Fin d) ℝ}
    (hGM : IsGreatest (muEqSet E M) (effOp E M)) (hGN : IsGreatest (muEqSet E N) (effOp E N))
    (hNM : (N - M).PosSemidef) : effOp E N ≤ effOp E M := by
  have hNeq : M + (N - M) = N := add_sub_cancel M N
  have hle : effOp E N ∈ muEqSet E N := hGN.1
  by_contra h
  rw [not_le] at h
  set l := effOp E N
  -- `f_M(l) > 0`
  have hfM : 0 < muBar E l M - muStarBar E l M := by
    have hm := sub_le_sub (muBar_mono hmono hd E M h.le) (muStarBar_anti hmono hd E M h.le)
    simp only at hm
    have h0 : muBar E (effOp E M) M - muStarBar E (effOp E M) M = 0 := sub_eq_zero.2 hGM.1
    rw [h0] at hm
    rcases lt_or_eq_of_le hm with hlt | heq
    · exact hlt
    · exact absurd (hGM.2 (sub_eq_zero.1 heq.symm)) (not_le.2 h)
  obtain ⟨h1, h2⟩ := muBar_le_add hmat hd E l M (N - M) hNM
  rw [hNeq] at h1 h2
  have : muBar E l N = muStarBar E l N := hle
  linarith

/-- **Lemma 6.4(2)**, one direction: `F̄_η(N) ≥ F̄_η(M) - d |M - N|₂`. -/
theorem effOp_ge_sub_of_isGreatest (hmono : MuMonotoneStmt) (hmat : MuMatrixMonotoneStmt)
    (hshift : MuShiftStmt) (hd : 1 ≤ d) (E : RandomEnvironment d)
    {M N : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (hN : N.IsSymm)
    (hGM : IsGreatest (muEqSet E M) (effOp E M)) (hGN : IsGreatest (muEqSet E N) (effOp E N)) :
    effOp E M - d * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (M - N)‖ ≤ effOp E N := by
  set t := ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (M - N)‖ with ht
  set lM := effOp E M with hlM
  have hA : (M - N + t • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef :=
    posSemidef_add_smul_one (hM.sub hN)
  have hMeq : N + (M - N + t • (1 : Matrix (Fin d) (Fin d) ℝ)) = M + t • 1 := by abel
  obtain ⟨hs1, hs2⟩ := muBar_shift hshift hd E (lM - d * t) t M
  rw [sub_add_cancel] at hs1 hs2
  obtain ⟨hm1, hm2⟩ := muBar_le_add hmat hd E (lM - d * t) N _ hA
  rw [hMeq, hs1] at hm1
  rw [hMeq, hs2] at hm2
  have heq : muBar E lM M = muStarBar E lM M := hGM.1
  have hfN : muBar E (lM - d * t) N - muStarBar E (lM - d * t) N ≤ 0 := by linarith
  by_contra h
  rw [not_le] at h
  have hmon := sub_le_sub (muBar_mono hmono hd E N h.le) (muStarBar_anti hmono hd E N h.le)
  simp only at hmon
  have h0 : muBar E (effOp E N) N - muStarBar E (effOp E N) N = 0 := sub_eq_zero.2 hGN.1
  rw [h0] at hmon
  have hin : lM - d * t ∈ muEqSet E N := sub_eq_zero.1 (le_antisymm hfN hmon)
  linarith [hGN.2 hin]

/-- `F̄_η(M + tI) = F̄_η(M) - d t`, given that `F̄_η(M)` is attained. -/
theorem effOp_add_smul_one_of_isGreatest (hshift : MuShiftStmt) (hd : 1 ≤ d)
    (E : RandomEnvironment d) {M : Matrix (Fin d) (Fin d) ℝ}
    (hGM : IsGreatest (muEqSet E M) (effOp E M)) (t : ℝ) :
    effOp E (M + t • 1) = effOp E M - d * t := by
  have hmem : ∀ l, l ∈ muEqSet E (M + t • 1) ↔ l + d * t ∈ muEqSet E M := by
    intro l
    obtain ⟨h1, h2⟩ := muBar_shift hshift hd E l t M
    simp only [muEqSet, Set.mem_ofPred_eq, h1, h2]
  have hG : IsGreatest (muEqSet E (M + t • 1)) (effOp E M - d * t) := by
    refine ⟨(hmem _).2 (by rw [sub_add_cancel]; exact hGM.1), fun l hl => ?_⟩
    have := hGM.2 ((hmem l).1 hl)
    linarith
  exact hG.csSup_eq

end EffectiveOperatorBasic

open EffectiveOperatorBasic in
/-- **Reduction of Lemma 6.4** (`EffectiveOperatorBasicStmt`) with `C = d`. -/
theorem effectiveOperatorBasic_of_steps (hmono : MuMonotoneStmt) (hmat : MuMatrixMonotoneStmt)
    (hshift : MuShiftStmt) (hlip : MuLipschitzLocStmt) (hpos : MuPositiveStmt) :
    EffectiveOperatorBasicStmt := by
  intro d hd ηmin ηmax
  have hd1 : 1 ≤ d := by omega
  refine ⟨d, by exact_mod_cast (show 0 < d by omega), fun E _ _ M N hM hN => ?_⟩
  have hGM := isGreatest_muEqSet hmono hlip hpos hd E hM
  have hGN := isGreatest_muEqSet hmono hlip hpos hd E hN
  refine ⟨effOp_anti_of_isGreatest hmono hmat hd1 E hGM hGN, ?_, hGM⟩
  have h1 := effOp_ge_sub_of_isGreatest hmono hmat hshift hd1 E hM hN hGM hGN
  have h2 := effOp_ge_sub_of_isGreatest hmono hmat hshift hd1 E hN hM hGN hGM
  have hnorm : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (N - M)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (M - N)‖ := by
    rw [← neg_sub, map_neg, norm_neg]
  rw [hnorm] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

end RandomSandpile

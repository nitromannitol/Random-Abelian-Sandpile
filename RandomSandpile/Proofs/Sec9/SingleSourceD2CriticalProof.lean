import RandomSandpile.Proofs.Sec9.SingleSourceD2CriticalGeom
import RandomSandpile.Proofs.Sec6.StrictConcavityFinal
import RandomSandpile.Proofs.Sec6.MuLipschitzShell

/-!
# Theorem 9.2 in dimension two: flatness at critical matrices

`criticalFlat : CriticalFlatD2Stmt`: if `F̄(Q) = 0` and `Q` is
not positive definite, then `μ̄*(0, Q) = 0`.

Proof. Otherwise `α = μ̄(0, Q) = μ̄*(0, Q) > 0` (`isGreatest_effOp`). Lemma 6.2' with a
legal stabilizing witness (`nearMaxBendingStabilizing_of_muConvergence`, both halves) and the shell
estimate give, on `B_n`, a legal stabilizer `h` with a supporting plane `P = q_Q + affine ≥ h`
touching at `x₀ ∈ B_{βn}`, with gap `g = P - h ≥ cα n²/4` on `∂B_n`; and on `B_R`, `R = ⌊κn⌋`, a legal
stabilizer `h'` with a lower supporting plane at `z₀ ∈ B_{δR}` and gap `b ≥ cα R²/4` on `∂B_R`.
* Step A (`le_of_symmetric_bdry`, `critical_stepA`). For `y ∈ ∂B_n` near `n e`, `q_Q(e) < cα/16`,
  also `-y ∈ ∂B_n`, and `P(y) + P(-y) = 2P(0) + 2q_Q(y)` gives `P(0) ≥ cα n²/4 - q_Q(y)`. Then
  `P(z) = (P(2z) + P(0))/2 - q_Q(z)`, `P(2z) ≥ 0`, and the growth estimate (1.8) for `g` at `x₀` give
  `h ≥ 1` on `B_{κn}` (the role of (4.2)).
* Step B (`gap_le_of_recurrent`, `critical_stepB`). By the last-toppling characterization
  (Proposition 3.4) `s = η + Δh` is recurrent in `B_R`; `D = h' - h + G`, `G` the integer harmonic
  rounding of the slope difference, has `s + ΔD = η + Δh' ≤ 3`, so the recurrent minimum principle
  (1.6) gives `y ∈ ∂B_R` with `D(y) ≤ D(x₀)`; the gaps then give `cα R²/4 ≤ C (βn + δR)² + O(R)`,
  impossible for `δ`, `β` small and `R` large.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter

namespace RandomSandpile

open EffectiveOperatorBasic

namespace SingleSourceD2

/-- The growth estimate (1.8) at contact points, with constant `C` for Laplacian bound `λ`. -/
def HarnackNear (lam C : ℝ) : Prop :=
  ∀ (r : ℝ) (g : Site 2 → ℝ) (x₀ : Site 2), ‖toE x₀‖ ≤ r / 2 →
    (∀ y ∈ dClosure (ballZ0 (d := 2) r), 0 ≤ g y) → g x₀ = 0 →
    (∀ y ∈ ballZ0 (d := 2) r, |lapR g y| ≤ lam) →
    ∀ y : Site 2, ‖toE y - toE x₀‖ < r / 4 → g y ≤ C * ‖toE y - toE x₀‖ ^ 2

/-- The Laplacian bound `λ` for legal stabilizing perturbations of `q_Q` with `l = 0`. -/
def lapBound (ηmin ηmax : ℤ) (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  |(ηmin : ℝ)| + |(ηmax : ℝ)| + 2 * ((2 : ℕ) : ℝ) + |0 + Q.trace|

theorem abs_lapR_gapBelow_le {η : Site 2 → ℤ} {ηmin ηmax : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) {Q : Matrix (Fin 2) (Fin 2) ℝ} {A : Set (Site 2)}
    {h : Site 2 → ℤ} (hh : h ∈ locLegal η A ∩ stabilizing η A) (x₀ : Site 2) (p₀ : Rd 2) :
    ∀ y ∈ A, |lapR (Flat.gapBelow (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ p₀) y| ≤
      lapBound ηmin ηmax Q := fun y hy => by
  rw [Flat.lapR_gapBelow, abs_neg, lapBound]
  exact Flat.abs_lapR_perturbed_le (by norm_num) hη hh hy

theorem abs_lapR_gapAbove_le {η : Site 2 → ℤ} {ηmin ηmax : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) {Q : Matrix (Fin 2) (Fin 2) ℝ} {A : Set (Site 2)}
    {h : Site 2 → ℤ} (hh : h ∈ locLegal η A ∩ stabilizing η A) (x₀ : Site 2) (p₀ : Rd 2) :
    ∀ y ∈ A, |lapR (Flat.gapAbove (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ p₀) y| ≤
      lapBound ηmin ηmax Q := fun y hy => by
  rw [Flat.lapR_gapAbove, lapBound]
  exact Flat.abs_lapR_perturbed_le (by norm_num) hη hh hy

/-- The bending of Lemma 6.2' on `∂B_n`, seen from `x₀ ∈ B_{βn}`, `β ≤ 1/2`: the gap is
`≥ cα n²/4`. -/
theorem gapBelow_ge_of_bend {w : Site 2 → ℝ} {x₀ : Site 2} {p₀ : Rd 2} {n : ℕ} {β ca : ℝ}
    (hβ : β ≤ 1 / 2) (hca : 0 ≤ ca) (hx₀ : x₀ ∈ ballZ0 (d := 2) (β * n))
    (hb : ∀ y ∈ bdry (ballZ0 (d := 2) (n : ℝ)),
      w y ≤ w x₀ + inner ℝ p₀ (toE y - toE x₀) - ca * ((1 - β) * n) * ‖toE y - toE x₀‖) :
    ∀ y ∈ bdry (ballZ0 (d := 2) (n : ℝ)), ca * (n : ℝ) ^ 2 / 4 ≤ Flat.gapBelow w x₀ p₀ y := by
  intro y hy
  have h1 := hb y hy
  have h2 := Flat.quarter_le_bend hβ hx₀ hy
  have h3 : ca * ((n : ℝ) ^ 2 / 4) ≤ ca * ((1 - β) * n * ‖toE y - toE x₀‖) :=
    mul_le_mul_of_nonneg_left h2 hca
  have e : ca * ((1 - β) * n) * ‖toE y - toE x₀‖ = ca * ((1 - β) * n * ‖toE y - toE x₀‖) := by
    ring
  unfold Flat.gapBelow
  linarith

/-- The dual of `gapBelow_ge_of_bend`. -/
theorem gapAbove_ge_of_bend {w : Site 2 → ℝ} {x₀ : Site 2} {p₀ : Rd 2} {n : ℕ} {β ca : ℝ}
    (hβ : β ≤ 1 / 2) (hca : 0 ≤ ca) (hx₀ : x₀ ∈ ballZ0 (d := 2) (β * n))
    (hb : ∀ y ∈ bdry (ballZ0 (d := 2) (n : ℝ)),
      w x₀ + inner ℝ p₀ (toE y - toE x₀) + ca * ((1 - β) * n) * ‖toE y - toE x₀‖ ≤ w y) :
    ∀ y ∈ bdry (ballZ0 (d := 2) (n : ℝ)), ca * (n : ℝ) ^ 2 / 4 ≤ Flat.gapAbove w x₀ p₀ y := by
  intro y hy
  have h1 := hb y hy
  have h2 := Flat.quarter_le_bend hβ hx₀ hy
  have h3 : ca * ((n : ℝ) ^ 2 / 4) ≤ ca * ((1 - β) * n * ‖toE y - toE x₀‖) :=
    mul_le_mul_of_nonneg_left h2 hca
  have e : ca * ((1 - β) * n) * ‖toE y - toE x₀‖ = ca * ((1 - β) * n * ‖toE y - toE x₀‖) := by
    ring
  unfold Flat.gapAbove
  linarith

/-! ### Step A: the legal stabilizer is positive near the centre -/

/-- The plane-plus-quadratic `P = h + g` lies above the legal stabilizer `h`; symmetric boundary
points and doubling give `h(y) ≥ (a - T)/2 - |Q| |y|² - g(y)`. -/
theorem le_of_symmetric_bdry {Q : Matrix (Fin 2) (Fin 2) ℝ} {n : ℕ} {h : Site 2 → ℤ}
    (hnn : ∀ x, 0 ≤ h x) {x₀ : Site 2} {p₀ : Rd 2}
    (hp₀ : p₀ ∈ supGrad (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ (ballZ0 (n : ℝ))) {a : ℝ}
    (hbend : ∀ y ∈ bdry (ballZ0 (d := 2) (n : ℝ)),
      a ≤ Flat.gapBelow (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ p₀ y)
    {yb : Site 2} (hyb : yb ∈ bdry (ballZ0 (d := 2) (n : ℝ))) {T : ℝ} (hT : qMZ Q yb ≤ T)
    {y : Site 2} (hy : ‖toE y‖ < n / 2) :
    (a - T) / 2 - matBound Q * ‖toE y‖ ^ 2 -
      Flat.gapBelow (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ p₀ y ≤ h y := by
  set w : Site 2 → ℝ := fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x) with hw
  have hql : ∀ x : Site 2, qlZ 0 x = 0 := fun x => by simp [qlZ, ql]
  have hP : ∀ z : Site 2, (h z : ℝ) + Flat.gapBelow w x₀ p₀ z =
      w x₀ + inner ℝ p₀ (toE z) - inner ℝ p₀ (toE x₀) + qM Q (toE z) := fun z => by
    simp only [Flat.gapBelow, hw, hql, qMZ, inner_sub_right]
    ring
  have hg0 := Flat.gapBelow_nonneg hp₀
  have hb1 := hbend yb hyb
  have hb2 := hbend (-yb) (neg_mem_bdry_ballZ0 hyb)
  have e1 := hP yb
  have e2 := hP (-yb)
  rw [Flat.toE_neg, inner_neg_right, qM_neg'] at e2
  have hT' : qM Q (toE yb) ≤ T := hT
  have n1 : (0 : ℝ) ≤ h yb := by exact_mod_cast hnn yb
  have n2 : (0 : ℝ) ≤ h (-yb) := by exact_mod_cast hnn (-yb)
  have hP0 : a - T ≤ w x₀ - inner ℝ p₀ (toE x₀) := by linarith
  have hyy : y + y ∈ dClosure (ballZ0 (d := 2) (n : ℝ)) := by
    refine subset_dClosure _ (MuLipschitz.mem_ballZ0.2 ?_)
    rw [MuLipschitz.toE_add]
    calc ‖toE y + toE y‖ ≤ ‖toE y‖ + ‖toE y‖ := norm_add_le _ _
      _ < n := by linarith
  have e3 := hP (y + y)
  rw [MuLipschitz.toE_add, ← two_smul ℝ (toE y), inner_smul_right, qM_smul'] at e3
  have n3 : (0 : ℝ) ≤ h (y + y) := by exact_mod_cast hnn _
  have g3 := hg0 _ hyy
  have e4 := hP y
  have hq := qM_le Q (toE y)
  linarith

/-- **Step A.** `h ≥ 1` on `B_{κn}`. -/
theorem critical_stepA {η : Site 2 → ℤ} {ηmin ηmax : ℤ} (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax)
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {CH : ℝ} (hCH : HarnackNear (lapBound ηmin ηmax Q) CH)
    (hCH0 : 0 ≤ CH) {ca κ β : ℝ} (hca : 0 < ca) {e : Rd 2} (he : ‖e‖ = 1)
    (heθ : qM Q e < ca / 16) (hκ8 : κ ≤ 1 / 8) (hβκ : β ≤ κ)
    (hκS : (matBound Q + 4 * CH) * κ ^ 2 ≤ ca / 64) {n : ℕ}
    (hn : 64 * (132 * matBound Q + 2) / ca ≤ n) (hn2 : 2 ≤ n) {h : Site 2 → ℤ}
    (hh : h ∈ locLegal η (ballZ0 (n : ℝ)) ∩ stabilizing η (ballZ0 (n : ℝ))) {x₀ : Site 2}
    (hx₀ : x₀ ∈ ballZ0 (d := 2) (β * n)) {p₀ : Rd 2}
    (hp₀ : p₀ ∈ supGrad (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ (ballZ0 (n : ℝ)))
    (hbend : ∀ y ∈ bdry (ballZ0 (d := 2) (n : ℝ)),
      ca * (n : ℝ) ^ 2 / 4 ≤ Flat.gapBelow (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ p₀ y) :
    ∀ y ∈ ballZ0 (d := 2) (κ * n), 1 ≤ h y := by
  intro y hy
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hS0 := matBound_nonneg Q
  have hy' : ‖toE y‖ < κ * n := MuLipschitz.mem_ballZ0.1 hy
  have hx₀' : ‖toE x₀‖ < β * n := MuLipschitz.mem_ballZ0.1 hx₀
  have hβn : β * n ≤ κ * n := mul_le_mul_of_nonneg_right hβκ (by linarith)
  have hκn : κ * n ≤ n / 8 := by nlinarith
  -- a boundary point near `n e`
  obtain ⟨yb, hyb, hybd⟩ := exists_bdry_near hn2 he
  have hqb : qMZ Q yb ≤ ca / 16 * (n : ℝ) ^ 2 + 132 * matBound Q * n := by
    have e1 : toE yb = (n : ℝ) • e + (toE yb - (n : ℝ) • e) := by abel
    have h1 := qM_add_le Q ((n : ℝ) • e) (toE yb - (n : ℝ) • e)
    rw [← e1, qM_smul', norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg n)] at h1
    have hr0 := norm_nonneg (toE yb - (n : ℝ) • e)
    have hr2 : (n : ℝ) * ‖toE yb - (n : ℝ) • e‖ + ‖toE yb - (n : ℝ) • e‖ ^ 2 ≤ 11 * n + 121 := by
      nlinarith
    have h2 : matBound Q * ((n : ℝ) * ‖toE yb - (n : ℝ) • e‖ + ‖toE yb - (n : ℝ) • e‖ ^ 2) ≤
        matBound Q * (11 * n + 121) := mul_le_mul_of_nonneg_left hr2 hS0
    have h3 : (n : ℝ) ^ 2 * qM Q e ≤ (n : ℝ) ^ 2 * (ca / 16) :=
      mul_le_mul_of_nonneg_left heθ.le (sq_nonneg _)
    have h4 : matBound Q * 121 ≤ matBound Q * 121 * n := by nlinarith
    show qM Q (toE yb) ≤ _
    nlinarith
  -- the growth estimate for the gap at `x₀`
  have hHg := hCH (n : ℝ) (Flat.gapBelow (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ p₀) x₀
    (by linarith) (Flat.gapBelow_nonneg hp₀)
    (Flat.gapBelow_self _ _ _) (abs_lapR_gapBelow_le hη hh x₀ p₀)
  have hyx : ‖toE y - toE x₀‖ < 2 * κ * n := by
    have := norm_sub_le (toE y) (toE x₀)
    linarith
  have hgy := hHg y (by linarith)
  have key := le_of_symmetric_bdry hh.2.1.1 hp₀ hbend hyb hqb (y := y) (by linarith)
  -- numerics
  have hy2 : ‖toE y‖ ^ 2 ≤ κ ^ 2 * (n : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hy'.le 2
    rw [mul_pow] at this; exact this
  have hyx2 : ‖toE y - toE x₀‖ ^ 2 ≤ 4 * κ ^ 2 * (n : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hyx.le 2
    nlinarith
  have hS : matBound Q * ‖toE y‖ ^ 2 ≤ matBound Q * (κ ^ 2 * (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hy2 hS0
  have hC : CH * ‖toE y - toE x₀‖ ^ 2 ≤ CH * (4 * κ ^ 2 * (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hyx2 hCH0
  have hκ' : (matBound Q + 4 * CH) * κ ^ 2 * (n : ℝ) ^ 2 ≤ ca / 64 * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hκS (sq_nonneg _)
  have hnK : 64 * (132 * matBound Q + 2) ≤ ca * n := by
    rw [div_le_iff₀ hca] at hn; linarith
  have hnK' : 64 * (132 * matBound Q + 2) * n ≤ ca * n * n :=
    mul_le_mul_of_nonneg_right hnK (by linarith)
  have hreal : (1 : ℝ) ≤ h y := by nlinarith
  exact_mod_cast hreal

/-! ### Step B: the recurrent minimum principle -/

/-- The comparison of the two gaps through the recurrent minimum principle (1.6). -/
theorem gap_le_of_recurrent {η : Site 2 → ℤ} {Q : Matrix (Fin 2) (Fin 2) ℝ} {n R : ℕ}
    (hR : 1 ≤ R) (hRn : (R : ℝ) + 1 ≤ n) {h h' : Site 2 → ℤ}
    (hh : h ∈ locLegal η (ballZ0 (n : ℝ)) ∩ stabilizing η (ballZ0 (n : ℝ)))
    (hh' : h' ∈ locLegal η (ballZ0 (R : ℝ)) ∩ stabilizing η (ballZ0 (R : ℝ)))
    (hge : ∀ y ∈ ballZ0 (d := 2) (R : ℝ), 1 ≤ h y) {x₀ : Site 2}
    (hx₀ : x₀ ∈ ballZ0 (d := 2) (R : ℝ)) {p₀ : Rd 2}
    (hp₀ : p₀ ∈ supGrad (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ (ballZ0 (n : ℝ)))
    {z₀ : Site 2} {p₁ : Rd 2} {a H : ℝ}
    (hbend : ∀ y ∈ bdry (ballZ0 (d := 2) (R : ℝ)),
      a ≤ Flat.gapAbove (fun x => (h' x : ℝ) - (qlZ 0 x + qMZ Q x)) z₀ p₁ y)
    (hHx : Flat.gapAbove (fun x => (h' x : ℝ) - (qlZ 0 x + qMZ Q x)) z₀ p₁ x₀ ≤ H) :
    a ≤ H + 2 * ((R : ℝ) + 1) + 2 * ‖toE x₀‖ := by
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hn0 : (0 : ℝ) < n := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hAB : ballZ0 (d := 2) (R : ℝ) ⊆ ballZ0 (n : ℝ) := fun x hx =>
    MuLipschitz.mem_ballZ0.2 ((MuLipschitz.mem_ballZ0.1 hx).trans_le (by linarith))
  have hrec : IsRecurrentOn (fun x => lap h x + η x) (ballZ0 (d := 2) (R : ℝ)) :=
    recurrentOfToppled 2 le_rfl _ _ hAB (Flat.ballZ0_connected hR0) (Flat.ballZ0_connected hn0) η h
      hh.1 hge
  obtain ⟨G, hG, -, hGr⟩ := Flat.exists_int_harmonic (d := 2) (p₁ - p₀)
  have hlapD : ∀ x ∈ ballZ0 (d := 2) (R : ℝ),
      lap (fun y => h' y - h y + G y) x + (lap h x + η x) ≤ 2 * (2 : ℤ) - 1 := by
    intro x hx
    have e1 := Burning.lap_add_apply' (fun y => h' y - h y) G x
    have e2 := Burning.lap_sub_apply' h' h x
    have e3 := hG x
    have e4 := hh'.2.2 x hx
    push_cast at e4
    rw [e1, e2, e3]
    omega
  obtain ⟨y, hy, hle⟩ := recurrent_minPrinciple (MuLipschitz.ballZ0_finite _)
    (Flat.ballZ0_connected hR0) hrec hlapD x₀ hx₀
  have hle' : ((h' y - h y + G y : ℤ) : ℝ) ≤ ((h' x₀ - h x₀ + G x₀ : ℤ) : ℝ) := by
    exact_mod_cast hle
  push_cast at hle'
  have hga := Flat.gap_add (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x))
    (fun x => (h' x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ z₀ p₀ p₁ y
  have hgb := Flat.gap_add (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x))
    (fun x => (h' x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ z₀ p₀ p₁ x₀
  have hyn := MuLipschitz.norm_lt_of_mem_bdry_ballZ0 hy
  have hyB : y ∈ dClosure (ballZ0 (d := 2) (n : ℝ)) :=
    subset_dClosure _ (MuLipschitz.mem_ballZ0.2 (by linarith))
  have hy1 := Flat.gapBelow_nonneg hp₀ y hyB
  have hx1 := Flat.gapBelow_self (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ p₀
  have hyb := hbend y hy
  have hGy := abs_le.1 (hGr y)
  have hGx := abs_le.1 (hGr x₀)
  push_cast at hGy hGx
  linarith

/-- **Step B.** The final contradiction on `B_R`. -/
theorem critical_stepB {η : Site 2 → ℤ} {ηmin ηmax : ℤ} (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax)
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {CH : ℝ} (hCH : HarnackNear (lapBound ηmin ηmax Q) CH)
    (hCH0 : 0 ≤ CH) {ca δ β : ℝ} (hca : 0 < ca) (hδ8 : δ ≤ 1 / 8)
    (hCHδ : 4 * CH * δ ^ 2 ≤ ca / 16) {n R : ℕ} (hR2 : 2 ≤ R) (hRca : 80 / ca + 1 ≤ R)
    (hRn : (R : ℝ) + 1 ≤ n) (hβn : β * n ≤ δ * R) {h h' : Site 2 → ℤ}
    (hh : h ∈ locLegal η (ballZ0 (n : ℝ)) ∩ stabilizing η (ballZ0 (n : ℝ)))
    (hh' : h' ∈ locLegal η (ballZ0 (R : ℝ)) ∩ stabilizing η (ballZ0 (R : ℝ)))
    (hge : ∀ y ∈ ballZ0 (d := 2) (R : ℝ), 1 ≤ h y) {x₀ : Site 2}
    (hx₀ : x₀ ∈ ballZ0 (d := 2) (β * n)) {p₀ : Rd 2}
    (hp₀ : p₀ ∈ supGrad (fun x => (h x : ℝ) - (qlZ 0 x + qMZ Q x)) x₀ (ballZ0 (n : ℝ)))
    {z₀ : Site 2} (hz₀ : z₀ ∈ ballZ0 (d := 2) (δ * R)) {p₁ : Rd 2}
    (hp₁ : p₁ ∈ subGrad (fun x => (h' x : ℝ) - (qlZ 0 x + qMZ Q x)) z₀ (ballZ0 (R : ℝ)))
    (hbend : ∀ y ∈ bdry (ballZ0 (d := 2) (R : ℝ)),
      ca * (R : ℝ) ^ 2 / 4 ≤ Flat.gapAbove (fun x => (h' x : ℝ) - (qlZ 0 x + qMZ Q x)) z₀ p₁ y) :
    False := by
  have hR2' : (2 : ℝ) ≤ R := by exact_mod_cast hR2
  have hx₀' : ‖toE x₀‖ < β * n := MuLipschitz.mem_ballZ0.1 hx₀
  have hz₀' : ‖toE z₀‖ < δ * R := MuLipschitz.mem_ballZ0.1 hz₀
  have hδR : δ * R ≤ R / 8 := by nlinarith
  have hx₀R : x₀ ∈ ballZ0 (d := 2) (R : ℝ) := MuLipschitz.mem_ballZ0.2 (by linarith)
  have hxz : ‖toE x₀ - toE z₀‖ < 2 * δ * R := by
    have := norm_sub_le (toE x₀) (toE z₀)
    linarith
  have hHb := hCH (R : ℝ) (Flat.gapAbove (fun x => (h' x : ℝ) - (qlZ 0 x + qMZ Q x)) z₀ p₁) z₀
    (by linarith) (Flat.gapAbove_nonneg hp₁)
    (Flat.gapAbove_self _ _ _) (abs_lapR_gapAbove_le hη hh' z₀ p₁) x₀ (by linarith)
  have hmain := gap_le_of_recurrent (by omega) hRn hh hh' hge hx₀R hp₀ hbend hHb
  have hxz2 : ‖toE x₀ - toE z₀‖ ^ 2 ≤ 4 * δ ^ 2 * (R : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hxz.le 2
    nlinarith
  have hC : CH * ‖toE x₀ - toE z₀‖ ^ 2 ≤ CH * (4 * δ ^ 2 * (R : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hxz2 hCH0
  have hC' : 4 * CH * δ ^ 2 * (R : ℝ) ^ 2 ≤ ca / 16 * (R : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hCHδ (sq_nonneg _)
  have hRca' : 80 + ca ≤ ca * R := by
    have h4 : 80 / ca ≤ (R : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hca] at h4
    linarith
  have hRca'' : (80 + ca) * R ≤ ca * R * R := mul_le_mul_of_nonneg_right hRca' (by linarith)
  have hcaR : 0 ≤ ca * R := by nlinarith
  nlinarith

/-! ### Contact points near the centre (even convergence) -/

theorem exists_contact_sup {n : ℕ} (hn : 1 ≤ n) {w : Site 2 → ℝ} {α β ε : ℝ} (hα : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hε : 0 < ε) (hεβ : 2 * ε < β ^ 2 * α)
    (hN : ENNReal.ofReal ((α - ε) * ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ)) ≤
      volume (supGradSet w (ballZ0 (n : ℝ))))
    (hS : volume (⋃ x ∈ ballZ0 (d := 2) (n : ℝ) \ ballZ0 (β * n), supGrad w x (ballZ0 (n : ℝ))) ≤
      ENNReal.ofReal (((1 - β ^ 2) * α + ε) * ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ))) :
    ∃ x ∈ ballZ0 (d := 2) (β * n), (supGrad w x (ballZ0 (n : ℝ))).Nonempty := by
  have hN0 : (0 : ℝ) < ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ) := by
    exact_mod_cast MuLipschitz.ncard_ballZ0_pos hn
  have hβ2 : β ^ 2 ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have h0 : 0 ≤ (1 - β ^ 2) * α := mul_nonneg (by linarith) hα.le
  exact Flat.exists_mem_supGrad_of_mass (mul_nonneg (by linarith) hN0.le)
    (mul_lt_mul_of_pos_right (by linarith) hN0) hN hS

theorem exists_contact_sub {n : ℕ} (hn : 1 ≤ n) {w : Site 2 → ℝ} {α β ε : ℝ} (hα : 0 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hε : 0 < ε) (hεβ : 2 * ε < β ^ 2 * α)
    (hN : ENNReal.ofReal ((α - ε) * ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ)) ≤
      volume (subGradSet w (ballZ0 (n : ℝ))))
    (hS : volume (⋃ x ∈ ballZ0 (d := 2) (n : ℝ) \ ballZ0 (β * n), subGrad w x (ballZ0 (n : ℝ))) ≤
      ENNReal.ofReal (((1 - β ^ 2) * α + ε) * ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ))) :
    ∃ x ∈ ballZ0 (d := 2) (β * n), (subGrad w x (ballZ0 (n : ℝ))).Nonempty := by
  have hN0 : (0 : ℝ) < ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ) := by
    exact_mod_cast MuLipschitz.ncard_ballZ0_pos hn
  have hβ2 : β ^ 2 ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have h0 : 0 ≤ (1 - β ^ 2) * α := mul_nonneg (by linarith) hα.le
  exact Flat.exists_mem_subGrad_of_mass (mul_nonneg (by linarith) hN0.le)
    (mul_lt_mul_of_pos_right (by linarith) hN0) hN hS

/-! ### The choice of constants -/

/-- The constants `κ`, `δ` of D2-PROOF §4: `(|Q| + 4C) κ² ≤ cα/64` and `4 C δ² ≤ cα/16`. -/
theorem exists_small_const {ca S : ℝ} (hca : 0 < ca) (hS : 0 ≤ S) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 8 ∧ S * κ ^ 2 ≤ ca / 64 := by
  have hS1 : (0 : ℝ) < 64 * (S + 1) := by linarith
  have hq : 0 < ca / (64 * (S + 1)) := div_pos hca hS1
  refine ⟨min (1 / 8) (ca / (64 * (S + 1))), lt_min (by norm_num) hq, min_le_left _ _, ?_⟩
  have hκ0 : 0 < min (1 / 8) (ca / (64 * (S + 1))) := lt_min (by norm_num) hq
  have hκ8 : min (1 / 8) (ca / (64 * (S + 1))) ≤ 1 / 8 := min_le_left _ _
  have h1 : min (1 / 8) (ca / (64 * (S + 1))) ≤ ca / (64 * (S + 1)) := min_le_right _ _
  set κ := min (1 / 8) (ca / (64 * (S + 1)))
  have h2 : κ * (64 * (S + 1)) ≤ ca := by rwa [le_div_iff₀ hS1] at h1
  have h3 := mul_le_mul_of_nonneg_left h2 hκ0.le
  have h4 := mul_le_mul_of_nonneg_right hκ8 hca.le
  nlinarith [sq_nonneg κ]

/-! ### Flatness at critical matrices -/

/-- The core of `criticalFlat`, for one environment `η` in the good event. -/
theorem critical_of_ae {E : RandomEnvironment 2} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hEq : muBar E 0 Q = muStarBar E 0 Q) (hpos : 0 < muBar E 0 Q) {c : ℝ} (hc : 0 < c)
    (hQ : Q.IsSymm) (hnot : ¬ Q.PosDef) {η : Site 2 → ℤ}
    (h1 : ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ w ∈ perturbedSub (ballZ0 (n : ℝ)) η 0 Q ∩ perturbedSuper (ballZ0 (n : ℝ)) η 0 Q,
        ENNReal.ofReal ((muBar E 0 Q - ε) * ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ)) ≤
            volume (supGradSet w (ballZ0 (n : ℝ))) ∧
          ∀ x₀ ∈ ballZ0 (d := 2) (β * n), ∀ p₀ ∈ supGrad w x₀ (ballZ0 (n : ℝ)),
            ∀ y ∈ bdry (ballZ0 (d := 2) (n : ℝ)),
              w y ≤ w x₀ + inner ℝ p₀ (toE y - toE x₀) -
                c * muBar E 0 Q * ((1 - β) * n) * ‖toE y - toE x₀‖)
    (h2 : ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ w ∈ perturbedSub (ballZ0 (n : ℝ)) η 0 Q ∩ perturbedSuper (ballZ0 (n : ℝ)) η 0 Q,
        ENNReal.ofReal ((muStarBar E 0 Q - ε) * ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ)) ≤
            volume (subGradSet w (ballZ0 (n : ℝ))) ∧
          ∀ x₀ ∈ ballZ0 (d := 2) (β * n), ∀ p₀ ∈ subGrad w x₀ (ballZ0 (n : ℝ)),
            ∀ y ∈ bdry (ballZ0 (d := 2) (n : ℝ)),
              w x₀ + inner ℝ p₀ (toE y - toE x₀) +
                c * muStarBar E 0 Q * ((1 - β) * n) * ‖toE y - toE x₀‖ ≤ w y)
    (h3 : ∀ τ : ℝ, 0 < τ → τ < 1 → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ w ∈ perturbedSub (ballZ0 (n : ℝ)) η 0 Q,
        volume (⋃ x ∈ ballZ0 (d := 2) (n : ℝ) \ ballZ0 ((1 - τ) * n),
            supGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal (((1 - (1 - τ) ^ 2) * muBar E 0 Q + ε) *
            ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ))) ∧
      (∀ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η 0 Q,
        volume (⋃ x ∈ ballZ0 (d := 2) (n : ℝ) \ ballZ0 ((1 - τ) * n),
            subGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal (((1 - (1 - τ) ^ 2) * muStarBar E 0 Q + ε) *
            ((ballZ0 (d := 2) (n : ℝ)).ncard : ℝ))))
    (hη : ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax) : False := by
  set α := muBar E 0 Q
  rw [← hEq] at h2 h3
  have hca : 0 < c * α := mul_pos hc hpos
  obtain ⟨CH, hCH0, hCH⟩ := harnack_near (d := 2) le_rfl (lapBound E.ηmin E.ηmax Q)
  obtain ⟨e, he, heθ⟩ := exists_unit_qM_lt hQ hnot (div_pos hca (by norm_num : (0 : ℝ) < 16))
  have hS0 := matBound_nonneg Q
  obtain ⟨κ, hκ0, hκ8, hκS⟩ :=
    exists_small_const hca (by linarith : 0 ≤ matBound Q + 4 * CH)
  obtain ⟨δ, hδ0, hδ8, hCHδ'⟩ := exists_small_const hca (by linarith : 0 ≤ 4 * CH)
  have hCHδ : 4 * CH * δ ^ 2 ≤ c * α / 16 := by linarith
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = δ * κ / 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; have := mul_pos hδ0 hκ0; linarith
  have hβκ : β ≤ κ := by rw [hβ]; nlinarith
  have hβ1 : β < 1 := by linarith
  have hβ2 : β ≤ 1 / 2 := by linarith
  have hδ1 : δ < 1 := by linarith
  have hδ2 : δ ≤ 1 / 2 := by linarith
  have hε1 : 0 < β ^ 2 * α / 4 := by have := mul_pos (pow_pos hβ0 2) hpos; linarith
  have hε2 : 0 < δ ^ 2 * α / 4 := by have := mul_pos (pow_pos hδ0 2) hpos; linarith
  have hεβ1 : 2 * (β ^ 2 * α / 4) < β ^ 2 * α := by linarith
  have hεβ2 : 2 * (δ ^ 2 * α / 4) < δ ^ 2 * α := by linarith
  obtain ⟨na, hna⟩ := h1 _ hε1 β hβ0 hβ1
  obtain ⟨nb, hnb⟩ := h2 _ hε2 δ hδ0 hδ1
  obtain ⟨nc, hnc⟩ := h3 (1 - β) (by linarith) (by linarith) _ hε1
  obtain ⟨nd, hnd⟩ := h3 (1 - δ) (by linarith) (by linarith) _ hε2
  -- the radii
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = max (max nb nd) (⌈80 / (c * α)⌉₊ + 2) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = max (max na nc)
      (max ⌈64 * (132 * matBound Q + 2) / (c * α)⌉₊ (max ⌈((M : ℝ) + 2) / κ⌉₊ 2)) := ⟨_, rfl⟩
  have hna' : na ≤ n := by rw [hn]; exact le_max_of_le_left (le_max_left _ _)
  have hnc' : nc ≤ n := by rw [hn]; exact le_max_of_le_left (le_max_right _ _)
  have hn1 : ⌈64 * (132 * matBound Q + 2) / (c * α)⌉₊ ≤ n := by
    rw [hn]; exact le_max_of_le_right (le_max_left _ _)
  have hn3 : ⌈((M : ℝ) + 2) / κ⌉₊ ≤ n := by
    rw [hn]; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hn2 : 2 ≤ n := by rw [hn]; exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn1' : 64 * (132 * matBound Q + 2) / (c * α) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn1)
  have hn3' : ((M : ℝ) + 2) / κ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn3)
  have hκn : (M : ℝ) + 2 ≤ κ * n := by rw [div_le_iff₀ hκ0] at hn3'; linarith
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = ⌊κ * (n : ℝ)⌋₊ := ⟨_, rfl⟩
  have hRle : (R : ℝ) ≤ κ * n := by
    rw [hR]; exact Nat.floor_le (mul_nonneg hκ0.le (Nat.cast_nonneg n))
  have hRgt : κ * n < R + 1 := by rw [hR]; exact Nat.lt_floor_add_one _
  have hMR : M ≤ R := by rw [hR]; exact Nat.le_floor (by linarith)
  have hnbR : nb ≤ R := le_trans (by rw [hM]; exact le_max_of_le_left (le_max_left _ _)) hMR
  have hndR : nd ≤ R := le_trans (by rw [hM]; exact le_max_of_le_left (le_max_right _ _)) hMR
  have hR80 : ⌈80 / (c * α)⌉₊ + 2 ≤ R := le_trans (by rw [hM]; exact le_max_right _ _) hMR
  have hR2 : 2 ≤ R := by omega
  have hR2' : (2 : ℝ) ≤ R := by exact_mod_cast hR2
  have hRca : 80 / (c * α) + 1 ≤ R := by
    have h4 := Nat.le_ceil (80 / (c * α))
    have h5 : ((⌈80 / (c * α)⌉₊ + 2 : ℕ) : ℝ) ≤ R := by exact_mod_cast hR80
    push_cast at h5
    linarith
  have hRn : (R : ℝ) + 1 ≤ n := by
    have : κ * n ≤ n / 8 := by nlinarith
    linarith
  have hβn : β * n ≤ δ * R := by
    have h4 : κ * n ≤ 2 * R := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hδ0.le
    rw [hβ]; nlinarith
  -- the near-maximizers and their contact points
  obtain ⟨u, hu, hNu, hBu⟩ := hna n hna'
  obtain ⟨v, hv, hNv, hBv⟩ := hnb R hnbR
  have hSu := (hnc n hnc').1 u hu.1
  have hSv := (hnd R hndR).2 v hv.2
  rw [sub_sub_cancel] at hSu hSv
  obtain ⟨x₀, hx₀, p₀, hp₀⟩ := exists_contact_sup (by omega) hpos hβ0 hβ1 hε1 hεβ1 hNu hSu
  obtain ⟨z₀, hz₀, p₁, hp₁⟩ := exists_contact_sub (by omega) hpos hδ0 hδ1 hε2 hεβ2 hNv hSv
  have hbu := gapBelow_ge_of_bend hβ2 hca.le hx₀ (hBu x₀ hx₀ p₀ hp₀)
  have hbv := gapAbove_ge_of_bend hδ2 hca.le hz₀ (hBv z₀ hz₀ p₁ hp₁)
  obtain ⟨h, hhLS, rfl⟩ := Flat.exists_of_mem_inter hu
  obtain ⟨h', hh'LS, rfl⟩ := Flat.exists_of_mem_inter hv
  have hge := critical_stepA hη hCH hCH0 hca he heθ hκ8 hβκ hκS hn1' hn2 hhLS hx₀ hp₀ hbu
  exact critical_stepB hη hCH hCH0 hca hδ8 hCHδ hR2 hRca hRn hβn hhLS hh'LS
    (fun y hy => hge y (MuLipschitz.mem_ballZ0.2 ((MuLipschitz.mem_ballZ0.1 hy).trans_le hRle)))
    hx₀ hp₀ hz₀ hp₁ hbv

/-- **Flatness at a critical matrix**. -/
theorem criticalFlat : CriticalFlatD2Stmt := by
  intro E hE Q hQ hF hnot
  have hG := isGreatest_effOp muConvergence_unconditional le_rfl E hQ
  have hEq : muBar E 0 Q = muStarBar E 0 Q := by
    have h1 : muBar E (effOp E Q) Q = muStarBar E (effOp E Q) Q := hG.1
    rwa [hF] at h1
  by_contra hne
  have hpos' : 0 < muStarBar E 0 Q := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
  have hpos : 0 < muBar E 0 Q := hEq ▸ hpos'
  obtain ⟨c, hc, hcE⟩ := nearMaxBendingStabilizing_of_muConvergence muConvergence_unconditional 2
    le_rfl E.ηmin E.ηmax 0 Q
  obtain ⟨hsub, hsup⟩ := hcE E rfl rfl
  have hshell := shellBound_of_muConvergence muConvergence_unconditional 2 le_rfl E 0 Q
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  obtain ⟨η, h1, h2, h3, hη⟩ := ((hsub hpos).and ((hsup hpos').and (hshell.and hbdd))).exists
  exact critical_of_ae hEq hpos hc hQ hnot h1 h2 h3 hη

end SingleSourceD2

end RandomSandpile

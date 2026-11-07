import RandomSandpile.Proofs.Sec7.FlatBarrier
import RandomSandpile.Proofs.Sec3.Abelian
import RandomSandpile.Proofs.Sec3.RecurrentOfToppled
import RandomSandpile.Proofs.Sec5.MuConvergenceRestrict

/-! # Lemma 7.5 (`flat`): proof of the deterministic step

`noOppositeBending : NoOppositeBendingStmt`, and Lemma 7.5 from the remaining
inputs, `flat_of_bending`.

* `comparison`: for `h, h' ∈ 𝓛(η, B_n) ∩ 𝒮(η, B_n)` and an integer harmonic `G`, some
  `y ∈ ∂B_{(1-ε)n}` has `(h' + G - h)(y) ≤ (h' + G - h)(0)`, when the odometer `w` of `η` in `B_n`
  is `≥ 1` on `B_{(1-ε)n}`. This is of Prop 3.3 on `A = B_{(1-ε)n}` for the sandpile
  `Δ w + η`, stable (`w` stabilizing) and recurrent on `A` (Prop 3.4), applied to the restrictions
  to `Ā` of the boundary parts `h - w`, `h' - w` (Prop 3.2, with the uniqueness of Prop 3.1).
* `exists_int_harmonic`: the integer harmonic rounding `G(y) = -∑ ⌊P_i⌋ y_i` of `-P · y`, with error `≤ d |y|`.
* `noOppositeBending`: the gaps `g_u`, `g_v` are `≤ C (βn)²` at `0` (Harnack), `≥ c n² - O(ε n² + n)`
  on `∂B_{(1-ε)n}` (barrier), and `(g_u + g_v)(y) ≤ (g_u + g_v)(0) + d |y|` there (comparison).
-/

open MeasureTheory LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace Flat

variable {d : ℕ}

/-- An element of `S(A, η, l, M) ∩ S*(A, η, l, M)` is `h - q_l - q_M` with `h ∈ 𝓛 ∩ 𝒮`. -/
theorem exists_of_mem_inter {A : Set (Site d)} {η : Site d → ℤ} {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {u : Site d → ℝ}
    (hu : u ∈ perturbedSub A η l M ∩ perturbedSuper A η l M) :
    ∃ h ∈ locLegal η A ∩ stabilizing η A, u = fun x => (h x : ℝ) - (qlZ l x + qMZ M x) := by
  obtain ⟨h, hL, rfl⟩ := mem_perturbedSub.1 hu.1
  obtain ⟨h₂, hS, he⟩ := mem_perturbedSuper.1 hu.2
  have : h₂ = h := funext fun x => by
    have : (h₂ x : ℝ) - (qlZ l x + qMZ M x) = (h x : ℝ) - (qlZ l x + qMZ M x) := (congrFun he x).symm
    exact_mod_cast (by linarith : (h₂ x : ℝ) = h x)
  exact ⟨h, ⟨hL, this ▸ hS⟩, rfl⟩

theorem lapR_perturbed (hd : 1 ≤ d) (h : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (y : Site d) :
    lapR (fun x => (h x : ℝ) - (qlZ l x + qMZ M x)) y = lap h y - (l + M.trace) := by
  rw [lapR_sub', lapR_intCast, lapQuadratic d hd l M y]

/-- The comparison step on `A = B_{(1-ε)n}`. -/
theorem comparison (hd : 2 ≤ d) {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hεn : 1 ≤ ε * n)
    {η : Site d → ℤ}
    (hlow : ∀ w ∈ locLegal η (ballZ0 (n : ℝ)) ∩ stabilizing η (ballZ0 (n : ℝ)),
      (∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)), w y = 0) →
      ∀ x ∈ ballZ0 (d := d) ((1 - ε) * n), 1 ≤ w x)
    {h h' : Site d → ℤ} (hh : h ∈ locLegal η (ballZ0 (n : ℝ)) ∩ stabilizing η (ballZ0 (n : ℝ)))
    (hh' : h' ∈ locLegal η (ballZ0 (n : ℝ)) ∩ stabilizing η (ballZ0 (n : ℝ)))
    (G : Site d → ℤ) (hG : ∀ x, lap G x = 0) :
    ∃ y ∈ bdry (ballZ0 (d := d) ((1 - ε) * n)), (h' y + G y) - h y ≤ (h' 0 + G 0) - h 0 := by
  set B := ballZ0 (d := d) (n : ℝ) with hB
  set A := ballZ0 (d := d) ((1 - ε) * n) with hA
  have hn : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg (α := ℝ) n).lt_or_eq with h | h
    · exact h
    · rw [← h] at hεn; simp at hεn; linarith
  have hAr : 0 < (1 - ε) * n := mul_pos (by linarith) hn
  have hBfin : B.Finite := MuLipschitz.ballZ0_finite _
  have hAfin : A.Finite := MuLipschitz.ballZ0_finite _
  have hBc := ballZ0_connected (d := d) hn
  have hAc := ballZ0_connected (d := d) hAr
  have hAB : A ⊆ B := fun x hx => MuLipschitz.mem_ballZ0.2
    ((MuLipschitz.mem_ballZ0.1 hx).trans_le (by nlinarith))
  have h0A : (0 : Site d) ∈ A :=
    MuLipschitz.mem_ballZ0.2 (by simp only [MuLipschitz.toE_zero, norm_zero]; exact hAr)
  obtain ⟨w, u₂, hsplit, ⟨hwLS, hw0⟩, ⟨hu₂L, hu₂S⟩, -⟩ :=
    abelianDecomposition d hd B hBfin hBc η h h hh (fun _ _ => rfl) (fun y _ => hh.2.1.1 y)
  obtain ⟨w', v₂, hsplit', ⟨hw'LS, hw'0⟩, ⟨hv₂L, hv₂S⟩, -⟩ :=
    abelianDecomposition d hd B hBfin hBc η h' h' hh' (fun _ _ => rfl) (fun y _ => hh'.2.1.1 y)
  obtain ⟨v, -, -, -, huniq⟩ := leastAction d hd B hBfin hBc η
  have hww : w' = w := (huniq w' hw'LS hw'0).trans (huniq w hwLS hw0).symm
  subst hww
  set s : Site d → ℤ := fun x => η x + lap w' x with hs
  have hstable : IsStableOn s A := fun x hx => by
    have := hwLS.2.2 x (hAB hx)
    simp only [hs]; omega
  have hrec : IsRecurrentOn s A := by
    have := recurrentOfToppled d hd A B hAB hAc hBc η w' hwLS.1 (hlow w' hwLS hw0)
    have e : (fun x => lap w' x + η x) = s := funext fun x => add_comm _ _
    rwa [e] at this
  have hUL := locLegalRestrict d s B A u₂ hAB hu₂L
  have hUS := stabilizingRestrict d s B A u₂ hAB hu₂S
  have hVL := locLegalRestrict d s B A v₂ hAB hv₂L
  have hVS := stabilizingRestrict d s B A v₂ hAB hv₂S
  have hind : ∀ (f : Site d → ℤ) (x : Site d), x ∈ dClosure A → (dClosure A).indicator f x = f x :=
    fun f x hx => Set.indicator_of_mem hx f
  have hnn : ∀ (f : Site d → ℤ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ (dClosure A).indicator f x :=
    fun f hf x => Set.indicator_nonneg (fun y _ => hf y) x
  obtain ⟨-, -, hcomp⟩ := burning d hd A hAfin hAc ((dClosure A).indicator u₂) s
    ((dClosure A).indicator u₂) (fun y _ => hnn u₂ hu₂S.1.1 y) ⟨hUL, hUS⟩ (fun _ _ => rfl)
  obtain ⟨y, hy, hle⟩ := hcomp hstable hrec ((dClosure A).indicator v₂) ((dClosure A).indicator v₂)
    (fun y _ => hnn v₂ hv₂S.1.1 y) ⟨hVL, hVS⟩ (fun _ _ => rfl) G 0 (fun x _ => hG x)
    (fun x _ => Burning.lap_const_apply 0 x) 0 h0A
  refine ⟨y, hy, ?_⟩
  have hyA := bdry_subset_dClosure A hy
  have h0A' := subset_dClosure A h0A
  rw [hind u₂ y hyA, hind v₂ y hyA, hind u₂ 0 h0A', hind v₂ 0 h0A'] at hle
  have e1 := congrFun hsplit y
  have e2 := congrFun hsplit' y
  have e3 := congrFun hsplit 0
  have e4 := congrFun hsplit' 0
  simp only [Pi.add_apply, Pi.zero_apply] at e1 e2 e3 e4 hle
  omega

/-- The integer harmonic rounding of `-P · y`. -/
theorem exists_int_harmonic (P : Rd d) : ∃ G : Site d → ℤ, (∀ x, lap G x = 0) ∧ G 0 = 0 ∧
    ∀ y, |(G y : ℝ) + inner ℝ P (toE y)| ≤ d * ‖toE y‖ := by
  have hinner : ∀ (Q : Rd d) (y : Site d), inner ℝ Q (toE y) = ∑ i, Q i * (y i : ℝ) :=
    fun Q y => by rw [PiLp.inner_apply]; simp [mul_comm]
  refine ⟨fun y => -∑ i, ⌊P i⌋ * y i, fun x => ?_, by simp, fun y => ?_⟩
  · have hR : ((lap (fun y => -∑ i, ⌊P i⌋ * y i) x : ℤ) : ℝ) = 0 := by
      rw [← lapR_intCast]
      have e : (fun y : Site d => (((-∑ i, ⌊P i⌋ * y i : ℤ)) : ℝ)) = fun y =>
          0 + inner ℝ (WithLp.toLp 2 (fun i => -(⌊P i⌋ : ℝ)) : Rd d) (toE y - toE 0) := by
        funext y
        rw [MuLipschitz.toE_zero, sub_zero, hinner]
        push_cast
        simp [Finset.sum_neg_distrib]
      rw [e, lapR_affine]
    exact_mod_cast hR
  · have e : (((-∑ i, ⌊P i⌋ * y i : ℤ)) : ℝ) + inner ℝ P (toE y) =
        ∑ i, (P i - ⌊P i⌋) * (y i : ℝ) := by
      rw [hinner]
      push_cast
      rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    calc |∑ i, (P i - ⌊P i⌋) * (y i : ℝ)| ≤ ∑ i, |(P i - ⌊P i⌋) * (y i : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, ‖toE y‖ := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          have h1 : |P i - ⌊P i⌋| ≤ 1 := by
            rw [abs_of_nonneg (by linarith [Int.floor_le (P i)])]
            linarith [Int.lt_floor_add_one (P i)]
          have h2 : |(y i : ℝ)| ≤ ‖toE y‖ := by
            have := PiLp.norm_apply_le (toE y) i
            simpa only [toE_apply, Real.norm_eq_abs] using this
          calc |P i - ⌊P i⌋| * |(y i : ℝ)| ≤ 1 * ‖toE y‖ :=
                mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
            _ = ‖toE y‖ := one_mul _
      _ = d * ‖toE y‖ := by simp [Finset.sum_const, Finset.card_univ]

/-! ### Gaps below and above supporting planes -/

/-- The gap of `f` below its supporting plane at `x₀` with slope `p₀`. -/
noncomputable def gapBelow (f : Site d → ℝ) (x₀ : Site d) (p₀ : Rd d) (y : Site d) : ℝ :=
  f x₀ + inner ℝ p₀ (toE y - toE x₀) - f y

/-- The gap of `f` above its supporting plane at `x₀` with slope `p₀`. -/
noncomputable def gapAbove (f : Site d → ℝ) (x₀ : Site d) (p₀ : Rd d) (y : Site d) : ℝ :=
  f y - (f x₀ + inner ℝ p₀ (toE y - toE x₀))

theorem gapBelow_nonneg {f : Site d → ℝ} {x₀ : Site d} {p₀ : Rd d} {A : Set (Site d)}
    (hp : p₀ ∈ supGrad f x₀ A) : ∀ y ∈ dClosure A, 0 ≤ gapBelow f x₀ p₀ y := fun y hy => by
  have := hp y hy; unfold gapBelow; linarith

theorem gapAbove_nonneg {f : Site d → ℝ} {x₀ : Site d} {p₀ : Rd d} {A : Set (Site d)}
    (hp : p₀ ∈ subGrad f x₀ A) : ∀ y ∈ dClosure A, 0 ≤ gapAbove f x₀ p₀ y := fun y hy => by
  have := hp y hy; unfold gapAbove; linarith

theorem gapBelow_self (f : Site d → ℝ) (x₀ : Site d) (p₀ : Rd d) : gapBelow f x₀ p₀ x₀ = 0 := by
  simp [gapBelow]

theorem gapAbove_self (f : Site d → ℝ) (x₀ : Site d) (p₀ : Rd d) : gapAbove f x₀ p₀ x₀ = 0 := by
  simp [gapAbove]

theorem lapR_gapBelow (f : Site d → ℝ) (x₀ : Site d) (p₀ : Rd d) (y : Site d) :
    lapR (gapBelow f x₀ p₀) y = -lapR f y := by
  have e : gapBelow f x₀ p₀ = fun z => (f x₀ + inner ℝ p₀ (toE z - toE x₀)) - f z := rfl
  rw [e, lapR_sub', lapR_affine, zero_sub]

theorem lapR_gapAbove (f : Site d → ℝ) (x₀ : Site d) (p₀ : Rd d) (y : Site d) :
    lapR (gapAbove f x₀ p₀) y = lapR f y := by
  have e : gapAbove f x₀ p₀ = fun z => f z - (f x₀ + inner ℝ p₀ (toE z - toE x₀)) := rfl
  rw [e, lapR_sub', lapR_affine, sub_zero]

theorem gap_add (u v : Site d → ℝ) (x₀ x₀' : Site d) (p₀ p₀' : Rd d) (z : Site d) :
    gapBelow u x₀ p₀ z + gapAbove v x₀' p₀' z = (v z - u z) - inner ℝ (p₀' - p₀) (toE z) +
      (u x₀ - v x₀' - inner ℝ p₀ (toE x₀) + inner ℝ p₀' (toE x₀')) := by
  simp only [gapBelow, gapAbove, inner_sub_right, inner_sub_left]; ring

/-- The Laplacian of `h - q_l - q_M`, `h ∈ 𝓛 ∩ 𝒮`, is bounded in `A`. -/
theorem abs_lapR_perturbed_le (hd1 : 1 ≤ d) {η : Site d → ℤ} {ηmin ηmax : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) {l : ℝ} {M : Matrix (Fin d) (Fin d) ℝ}
    {A : Set (Site d)} {h : Site d → ℤ} (hh : h ∈ locLegal η A ∩ stabilizing η A)
    {y : Site d} (hy : y ∈ A) :
    |lapR (fun x => (h x : ℝ) - (qlZ l x + qMZ M x)) y| ≤
      |(ηmin : ℝ)| + |(ηmax : ℝ)| + 2 * d + |l + M.trace| := by
  rw [lapR_perturbed hd1]
  have := abs_lap_le hη hh.1 hh.2 hy
  calc |(lap h y : ℝ) - (l + M.trace)| ≤ |(lap h y : ℝ)| + |l + M.trace| := abs_sub _ _
    _ ≤ _ := by linarith

/-- The final arithmetic of `noOppositeBending`. -/
theorem flat_arith {c lam CH β ε n t d gu gv gu0 gv0 : ℝ} (hlam0 : 0 ≤ lam) (hdR : 1 ≤ d)
    (hnpos : 1 ≤ n) (hε0 : 0 < ε) (hε2 : ε ≤ 1 / 2) (hlamε : lam * ε ≤ c * d / 8)
    (hβsq : CH * (β * n) ^ 2 ≤ c * n ^ 2 / 8) (hn1 : 3 * lam + 2 * d < c * n)
    (ht1 : (1 - ε) * n ≤ t) (ht2 : t ≤ n)
    (hlu : c * n ^ 2 - lam * ((n + 1) ^ 2 - t ^ 2) / (2 * d) ≤ gu)
    (hlv : c * n ^ 2 - lam * ((n + 1) ^ 2 - t ^ 2) / (2 * d) ≤ gv)
    (hHu : gu0 ≤ CH * (β * n) ^ 2) (hHv : gv0 ≤ CH * (β * n) ^ 2)
    (hup : gu + gv ≤ gu0 + gv0 + d * t) : False := by
  have hy0 : 0 ≤ (1 - ε) * n := mul_nonneg (by linarith) (by linarith)
  have hysq : ((1 - ε) * n) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hy0 ht1 2
  have hT : (n + 1) ^ 2 - t ^ 2 ≤ 2 * ε * n ^ 2 + 2 * n + 1 := by
    have : 0 ≤ ε ^ 2 * n ^ 2 := by positivity
    nlinarith
  have hloss : lam * ((n + 1) ^ 2 - t ^ 2) / (2 * d) ≤ c * n ^ 2 / 8 + 3 * lam * n / 2 := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : lam * ((n + 1) ^ 2 - t ^ 2) ≤ lam * (2 * ε * n ^ 2 + 2 * n + 1) :=
      mul_le_mul_of_nonneg_left hT hlam0
    have h2 : lam * ε * n ^ 2 ≤ c * d / 8 * n ^ 2 := mul_le_mul_of_nonneg_right hlamε (sq_nonneg _)
    have h3 : lam * 1 ≤ lam * n := mul_le_mul_of_nonneg_left hnpos hlam0
    have h4 : lam * n * 1 ≤ lam * n * d := mul_le_mul_of_nonneg_left hdR (by positivity)
    nlinarith
  have hdt : d * t ≤ d * n := mul_le_mul_of_nonneg_left ht2 (by linarith)
  have hprod : (3 * lam + 2 * d) * n < c * n * n := mul_lt_mul_of_pos_right hn1 (by linarith)
  have hdn : 0 ≤ d * n := by positivity
  nlinarith

end Flat

open Flat in
/-- Step 2 of Lemma 7.5 (`NoOppositeBendingStmt`). -/
theorem noOppositeBending : NoOppositeBendingStmt := by
  intro d hd ηmin ηmax l M c hc
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = |(ηmin : ℝ)| + |(ηmax : ℝ)| + 2 * d + |l + M.trace| :=
    ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  obtain ⟨CH, hCH0, hCH⟩ := harnack_contact hd lam
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = min (1 / 4) (c / (8 * (CH + 1))) := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; exact lt_min (by norm_num) (by positivity)
  have hβ4 : β ≤ 1 / 4 := by rw [hβ]; exact min_le_left _ _
  have hβc : β ≤ c / (8 * (CH + 1)) := by rw [hβ]; exact min_le_right _ _
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (1 / 2) (c * d / (8 * (lam + 1))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min (by norm_num) (by positivity)
  have hε2 : ε ≤ 1 / 2 := by rw [hε]; exact min_le_left _ _
  have hεc : ε ≤ c * d / (8 * (lam + 1)) := by rw [hε]; exact min_le_right _ _
  have hlamε : lam * ε ≤ c * d / 8 := by
    have h1 : ε * (8 * (lam + 1)) ≤ c * d := by
      rw [le_div_iff₀ (by positivity)] at hεc; linarith
    nlinarith
  refine ⟨β, hβ0, by linarith, ε, hε0, by linarith,
    ⌈(3 * lam + 2 * d) / c⌉₊ + ⌈1 / ε⌉₊ + 1, ?_⟩
  intro n hn η hη hlow u hu v hv x₀ hx₀ p₀ hp₀ x₀' hx₀' p₀' hp₀' hbu hbv
  -- `n` is large
  have hnR : ((⌈(3 * lam + 2 * d) / c⌉₊ + ⌈1 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at hnR
  have hc1 := Nat.le_ceil ((3 * lam + 2 * d) / c)
  have hc2 := Nat.le_ceil (1 / ε)
  have hc3 : (0 : ℝ) ≤ ⌈1 / ε⌉₊ := Nat.cast_nonneg _
  have hc4 : (0 : ℝ) ≤ ⌈(3 * lam + 2 * d) / c⌉₊ := Nat.cast_nonneg _
  have hn1 : (3 * lam + 2 * d) / c < n := by linarith
  have hn1' : 3 * lam + 2 * d < c * n := by
    rw [div_lt_iff₀ hc] at hn1; linarith
  have hεn : 1 ≤ ε * n := by
    have : 1 / ε ≤ n := by linarith
    rw [div_le_iff₀ hε0] at this; linarith
  have hnpos : (1 : ℝ) ≤ n := by linarith
  have hβsq : CH * (β * n) ^ 2 ≤ c * n ^ 2 / 8 := by
    have h1 : β * (8 * (CH + 1)) ≤ c := by
      rw [le_div_iff₀ (by positivity)] at hβc; linarith
    have h2 : CH * β ^ 2 ≤ c / 8 := by nlinarith
    have : CH * (β * n) ^ 2 = CH * β ^ 2 * n ^ 2 := by ring
    rw [this]; nlinarith
  -- the legal stabilizing representatives
  obtain ⟨h, hhLS, rfl⟩ := exists_of_mem_inter hu
  obtain ⟨h', hh'LS, rfl⟩ := exists_of_mem_inter hv
  -- Harnack at the contact points
  have hHu := hCH n β hβ4 _ x₀ hx₀ (gapBelow_nonneg hp₀) (gapBelow_self _ _ _)
    (fun y hy => by rw [lapR_gapBelow, abs_neg, hlam]; exact abs_lapR_perturbed_le hd1 hη hhLS hy)
  have hHv := hCH n β hβ4 _ x₀' hx₀' (gapAbove_nonneg hp₀') (gapAbove_self _ _ _)
    (fun y hy => by rw [lapR_gapAbove, hlam]; exact abs_lapR_perturbed_le hd1 hη hh'LS hy)
  -- barrier
  have hBu := barrier hd1 hlam0 (g := gapBelow _ x₀ p₀) (fun x hx => by
      rw [lapR_gapBelow, hlam]
      exact (abs_le.1 (by rw [← abs_neg, neg_neg]; exact abs_lapR_perturbed_le hd1 hη hhLS hx)).2)
    (a := c * (n : ℝ) ^ 2) (fun y hy => by have := hbu y hy; unfold gapBelow; linarith)
  have hBv := barrier hd1 hlam0 (g := gapAbove _ x₀' p₀') (fun x hx => by
      rw [lapR_gapAbove, hlam]
      exact (abs_le.1 (abs_lapR_perturbed_le hd1 hη hh'LS hx)).2)
    (a := c * (n : ℝ) ^ 2) (fun y hy => by have := hbv y hy; unfold gapAbove; linarith)
  -- comparison
  obtain ⟨G, hG, hG0, hGr⟩ := exists_int_harmonic (p₀' - p₀)
  obtain ⟨y, hy, hcmp⟩ := comparison hd hε0 (by linarith) hεn hlow hhLS hh'LS G hG
  have hyn1 := MuLipschitz.le_norm_of_mem_bdry_ballZ0 hy
  have hyn2 := MuLipschitz.norm_lt_of_mem_bdry_ballZ0 hy
  have hyn3 : ‖toE y‖ ≤ n := by nlinarith
  have hyB : y ∈ ballZ0 (d := d) (n : ℝ) := MuLipschitz.mem_ballZ0.2 (by nlinarith)
  have hup : gapBelow (fun x => (h x : ℝ) - (qlZ l x + qMZ M x)) x₀ p₀ y +
      gapAbove (fun x => (h' x : ℝ) - (qlZ l x + qMZ M x)) x₀' p₀' y ≤
      gapBelow (fun x => (h x : ℝ) - (qlZ l x + qMZ M x)) x₀ p₀ 0 +
      gapAbove (fun x => (h' x : ℝ) - (qlZ l x + qMZ M x)) x₀' p₀' 0 + d * ‖toE y‖ := by
    rw [gap_add, gap_add, MuLipschitz.toE_zero, inner_zero_right]
    have h1 : ((h' y + G y - h y : ℤ) : ℝ) ≤ ((h' 0 + G 0 - h 0 : ℤ) : ℝ) := by exact_mod_cast hcmp
    push_cast at h1
    rw [hG0, Int.cast_zero] at h1
    have h2 := (abs_le.1 (hGr y)).1
    linarith
  exact flat_arith hlam0 hdR hnpos hε0 hε2 hlamε hβsq hn1' hyn1 hyn3 (hBu y hyB) (hBv y hyB)
    hHu hHv hup

/-- **Lemma 7.5** (`flat`) from the remaining inputs: Lemma 6.2' with a legal
stabilizing witness, the shell estimate (Lemma 5.5 on annuli), Lemma 7.4 and Lemma 6.4(3). -/
theorem flat_of_bending (hbend : NearMaxBendingStabilizingStmt) (hshell : ShellBoundStmt)
    (hlow : OdometerLowerBoundStmt) (heff : EffectiveOperatorBasicStmt) : FlatStmt :=
  flat_of_steps hbend hshell hlow heff noOppositeBending

end RandomSandpile

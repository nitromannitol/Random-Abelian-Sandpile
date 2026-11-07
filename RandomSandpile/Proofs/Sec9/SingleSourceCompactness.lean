import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessAA
import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessOuter
import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessGradient
import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessErr
import RandomSandpile.Proofs.Sec5.MuBounded
import RandomSandpile.Proofs.Sec9.OpenBoundaryLapLipschitz

/-! # Theorem 9.2: `SSCompactnessStmt` from Fey-Levine-Peres 2010, Theorem 1.1

`ssCompactness_of_flp : LatticeProb.External.FeyLevinePeresRadius → SSCompactnessStmt`. The only
literature input is FLP Theorem 1.1, stated verbatim in Lattice-Probability (the outer bound,
reduced in `ssOuterBound_of_flp`); the lattice Green function asymptotics (a former input) are
Lattice-Probability theorems (`ssGreen_asymp`).

Notation: `v_n = singleSourceOdometer η n`, `s = n^{1/d}` (`ssScale`), `g = ssGreen d` (`Δ g = -δ_0`),
`w_n = v_n - n g` (`ssW`), `z = [s x]`. The rescaled odometer splits as
`v̄_n - G = W_n + E_n` (`SSComp.rescale_eq`) with the corrector
`W_n(x) = n^{-2/d} w_n(z) + n^{1-2/d} κ + λ_n` (`ssCorrector`) and the Green error `E_n`
(`ssGreenErr`, `→ 0` locally uniformly off `0`, `ssGreenErr_small`). Then:
1. `|Δ v_n + n δ_0| ≤ Λ = 4d - 3 + |η_min|` (`abs_lap_add_le`): the final configuration lies in
   `[min(η, 0), 2d - 1]` (`min_le_ssSandpile`: where `v_n > 0`, `v_n - δ_y` would otherwise be a
   smaller stabilizing function).
2. `v_n` vanishes outside `B_{R(n+1)^{1/d}}` (outer bound), so the gradient bound
   `ssGradient_core` and chaining along lattice paths give
   `|W_n(x) - W_n(y)| ≤ L_m (|x - y| + 1/s)` on `B̄_m` (`ssCorrector_lip`).
3. At a reference point `x₀` far out, `v_n = 0`, so `W_n(x₀) = -(E_n(x₀) + G(x₀))` is bounded, and
   `W_n` is bounded on every ball (`ssCorrector_bdd`).
4. Arzelà–Ascoli on balls (`arzelaAscoli_locallyUniform`) gives a subsequence `W_n → v`
   locally uniformly on `ℝ^d`, `v` continuous; with `E_n → 0` off `0`, `v̄_n → v + G` there.
This route replaces steps 3-4 of the decomposition (maximum principle, `SSInteriorLipschitzStmt`).
-/

noncomputable section

open Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- `w_n = v_n - n g` on the lattice. -/
def ssW (d : ℕ) (η : Site d → ℤ) (n : ℕ) (p : Site d) : ℝ :=
  (singleSourceOdometer η n p : ℝ) - n * ssGreen d p

/-- The corrector `W_n(x) = n^{-2/d} w_n([s x]) + n^{1-2/d} κ + λ_n`. -/
def ssCorrector (d : ℕ) (η : Site d → ℤ) (κ : ℝ) (n : ℕ) (x : Rd d) : ℝ :=
  (n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n (latticeRound (ssScale d n • x))
    + (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n

namespace SSComp

/-- `v̄_n = W_n + E_n + G`. -/
theorem rescale_eq (η : Site d → ℤ) (κ : ℝ) (n : ℕ) (x : Rd d) :
    rescaleSingleSource (singleSourceOdometer η n) n x
      = ssCorrector d η κ n x + ssGreenErr d κ n x + fundamentalSolution d x := by
  simp only [rescaleSingleSource, ssCorrector, ssW, ssGreenErr, ssScale]
  ring

theorem ssDirac_self (y : Site d) : dirac y y = 1 := by
  unfold dirac; simp

theorem ssDirac_of_ne {y z : Site d} (h : z ≠ y) : dirac y z = 0 := by
  unfold dirac; split_ifs with h' <;> simp_all

/-- **Lower bound for the final configuration**: `s_n = η + n δ_0 + Δ v_n ≥ min(η, 0)`. -/
theorem min_le_ssSandpile {η : Site d → ℤ} {n : ℕ}
    (hne : (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty) (y : Site d) :
    min (η y) 0 ≤ η y + (n : ℤ) * dirac 0 y + lap (singleSourceOdometer η n) y := by
  set v := singleSourceOdometer η n with hv
  have hmem : (∀ x, 0 ≤ v x) ∧ ∀ x, lap v x + (η x + (n : ℤ) * dirac 0 x) ≤ 2 * (d : ℤ) - 1 :=
    mem_stabilizing_univ.1 (isLeast_singleSourceOdometer hne).1
  have hdy : 0 ≤ (n : ℤ) * dirac 0 y :=
    mul_nonneg (Int.natCast_nonneg n) (SSOuter.dirac_nonneg' 0 y)
  by_cases hvy : v y = 0
  · have hlap : 0 ≤ lap v y := by
      rw [lap_eq, hvy]
      have := Rossin.nbrSumZ_nonneg hmem.1 y
      linarith
    have := min_le_left (η y) 0
    linarith
  · have hvy1 : 1 ≤ v y := by have := hmem.1 y; omega
    by_contra hcon
    push Not at hcon
    have hneg : η y + (n : ℤ) * dirac 0 y + lap v y ≤ -1 := by
      have := min_le_right (η y) 0; omega
    set v' : Site d → ℤ := fun z => v z - dirac y z with hv'
    have hsum : v = v' + dirac y := funext fun z => by simp [hv']
    have hlin : ∀ z, lap v' z = lap v z - lap (dirac y) z := fun z => by
      have := Rossin.lap_add' v' (dirac y) z
      rw [← hsum] at this
      linarith
    have hv'mem : v' ∈ stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ := by
      rw [mem_stabilizing_univ]
      refine ⟨fun z => ?_, fun z => ?_⟩
      · show 0 ≤ v z - dirac y z
        by_cases hz : z = y
        · rw [hz, ssDirac_self]; omega
        · rw [ssDirac_of_ne hz]; have := hmem.1 z; omega
      · have h1 := hlin z
        have h2 := lap_dirac_ge y z
        have h3 := hmem.2 z
        by_cases hz : z = y
        · subst hz
          rw [ssDirac_self] at h2
          linarith
        · rw [ssDirac_of_ne hz] at h2
          linarith
    have h5 : v y ≤ v y - dirac y y := singleSourceOdometer_le hv'mem y
    rw [ssDirac_self] at h5
    omega

/-- **`|Δ v_n + n δ_0| ≤ 4d - 3 + |η_min|`** for a background `η_min ≤ η ≤ 2d - 2`. -/
theorem abs_lap_add_le {ηmin : ℤ} {η : Site d → ℤ} (hd : 1 ≤ d)
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2) (n : ℕ) (y : Site d) :
    |(lap (singleSourceOdometer η n) y : ℝ) + (n : ℝ) * (if y = 0 then 1 else 0)|
      ≤ 4 * d - 3 + |(ηmin : ℝ)| := by
  have hne := ssNonempty d hd η (fun x => (hη x).2) n
  have hlow := min_le_ssSandpile hne y
  have hup := (mem_stabilizing_univ.1 (isLeast_singleSourceOdometer hne).1).2 y
  have h1 := (hη y).1
  have h2 := (hη y).2
  have hdZ : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hint : |lap (singleSourceOdometer η n) y + (n : ℤ) * dirac 0 y|
      ≤ 4 * (d : ℤ) - 3 + |ηmin| := by
    rw [abs_le]
    constructor
    · have hm : -|ηmin| ≤ min (η y) 0 :=
        le_min (by have := neg_abs_le ηmin; linarith) (by have := abs_nonneg ηmin; linarith)
      linarith
    · have := neg_abs_le ηmin
      linarith
  have hreal : ((|lap (singleSourceOdometer η n) y + (n : ℤ) * dirac 0 y| : ℤ) : ℝ)
      ≤ ((4 * (d : ℤ) - 3 + |ηmin| : ℤ) : ℝ) := Int.cast_le.2 hint
  push_cast at hreal
  have hcast : (n : ℝ) * (if y = 0 then 1 else 0) = (n : ℝ) * ((dirac 0 y : ℤ) : ℝ) := by
    by_cases hy : y = 0
    · rw [if_pos hy, hy, ssDirac_self]; simp
    · rw [if_neg hy, ssDirac_of_ne hy]; simp
  rw [hcast]
  exact hreal

theorem rpow_succ_le_two_mul (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ 2 * ssScale d n := by
  have h1 : (n : ℝ) + 1 ≤ 2 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : (2 : ℝ) ^ (1 / (d : ℝ)) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / (d : ℝ)) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by rw [div_le_one (by linarith)]; exact hd')
      _ = 2 := Real.rpow_one 2
  calc ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ (2 * (n : ℝ)) ^ (1 / (d : ℝ)) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = 2 ^ (1 / (d : ℝ)) * ssScale d n := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 2 * ssScale d n :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem abs_latticeRound_le (w : Rd d) (i : Fin d) :
    |((latticeRound w i : ℤ) : ℝ)| ≤ ‖w‖ + 1 := by
  have h1 := Int.floor_le (w i)
  have h2 := Int.lt_floor_add_one (w i)
  have h3 : |w i| ≤ ‖w‖ := by
    have := PiLp.norm_apply_le w i
    rwa [Real.norm_eq_abs] at this
  show |((⌊w i⌋ : ℤ) : ℝ)| ≤ ‖w‖ + 1
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

theorem abs_latticeRound_sub_le (w w' : Rd d) (i : Fin d) :
    |((latticeRound w i - latticeRound w' i : ℤ) : ℝ)| ≤ ‖w - w'‖ + 1 := by
  have h1 := Int.floor_le (w i)
  have h2 := Int.lt_floor_add_one (w i)
  have h1' := Int.floor_le (w' i)
  have h2' := Int.lt_floor_add_one (w' i)
  have h3 : |w i - w' i| ≤ ‖w - w'‖ := by
    have := PiLp.norm_apply_le (w - w') i
    rwa [PiLp.sub_apply, Real.norm_eq_abs] at this
  show |(((⌊w i⌋ - ⌊w' i⌋ : ℤ)) : ℝ)| ≤ ‖w - w'‖ + 1
  push_cast
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

/-- **Asymptotic Lipschitz bound for the corrector on `B̄_m`.** -/
theorem ssCorrector_lip (hd : 2 ≤ d) {ηmin : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2) {R0 : ℝ} (hR0 : 0 < R0)
    (hout : ∀ (n : ℕ) (z : Site d), R0 * ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ ‖toE z‖ →
      singleSourceOdometer η n z = 0) (κ : ℝ) (m : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Rd d, ‖x‖ ≤ m → ‖y‖ ≤ m →
      |ssCorrector d η κ n x - ssCorrector d η κ n y| ≤ L * dist x y + L / ssScale d n := by
  obtain ⟨C, hC, hgr⟩ := ssGradient_core d hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hΛ : (0 : ℝ) ≤ 4 * d - 3 + |(ηmin : ℝ)| := by
    have := abs_nonneg (ηmin : ℝ); linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hcm : (0 : ℝ) < 2 * R0 + m + 3 := by linarith
  refine ⟨d * C * (4 * d - 3 + |(ηmin : ℝ)|) * (2 * R0 + m + 3),
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC.le) hΛ) hcm.le, ?_⟩
  intro n hn x y hx hy
  have hs : 0 < ssScale d n := ssScale_pos hn
  have hs0 : ssScale d n ≠ 0 := hs.ne'
  have hs1 : 1 ≤ ssScale d n := one_le_ssScale hn
  obtain ⟨Rb, hRb⟩ : ∃ Rb : ℕ, Rb = ⌈(2 * R0 + m + 1) * ssScale d n⌉₊ := ⟨_, rfl⟩
  have hpos1 : 0 ≤ (2 * R0 + m + 1) * ssScale d n := mul_nonneg (by linarith) hs.le
  have hRb1 : (2 * R0 + m + 1) * ssScale d n ≤ Rb := hRb ▸ Nat.le_ceil _
  have hRb2 : (Rb : ℝ) < (2 * R0 + m + 1) * ssScale d n + 1 :=
    hRb ▸ Nat.ceil_lt_add_one hpos1
  have h2s := rpow_succ_le_two_mul (d := d) (by omega) hn
  have hu : ∀ z : Site d, (∃ i, (Rb : ℤ) ≤ |z i|) → singleSourceOdometer η n z = 0 := by
    rintro z ⟨i, hi⟩
    apply hout n z
    have h1 : |(z i : ℝ)| ≤ ‖toE z‖ := by
      have := PiLp.norm_apply_le (toE z) i
      rwa [toE_apply, Real.norm_eq_abs] at this
    have h2 : (Rb : ℝ) ≤ |(z i : ℝ)| := by
      have : ((Rb : ℤ) : ℝ) ≤ ((|z i| : ℤ) : ℝ) := Int.cast_le.2 hi
      push_cast at this
      exact this
    have h3 : R0 * ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ R0 * (2 * ssScale d n) :=
      mul_le_mul_of_nonneg_left h2s hR0.le
    have h4 : R0 * (2 * ssScale d n) ≤ (2 * R0 + m + 1) * ssScale d n := by nlinarith
    linarith
  have hM := fun y => abs_lap_add_le (ηmin := ηmin) (η := η) (by omega) hη n y
  have hstep : ∀ (p : Site d) (i : Fin d), p ∈ boxFinset (0 : Site d) (Rb + 1) →
      |ssW d η n (p + unit i) - ssW d η n p|
        ≤ C * (4 * d - 3 + |(ηmin : ℝ)|) * ((Rb : ℝ) + 1) := by
    intro p i hp
    have := hgr (singleSourceOdometer η n) (4 * d - 3 + |(ηmin : ℝ)|) n Rb hu hM p hp i
    have e : ssW d η n (p + unit i) - ssW d η n p
        = ((singleSourceOdometer η n (p + unit i) : ℝ) - singleSourceOdometer η n p)
          - (n : ℝ) * (ssGreen d (p + unit i) - ssGreen d p) := by
      simp only [ssW]; ring
    rw [e]; exact this
  have hzb : ∀ w : Rd d, ‖w‖ ≤ ssScale d n * m → ∀ i, |latticeRound w i| ≤ (Rb : ℤ) + 1 := by
    intro w hw i
    have h1 := abs_latticeRound_le w i
    have h2 : ssScale d n * m ≤ Rb := by nlinarith
    have h3 : ((|latticeRound w i| : ℤ) : ℝ) ≤ (((Rb : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h3
  have hxs : ‖ssScale d n • x‖ ≤ ssScale d n * m := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]; exact mul_le_mul_of_nonneg_left hx hs.le
  have hys : ‖ssScale d n • y‖ ≤ ssScale d n * m := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]; exact mul_le_mul_of_nonneg_left hy hs.le
  have hGood : ∀ p : Site d, (∀ i, min (latticeRound (ssScale d n • x) i)
        (latticeRound (ssScale d n • y) i) ≤ p i ∧
        p i ≤ max (latticeRound (ssScale d n • x) i) (latticeRound (ssScale d n • y) i)) →
      p ∈ boxFinset (0 : Site d) (Rb + 1) := by
    intro p hp
    rw [mem_boxFinset_iff]
    intro i
    have hzi := hzb _ hxs i
    have hz'i := hzb _ hys i
    obtain ⟨hp1, hp2⟩ := hp i
    simp only [Pi.zero_apply, sub_zero]
    push_cast
    rw [abs_le] at hzi hz'i ⊢
    have hmin : -((Rb : ℤ) + 1) ≤ min (latticeRound (ssScale d n • x) i)
        (latticeRound (ssScale d n • y) i) := le_min hzi.1 hz'i.1
    have hmax : max (latticeRound (ssScale d n • x) i) (latticeRound (ssScale d n • y) i)
        ≤ (Rb : ℤ) + 1 := max_le hzi.2 hz'i.2
    constructor <;> linarith
  have hch := OpenBoundaryLapLipschitz.chain_bound (f := ssW d η n)
    (K := C * (4 * d - 3 + |(ηmin : ℝ)|) * ((Rb : ℝ) + 1))
    (Good := fun p => p ∈ boxFinset (0 : Site d) (Rb + 1)) hstep _
    (latticeRound (ssScale d n • x)) (latticeRound (ssScale d n • y)) rfl hGood
  have hsx : 0 ≤ ssScale d n * ‖x - y‖ + 1 := by
    have := mul_nonneg hs.le (norm_nonneg (x - y)); linarith
  have hNle : ((∑ i, (latticeRound (ssScale d n • y) i
        - latticeRound (ssScale d n • x) i).natAbs : ℕ) : ℝ)
      ≤ d * (ssScale d n * ‖x - y‖ + 1) := by
    rw [Nat.cast_sum]
    calc ∑ i, (((latticeRound (ssScale d n • y) i
            - latticeRound (ssScale d n • x) i).natAbs : ℕ) : ℝ)
        ≤ ∑ _i : Fin d, (ssScale d n * ‖x - y‖ + 1) := Finset.sum_le_sum fun i _ => by
          have h0 : (((latticeRound (ssScale d n • y) i
              - latticeRound (ssScale d n • x) i).natAbs : ℕ) : ℝ)
              = |((latticeRound (ssScale d n • y) i - latticeRound (ssScale d n • x) i : ℤ) : ℝ)| := by
            simp
          rw [h0]
          have h1 := abs_latticeRound_sub_le (ssScale d n • y) (ssScale d n • x) i
          have e : ‖ssScale d n • y - ssScale d n • x‖ = ssScale d n * ‖x - y‖ := by
            rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs, norm_sub_rev]
          linarith
      _ = d * (ssScale d n * ‖x - y‖ + 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hW : ssCorrector d η κ n x - ssCorrector d η κ n y
      = (n : ℝ) ^ (-(2 / (d : ℝ))) * (ssW d η n (latticeRound (ssScale d n • x))
        - ssW d η n (latticeRound (ssScale d n • y))) := by
    simp only [ssCorrector]; ring
  rw [hW, rpow_neg_two_div, abs_mul, abs_of_pos (inv_pos.2 (pow_pos hs 2))]
  have hK0 : 0 ≤ C * (4 * d - 3 + |(ηmin : ℝ)|) * ((Rb : ℝ) + 1) :=
    mul_nonneg (mul_nonneg hC.le hΛ) (by positivity)
  have hRbs : (Rb : ℝ) + 1 ≤ (2 * R0 + m + 3) * ssScale d n := by nlinarith
  have hA : |ssW d η n (latticeRound (ssScale d n • x)) - ssW d η n (latticeRound (ssScale d n • y))|
      ≤ d * (ssScale d n * ‖x - y‖ + 1) *
        (C * (4 * d - 3 + |(ηmin : ℝ)|) * ((2 * R0 + m + 3) * ssScale d n)) := by
    calc _ ≤ _ := hch
      _ ≤ d * (ssScale d n * ‖x - y‖ + 1) * (C * (4 * d - 3 + |(ηmin : ℝ)|) * ((Rb : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hNle hK0
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hRbs (mul_nonneg hC.le hΛ))
          (mul_nonneg (Nat.cast_nonneg _) hsx)
  calc (ssScale d n ^ 2)⁻¹ * |ssW d η n (latticeRound (ssScale d n • x))
        - ssW d η n (latticeRound (ssScale d n • y))|
      ≤ (ssScale d n ^ 2)⁻¹ * (d * (ssScale d n * ‖x - y‖ + 1) *
        (C * (4 * d - 3 + |(ηmin : ℝ)|) * ((2 * R0 + m + 3) * ssScale d n))) :=
        mul_le_mul_of_nonneg_left hA (inv_nonneg.2 (pow_nonneg hs.le 2))
    _ = d * C * (4 * d - 3 + |(ηmin : ℝ)|) * (2 * R0 + m + 3) * dist x y
        + d * C * (4 * d - 3 + |(ηmin : ℝ)|) * (2 * R0 + m + 3) / ssScale d n := by
        rw [dist_eq_norm]
        field_simp

/-- **The corrector is bounded on every ball.** -/
theorem ssCorrector_bdd (hd : 2 ≤ d) {ηmin : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2) {R0 : ℝ} (hR0 : 0 < R0)
    (hout : ∀ (n : ℕ) (z : Site d), R0 * ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ ‖toE z‖ →
      singleSourceOdometer η n z = 0) {κ C1 R1 : ℝ} (hR1 : 1 ≤ R1)
    (hasymp : ∀ z : Site d, R1 ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C1 * ‖toE z‖ ^ (-(d : ℝ)))
    (m : ℕ) : ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ x : Rd d, ‖x‖ ≤ m →
      |ssCorrector d η κ n x| ≤ K := by
  have hsd := Real.sqrt_nonneg (d : ℝ)
  set ρ0 : ℝ := 2 * R0 + Real.sqrt d + 1 with hρ0
  have hρ0pos : 0 < ρ0 := by linarith
  set x0 : Rd d := ρ0 • toE (unit (⟨0, by omega⟩ : Fin d)) with hx0def
  have hx0 : ‖x0‖ = ρ0 := by
    rw [hx0def, norm_smul, Real.norm_eq_abs, abs_of_pos hρ0pos,
      OpenBoundaryLapLipschitz.norm_toE_unit', mul_one]
  have hx0ne : x0 ≠ 0 := norm_pos_iff.1 (by rw [hx0]; exact hρ0pos)
  obtain ⟨N, hN⟩ := ssGreenErr_small hd hR1 hasymp (isCompact_singleton (x := x0))
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hx0ne) one_pos
  set B : ℝ := ∑ k ∈ Finset.range N, |ssGreenErr d κ k x0| + 1 with hBdef
  have hB : ∀ n, |ssGreenErr d κ n x0| ≤ B := fun n => by
    rcases lt_or_ge n N with h | h
    · have := Finset.single_le_sum (f := fun k => |ssGreenErr d κ k x0|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.2 h)
      linarith
    · have := hN n h x0 (Set.mem_singleton x0)
      have hS : 0 ≤ ∑ k ∈ Finset.range N, |ssGreenErr d κ k x0| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
  have hWx0 : ∀ n, 1 ≤ n →
      ssCorrector d η κ n x0 = -(ssGreenErr d κ n x0 + fundamentalSolution d x0) := by
    intro n hn
    have hs := ssScale_pos (d := d) hn
    have hs1 := one_le_ssScale (d := d) hn
    have h1 := rescale_eq η κ n x0
    have hz := SSComp.norm_toE_latticeRound_sub_le_sqrt (ssScale d n • x0)
    have hw : ‖ssScale d n • x0‖ = ssScale d n * ρ0 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, hx0]
    have hge : ssScale d n * ρ0 - Real.sqrt d ≤ ‖toE (latticeRound (ssScale d n • x0))‖ := by
      have := norm_le_insert' (ssScale d n • x0) (toE (latticeRound (ssScale d n • x0)))
      rw [norm_sub_rev] at this
      linarith
    have h2s := rpow_succ_le_two_mul (d := d) (by omega) hn
    have hfar : R0 * ((n : ℝ) + 1) ^ (1 / (d : ℝ))
        ≤ ‖toE (latticeRound (ssScale d n • x0))‖ := by
      have e1 := mul_le_mul_of_nonneg_left h2s hR0.le
      have e2 := mul_nonneg (sub_nonneg.2 hs1) hsd
      rw [hρ0] at hge
      nlinarith
    have h2 : rescaleSingleSource (singleSourceOdometer η n) n x0 = 0 := by
      have hv : singleSourceOdometer η n (latticeRound (ssScale d n • x0)) = 0 := hout n _ hfar
      simp only [rescaleSingleSource]
      rw [show (n : ℝ) ^ (1 / (d : ℝ)) = ssScale d n from rfl, hv]
      simp
    linarith
  obtain ⟨L, hL0, hL⟩ := ssCorrector_lip hd hη hR0 hout κ (max m ⌈ρ0⌉₊)
  refine ⟨B + |fundamentalSolution d x0| + L * (m + ρ0) + L, fun n hn x hx => ?_⟩
  have hxm : ‖x‖ ≤ ((max m ⌈ρ0⌉₊ : ℕ) : ℝ) :=
    hx.trans (by exact_mod_cast le_max_left _ _)
  have hx0m : ‖x0‖ ≤ ((max m ⌈ρ0⌉₊ : ℕ) : ℝ) := by
    rw [hx0]; exact (Nat.le_ceil ρ0).trans (by exact_mod_cast le_max_right _ _)
  have h1 := hL n hn x x0 hxm hx0m
  have h2 : dist x x0 ≤ m + ρ0 := (dist_le_norm_add_norm x x0).trans (by rw [hx0]; linarith)
  have h3 : L / ssScale d n ≤ L := div_le_self hL0 (one_le_ssScale hn)
  rw [hWx0 n hn] at h1
  have h4 := hB n
  have h5 : L * dist x x0 ≤ L * (m + ρ0) := mul_le_mul_of_nonneg_left h2 hL0
  have h6 : |ssCorrector d η κ n x| ≤ |ssCorrector d η κ n x
      - -(ssGreenErr d κ n x0 + fundamentalSolution d x0)|
      + |-(ssGreenErr d κ n x0 + fundamentalSolution d x0)| := by
    have := abs_sub_abs_le_abs_sub (ssCorrector d η κ n x)
      (-(ssGreenErr d κ n x0 + fundamentalSolution d x0))
    linarith
  have h7 : |-(ssGreenErr d κ n x0 + fundamentalSolution d x0)|
      ≤ B + |fundamentalSolution d x0| := by
    rw [abs_neg]
    exact (abs_add_le _ _).trans (by linarith)
  linarith

end SSComp

open SSComp in
/-- **Theorem 9.2** (`SSCompactnessStmt`), from
Fey-Levine-Peres 2010, Theorem 1.1 (`LatticeProb.External.FeyLevinePeresRadius`, verbatim). -/
theorem ssCompactness_of_flp (hFLP : External.FeyLevinePeresRadius) : SSCompactnessStmt := by
  intro d hd ηmin η hη nk hnk
  obtain ⟨R0, hR0, hout0⟩ := ssOuterBound_of_flp hFLP d hd ηmin
  have hout : ∀ (n : ℕ) (z : Site d), R0 * ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ ‖toE z‖ →
      singleSourceOdometer η n z = 0 := fun n z h => hout0 η hη n z h
  obtain ⟨κ, C1, R1, hR1, hasymp⟩ := ssGreen_asymp hd
  set F : ℕ → Rd d → ℝ := fun j => ssCorrector d η κ (nk (j + 1)) with hF
  have hnk1 : ∀ j, 1 ≤ nk (j + 1) := fun j => by
    have : j + 1 ≤ nk (j + 1) := hnk.id_le (j + 1)
    omega
  have hnkT : Tendsto (fun j => nk (j + 1)) atTop atTop :=
    hnk.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hK : ∀ m : ℕ, ∃ K : ℝ, ∀ j x, ‖x‖ ≤ m → |F j x| ≤ K := fun m => by
    obtain ⟨K, hK⟩ := ssCorrector_bdd hd hη hR0 hout hR1 hasymp m
    exact ⟨K, fun j x hx => hK _ (hnk1 j) x hx⟩
  have hL : ∀ m : ℕ, ∃ L : ℝ, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ j x y, ‖x‖ ≤ m → ‖y‖ ≤ m → |F j x - F j y| ≤ L * dist x y + e j := fun m => by
    obtain ⟨L, -, hL⟩ := ssCorrector_lip hd hη hR0 hout κ m
    refine ⟨L, fun j => L / ssScale d (nk (j + 1)), ?_, fun j x y hx hy => hL _ (hnk1 j) x y hx hy⟩
    exact tendsto_const_nhds.div_atTop ((ssScale_tendsto (by omega)).comp hnkT)
  obtain ⟨φ, hφ, V, hV, hTLU⟩ := arzelaAscoli_locallyUniform d F hK hL
  refine ⟨fun j => φ j + 1, fun a b hab => Nat.add_lt_add_right (hφ hab) 1, V, hV, ?_⟩
  beta_reduce
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ne]
  intro K hKs hKc
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hU := Metric.tendstoUniformlyOn_iff.1
    ((tendstoLocallyUniformly_iff_forall_isCompact.1 hTLU) K hKc) (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := ssGreenErr_small hd hR1 hasymp hKc (fun x hx => hKs hx)
    (by positivity : 0 < ε / 2)
  have hev : ∀ᶠ j in atTop, N ≤ nk (φ j + 1) :=
    (hnkT.comp hφ.tendsto_atTop).eventually_ge_atTop N
  filter_upwards [hU, hev] with j hj hjN x hx
  have h1 : |V x - ssCorrector d η κ (nk (φ j + 1)) x| < ε / 2 := by
    have := hj x hx
    rwa [Real.dist_eq] at this
  have h2 := hN _ hjN x hx
  rw [rescale_eq η κ (nk (φ j + 1)) x, Real.dist_eq]
  calc |V x + fundamentalSolution d x - (ssCorrector d η κ (nk (φ j + 1)) x
        + ssGreenErr d κ (nk (φ j + 1)) x + fundamentalSolution d x)|
      = |(V x - ssCorrector d η κ (nk (φ j + 1)) x) - ssGreenErr d κ (nk (φ j + 1)) x| := by
        congr 1; ring
    _ ≤ |V x - ssCorrector d η κ (nk (φ j + 1)) x| + |ssGreenErr d κ (nk (φ j + 1)) x| :=
        abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end RandomSandpile

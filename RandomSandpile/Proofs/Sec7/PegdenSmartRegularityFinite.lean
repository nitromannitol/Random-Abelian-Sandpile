import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTrace
import RandomSandpile.Steps.Sec7.OdometerLowerBound

/-!
# Finitely supported sandpiles on `ℤ^d` are stabilizable; the free odometer is finite

A configuration `σ : ℤ^d → ℤ` with `σ ≤ 0` off a finite set `S` is stabilizable on `ℤ^d`
(`stabilizing_nonempty_of_finset`, for `d ≥ 1`). Proof by Rossin's observation
(`rossinStabilizable`, `RandomSandpile/Infra/Rossin.lean`): with `M ≥ max σ`, `S ⊆ [-K, K)^d`
and a period `N ≥ 2K` with `M (2K)^d < N`, the `N`-periodic configuration `φ` equal to `M` on the
translates of `[-K, K)^d` and `0` elsewhere dominates `σ` and has fewer than `d N^d` chips per
period, so its stabilizing odometer `w` also stabilizes `σ`.

Consequence: for bounded `W` the free odometer `v_n = freeOdometer η W_n` is not the junk value,
and `Δ_{ℤ^d} v_n + η 𝟙_{W_n} ≤ 2d - 1` on `ℤ^d` (`lap_freeOdometer_add_indicator_le`), the
finiteness left open in the docstring of `RandomSandpile/Defs/Odometer.lean`.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace PegdenSmartRegularity

variable {d : ℕ}

theorem red_add_smul_eq {N : ℕ} (y m : Site d) : Rossin.red N (y + (N : ℤ) • m) = Rossin.red N y := by
  funext i
  simp only [Rossin.red, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact Int.add_mul_emod_self_left (y i) N (m i)

/-- **Finitely supported configurations stabilize on `ℤ^d`** (by Rossin's observation). -/
theorem stabilizing_nonempty_of_finset (hd : 1 ≤ d) (σ : Site d → ℤ) (S : Finset (Site d))
    (hS : ∀ z, z ∉ S → σ z ≤ 0) : (stabilizing σ Set.univ).Nonempty := by
  classical
  set M : ℤ := ∑ z ∈ S, |σ z| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun z _ => abs_nonneg _
  have hσM : ∀ z ∈ S, σ z ≤ M := fun z hz =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun z => |σ z|) (fun z _ => abs_nonneg _) hz)
  set K : ℤ := ∑ z ∈ S, ∑ i, |z i| + 1 with hK
  have hzK : ∀ z ∈ S, ∀ i, |z i| < K := fun z hz i => by
    have h1 : |z i| ≤ ∑ i, |z i| :=
      Finset.single_le_sum (f := fun i => |z i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, |z i| ≤ ∑ z ∈ S, ∑ i, |z i| :=
      Finset.single_le_sum (f := fun z : Site d => ∑ i, |z i|)
        (fun z _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hz
    omega
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ z ∈ S, ∑ i, |z i| := Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun i _ => abs_nonneg _
    omega
  set N : ℕ := (M * (2 * K) ^ d).toNat + (2 * K).toNat + 1 with hNdef
  have hN : 0 < N := by omega
  have hN2K : 2 * K ≤ N := by
    have := Int.self_le_toNat (2 * K); omega
  have hNbig : M * (2 * K) ^ d < N := by
    have := Int.self_le_toNat (M * (2 * K) ^ d); omega
  set Kv : Site d := fun _ => K with hKv
  set φ' : Site d → ℤ := fun z => if ∀ i, Rossin.red N z i < 2 * K then M else 0 with hφ'
  set φ : Site d → ℤ := fun z => φ' (z + Kv) with hφ
  have hper' : IsPeriodic N φ' := fun x m => by simp only [hφ', red_add_smul_eq]
  have hper : IsPeriodic N φ := fun x m => by
    simp only [hφ]
    rw [show x + (N : ℤ) • m + Kv = (x + Kv) + (N : ℤ) • m by abel]
    exact hper' _ _
  -- the number of chips per period
  have hsum : ∑ x ∈ periodBox d N, φ x < (d : ℤ) * (N : ℤ) ^ d := by
    have h1 : ∑ x ∈ periodBox d N, φ x = ∑ x ∈ periodBox d N, φ' x :=
      Rossin.sum_box_add hN hper' Kv
    have h2 : ∑ x ∈ periodBox d N, φ' x ≤
        ∑ x ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) (2 * K)), M := by
      rw [← Finset.sum_filter_add_sum_filter_not (periodBox d N) (fun x => ∀ i, x i < 2 * K)]
      have h0 : ∑ x ∈ (periodBox d N).filter (fun x => ¬ ∀ i, x i < 2 * K), φ' x = 0 :=
        Finset.sum_eq_zero fun x hx => by
          rw [Finset.mem_filter] at hx
          simp only [hφ', Rossin.red_of_mem hx.1, ite_eq_right hx.2]
      rw [h0, add_zero]
      refine (Finset.sum_le_sum fun x hx => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hM0)
      · simp only [hφ']; split_ifs <;> omega
      · intro x hx
        rw [Finset.mem_filter] at hx
        simp only [periodBox, Fintype.mem_piFinset, Finset.mem_Ico] at hx ⊢
        exact fun i => ⟨(hx.1 i).1, hx.2 i⟩
    have h3 : ∑ x ∈ Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) (2 * K)), M =
        M * (2 * K) ^ d := by
      rw [Finset.sum_const, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Int.card_Ico, nsmul_eq_mul, sub_zero]
      push_cast
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have h4 : (N : ℤ) ≤ (d : ℤ) * (N : ℤ) ^ d := by
      have hNpow : (N : ℤ) ≤ (N : ℤ) ^ d := by
        calc (N : ℤ) = (N : ℤ) ^ 1 := (pow_one _).symm
          _ ≤ (N : ℤ) ^ d := pow_le_pow_right₀ (by omega) hd
      have : (1 : ℤ) ≤ d := by exact_mod_cast hd
      nlinarith [pow_pos (show (0 : ℤ) < N by omega) d]
    omega
  obtain ⟨-, w, -, -, -, hwL⟩ := rossinStabilizable d N φ hN hper hsum
  obtain ⟨hw0, hw⟩ := mem_stabilizing_univ.1 hwL.1
  refine ⟨w, mem_stabilizing_univ.2 ⟨hw0, fun x => ?_⟩⟩
  have hφx : σ x ≤ φ x := by
    by_cases hx : x ∈ S
    · have hred : ∀ i, Rossin.red N (x + Kv) i < 2 * K := fun i => by
        have := abs_lt.1 (hzK x hx i)
        simp only [Rossin.red, Pi.add_apply, hKv]
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        omega
      simp only [hφ, hφ', ite_eq_left hred]
      exact hσM x hx
    · have := hS x hx
      simp only [hφ, hφ']; split_ifs <;> omega
  linarith [hw x]

theorem discretize_finite {W : Set (Rd d)} (hW : Bornology.IsBounded W) (n : ℕ) :
    (discretize W n).Finite := by
  obtain ⟨R, hR⟩ := hW.subset_closedBall 0
  refine (OdometerLowerBound.ballZ0_finite ((n : ℝ) * R + 1)).subset fun z hz => ?_
  rw [OdometerLowerBound.mem_ballZ0]
  obtain ⟨w, hw, hwz⟩ := Set.mem_smul_set.1 hz
  have hw' : ‖w‖ ≤ R := by simpa using hR hw
  rw [← hwz, norm_smul, Real.norm_natCast]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- **The free odometer is finite** for bounded `W`. -/
theorem freeOdometer_stabilizing_nonempty (hd : 1 ≤ d) (η : Site d → ℤ) {W : Set (Rd d)}
    (hW : Bornology.IsBounded W) (n : ℕ) :
    (stabilizing ((discretize W n).indicator η) Set.univ).Nonempty :=
  stabilizing_nonempty_of_finset hd _ (discretize_finite hW n).toFinset fun z hz => by
    rw [Set.indicator_of_notMem (by simpa using hz)]

/-- `Δ_{ℤ^d} v_n + η 𝟙_{W_n} ≤ 2d - 1` on `ℤ^d` for the free odometer of a bounded `W`. -/
theorem lap_freeOdometer_add_indicator_le (hd : 1 ≤ d) (η : Site d → ℤ) {W : Set (Rd d)}
    (hW : Bornology.IsBounded W) (n : ℕ) (z : Site d) :
    lap (freeOdometer η (discretize W n)) z + (discretize W n).indicator η z ≤ 2 * (d : ℤ) - 1 :=
  (mem_stabilizing_univ.1 (isLeast_freeOdometer (freeOdometer_stabilizing_nonempty hd η hW n)).1).2 z

end PegdenSmartRegularity

end RandomSandpile

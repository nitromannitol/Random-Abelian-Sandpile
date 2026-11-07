import LatticeProb.Sandpile.RadiusConsequences
import RandomSandpile.Infra.Rossin
import RandomSandpile.Proofs.Sec9.SingleSource
import RandomSandpile.Proofs.Sec9.SingleSourceCompactnessSteps

/-! # Theorem 9.2: the outer bound `SSOuterBoundStmt` from Fey-Levine-Peres

The literature input is Fey-Levine-Peres, *Growth rates and explosions in sandpiles*, J. Stat.
Phys. 138 (2010), Theorem 1.1, stated verbatim in Lattice-Probability as
`LatticeProb.External.FeyLevinePeresRadius`. The monotonicity reduction is proved here. Lattice-Probability's
`Sandpile.flp_specialization` specialises it to the background `h = 2d - 2` and `ε = 1`: for
`N ≥ N₀`, every site toppling in the parallel stabilization of `(2d - 2) + N δ_0` lies in the cube
of radius `A N^{1/d}`.

The reduction (`ssOuterBound_of_flp`):
1. (`exists_stabilizing_podo_limit`) if `s₀` has a stabilizing toppling function, the parallel
   toppling procedure `podo s₀` converges pointwise (it is nondecreasing and bounded by every
   stabilizing function, least action principle `LatticeProb.Sandpile.le_of_isLegalToppling`), and
   its limit `w` is stabilizing; so the least stabilizing function vanishes where no toppling
   occurs.
2. (`singleSourceOdometer_le_of_le`) the single-source odometer is monotone in the background and
   in the number of chips, so `v_{η,n} ≤ v_{2d-2, max n N₀}` for `η ≤ 2d - 2`.
3. The cube of radius `A N^{1/d}` lies in the Euclidean ball of radius `√d A N^{1/d}`, and
   `max(n, N₀)^{1/d} ≤ N₀^{1/d} (n + 1)^{1/d}`.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

namespace SSOuter

open Rossin

/-- Along the parallel toppling procedure of a sandpile with a stabilizing toppling function, the
odometer at each site is eventually constant. -/
theorem podo_eventually_const {s0 u : Site d → ℤ} (hu : u ∈ stabilizing s0 Set.univ)
    (x : Site d) : ∃ T, ∀ t, T ≤ t → podo s0 t x = podo s0 T x := by
  have hu' := mem_stabilizing_univ.1 hu
  have hle : ∀ t, podo s0 t x ≤ u x := fun t =>
    le_of_isLegalToppling (isLegalToppling_podo s0) hu'.1
      (fun y => by have := hu'.2 y; omega) t x
  by_contra hne
  push Not at hne
  have hgrow : ∀ k : ℕ, ∃ t, (k : ℤ) ≤ podo s0 t x := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', ht', hne'⟩ := hne t
      have hmono := Rossin.podo_mono' s0 ht' x
      refine ⟨t', ?_⟩
      push_cast
      omega
  obtain ⟨t, ht⟩ := hgrow ((u x).toNat + 1)
  have h1 := hle t
  have h2 : ((u x).toNat : ℤ) = u x := Int.toNat_of_nonneg (hu'.1 x)
  push_cast at ht
  omega

/-- **Least action through the parallel toppling procedure.** If `s₀` has a stabilizing toppling
function, the pointwise limit `w` of the parallel toppling odometers is stabilizing, and `w x > 0`
only at sites that topple at some time. -/
theorem exists_stabilizing_podo_limit {s0 u : Site d → ℤ} (hu : u ∈ stabilizing s0 Set.univ) :
    ∃ w ∈ stabilizing s0 Set.univ, ∀ x, 0 < w x → ∃ t, 0 < podo s0 t x := by
  choose T hT using podo_eventually_const hu
  refine ⟨fun x => podo s0 (T x) x, ?_, fun x hx => ⟨T x, hx⟩⟩
  rw [mem_stabilizing_univ]
  refine ⟨fun x => (isLegalToppling_podo s0).nonneg _ x, fun y => ?_⟩
  set τ : ℕ := T y + ∑ i, (T (y + unit i) + T (y - unit i)) with hτ
  have hTy : T y ≤ τ := Nat.le_add_right _ _
  have hsum : ∀ i, T (y + unit i) + T (y - unit i) ≤ ∑ j, (T (y + unit j) + T (y - unit j)) :=
    fun i => Finset.single_le_sum (f := fun j => T (y + unit j) + T (y - unit j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hTp : ∀ i, T (y + unit i) ≤ τ := fun i => by have := hsum i; omega
  have hTm : ∀ i, T (y - unit i) ≤ τ := fun i => by have := hsum i; omega
  have e1 : ∀ i, podo s0 τ (y + unit i) = podo s0 (T (y + unit i)) (y + unit i) :=
    fun i => hT _ τ (hTp i)
  have e2 : ∀ i, podo s0 τ (y - unit i) = podo s0 (T (y - unit i)) (y - unit i) :=
    fun i => hT _ τ (hTm i)
  have e0 : podo s0 τ y = podo s0 (T y) y := hT y τ hTy
  have hlapeq : lap (podo s0 τ) y = lap (fun x => podo s0 (T x) x) y := by
    simp only [Sandpile.lap, nbrSumZ, e1, e2, e0]
  by_contra hcon
  push Not at hcon
  have hpc : 2 * (d : ℤ) ≤ pconf s0 τ y := by
    simp only [pconf]
    rw [hlapeq]
    omega
  have hp := podo_succ s0 τ y
  rw [if_pos hpc] at hp
  have h1 := hT y (τ + 1) (by omega)
  omega

/-- The single-source odometer is monotone in the background and in the number of chips. -/
theorem singleSourceOdometer_le_of_le {η η' : Site d → ℤ} {n N : ℕ}
    (hle : ∀ x, η x + (n : ℤ) * dirac 0 x ≤ η' x + (N : ℤ) * dirac 0 x)
    (hne : (stabilizing (fun x => η' x + (N : ℤ) * dirac 0 x) Set.univ).Nonempty) :
    singleSourceOdometer η n ≤ singleSourceOdometer η' N := by
  have hmem := mem_stabilizing_univ.1 (isLeast_singleSourceOdometer hne).1
  apply singleSourceOdometer_le
  rw [mem_stabilizing_univ]
  exact ⟨hmem.1, fun x => by have := hmem.2 x; have := hle x; linarith⟩

theorem dirac_nonneg' (z x : Site d) : 0 ≤ dirac z x := by
  unfold dirac; split_ifs <;> norm_num

/-- The Euclidean norm of a lattice point in the cube of radius `B` is at most `√d B`. -/
theorem norm_toE_le_of_abs_le {z : Site d} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i, |(z i : ℝ)| ≤ B) : ‖toE z‖ ≤ Real.sqrt d * B := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ∑ i, ‖toE z i‖ ^ 2 ≤ ∑ _i : Fin d, B ^ 2 := Finset.sum_le_sum fun i _ => by
    rw [toE_apply, Real.norm_eq_abs]
    have := h i
    have := abs_nonneg (z i : ℝ)
    nlinarith
  calc Real.sqrt (∑ i, ‖toE z i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin d, B ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt d * B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]

end SSOuter

open SSOuter in
/-- **The outer bound `SSOuterBoundStmt` from Fey-Levine-Peres 2010, Theorem 1.1**
(`LatticeProb.External.FeyLevinePeresRadius`, the published statement verbatim), by the
monotonicity reduction of the module docstring. The radius depends on `d` only. -/
theorem ssOuterBound_of_flp (hFLP : External.FeyLevinePeresRadius) : SSOuterBoundStmt := by
  intro d hd ηmin
  obtain ⟨A, hA, N0, hN0, hflp⟩ := Sandpile.flp_specialization hFLP d hd
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  have hdinv : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  set R : ℝ := Real.sqrt d * A * (N0 : ℝ) ^ (1 / (d : ℝ)) + 1 with hR
  refine ⟨R, by positivity, fun η hη n z hz => ?_⟩
  by_contra hne0
  have hpos : 0 < singleSourceOdometer η n z :=
    lt_of_le_of_ne (singleSourceOdometer_nonneg η n z) (Ne.symm hne0)
  set N : ℕ := max n N0 with hN
  set η' : Site d → ℤ := fun _ => 2 * (d : ℤ) - 2 with hη'
  have hne' := ssNonempty d (by omega) η' (fun _ => le_rfl) N
  have hmono : singleSourceOdometer η n z ≤ singleSourceOdometer η' N z :=
    singleSourceOdometer_le_of_le (η := η) (η' := η') (n := n) (N := N)
    (fun x => by
      have h1 := (hη x).2
      have h2 : (n : ℤ) * dirac 0 x ≤ (N : ℤ) * dirac 0 x :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left n N0) (dirac_nonneg' 0 x)
      show η x + (n : ℤ) * dirac 0 x ≤ 2 * (d : ℤ) - 2 + (N : ℤ) * dirac 0 x
      linarith) hne' z
  obtain ⟨w, hw, hwpos⟩ := exists_stabilizing_podo_limit (isLeast_singleSourceOdometer hne').1
  have hvw : singleSourceOdometer η' N z ≤ w z := singleSourceOdometer_le hw z
  obtain ⟨t, ht⟩ := hwpos z (by omega)
  have hcube := hflp N (le_max_right _ _) z ⟨t, ht⟩
  have hAN : (0 : ℝ) ≤ A * (N : ℝ) ^ (1 / (d : ℝ)) := by positivity
  have hnorm := norm_toE_le_of_abs_le hAN hcube
  -- `max(n, N₀)^{1/d} ≤ N₀^{1/d} (n + 1)^{1/d}`
  have hNle : (N : ℝ) ≤ (N0 : ℝ) * ((n : ℝ) + 1) := by
    have h1 : N ≤ N0 * (n + 1) := by
      rcases le_total n N0 with h | h
      · rw [hN, max_eq_right h]; nlinarith
      · rw [hN, max_eq_left h]; nlinarith
    exact_mod_cast h1
  have hpow : (N : ℝ) ^ (1 / (d : ℝ)) ≤ (N0 : ℝ) ^ (1 / (d : ℝ)) * ((n : ℝ) + 1) ^ (1 / (d : ℝ)) := by
    rw [← Real.mul_rpow (Nat.cast_nonneg _) (by positivity)]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hNle hdinv
  have hn1 : 0 < ((n : ℝ) + 1) ^ (1 / (d : ℝ)) := by positivity
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hfin : ‖toE z‖ ≤ Real.sqrt d * A * (N0 : ℝ) ^ (1 / (d : ℝ)) * ((n : ℝ) + 1) ^ (1 / (d : ℝ)) := by
    calc ‖toE z‖ ≤ Real.sqrt d * (A * (N : ℝ) ^ (1 / (d : ℝ))) := hnorm
      _ ≤ Real.sqrt d * (A * ((N0 : ℝ) ^ (1 / (d : ℝ)) * ((n : ℝ) + 1) ^ (1 / (d : ℝ)))) := by
        gcongr
      _ = _ := by ring
  have hz' : R * ((n : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ ‖toE z‖ := hz
  rw [hR] at hz'
  nlinarith

end RandomSandpile

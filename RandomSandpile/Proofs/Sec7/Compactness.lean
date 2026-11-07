import RandomSandpile.Steps.Sec7.Compactness
import RandomSandpile.Proofs.Sec7.OneDimToppling
import RandomSandpile.Proofs.Sec7.CompactnessGradient
import RandomSandpile.Proofs.Sec7.CompactnessArzelaAscoli

/-!
# Proofs of the steps, of Lemma 7.2

* `freeOdometerUpperBound_of_oneDim`: step from Lemma 7.1 (`OneDimTopplingStmt`), by the
  comparison with the one-dimensional toppling functions `u_i(x) = g(x_i)`;
* `freeOdometerLapBound`: step, the bound `|Δ_{ℤ^d} v_n| ≤ 2d + |η_min| + |η_max|`;
* `lapGradientBound`, `asymptoticArzelaAscoli`: steps, proved in
  `Proofs/Sec7/CompactnessGradient.lean` and `Proofs/Sec7/CompactnessArzelaAscoli.lean`;
* `compactness : CompactnessStmt`, Lemma 7.2.
-/

noncomputable section

open Finset LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-! ### Step: the Laplacian of the free odometer is bounded -/

/-- The free odometer is a least element of its class: where it is positive, removing one
toppling at `x` breaks the stabilizing inequality at `x`, so `Δ v(x) ≥ -η 𝟙_{W_n}(x)`. -/
theorem neg_le_lap_freeOdometer {d : ℕ} {η : Site d → ℤ} {Wn : Set (Site d)}
    (hne : (stabilizing (Wn.indicator η) Set.univ).Nonempty) (x : Site d) :
    -Wn.indicator η x ≤ lap (freeOdometer η Wn) x ∨ freeOdometer η Wn x = 0 := by
  have hleast := isLeast_freeOdometer hne
  have hst := mem_stabilizing_univ.1 hleast.1
  set v := freeOdometer η Wn with hv
  by_cases h0 : v x = 0
  · exact Or.inr h0
  left
  have hpos : 1 ≤ v x := by have := hst.1 x; omega
  set w : Site d → ℤ := fun y => if y = x then v x - 1 else v y with hw
  have hwv : ∀ y, w y ≤ v y := by
    intro y; simp only [hw]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  have hnb : ∀ i : Fin d, x + unit i ≠ x ∧ x - unit i ≠ x := by
    intro i
    have hu : unit i ≠ (0 : Site d) := by
      intro h
      have := congrFun h i
      simp [unit] at this
    constructor
    · intro h; exact hu (by simpa using h)
    · intro h; exact hu (by simpa [sub_eq_self] using h)
  by_contra hlt
  push Not at hlt
  have hwst : w ∈ stabilizing (Wn.indicator η) Set.univ := by
    refine mem_stabilizing_univ.2 ⟨fun y => ?_, fun y => ?_⟩
    · simp only [hw]; split_ifs
      · omega
      · exact hst.1 y
    · by_cases hy : y = x
      · subst hy
        have hnbr : nbrSumZ w y = nbrSumZ v y := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hw, if_neg (hnb i).1, if_neg (hnb i).2]
        have : w y = v y - 1 := by simp [hw]
        simp only [lap_eq, hnbr, this] at hlt ⊢
        have hd : (0 : ℤ) ≤ d := Nat.cast_nonneg d
        nlinarith
      · have hnbr : nbrSumZ w y ≤ nbrSumZ v y := nbrSumZ_mono hwv y
        have : w y = v y := by simp [hw, hy]
        have := hst.2 y
        simp only [lap_eq] at this ⊢
        rw [‹w y = v y›]
        linarith
  have := hleast.2 hwst x
  simp [hw] at this

/-- **Step**. -/
theorem freeOdometerLapBound : FreeOdometerLapBoundStmt := by
  intro d ηmin ηmax η Wn hη hne x
  have hst := mem_stabilizing_univ.1 (isLeast_freeOdometer hne).1
  have hind : |Wn.indicator η x| ≤ |ηmin| + |ηmax| := by
    by_cases hx : x ∈ Wn
    · rw [Set.indicator_of_mem hx, abs_le]
      have h1 := (hη x).1; have h2 := (hη x).2
      have := neg_abs_le ηmin; have := le_abs_self ηmax
      have := abs_nonneg ηmin; have := abs_nonneg ηmax
      constructor <;> linarith
    · rw [Set.indicator_of_notMem hx]; simp; positivity
  have hd : (0 : ℤ) ≤ d := Nat.cast_nonneg d
  rw [abs_le] at hind ⊢
  constructor
  · rcases neg_le_lap_freeOdometer hne x with h | h
    · linarith
    · have : 0 ≤ lap (freeOdometer η Wn) x := by
        rw [lap_eq, h]
        simp only [mul_zero, sub_zero, nbrSumZ]
        exact Finset.sum_nonneg fun i _ =>
          add_nonneg (freeOdometer_nonneg _ _ _) (freeOdometer_nonneg _ _ _)
      linarith
  · have := hst.2 x
    linarith

/-! ### Step: comparison with the one-dimensional toppling functions -/

/-- The toppling function `u_i(x) = g(x_i)` built from a function `g` on `ℤ` has Laplacian equal
to the one-dimensional second difference of `g` at `x_i`. -/
theorem lap_comp_coord {d : ℕ} (g : ℤ → ℤ) (i : Fin d) (x : Site d) :
    lap (fun y : Site d => g (y i)) x = g (x i + 1) + g (x i - 1) - 2 * g (x i) := by
  rw [lap_eq_sum_second_diff, Finset.sum_eq_single i]
  · simp [unit]; ring
  · intro j _ hji
    have h1 : (x + unit j) i = x i := by simp [unit, Ne.symm hji]
    have h2 : (x - unit j) i = x i := by simp [unit, Ne.symm hji]
    simp only [h1, h2]; ring
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Step**, from Lemma 7.1 in the corrected form [C5]. -/
theorem freeOdometerUpperBound_of_oneDim (hOne : OneDimTopplingStmt) :
    FreeOdometerUpperBoundStmt := by
  intro d hd W hW ηmax
  -- `W ⊆ B_ρ(0)` with `ρ ∈ ℕ`
  obtain ⟨r₀, hr₀⟩ := hW.subset_closedBall 0
  set ρ : ℕ := ⌈r₀⌉₊ with hρ
  -- the parameters `k ≥ 1`, `r` of Lemma 7.1 for `η' = max η_max (2d)`
  set S : ℕ := (max ηmax (2 * (d : ℤ)) - 2 * d).toNat with hS
  have hSeq : (S : ℤ) = max ηmax (2 * (d : ℤ)) - 2 * d := by
    rw [hS, Int.toNat_of_nonneg]; have := le_max_right ηmax (2 * (d : ℤ)); omega
  set r : ℕ := (S + 2) / 2 with hr
  set k : ℕ := 2 * r - S with hk
  have hk1 : 1 ≤ k := by omega
  have hRk : max ηmax (2 * (d : ℤ)) - (2 * (d : ℤ) - k) = 2 * r := by
    have : (k : ℤ) = 2 * r - S := by rw [hk]; push_cast [show S ≤ 2 * r by omega]; ring
    rw [this]; linarith
  obtain ⟨C₁, hC₁, hg⟩ := hOne r
  refine ⟨C₁ * ((ρ : ℝ) + 1) ^ 2, ρ * (r + 1) + r, fun η hη n => ?_⟩
  obtain ⟨g, hgΔ, hgsupp, hgC⟩ := hg d (max ηmax (2 * (d : ℤ))) (ρ * n) k hRk
  -- lattice points of `W_n` lie in the cube `|x|_∞ ≤ ρ n`
  have hWn : ∀ x ∈ discretize W n, ∀ i, |x i| ≤ ((ρ * n : ℕ) : ℤ) := by
    intro x hx i
    obtain ⟨w, hwW, hwx⟩ := Set.mem_smul_set.1 hx
    have hw : ‖w‖ ≤ ρ := (mem_closedBall_zero_iff.1 (hr₀ hwW)).trans (Nat.le_ceil r₀)
    have hcoord : |((x i : ℤ) : ℝ)| ≤ ‖toE x‖ := by
      have := PiLp.norm_apply_le (toE x) i
      simpa [Real.norm_eq_abs] using this
    rw [← hwx, norm_smul, Real.norm_natCast] at hcoord
    have : |((x i : ℤ) : ℝ)| ≤ ((ρ * n : ℕ) : ℝ) := by
      push_cast
      calc |((x i : ℤ) : ℝ)| ≤ n * ‖w‖ := hcoord
        _ ≤ n * ρ := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg n)
        _ = ρ * n := by ring
    exact_mod_cast this
  -- each `u_i(x) = g(x_i)` is a stabilizing toppling function
  have hu : ∀ i : Fin d, (fun y : Site d => ((g (y i) : ℕ) : ℤ)) ∈
      stabilizing ((discretize W n).indicator η) Set.univ := by
    intro i
    refine mem_stabilizing_univ.2 ⟨fun y => Nat.cast_nonneg _, fun x => ?_⟩
    rw [lap_comp_coord (fun t => ((g t : ℕ) : ℤ)) i x, hgΔ (x i)]
    have hd2 : (2 : ℤ) ≤ d := by exact_mod_cast hd
    by_cases hx : x ∈ discretize W n
    · rw [Set.indicator_of_mem hx, if_pos (hWn x hx i), hRk]
      have := hη x
      have := le_max_left ηmax (2 * (d : ℤ))
      have : (2 * r : ℤ) = max ηmax (2 * (d : ℤ)) - 2 * d + k := by linarith
      have : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      linarith
    · rw [Set.indicator_of_notMem hx, add_zero]
      split_ifs <;> linarith [show (0 : ℤ) ≤ 2 * r by positivity]
  have hd0 : 0 < d := by omega
  refine ⟨⟨_, hu ⟨0, hd0⟩⟩, fun x => ?_, fun x ⟨i, hi⟩ => ?_⟩
  · have h1 := freeOdometer_le (hu ⟨0, hd0⟩) x
    have h2 : (freeOdometer η (discretize W n) x : ℝ) ≤ (g (x ⟨0, hd0⟩) : ℝ) := by
      exact_mod_cast h1
    refine h2.trans ((hgC _).trans ?_)
    have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC₁.le
    have : (ρ : ℝ) * n + 1 ≤ (ρ + 1) * (n + 1) := by nlinarith
    calc ((ρ : ℝ) * n + 1) ^ 2 ≤ ((ρ + 1) * (n + 1)) ^ 2 := by gcongr
      _ = ((ρ : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by ring
  · have h1 := freeOdometer_le (hu i) x
    have hg0 : g (x i) = 0 := by
      apply hgsupp
      have : ((ρ * n : ℕ) : ℤ) * (r + 1) + r ≤ ((ρ * (r + 1) + r : ℕ) : ℤ) * ((n : ℤ) + 1) := by
        push_cast; nlinarith [(Nat.cast_nonneg (α := ℤ) ρ), (Nat.cast_nonneg (α := ℤ) n),
          (Nat.cast_nonneg (α := ℤ) r)]
      exact this.trans hi
    have h0 := freeOdometer_nonneg η (discretize W n) x
    simp only [hg0, Nat.cast_zero] at h1
    omega

/-! ### Steps, and Lemma 7.2 -/

/-- **Step**: discrete gradient estimate from a bounded Laplacian. -/
theorem lapGradientBound : LapGradientBoundStmt := lapGradientBound_core

/-- **Step**: Arzelà–Ascoli for asymptotically equicontinuous sequences. -/
theorem asymptoticArzelaAscoli : AsymptoticArzelaAscoliStmt :=
  fun d F K L ρ e hK hρ hL he => asymptoticArzelaAscoli_core d F K L ρ e hK hρ hL he

/-- **Lemma 7.2** (`compactness`). -/
theorem compactness : CompactnessStmt :=
  compactness_of_steps (freeOdometerUpperBound_of_oneDim oneDimToppling) freeOdometerLapBound
    lapGradientBound asymptoticArzelaAscoli

end RandomSandpile

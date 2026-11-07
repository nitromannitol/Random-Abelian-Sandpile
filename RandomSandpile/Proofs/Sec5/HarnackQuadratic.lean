import RandomSandpile.Proofs.Sec5.HarnackQuadraticBox

/-! # Proposition 5.2 (quadratic growth from the discrete Harnack inequality)

Proofs of the steps `LatticeSegmentStmt` and `ExpGrowthBddLapStmt`, and the theorem
`harnackQuadratic : HarnackQuadraticStmt` from the reduction `harnackQuadratic_of_steps`
(`RandomSandpile/Steps/Sec5/HarnackQuadratic.lean`) and the box Harnack inequality
`boxHarnackBddLap` (`RandomSandpile/Proofs/Sec5/HarnackQuadraticBox.lean`). -/

open LatticeProb

namespace RandomSandpile

/-- The discrete segment `c_k = ⌊k x / N⌋` from `0` to `x`. -/
theorem latticeSegment : LatticeSegmentStmt := by
  intro d x N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun k i => ⌊(k : ℝ) * x i / N⌋, ?_, ?_, ?_, ?_⟩
  · funext i; simp
  · funext i
    simp only
    rw [mul_div_cancel_left₀ _ hN0.ne']
    exact Int.floor_intCast _
  · intro k hk i
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hfl := Int.floor_le ((k : ℝ) * x i / N)
    rcases le_or_gt 0 (x i) with hx | hx
    · have hx' : (0 : ℝ) ≤ x i := by exact_mod_cast hx
      have ht0 : 0 ≤ (k : ℝ) * x i / N := by positivity
      have htx : (k : ℝ) * x i / N ≤ x i := by
        rw [div_le_iff₀ hN0]; nlinarith
      have h1 : 0 ≤ ⌊(k : ℝ) * x i / N⌋ := Int.floor_nonneg.mpr ht0
      have h2 : ⌊(k : ℝ) * x i / N⌋ ≤ x i := by
        have : ((⌊(k : ℝ) * x i / N⌋ : ℤ) : ℝ) ≤ x i := hfl.trans htx
        exact_mod_cast this
      rw [abs_of_nonneg h1, abs_of_nonneg hx]
      exact h2
    · have hx' : (x i : ℝ) < 0 := by exact_mod_cast hx
      have ht0 : (k : ℝ) * x i / N ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hk0 hx'.le) hN0.le
      have htx : (x i : ℝ) ≤ (k : ℝ) * x i / N := by
        rw [le_div_iff₀ hN0]; nlinarith
      have h1 : x i ≤ ⌊(k : ℝ) * x i / N⌋ := Int.le_floor.mpr htx
      have h2 : ⌊(k : ℝ) * x i / N⌋ ≤ 0 := Int.floor_nonpos ht0
      rw [abs_of_nonpos h2, abs_of_neg hx]
      omega
  · intro k _ i
    show |((⌊((k + 1 : ℕ) : ℝ) * x i / N⌋ - ⌊(k : ℝ) * x i / N⌋ : ℤ) : ℝ)| ≤ _
    have e : ((k + 1 : ℕ) : ℝ) * x i / N = (k : ℝ) * x i / N + x i / N := by
      push_cast; ring
    rw [e, Int.cast_sub]
    have h1 := Int.floor_le ((k : ℝ) * x i / N + x i / N)
    have h2 := Int.lt_floor_add_one ((k : ℝ) * x i / N + x i / N)
    have h3 := Int.floor_le ((k : ℝ) * x i / N)
    have h4 := Int.lt_floor_add_one ((k : ℝ) * x i / N)
    have habs : |(x i : ℝ) / N| = |(x i : ℝ)| / N := by rw [abs_div, abs_of_pos hN0]
    have h5 := le_abs_self ((x i : ℝ) / N)
    have h6 := neg_abs_le ((x i : ℝ) / N)
    rw [habs] at h5 h6
    rw [abs_le]
    constructor <;> linarith

/-- The exponential growth bound `f(z) ≤ λ (2d + 1)^{|z|_1}`, by induction on `|z|_1`. -/
theorem expGrowthBddLap : ExpGrowthBddLapStmt := by
  intro d R lam f hf hf0 hlam hlap
  have hb : (1 : ℝ) ≤ 2 * (d : ℝ) + 1 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  suffices H : ∀ n : ℕ, ∀ z ∈ ballZ0 R, ∑ i, (z i).natAbs ≤ n →
      f z ≤ lam * (2 * (d : ℝ) + 1) ^ n from fun z hz => H _ z hz le_rfl
  intro n
  induction n with
  | zero =>
    intro z _ hsum
    have hz : z = 0 := by
      funext i
      have := Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hsum) i (Finset.mem_univ _)
      simpa using this
    subst hz
    rw [hf0]
    simpa using hlam
  | succ n ih =>
    intro z hz hsum
    by_cases hz0 : z = 0
    · subst hz0
      rw [hf0]
      positivity
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz0 (funext h)
    have key : ∀ z' : Site d, (∀ j, |z' j| ≤ |z j|) → |z' i| < |z i| →
        (z = z' + unit i ∨ z = z' - unit i) → f z ≤ lam * (2 * (d : ℝ) + 1) ^ (n + 1) := by
      intro z' hle hlt hz'
      have hz'R : z' ∈ ballZ0 R := by
        rw [mem_ballZ0_iff_norm] at hz ⊢
        exact (norm_toE_le_of_abs_le hle).trans_lt hz
      have hsum' : ∑ j, (z' j).natAbs ≤ n := by
        have hlt' : ∑ j, (z' j).natAbs < ∑ j, (z j).natAbs := by
          apply Finset.sum_lt_sum
          · intro j _
            have := hle j
            zify
            exact this
          · exact ⟨i, Finset.mem_univ _, by zify; exact hlt⟩
        omega
      have hfz' := ih z' hz'R hsum'
      have hnb : f z ≤ nbrSum f z' := by
        have hterm : f z ≤ f (z' + unit i) + f (z' - unit i) := by
          rcases hz' with h | h <;> rw [← h] <;> linarith [hf (z' + unit i), hf (z' - unit i)]
        exact hterm.trans (Finset.single_le_sum
          (f := fun j => f (z' + unit j) + f (z' - unit j))
          (fun j _ => add_nonneg (hf _) (hf _)) (Finset.mem_univ i))
      have hlap' := hlap z' hz'R
      simp only [lapR] at hlap'
      have hpow : 1 ≤ (2 * (d : ℝ) + 1) ^ n := one_le_pow₀ hb
      have h1 : lam ≤ lam * (2 * (d : ℝ) + 1) ^ n := le_mul_of_one_le_right hlam hpow
      have h2 : 2 * (d : ℝ) * f z' ≤ 2 * (d : ℝ) * (lam * (2 * (d : ℝ) + 1) ^ n) :=
        mul_le_mul_of_nonneg_left hfz' (by positivity)
      calc f z ≤ nbrSum f z' := hnb
        _ ≤ lam + 2 * d * f z' := by linarith
        _ ≤ lam * (2 * (d : ℝ) + 1) ^ n + 2 * (d : ℝ) * (lam * (2 * (d : ℝ) + 1) ^ n) := by
            linarith
        _ = lam * (2 * (d : ℝ) + 1) ^ (n + 1) := by ring
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · refine key (z + unit i) (fun j => ?_) ?_ (Or.inr (add_sub_cancel_right z (unit i)).symm)
      · simp only [unit, Pi.add_apply, Pi.single_apply]
        split_ifs with h
        · rw [h, abs_of_nonpos (by omega : z i + 1 ≤ 0), abs_of_neg hneg]
          omega
        · simp
      · simp only [unit, Pi.add_apply, Pi.single_apply, if_true]
        rw [abs_of_nonpos (by omega : z i + 1 ≤ 0), abs_of_neg hneg]
        omega
    · refine key (z - unit i) (fun j => ?_) ?_ (Or.inl (sub_add_cancel z (unit i)).symm)
      · simp only [unit, Pi.sub_apply, Pi.single_apply]
        split_ifs with h
        · rw [h, abs_of_nonneg (by omega : 0 ≤ z i - 1), abs_of_pos hpos]
          omega
        · simp
      · simp only [unit, Pi.sub_apply, Pi.single_apply, if_true]
        rw [abs_of_nonneg (by omega : 0 ≤ z i - 1), abs_of_pos hpos]
        omega

/-- **Proposition 5.2** (harnack, Lemma 2.17), proved from the
discrete Harnack inequality of Lattice-Probability. -/
theorem harnackQuadratic : HarnackQuadraticStmt :=
  harnackQuadratic_of_steps boxHarnackBddLap expGrowthBddLap latticeSegment

end RandomSandpile

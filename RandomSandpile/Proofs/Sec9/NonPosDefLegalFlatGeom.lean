import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatPsi

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

/-- Path lemma: from `a ∈ B` to `c ∉ B` there is a boundary site within `ℓ¹` distance `N` of `a`,
where `N = ‖c - a‖₁`. -/
theorem exists_bdry_of_path {B : Set (Site d)} : ∀ (N : ℕ) (a c : Site d), a ∈ B → c ∉ B →
    ∑ i, |c i - a i| = (N : ℤ) → ∃ w ∈ bdry B, ∑ i, |w i - a i| ≤ (N : ℤ) := by
  intro N
  induction N with
  | zero =>
    intro a c ha hc hs
    exfalso
    have : ∀ i, c i = a i := fun i => by
      have h0 : ∀ j ∈ Finset.univ, 0 ≤ |c j - a j| := fun j _ => abs_nonneg _
      have := (Finset.sum_eq_zero_iff_of_nonneg h0).1 (by simpa using hs) i (Finset.mem_univ i)
      have := abs_eq_zero.1 this
      omega
    exact hc (by have : c = a := funext this; rw [this]; exact ha)
  | succ N ih =>
    intro a c ha hc hs
    have hne : ∃ i, c i ≠ a i := by
      by_contra h
      push Not at h
      simp [h] at hs
      omega
    obtain ⟨i, hi⟩ := hne
    -- step toward c in coordinate i
    obtain ⟨a', ha'adj, hdist, hstep⟩ : ∃ a' : Site d, Adj a' a ∧
        ∑ j, |a' j - a j| = 1 ∧ ∑ j, |c j - a' j| = (N : ℤ) := by
      rcases lt_or_gt_of_ne hi with h | h
      · refine ⟨a - unit i, adj_sub_unit a i, ?_, ?_⟩
        · rw [Finset.sum_eq_single i (fun j _ hj => by simp [unit, hj]) (by simp)]
          simp [unit]
        · have : ∑ j, |c j - a j| = ∑ j, |c j - (a - unit i) j| + 1 := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
              ← Finset.sum_erase_add _ (fun j => |c j - (a - unit i) j|) (Finset.mem_univ i)]
            have : ∑ j ∈ Finset.univ.erase i, |c j - a j| =
                ∑ j ∈ Finset.univ.erase i, |c j - (a - unit i) j| :=
              Finset.sum_congr rfl fun j hj => by simp [unit, Finset.ne_of_mem_erase hj]
            rw [this]
            simp only [unit, Pi.sub_apply, Pi.single_eq_same]
            rw [abs_of_neg (by omega), abs_of_nonpos (by omega)]
            ring
          push_cast at hs
          omega
      · refine ⟨a + unit i, adj_add_unit a i, ?_, ?_⟩
        · rw [Finset.sum_eq_single i (fun j _ hj => by simp [unit, hj]) (by simp)]
          simp [unit]
        · have : ∑ j, |c j - a j| = ∑ j, |c j - (a + unit i) j| + 1 := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
              ← Finset.sum_erase_add _ (fun j => |c j - (a + unit i) j|) (Finset.mem_univ i)]
            have : ∑ j ∈ Finset.univ.erase i, |c j - a j| =
                ∑ j ∈ Finset.univ.erase i, |c j - (a + unit i) j| :=
              Finset.sum_congr rfl fun j hj => by simp [unit, Finset.ne_of_mem_erase hj]
            rw [this]
            simp only [unit, Pi.add_apply, Pi.single_eq_same]
            rw [abs_of_pos (by omega), abs_of_nonneg (by omega)]
            ring
          push_cast at hs
          omega
    by_cases ha'B : a' ∈ B
    · obtain ⟨w, hw, hwd⟩ := ih a' c ha'B hc hstep
      refine ⟨w, hw, ?_⟩
      calc ∑ j, |w j - a j| ≤ ∑ j, (|w j - a' j| + |a' j - a j|) :=
            Finset.sum_le_sum fun j _ => by
              have := abs_add_le (w j - a' j) (a' j - a j)
              simpa using this
        _ = ∑ j, |w j - a' j| + ∑ j, |a' j - a j| := Finset.sum_add_distrib
        _ ≤ (N + 1 : ℕ) := by rw [hdist]; push_cast; linarith
    · refine ⟨a', mem_bdry.2 ⟨ha'B, a, ha, ha'adj⟩, ?_⟩
      rw [hdist]; push_cast; omega

theorem norm_le_sum_abs (v : Rd d) : ‖v‖ ≤ ∑ i, |v i| := by
  have h1 : ‖v‖ ^ 2 = ∑ i, (v i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by simp [sq_abs]
  set S := ∑ i, |v i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h2 : ∑ i, (v i) ^ 2 ≤ S * S := by
    calc ∑ i, (v i) ^ 2 = ∑ i, |v i| * |v i| := Finset.sum_congr rfl fun i _ => by rw [← sq, sq_abs]
      _ ≤ ∑ i, |v i| * S := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun j => |v j|)
            (fun j _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)
      _ = S * S := by rw [← Finset.sum_mul]
  by_contra h
  push Not at h
  nlinarith [norm_nonneg v]

theorem norm_toE_latticeRound_sub_le (x : Rd d) : ‖toE (latticeRound x) - x‖ ≤ Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖(toE (latticeRound x) - x) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := Int.floor_le (x i)
        have h2 := Int.lt_floor_add_one (x i)
        simp only [PiLp.sub_apply, toE_apply, latticeRound, Real.norm_eq_abs]
        have : |(⌊x i⌋ : ℝ) - x i| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        have h0 := abs_nonneg ((⌊x i⌋ : ℝ) - x i)
        nlinarith
    _ = d := by simp

/-- A sphere point has a boundary site of the ball within a bounded distance. -/
theorem bdry_near {R : ℝ} (hR : 2 * (Real.sqrt d + 1) ≤ R) (q : Rd d) (hq : ‖q‖ = R) :
    ∃ b ∈ bdry (ballZ0 (d := d) R),
      ‖toE b - q‖ ≤ d * (2 * (Real.sqrt d + 1) + 2 * Real.sqrt d) + Real.sqrt d + (Real.sqrt d + 1) := by
  set lam : ℝ := Real.sqrt d + 1 with hlam
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hlam0 : 0 < lam := by rw [hlam]; linarith
  have hR0 : 0 < R := by linarith
  have hlR : lam / R ≤ 1 / 2 := by rw [div_le_iff₀ hR0]; linarith
  set qin : Rd d := (1 - lam / R) • q with hqin
  set qout : Rd d := (1 + lam / R) • q with hqout
  have hnin : ‖qin‖ = R - lam := by
    rw [hqin, norm_smul, hq, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    field_simp
  have hnout : ‖qout‖ = R + lam := by
    rw [hqout, norm_smul, hq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
  have hdiff : ‖qout - qin‖ = 2 * lam := by
    have : qout - qin = (2 * lam / R) • q := by
      rw [hqout, hqin, ← sub_smul]; congr 1; ring
    rw [this, norm_smul, hq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
  have hin2 : ‖qin - q‖ = lam := by
    have : qin - q = (-(lam / R)) • q := by
      rw [hqin, sub_smul, one_smul, neg_smul]; abel
    rw [this, norm_smul, hq, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    field_simp
  set a : Site d := latticeRound qin with ha
  set c : Site d := latticeRound qout with hc
  have hra := norm_toE_latticeRound_sub_le qin
  have hrc := norm_toE_latticeRound_sub_le qout
  have haB : a ∈ ballZ0 (d := d) R := by
    rw [MuLipschitz.mem_ballZ0]
    have := norm_sub_norm_le (toE a) qin
    have h2 := norm_sub_rev (toE a) qin
    have := norm_le_norm_add_norm_sub' (toE a) qin
    calc ‖toE a‖ ≤ ‖qin‖ + ‖toE a - qin‖ := by
          have := norm_le_insert' (toE a) qin
          linarith
      _ < R := by rw [hnin]; rw [hlam] at *; linarith
  have hcB : c ∉ ballZ0 (d := d) R := by
    rw [MuLipschitz.mem_ballZ0, not_lt]
    have := norm_le_insert' qout (toE c)
    have h3 : ‖qout - toE c‖ = ‖toE c - qout‖ := norm_sub_rev _ _
    rw [hnout] at this
    rw [hlam] at *
    linarith
  -- ℓ¹ distance
  have hcoord : ∀ i, |((c i - a i : ℤ) : ℝ)| ≤ 2 * lam + 2 * Real.sqrt d := by
    intro i
    have h1 : |((c i - a i : ℤ) : ℝ)| ≤ ‖toE c - toE a‖ := by
      have := PiLp.norm_apply_le (toE c - toE a) i
      simpa [toE_apply, Real.norm_eq_abs] using this
    have h2 : ‖toE c - toE a‖ ≤ ‖toE c - qout‖ + ‖qout - qin‖ + ‖qin - toE a‖ := by
      calc ‖toE c - toE a‖ = ‖(toE c - qout) + (qout - qin) + (qin - toE a)‖ := by congr 1; abel
        _ ≤ _ := norm_add₃_le
    have h3 : ‖qin - toE a‖ = ‖toE a - qin‖ := norm_sub_rev _ _
    linarith
  set Z : ℤ := ∑ i, |c i - a i| with hZ
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hZle : (Z : ℝ) ≤ d * (2 * lam + 2 * Real.sqrt d) := by
    calc (Z : ℝ) = ∑ i, |((c i - a i : ℤ) : ℝ)| := by
          rw [hZ]; push_cast; rfl
      _ ≤ ∑ _i : Fin d, (2 * lam + 2 * Real.sqrt d) := Finset.sum_le_sum fun i _ => hcoord i
      _ = _ := by simp; ring
  obtain ⟨w, hw, hwd⟩ := exists_bdry_of_path (B := ballZ0 (d := d) R) Z.toNat a c haB hcB
    (by rw [Int.toNat_of_nonneg hZ0])
  refine ⟨w, hw, ?_⟩
  rw [Int.toNat_of_nonneg hZ0] at hwd
  have hl1 : ‖toE w - toE a‖ ≤ Z := by
    refine (norm_le_sum_abs _).trans ?_
    have : ∑ i, |(toE w - toE a) i| = ((∑ i, |w i - a i| : ℤ) : ℝ) := by
      push_cast; refine Finset.sum_congr rfl fun i _ => ?_; simp
    rw [this]; exact_mod_cast hwd
  calc ‖toE w - q‖ = ‖(toE w - toE a) + (toE a - qin) + (qin - q)‖ := by congr 1; abel
    _ ≤ ‖toE w - toE a‖ + ‖toE a - qin‖ + ‖qin - q‖ := norm_add₃_le
    _ ≤ _ := by rw [hin2]; linarith

end SingleSourceH0

end RandomSandpile

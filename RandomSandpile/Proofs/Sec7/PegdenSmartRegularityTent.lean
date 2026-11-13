import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTrace

/-!
# Tent-product weights on `ℤ^d`

The test weight `w_L(z) = ∏ᵢ (L - |zᵢ|)₊` used for the Hessian trace bound of Lemma 7.6(3)
(`FreeOdometerLimitHessianTraceStmt`). It is a positive combination of indicators of the boxes
`∏ᵢ [-kᵢ, kᵢ]`, `0 ≤ kᵢ < L` (`sum_tentW_mul`), so that weighted sums of the environment reduce to
box sums (the ergodic theorem for rectangles); its total mass is `L^{2d}` (`sum_tentW`).
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace PegdenSmartRegularity

variable {d : ℕ}

/-- The one-dimensional tent `(L - |t|)₊`. -/
def tent (L : ℕ) (t : ℤ) : ℤ := max ((L : ℤ) - |t|) 0

/-- The tent product `w_L(z) = ∏ᵢ (L - |zᵢ|)₊`. -/
def tentW (L : ℕ) (z : Site d) : ℝ := ∏ i, (tent L (z i) : ℝ)

/-- The box `∏ᵢ [-kᵢ, kᵢ]`. -/
def tentBox (k : Fin d → ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => Finset.Icc (-(k i : ℤ)) (k i)

/-- The box `[-L, L]^d`, containing the support of `w_L`. -/
def bigBox (d L : ℕ) : Finset (Site d) := Fintype.piFinset fun _ => Finset.Icc (-(L : ℤ)) L

theorem tent_nonneg (L : ℕ) (t : ℤ) : 0 ≤ tent L t := le_max_right _ _

theorem tent_le (L : ℕ) (t : ℤ) : tent L t ≤ L := by
  unfold tent; have := abs_nonneg t; omega

theorem tent_eq_zero {L : ℕ} {t : ℤ} (ht : (L : ℤ) ≤ |t|) : tent L t = 0 := by
  unfold tent; omega

theorem tent_eq_sum (L : ℕ) (t : ℤ) :
    tent L t = ∑ k ∈ Finset.range L, if |t| ≤ (k : ℤ) then (1 : ℤ) else 0 := by
  rw [Finset.sum_boole]
  have hf : (Finset.range L).filter (fun k : ℕ => |t| ≤ (k : ℤ)) = Finset.Ico t.natAbs L := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Int.abs_eq_natAbs,
      Nat.cast_le]
    omega
  rw [hf, Nat.card_Ico, tent, Int.abs_eq_natAbs]
  omega

theorem tentW_nonneg (L : ℕ) (z : Site d) : 0 ≤ tentW L z :=
  Finset.prod_nonneg fun i _ => by exact_mod_cast tent_nonneg L (z i)

theorem mem_tentBox {k : Fin d → ℕ} {z : Site d} : z ∈ tentBox k ↔ ∀ i, |z i| ≤ k i := by
  simp only [tentBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem tentBox_subset_bigBox {L : ℕ} {k : Fin d → ℕ}
    (hk : k ∈ Fintype.piFinset fun _ : Fin d => Finset.range L) : tentBox k ⊆ bigBox d L := by
  intro z hz
  rw [mem_tentBox] at hz
  simp only [Fintype.mem_piFinset, Finset.mem_range] at hk
  simp only [bigBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 := abs_le.1 (hz i)
  have h2 : (k i : ℤ) < L := by exact_mod_cast hk i
  omega

theorem tentW_eq_sum (L : ℕ) (z : Site d) :
    tentW L z = ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range L),
      if z ∈ tentBox k then (1 : ℝ) else 0 := by
  have h1 : ∀ i, (tent L (z i) : ℝ) =
      ∑ k ∈ Finset.range L, if |z i| ≤ (k : ℤ) then (1 : ℝ) else 0 := fun i => by
    rw [tent_eq_sum]; push_cast; rfl
  simp only [tentW, h1]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies, mem_tentBox]

/-- **Box decomposition of tent-weighted sums.** -/
theorem sum_tentW_mul (L : ℕ) (g : Site d → ℝ) :
    ∑ z ∈ bigBox d L, tentW L z * g z =
      ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range L), ∑ z ∈ tentBox k, g z := by
  simp only [tentW_eq_sum, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (tentBox_subset_bigBox hk)]

theorem card_tentBox (k : Fin d → ℕ) : ((tentBox k).card : ℝ) = ∏ i, (2 * (k i : ℝ) + 1) := by
  rw [tentBox, Fintype.card_piFinset]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Icc]
  have : ((k i : ℤ) + 1 - -(k i : ℤ)).toNat = 2 * k i + 1 := by omega
  rw [this]; push_cast; ring

theorem sum_range_odd (L : ℕ) : ∑ k ∈ Finset.range L, (2 * (k : ℝ) + 1) = (L : ℝ) ^ 2 := by
  induction L with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **The mass of the tent product**: `∑ w_L = L^{2d}`. -/
theorem sum_tentW (L : ℕ) : ∑ z ∈ bigBox d L, tentW L z = ((L : ℝ) ^ 2) ^ d := by
  have h := sum_tentW_mul (d := d) L (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  simp only [card_tentBox]
  rw [← Finset.prod_univ_sum (t := fun _ : Fin d => Finset.range L)
    (f := fun _ (k : ℕ) => 2 * (k : ℝ) + 1), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, sum_range_odd]

/-! ### The Laplacian of the tent product -/

/-- The second difference of the one-dimensional tent. -/
def tentD (L : ℕ) (t : ℤ) : ℤ := tent L (t + 1) + tent L (t - 1) - 2 * tent L t

theorem abs_tentD_le {L : ℕ} (hL : 1 ≤ L) (t : ℤ) :
    |tentD L t| ≤ (if t = 0 then 2 else 0) + (if t = L then 1 else 0) +
      (if t = -(L : ℤ) then 1 else 0) := by
  have key : ∀ s : ℤ, |s| = if 0 ≤ s then s else -s := fun s => by
    split_ifs with h
    exacts [abs_of_nonneg h, abs_of_neg (not_le.1 h)]
  have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
  simp only [tentD, tent, key]
  split_ifs <;> omega

theorem sum_Icc_tent (L : ℕ) : ∑ t ∈ Finset.Icc (-(L : ℤ)) L, (tent L t : ℝ) = (L : ℝ) ^ 2 := by
  have h1 : ∀ t, (tent L t : ℝ) = ∑ k ∈ Finset.range L, if |t| ≤ (k : ℤ) then (1 : ℝ) else 0 :=
    fun t => by rw [tent_eq_sum]; push_cast; rfl
  simp only [h1]
  rw [Finset.sum_comm, ← sum_range_odd]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_boole]
  have hk' : (k : ℤ) < L := by exact_mod_cast Finset.mem_range.1 hk
  have hf : (Finset.Icc (-(L : ℤ)) L).filter (fun t => |t| ≤ (k : ℤ)) = Finset.Icc (-(k : ℤ)) k := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, abs_le]
    omega
  rw [hf, Int.card_Icc]
  have : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
  rw [this]; push_cast; ring

theorem sum_Icc_abs_tentD_le {L : ℕ} (hL : 1 ≤ L) :
    ∑ t ∈ Finset.Icc (-(L : ℤ)) L, (|tentD L t| : ℝ) ≤ 4 := by
  have h1 : ∀ t ∈ Finset.Icc (-(L : ℤ)) L, (|tentD L t| : ℝ) ≤
      (if t = 0 then 2 else 0) + (if t = L then 1 else 0) + (if t = -(L : ℤ) then 1 else 0) :=
    fun t _ => by
      have := abs_tentD_le hL t
      have h' : ((|tentD L t| : ℤ) : ℝ) ≤ (((if t = 0 then 2 else 0) + (if t = L then 1 else 0) +
          (if t = -(L : ℤ) then 1 else 0) : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      simpa using h'
  refine (Finset.sum_le_sum h1).trans ?_
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_Icc]
  split_ifs <;> norm_num

/-- The product of the tents in the directions other than `i`. -/
def tentP (L : ℕ) (i : Fin d) (z : Site d) : ℝ := ∏ j ∈ Finset.univ.erase i, (tent L (z j) : ℝ)

theorem tentW_eq_mul (L : ℕ) (i : Fin d) (z : Site d) :
    tentW L z = (tent L (z i) : ℝ) * tentP L i z :=
  (Finset.mul_prod_erase Finset.univ (fun j => (tent L (z j) : ℝ)) (Finset.mem_univ i)).symm

theorem tentW_add_unit (L : ℕ) (i : Fin d) (z : Site d) :
    tentW L (z + unit i) = (tent L (z i + 1) : ℝ) * tentP L i z := by
  rw [tentW_eq_mul L i]
  congr 1
  · simp [unit]
  · refine Finset.prod_congr rfl fun j hj => ?_
    simp [unit, Finset.ne_of_mem_erase hj]

theorem tentW_sub_unit (L : ℕ) (i : Fin d) (z : Site d) :
    tentW L (z - unit i) = (tent L (z i - 1) : ℝ) * tentP L i z := by
  rw [tentW_eq_mul L i]
  congr 1
  · simp [unit]
  · refine Finset.prod_congr rfl fun j hj => ?_
    simp [unit, Finset.ne_of_mem_erase hj]

theorem lapR_tentW (L : ℕ) (z : Site d) :
    lapR (tentW L) z = ∑ i, tentP L i z * (tentD L (z i) : ℝ) := by
  rw [lapR_eq_sum_secondDiff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [secondDiff, tentW_add_unit, tentW_sub_unit, tentW_eq_mul L i, tentD]
  push_cast; ring

theorem tentP_nonneg (L : ℕ) (i : Fin d) (z : Site d) : 0 ≤ tentP L i z :=
  Finset.prod_nonneg fun j _ => by exact_mod_cast tent_nonneg L (z j)

/-- **The Laplacian of the tent product is small in `ℓ¹`**: `∑ |Δ w_L| ≤ 4d L^{2(d-1)}`. -/
theorem sum_abs_lapR_tentW_le {L : ℕ} (hL : 1 ≤ L) :
    ∑ z ∈ bigBox d L, |lapR (tentW L) z| ≤ 4 * d * ((L : ℝ) ^ 2) ^ (d - 1) := by
  have hpt : ∀ z : Site d, |lapR (tentW L) z| ≤ ∑ i, tentP L i z * (|tentD L (z i)| : ℝ) := fun z => by
    rw [lapR_tentW]
    calc |∑ i, tentP L i z * (tentD L (z i) : ℝ)| ≤ ∑ i, |tentP L i z * (tentD L (z i) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, tentP L i z * (|tentD L (z i)| : ℝ) := Finset.sum_congr rfl fun i _ => by
          rw [abs_mul, abs_of_nonneg (tentP_nonneg L i z)]
  refine (Finset.sum_le_sum fun z _ => hpt z).trans ?_
  rw [Finset.sum_comm]
  have hi : ∀ i : Fin d, ∑ z ∈ bigBox d L, tentP L i z * (|tentD L (z i)| : ℝ) ≤
      4 * ((L : ℝ) ^ 2) ^ (d - 1) := by
    intro i
    set f : Fin d → ℤ → ℝ := fun j t =>
      if j = i then (|tentD L t| : ℝ) else (tent L t : ℝ) with hf
    have h1 : ∀ z : Site d, tentP L i z * (|tentD L (z i)| : ℝ) = ∏ j, f j (z j) := fun z => by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (z j)) (Finset.mem_univ i)]
      simp only [hf, ite_eq_left rfl, tentP]
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
    simp only [h1, bigBox]
    rw [← Finset.prod_univ_sum (t := fun _ : Fin d => Finset.Icc (-(L : ℤ)) L) (f := f)]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have h2 : ∀ j ∈ Finset.univ.erase i, ∑ t ∈ Finset.Icc (-(L : ℤ)) L, f j t = (L : ℝ) ^ 2 :=
      fun j hj => by simp only [hf, ite_eq_right (Finset.ne_of_mem_erase hj)]; exact sum_Icc_tent L
    rw [Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    simp only [hf, ite_eq_left rfl]
    exact mul_le_mul_of_nonneg_right (sum_Icc_abs_tentD_le hL) (by positivity)
  refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### Summation by parts -/

theorem sum_mul_shift {w f : Site d → ℝ} {S B : Finset (Site d)} (hw : ∀ z ∉ S, w z = 0)
    (hSB : S ⊆ B) (e : Site d) (hSe : ∀ z ∈ S, z + e ∈ B) :
    ∑ z ∈ B, w z * f (z + e) = ∑ z ∈ B, w (z - e) * f z := by
  classical
  rw [← Finset.sum_subset hSB fun z _ hz => by rw [hw z hz, zero_mul]]
  have hmap : S.map (Equiv.addRight e).toEmbedding ⊆ B := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hz
    exact hSe y hy
  rw [← Finset.sum_subset hmap fun z _ hz => by
    have : z - e ∉ S := fun h => hz (Finset.mem_map.2 ⟨z - e, h, by simp⟩)
    rw [hw _ this, zero_mul]]
  rw [Finset.sum_map]
  simp

/-- **Summation by parts** on `ℤ^d`: `∑_B w Δf = ∑_B f Δw` when `w` vanishes off `S` and the
neighbours of `S` lie in `B`. -/
theorem sum_mul_lapR_comm {w f : Site d → ℝ} {S B : Finset (Site d)} (hw : ∀ z ∉ S, w z = 0)
    (hSB : S ⊆ B) (hSe : ∀ z ∈ S, ∀ i, z + unit i ∈ B ∧ z - unit i ∈ B) :
    ∑ z ∈ B, w z * lapR f z = ∑ z ∈ B, f z * lapR w z := by
  have h1 : ∀ i, ∑ z ∈ B, w z * f (z + unit i) = ∑ z ∈ B, w (z - unit i) * f z := fun i =>
    sum_mul_shift hw hSB _ fun z hz => (hSe z hz i).1
  have h2 : ∀ i, ∑ z ∈ B, w z * f (z - unit i) = ∑ z ∈ B, w (z + unit i) * f z := fun i => by
    have := sum_mul_shift (f := f) hw hSB (-unit i) fun z hz => by
      rw [← sub_eq_add_neg]; exact (hSe z hz i).2
    simpa [sub_eq_add_neg] using this
  have expand : ∀ g h : Site d → ℝ, ∑ z ∈ B, g z * lapR h z =
      ∑ i, (∑ z ∈ B, g z * h (z + unit i) + ∑ z ∈ B, g z * h (z - unit i)) -
        ∑ z ∈ B, 2 * (d : ℝ) * (g z * h z) := by
    intro g h
    calc ∑ z ∈ B, g z * lapR h z = ∑ z ∈ B, (∑ i, (g z * h (z + unit i) + g z * h (z - unit i)) -
          2 * (d : ℝ) * (g z * h z)) := Finset.sum_congr rfl fun z _ => by
            simp only [lapR, nbrSum, mul_sub, Finset.mul_sum, mul_add]; ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_comm]
        simp only [Finset.sum_add_distrib]
  rw [expand w f, expand f w]
  simp only [h1, h2]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun z _ => by ring
  · exact Finset.sum_congr rfl fun z _ => by ring

theorem tentW_eq_zero {L : ℕ} {z : Site d} (hz : z ∉ bigBox d (L - 1)) (hL : 1 ≤ L) :
    tentW L z = 0 := by
  simp only [bigBox, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hz
  obtain ⟨i, hi⟩ := hz
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [tent_eq_zero]; · simp
  have : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
  rw [this] at hi
  rw [abs_eq_max_neg]; omega

/-- Summation by parts for the tent product on `[-L, L]^d`. -/
theorem sum_tentW_mul_lapR {L : ℕ} (hL : 1 ≤ L) (f : Site d → ℝ) :
    ∑ z ∈ bigBox d L, tentW L z * lapR f z = ∑ z ∈ bigBox d L, f z * lapR (tentW L) z := by
  refine sum_mul_lapR_comm (S := bigBox d (L - 1)) (fun z hz => tentW_eq_zero hz hL) ?_ ?_
  · intro z hz
    simp only [bigBox, Fintype.mem_piFinset, Finset.mem_Icc] at hz ⊢
    intro i; have := hz i; omega
  · intro z hz i
    simp only [bigBox, Fintype.mem_piFinset, Finset.mem_Icc] at hz ⊢
    constructor <;> intro j <;> have := hz j <;>
      · simp only [Pi.add_apply, Pi.sub_apply, unit, Pi.single_apply]
        split_ifs <;> omega

end PegdenSmartRegularity

end RandomSandpile

import RandomSandpile.Steps.Sec7.Flat
import RandomSandpile.Proofs.Sec3.Burning
import RandomSandpile.Proofs.Sec5.HarnackQuadratic

/-! # Lemma 7.5 (`flat`): deterministic tools

Tools for the proof of `NoOppositeBendingStmt` (`Proofs/Sec7/Flat.lean`):
* the lattice balls `B_r`, `r > 0`, induce connected subgraphs of `ℤ^d` (`ballZ0_connected`);
* affine functions are discrete harmonic (`lapR_affine`), and the Laplacian of a locally legal
  stabilizing toppling is bounded by `|ηmin| + |ηmax| + 2d` (`abs_lap_le`);
* the minimum principle for discrete superharmonic functions (`le_of_lapR_nonpos`) and the barrier
  estimate moving a lower bound from `∂B_n` into `B_n` (`barrier`);
* the Harnack inequality (Prop 5.2) at a contact point (`harnack_contact`).
-/

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace Flat

variable {d : ℕ}

/-! ### Lattice balls are connected -/

theorem norm_toE_le_of_abs_le {x y : Site d} (h : ∀ i, |(y i : ℝ)| ≤ |(x i : ℝ)|) :
    ‖toE y‖ ≤ ‖toE x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [toE_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem reachable_zero {r : ℝ} (h0 : (0 : Site d) ∈ ballZ0 r) :
    ∀ (N : ℕ) (x : Site d) (hx : x ∈ ballZ0 r), ∑ i, (x i).natAbs = N →
      ((lattice d).induce (ballZ0 r)).Reachable ⟨0, h0⟩ ⟨x, hx⟩ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x hx hN
  by_cases hx0 : x = 0
  · subst hx0; rfl
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx0 (funext h)
  have key : ∃ x' : Site d, (lattice d).Adj x' x ∧ (∀ j, |(x' j : ℝ)| ≤ |(x j : ℝ)|) ∧
      (∀ j, (x' j).natAbs ≤ (x j).natAbs) ∧ (x' i).natAbs < (x i).natAbs := by
    by_cases hp : 0 < x i
    · refine ⟨x - unit i, Burning.adj_sub_unit' x i, fun j => ?_, fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp only [Pi.sub_apply, unit, Pi.single_eq_same]
          have : (1 : ℝ) ≤ x j := by exact_mod_cast hp
          push_cast
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
        · simp [unit, hj]
      · by_cases hj : j = i
        · subst hj; simp only [Pi.sub_apply, unit, Pi.single_eq_same]; omega
        · simp [unit, hj]
      · simp only [Pi.sub_apply, unit, Pi.single_eq_same]; omega
    · have hn : x i < 0 := lt_of_le_of_ne (not_lt.1 hp) hi
      refine ⟨x + unit i, Burning.adj_add_unit' x i, fun j => ?_, fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp only [Pi.add_apply, unit, Pi.single_eq_same]
          have : (x j : ℝ) ≤ -1 := by exact_mod_cast (show x j ≤ -1 by omega)
          push_cast
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
        · simp [unit, hj]
      · by_cases hj : j = i
        · subst hj; simp only [Pi.add_apply, unit, Pi.single_eq_same]; omega
        · simp [unit, hj]
      · simp only [Pi.add_apply, unit, Pi.single_eq_same]; omega
  obtain ⟨x', hadj, habs, hnat, hlt⟩ := key
  have hx' : x' ∈ ballZ0 r :=
    MuLipschitz.mem_ballZ0.2 ((norm_toE_le_of_abs_le habs).trans_lt (MuLipschitz.mem_ballZ0.1 hx))
  have hsum : ∑ j, (x' j).natAbs < N :=
    hN ▸ Finset.sum_lt_sum (fun j _ => hnat j) ⟨i, Finset.mem_univ _, hlt⟩
  exact (ih _ hsum x' hx' rfl).trans (SimpleGraph.Adj.reachable hadj)

/-- The lattice ball `B_r`, `r > 0`, induces a connected subgraph of `ℤ^d`. -/
theorem ballZ0_connected {r : ℝ} (hr : 0 < r) :
    ((lattice d).induce (ballZ0 (d := d) r)).Connected := by
  have h0 : (0 : Site d) ∈ ballZ0 r :=
    MuLipschitz.mem_ballZ0.2 (by simp only [MuLipschitz.toE_zero, norm_zero]; exact hr)
  have : Nonempty (ballZ0 (d := d) r) := ⟨⟨0, h0⟩⟩
  exact ⟨fun a b => (reachable_zero h0 _ a.1 a.2 rfl).symm.trans (reachable_zero h0 _ b.1 b.2 rfl)⟩

/-! ### Laplacians -/

theorem toE_neg (x : Site d) : toE (-x) = -toE x := by
  ext i; simp

/-- Affine functions are discrete harmonic. -/
theorem lapR_affine (a : ℝ) (p : Rd d) (z x : Site d) :
    lapR (fun y => a + inner ℝ p (toE y - toE z)) x = 0 := by
  have h : ∀ i : Fin d, (a + inner ℝ p (toE (x + unit i) - toE z)) +
      (a + inner ℝ p (toE (x - unit i) - toE z)) = 2 * (a + inner ℝ p (toE x - toE z)) := by
    intro i
    rw [MuLipschitz.toE_add, MuLipschitz.toE_sub]
    have e1 : toE x + toE (unit i) - toE z = (toE x - toE z) + toE (unit i) := by abel
    have e2 : toE x - toE (unit i) - toE z = (toE x - toE z) - toE (unit i) := by abel
    rw [e1, e2]
    simp only [inner_add_right, inner_sub_right]
    ring
  simp only [lapR, nbrSum, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem lapR_qlZ' (hd : 1 ≤ d) (l : ℝ) (x : Site d) : lapR (qlZ l) x = l := by
  have h := lapQuadratic d hd l 0 x
  have hq : (fun y => qlZ l y + qMZ (0 : Matrix (Fin d) (Fin d) ℝ) y) = qlZ l :=
    funext fun y => by simp [qMZ, qM]
  rw [hq] at h
  simpa using h

/-- The Laplacian of a locally legal stabilizing toppling is bounded in `A`. -/
theorem abs_lap_le {η : Site d → ℤ} {ηmin ηmax : ℤ} (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax)
    {A : Set (Site d)} {h : Site d → ℤ} (hL : h ∈ locLegal η A) (hS : h ∈ stabilizing η A)
    {x : Site d} (hx : x ∈ A) :
    |(lap h x : ℝ)| ≤ |(ηmin : ℝ)| + |(ηmax : ℝ)| + 2 * d := by
  have h1 := locLegalLapLower d η A h hL x hx
  have h2 := hS.2 x hx
  have h3 := hη x
  have hlo : -ηmax ≤ lap h x ∨ 0 ≤ lap h x := by
    rcases le_total 0 (η x) with h4 | h4
    · rw [min_eq_left h4] at h1; left; omega
    · rw [min_eq_right h4] at h1; right; omega
  have hhi : (lap h x : ℝ) ≤ 2 * d - 1 - ηmin := by
    have : lap h x ≤ 2 * (d : ℤ) - 1 - ηmin := by omega
    exact_mod_cast this
  have hlo' : -(ηmax : ℝ) ≤ lap h x ∨ 0 ≤ (lap h x : ℝ) := by
    rcases hlo with h4 | h4
    · left; exact_mod_cast h4
    · right; exact_mod_cast h4
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rcases hlo' with h4 | h4
    · linarith [le_abs_self (ηmax : ℝ), abs_nonneg (ηmin : ℝ), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    · linarith [abs_nonneg (ηmax : ℝ), abs_nonneg (ηmin : ℝ), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  · linarith [neg_le_abs (ηmin : ℝ), abs_nonneg (ηmax : ℝ)]

/-! ### Minimum principle and barrier -/

/-- The minimum principle: a discrete superharmonic function on a finite `A` that is `≥ m` on `∂A`
is `≥ m` in `A`. -/
theorem le_of_lapR_nonpos (hd : 0 < d) {A : Set (Site d)} (hA : A.Finite) {φ : Site d → ℝ}
    (hlap : ∀ x ∈ A, lapR φ x ≤ 0) {m : ℝ} (hb : ∀ y ∈ bdry A, m ≤ φ y) :
    ∀ x ∈ A, m ≤ φ x := by
  by_contra hcon
  simp only [not_forall, not_le] at hcon
  obtain ⟨x₁, hx₁, hlt⟩ := hcon
  obtain ⟨z₀, hz₀, hmin⟩ := Set.exists_min_image A φ hA ⟨x₁, hx₁⟩
  have hT : {x | x ∈ A ∧ φ x = φ z₀}.Finite := hA.subset fun x hx => hx.1
  obtain ⟨z, ⟨hzA, hzv⟩, hz⟩ := Burning.exists_add_unit_notMem hd hT ⟨z₀, hz₀, rfl⟩
  have hφz : φ z < m := by rw [hzv]; exact lt_of_le_of_lt (hmin x₁ hx₁) hlt
  have hnb : ∀ y, y ∈ A ∨ y ∈ bdry A → φ z ≤ φ y := by
    rintro y (hy | hy)
    · rw [hzv]; exact hmin y hy
    · exact (hφz.trans_le (hb y hy)).le
  have hstrict : φ z < φ (z + unit ⟨0, hd⟩) := by
    rcases Burning.add_unit_mem hzA ⟨0, hd⟩ with h | h
    · rcases (hnb _ (Or.inl h)).lt_or_eq with h' | h'
      · exact h'
      · exact absurd ⟨h, by rw [← h', hzv]⟩ hz
    · exact hφz.trans_le (hb _ h)
  have hsum : lapR φ z = ∑ i : Fin d, ((φ (z + unit i) - φ z) + (φ (z - unit i) - φ z)) := by
    have e : ∀ i : Fin d, (φ (z + unit i) - φ z) + (φ (z - unit i) - φ z) =
        (φ (z + unit i) + φ (z - unit i)) - 2 * φ z := fun i => by ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, lapR, nbrSum]
    ring
  have hpos : 0 < lapR φ z := by
    rw [hsum]
    apply Finset.sum_pos' (fun i _ => add_nonneg (sub_nonneg.2 (hnb _ (Burning.add_unit_mem hzA i)))
      (sub_nonneg.2 (hnb _ (Burning.sub_unit_mem hzA i))))
    exact ⟨⟨0, hd⟩, Finset.mem_univ _,
      by linarith [hstrict, hnb _ (Burning.sub_unit_mem hzA ⟨0, hd⟩)]⟩
  linarith [hlap z hzA]

/-- The barrier estimate: if `Δ g ≤ λ` in `B_n` and `g ≥ a` on `∂B_n`, then
`g(x) ≥ a - λ ((n+1)² - |x|²) / (2d)` in `B_n`. -/
theorem barrier (hd : 1 ≤ d) {n : ℕ} {g : Site d → ℝ} {lam a : ℝ} (hlam : 0 ≤ lam)
    (hlap : ∀ x ∈ ballZ0 (d := d) (n : ℝ), lapR g x ≤ lam)
    (hb : ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)), a ≤ g y) :
    ∀ x ∈ ballZ0 (d := d) (n : ℝ), a - lam * (((n : ℝ) + 1) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) ≤ g x := by
  intro x hx
  have hd' : (0 : ℝ) < 2 * d := by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                                   linarith
  have key := le_of_lapR_nonpos (by omega) (MuLipschitz.ballZ0_finite (n : ℝ))
    (φ := fun y => g y - qlZ lam y)
    (fun y hy => by rw [lapR_sub', lapR_qlZ' hd lam]; linarith [hlap y hy])
    (m := a - lam * ((n : ℝ) + 1) ^ 2 / (2 * d)) (fun y hy => ?_) x hx
  · simp only [qlZ, ql] at key
    have e : a - lam * (((n : ℝ) + 1) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) =
        (a - lam * ((n : ℝ) + 1) ^ 2 / (2 * d)) + lam * ‖toE x‖ ^ 2 / (2 * d) := by ring
    rw [e]; linarith
  · simp only [qlZ, ql]
    have h1 := MuLipschitz.norm_lt_of_mem_bdry_ballZ0 hy
    have h2 : ‖toE y‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1.le 2
    have h3 : lam * ‖toE y‖ ^ 2 / (2 * d) ≤ lam * ((n : ℝ) + 1) ^ 2 / (2 * d) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hlam) hd'.le
    linarith [hb y hy]

/-! ### Harnack at a contact point -/

theorem lapR_congr_nbr {f g : Site d → ℝ} {z : Site d} (h0 : f z = g z)
    (hp : ∀ i, f (z + unit i) = g (z + unit i)) (hm : ∀ i, f (z - unit i) = g (z - unit i)) :
    lapR f z = lapR g z := by
  simp only [lapR, nbrSum, h0, hp, hm]

theorem mem_dClosure_of_nbr {B : Set (Site d)} {x : Site d} (hx : x ∈ B) (i : Fin d) :
    x + unit i ∈ dClosure B ∧ x - unit i ∈ dClosure B := by
  constructor
  · rcases Burning.add_unit_mem hx i with h | h
    · exact subset_dClosure _ h
    · exact bdry_subset_dClosure _ h
  · rcases Burning.sub_unit_mem hx i with h | h
    · exact subset_dClosure _ h
    · exact bdry_subset_dClosure _ h

/-- The Harnack inequality (Prop 5.2) at a contact point: a gap `g ≥ 0` on `B̄_n` vanishing at
`x₀ ∈ B_{βn}`, `β ≤ 1/4`, with `|Δ g| ≤ λ` in `B_n`, satisfies `g(0) ≤ C (β n)²`. -/
theorem harnack_contact (hd : 2 ≤ d) (lam : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (β : ℝ), β ≤ 1 / 4 → ∀ (g : Site d → ℝ) (x₀ : Site d),
      x₀ ∈ ballZ0 (β * n) → (∀ y ∈ dClosure (ballZ0 (d := d) (n : ℝ)), 0 ≤ g y) → g x₀ = 0 →
      (∀ y ∈ ballZ0 (d := d) (n : ℝ), |lapR g y| ≤ lam) → g 0 ≤ C * (β * n) ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := harnackQuadratic d hd (1 / 2) (by norm_num) (by norm_num) lam
  refine ⟨max C 0, le_max_right _ _, fun n β hβ g x₀ hx₀ hg0 hgx₀ hlap => ?_⟩
  have hx₀n : ‖toE x₀‖ < β * n := MuLipschitz.mem_ballZ0.1 hx₀
  have hβn : 0 ≤ β * n := le_trans (norm_nonneg _) hx₀n.le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hβn4 : β * n ≤ n / 4 := by
    rcases eq_or_lt_of_le hn0 with h | h
    · rw [← h]; simp
    · have : β * n ≤ 1 / 4 * n := mul_le_mul_of_nonneg_right hβ hn0
      linarith
  have hx₀B : x₀ ∈ ballZ0 (d := d) (n : ℝ) := MuLipschitz.mem_ballZ0.2 (by linarith)
  set B := ballZ0 (d := d) (n : ℝ) with hB
  set f : Site d → ℝ := fun z => if z + x₀ ∈ dClosure B then g (z + x₀) else 0 with hf
  have hf0 : ∀ z, 0 ≤ f z := fun z => by
    simp only [hf]; split_ifs with h
    · exact hg0 _ h
    · exact le_rfl
  have hfz : ∀ z, z + x₀ ∈ dClosure B → f z = g (z + x₀) := fun z h => by simp only [hf]; exact ite_eq_left h
  have hf00 : f 0 = 0 := by rw [hfz 0 (by rw [zero_add]; exact subset_dClosure _ hx₀B), zero_add, hgx₀]
  have hlapf : ∀ z ∈ ballZ0 (1 * ((n : ℝ) / 2)), |lapR f z| ≤ lam := by
    intro z hz
    have hz' : ‖toE z‖ < n / 2 := by have := MuLipschitz.mem_ballZ0.1 hz; linarith
    have hzB : z + x₀ ∈ B := by
      refine MuLipschitz.mem_ballZ0.2 ?_
      rw [MuLipschitz.toE_add]
      calc ‖toE z + toE x₀‖ ≤ ‖toE z‖ + ‖toE x₀‖ := norm_add_le _ _
        _ < n := by linarith
    have heq : lapR f z = lapR (fun w => g (w + x₀)) z := by
      refine lapR_congr_nbr (hfz z (subset_dClosure _ hzB)) (fun i => hfz _ ?_) (fun i => hfz _ ?_)
      · rw [add_right_comm]; exact (mem_dClosure_of_nbr hzB i).1
      · rw [sub_add_eq_add_sub]; exact (mem_dClosure_of_nbr hzB i).2
    rw [heq, lapR_comp_add]
    exact hlap _ hzB
  have hlapf' : ∀ z ∈ ballZ0 ((n : ℝ) / 2), |lapR f z| ≤ lam := fun z hz =>
    hlapf z (by rw [one_mul]; exact hz)
  have hmem : -x₀ ∈ ballZ0 (1 / 2 * ((n : ℝ) / 2)) := by
    refine MuLipschitz.mem_ballZ0.2 ?_
    rw [toE_neg, norm_neg]; linarith
  have hH := hC ((n : ℝ) / 2) f hf0 hf00 hlapf' (-x₀) hmem
  rw [hfz (-x₀) (by rw [neg_add_cancel]; exact subset_dClosure _ (MuLipschitz.mem_ballZ0.2
    (by simp only [MuLipschitz.toE_zero, norm_zero]; linarith [norm_nonneg (toE x₀)]))),
    neg_add_cancel, toE_neg,
    norm_neg] at hH
  have hsq : ‖toE x₀‖ ^ 2 ≤ (β * n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx₀n.le 2
  calc g 0 ≤ C * ‖toE x₀‖ ^ 2 := hH
    _ ≤ max C 0 * ‖toE x₀‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max C 0 * (β * n) ^ 2 := mul_le_mul_of_nonneg_left hsq (le_max_right _ _)

end Flat

end RandomSandpile

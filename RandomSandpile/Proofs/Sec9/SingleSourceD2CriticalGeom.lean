import RandomSandpile.Proofs.Sec9.SingleSourceD2Recurrent
import RandomSandpile.Proofs.Sec9.SingleSourceD2Lower
import RandomSandpile.Proofs.Sec9.SingleSourceD2Loop
import RandomSandpile.Proofs.Sec7.Flat

/-!
# Theorem 9.2 in dimension two: lattice tools for flatness at critical matrices

Deterministic tools for the proof of `CriticalFlatD2Stmt`.
* `exists_bdry_of_step`, `neg_mem_bdry_ballZ0`, `exists_bdry_near`: walking from a point of `A` in a
  unit lattice direction, the first point outside `A` lies on `∂A`; `∂B_r` is symmetric; for a unit
  vector `e`, some `y ∈ ∂B_n` has `|y - n e| ≤ 11` (the boundary vertices `y_n^± = ±n e + O(1)` of
  D2-PROOF §4).
* `qM_neg'`, `qM_smul'`, `qM_add_le`, `exists_unit_qM_lt`: the quadratic `q_Q`, and a direction in
  which `q_Q < θ` when `Q` is not positive definite.
* `harnack_near`: the bounded-Laplacian growth estimate (1.8) (Bou-Rabee Proposition 5.2) at a
  contact point `x₀` of `B_r`, `|x₀| ≤ r/2`: a gap `g ≥ 0` on `B̄_r` with `g(x₀) = 0` and
  `|Δg| ≤ λ` in `B_r` has `g(y) ≤ C |y - x₀|²` for `|y - x₀| < r/4`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace SingleSourceD2

/-! ### Boundary points of lattice balls -/

/-- Walking from a point of `A` with a fixed lattice step `v` that leads from `A` into `Ā`, the first
point outside `A` lies on `∂A`. -/
theorem exists_bdry_of_step {d : ℕ} {A : Set (Site d)} {v : Site d}
    (hv : ∀ x ∈ A, x + v ∈ A ∨ x + v ∈ bdry A) {x : Site d} (hx : x ∈ A) :
    ∀ k : ℕ, x + (k : ℤ) • v ∉ A → ∃ j : ℕ, j ≤ k ∧ x + (j : ℤ) • v ∈ bdry A := by
  intro k
  induction k with
  | zero =>
    intro h
    simp only [Nat.cast_zero, zero_smul, add_zero] at h
    exact (h hx).elim
  | succ k ih =>
    intro h
    have e : x + ((k + 1 : ℕ) : ℤ) • v = (x + (k : ℤ) • v) + v := by
      rw [Nat.cast_succ, add_smul, one_smul, add_assoc]
    by_cases hk : x + (k : ℤ) • v ∈ A
    · rcases hv _ hk with h' | h'
      · exact (h (by rw [e]; exact h')).elim
      · exact ⟨k + 1, le_rfl, by rw [e]; exact h'⟩
    · obtain ⟨j, hj, hb⟩ := ih hk
      exact ⟨j, by omega, hb⟩

/-- `∂B_r` is symmetric. -/
theorem neg_mem_bdry_ballZ0 {d : ℕ} {r : ℝ} {y : Site d} (hy : y ∈ bdry (ballZ0 (d := d) r)) :
    -y ∈ bdry (ballZ0 (d := d) r) := by
  have hneg : ∀ z : Site d, -z ∈ ballZ0 (d := d) r ↔ z ∈ ballZ0 (d := d) r := fun z => by
    rw [MuLipschitz.mem_ballZ0, MuLipschitz.mem_ballZ0, Flat.toE_neg, norm_neg]
  obtain ⟨hy1, x, hx, i, hi | hi⟩ := mem_bdry.1 hy
  · refine mem_bdry.2 ⟨fun h => hy1 ((hneg y).1 h), -x, (hneg x).2 hx, ?_⟩
    exact (show (lattice d).Adj (-y) (-x) from ⟨i, Or.inr (by rw [hi]; abel)⟩)
  · refine mem_bdry.2 ⟨fun h => hy1 ((hneg y).1 h), -x, (hneg x).2 hx, ?_⟩
    exact (show (lattice d).Adj (-y) (-x) from ⟨i, Or.inl (by rw [hi]; abel)⟩)

theorem toE_zsmul {d : ℕ} (k : ℤ) (v : Site d) : toE (k • v) = (k : ℝ) • toE v := by
  ext i; simp

theorem inner_toE_unit {d : ℕ} (i : Fin d) (e : Rd d) : inner ℝ (toE (unit i)) e = e i := by
  simp [PiLp.inner_apply, unit, Pi.single_apply]

/-- `|v| ≤ 1` for the rounding error `v = [w] - w` in the plane. -/
theorem norm_round_sub_le (w : Rd 2) : ‖toE (fun i => round (w i)) - w‖ ≤ 1 := by
  have h0 := abs_sub_round (w 0)
  have h1 := abs_sub_round (w 1)
  have hsq := norm_sq_two (toE (fun i => round (w i)) - w)
  simp only [PiLp.sub_apply, toE_apply] at hsq
  have a0 := abs_le.1 h0
  have a1 := abs_le.1 h1
  have hb : ‖toE (fun i => round (w i)) - w‖ ^ 2 ≤ 1 := by
    rw [hsq]; nlinarith
  nlinarith [norm_nonneg (toE (fun i => round (w i)) - w)]

/-- For a unit vector `e` and `n ≥ 2`, some `y ∈ ∂B_n` has `|y - n e| ≤ 11`. -/
theorem exists_bdry_near {n : ℕ} (hn : 2 ≤ n) {e : Rd 2} (he : ‖e‖ = 1) :
    ∃ y ∈ bdry (ballZ0 (d := 2) (n : ℝ)), ‖toE y - (n : ℝ) • e‖ ≤ 11 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set w : Rd 2 := ((n : ℝ) - 2) • e with hw
  set x : Site 2 := fun i => round (w i)
  have hr : ‖toE x - w‖ ≤ 1 := norm_round_sub_le w
  have hwn : ‖w‖ = n - 2 := by
    rw [hw, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hxB : x ∈ ballZ0 (d := 2) (n : ℝ) := by
    refine MuLipschitz.mem_ballZ0.2 ?_
    calc ‖toE x‖ = ‖w + (toE x - w)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w‖ + ‖toE x - w‖ := norm_add_le _ _
      _ < n := by linarith
  have hxe : (n : ℝ) - 3 ≤ inner ℝ (toE x) e := by
    have h1 : inner ℝ (toE x) e = inner ℝ w e + inner ℝ (toE x - w) e := by
      rw [← inner_add_left, add_sub_cancel]
    have h2 : inner ℝ w e = (n : ℝ) - 2 := by
      rw [hw, real_inner_smul_left, real_inner_self_eq_norm_sq, he]; ring
    have h3 : -(‖toE x - w‖ * ‖e‖) ≤ inner ℝ (toE x - w) e :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    rw [he, mul_one] at h3
    linarith
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, 1 / 2 ≤ |e i| := by
    have hsq := norm_sq_two e
    rw [he] at hsq
    by_cases h0 : 1 / 2 ≤ |e 0|
    · exact ⟨0, h0⟩
    · refine ⟨1, ?_⟩
      by_contra h1
      have a0 : |e 0| < 1 / 2 := not_le.mp h0
      have a1 : |e 1| < 1 / 2 := not_le.mp h1
      nlinarith [abs_nonneg (e 0), abs_nonneg (e 1), sq_abs (e 0), sq_abs (e 1)]
  obtain ⟨v, hv, hve, hvn⟩ : ∃ v : Site 2, (∀ z ∈ ballZ0 (d := 2) (n : ℝ),
      z + v ∈ ballZ0 (d := 2) (n : ℝ) ∨ z + v ∈ bdry (ballZ0 (d := 2) (n : ℝ))) ∧
      1 / 2 ≤ inner ℝ (toE v) e ∧ ‖toE v‖ = 1 := by
    rcases le_or_gt 0 (e i) with hs | hs
    · refine ⟨unit i, fun z hz => Burning.add_unit_mem hz i, ?_, MuLipschitz.norm_toE_unit i⟩
      rw [inner_toE_unit]
      rwa [abs_of_nonneg hs] at hi
    · refine ⟨-unit i, fun z hz => ?_, ?_, ?_⟩
      · rw [← sub_eq_add_neg]; exact Burning.sub_unit_mem hz i
      · rw [Flat.toE_neg, inner_neg_left, inner_toE_unit]
        rw [abs_of_neg hs] at hi
        linarith
      · rw [Flat.toE_neg, norm_neg, MuLipschitz.norm_toE_unit]
  have hout : x + ((8 : ℕ) : ℤ) • v ∉ ballZ0 (d := 2) (n : ℝ) := by
    intro h
    have h1 := MuLipschitz.mem_ballZ0.1 h
    have h2 := real_inner_le_norm (toE (x + ((8 : ℕ) : ℤ) • v)) e
    rw [he, mul_one, MuLipschitz.toE_add, toE_zsmul, inner_add_left, real_inner_smul_left] at h2
    rw [MuLipschitz.toE_add, toE_zsmul] at h1
    push_cast at h2 h1
    linarith
  obtain ⟨j, hj, hb⟩ := exists_bdry_of_step hv hxB 8 hout
  refine ⟨_, hb, ?_⟩
  rw [MuLipschitz.toE_add, toE_zsmul]
  have hj' : (j : ℝ) ≤ 8 := by exact_mod_cast hj
  have hwe : ‖w - (n : ℝ) • e‖ = 2 := by
    rw [hw, ← sub_smul, norm_smul, he, mul_one, show (n : ℝ) - 2 - n = -2 by ring]
    norm_num
  have hjv : ‖((j : ℤ) : ℝ) • toE v‖ ≤ 8 := by
    rw [norm_smul, hvn, mul_one, Int.cast_natCast, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg j)]
    exact hj'
  calc ‖toE x + ((j : ℤ) : ℝ) • toE v - (n : ℝ) • e‖ =
        ‖(toE x - w) + (w - (n : ℝ) • e) + ((j : ℤ) : ℝ) • toE v‖ := by congr 1; abel
    _ ≤ ‖toE x - w‖ + ‖w - (n : ℝ) • e‖ + ‖((j : ℤ) : ℝ) • toE v‖ := norm_add₃_le
    _ ≤ 11 := by linarith

/-! ### The quadratic `q_Q` in the plane -/

theorem qM_neg' (Q : Matrix (Fin 2) (Fin 2) ℝ) (v : Rd 2) : qM Q (-v) = qM Q v := by
  rw [qM_two, qM_two]; simp only [PiLp.neg_apply]; ring

theorem qM_smul' (Q : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (v : Rd 2) :
    qM Q (t • v) = t ^ 2 * qM Q v := by
  rw [qM_two, qM_two]; simp only [PiLp.smul_apply, smul_eq_mul]; ring

/-- The entrywise size of a `2 × 2` matrix. -/
def matBound (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := |Q 0 0| + |Q 0 1| + |Q 1 0| + |Q 1 1|

theorem matBound_nonneg (Q : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ matBound Q := by
  unfold matBound; positivity

theorem mul3_le {x q y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : x * q * y ≤ |q| * (X * Y) := by
  calc x * q * y ≤ |x * q * y| := le_abs_self _
    _ = |q| * (|x| * |y|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ |q| * (X * Y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx))
          (abs_nonneg _)

theorem abs_apply_le_norm (v : Rd 2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  rwa [Real.norm_eq_abs] at this

/-- `q_Q(a + r) ≤ q_Q(a) + |Q| (|a| |r| + |r|²)`. -/
theorem qM_add_le (Q : Matrix (Fin 2) (Fin 2) ℝ) (a r : Rd 2) :
    qM Q (a + r) ≤ qM Q a + matBound Q * (‖a‖ * ‖r‖ + ‖r‖ ^ 2) := by
  have ha0 := abs_apply_le_norm a 0
  have ha1 := abs_apply_le_norm a 1
  have hr0 := abs_apply_le_norm r 0
  have hr1 := abs_apply_le_norm r 1
  have key : qM Q (a + r) - qM Q a = (a 0 * Q 0 0 * r 0 + a 0 * Q 0 1 * r 1 + a 1 * Q 1 0 * r 0 +
      a 1 * Q 1 1 * r 1 + r 0 * Q 0 0 * a 0 + r 0 * Q 0 1 * a 1 + r 1 * Q 1 0 * a 0 +
      r 1 * Q 1 1 * a 1 + r 0 * Q 0 0 * r 0 + r 0 * Q 0 1 * r 1 + r 1 * Q 1 0 * r 0 +
      r 1 * Q 1 1 * r 1) / 2 := by
    rw [qM_two, qM_two]; simp only [PiLp.add_apply]; ring
  have t1 := mul3_le (q := Q 0 0) ha0 hr0
  have t2 := mul3_le (q := Q 0 1) ha0 hr1
  have t3 := mul3_le (q := Q 1 0) ha1 hr0
  have t4 := mul3_le (q := Q 1 1) ha1 hr1
  have t5 := mul3_le (q := Q 0 0) hr0 ha0
  have t6 := mul3_le (q := Q 0 1) hr0 ha1
  have t7 := mul3_le (q := Q 1 0) hr1 ha0
  have t8 := mul3_le (q := Q 1 1) hr1 ha1
  have t9 := mul3_le (q := Q 0 0) hr0 hr0
  have t10 := mul3_le (q := Q 0 1) hr0 hr1
  have t11 := mul3_le (q := Q 1 0) hr1 hr0
  have t12 := mul3_le (q := Q 1 1) hr1 hr1
  have hS : matBound Q * (‖a‖ * ‖r‖ + ‖r‖ ^ 2) = |Q 0 0| * (‖a‖ * ‖r‖) + |Q 0 1| * (‖a‖ * ‖r‖) +
      |Q 1 0| * (‖a‖ * ‖r‖) + |Q 1 1| * (‖a‖ * ‖r‖) + |Q 0 0| * (‖r‖ * ‖r‖) +
      |Q 0 1| * (‖r‖ * ‖r‖) + |Q 1 0| * (‖r‖ * ‖r‖) + |Q 1 1| * (‖r‖ * ‖r‖) := by
    unfold matBound; ring
  have e1 : |Q 0 0| * (‖r‖ * ‖a‖) = |Q 0 0| * (‖a‖ * ‖r‖) := by ring
  have e2 : |Q 0 1| * (‖r‖ * ‖a‖) = |Q 0 1| * (‖a‖ * ‖r‖) := by ring
  have e3 : |Q 1 0| * (‖r‖ * ‖a‖) = |Q 1 0| * (‖a‖ * ‖r‖) := by ring
  have e4 : |Q 1 1| * (‖r‖ * ‖a‖) = |Q 1 1| * (‖a‖ * ‖r‖) := by ring
  have p1 : 0 ≤ |Q 0 0| * (‖r‖ * ‖r‖) := by positivity
  have p2 : 0 ≤ |Q 0 1| * (‖r‖ * ‖r‖) := by positivity
  have p3 : 0 ≤ |Q 1 0| * (‖r‖ * ‖r‖) := by positivity
  have p4 : 0 ≤ |Q 1 1| * (‖r‖ * ‖r‖) := by positivity
  rw [e1] at t5; rw [e2] at t6; rw [e3] at t7; rw [e4] at t8
  linarith

/-- `q_Q(v) ≤ |Q| |v|²`. -/
theorem qM_le (Q : Matrix (Fin 2) (Fin 2) ℝ) (v : Rd 2) : qM Q v ≤ matBound Q * ‖v‖ ^ 2 := by
  have h := qM_add_le Q 0 v
  rw [zero_add, norm_zero, zero_mul, zero_add] at h
  have h0 : qM Q (0 : Rd 2) = 0 := by simp [qM]
  linarith

/-- If `Q` is not positive definite, then `q_Q < θ` in some unit direction. -/
theorem exists_unit_qM_lt {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.IsSymm) (hnot : ¬ Q.PosDef)
    {θ : ℝ} (hθ : 0 < θ) : ∃ e : Rd 2, ‖e‖ = 1 ∧ qM Q e < θ := by
  by_contra hcon
  refine hnot (posDef_of_qM_ge hQ hθ fun h => ?_)
  by_cases h0 : h = 0
  · subst h0; simp [qM]
  · have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
    have h1 : ‖‖h‖⁻¹ • h‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h2 : θ ≤ qM Q (‖h‖⁻¹ • h) := not_lt.1 fun hlt => hcon ⟨_, h1, hlt⟩
    rw [qM_smul'] at h2
    have h3 : ‖h‖⁻¹ ^ 2 * ‖h‖ ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hn.ne', one_pow]
    calc θ * ‖h‖ ^ 2 ≤ (‖h‖⁻¹ ^ 2 * qM Q h) * ‖h‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = qM Q h * (‖h‖⁻¹ ^ 2 * ‖h‖ ^ 2) := by ring
      _ = qM Q h := by rw [h3, mul_one]

/-! ### The growth estimate (1.8) at a contact point -/

/-- **(1.8)** (Bou-Rabee Proposition 5.2) at a contact point `x₀`, `|x₀| ≤ r/2`, of `B_r`. -/
theorem harnack_near {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (g : Site d → ℝ) (x₀ : Site d), ‖toE x₀‖ ≤ r / 2 →
      (∀ y ∈ dClosure (ballZ0 (d := d) r), 0 ≤ g y) → g x₀ = 0 →
      (∀ y ∈ ballZ0 (d := d) r, |lapR g y| ≤ lam) →
      ∀ y : Site d, ‖toE y - toE x₀‖ < r / 4 → g y ≤ C * ‖toE y - toE x₀‖ ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := harnackQuadratic d hd (1 / 2) (by norm_num) (by norm_num) lam
  refine ⟨max C 0, le_max_right _ _, fun r g x₀ hx₀ hg0 hgx₀ hlap y hy => ?_⟩
  have hr : 0 < r := by linarith [norm_nonneg (toE y - toE x₀)]
  set B := ballZ0 (d := d) r with hB
  have hx₀B : x₀ ∈ B := MuLipschitz.mem_ballZ0.2 (by linarith)
  set f : Site d → ℝ := fun z => if z + x₀ ∈ dClosure B then g (z + x₀) else 0 with hf
  have hf0 : ∀ z, 0 ≤ f z := fun z => by
    simp only [hf]; split_ifs with h
    · exact hg0 _ h
    · exact le_rfl
  have hfz : ∀ z, z + x₀ ∈ dClosure B → f z = g (z + x₀) := fun z h => by
    simp only [hf]; exact if_pos h
  have hf00 : f 0 = 0 := by
    rw [hfz 0 (by rw [zero_add]; exact subset_dClosure _ hx₀B), zero_add, hgx₀]
  have hlapf : ∀ z ∈ ballZ0 (d := d) (r / 2), |lapR f z| ≤ lam := by
    intro z hz
    have hz' : ‖toE z‖ < r / 2 := MuLipschitz.mem_ballZ0.1 hz
    have hzB : z + x₀ ∈ B := by
      refine MuLipschitz.mem_ballZ0.2 ?_
      rw [MuLipschitz.toE_add]
      calc ‖toE z + toE x₀‖ ≤ ‖toE z‖ + ‖toE x₀‖ := norm_add_le _ _
        _ < r := by linarith
    have heq : lapR f z = lapR (fun w => g (w + x₀)) z := by
      refine Flat.lapR_congr_nbr (hfz z (subset_dClosure _ hzB)) (fun i => hfz _ ?_)
        (fun i => hfz _ ?_)
      · rw [add_right_comm]; exact (Flat.mem_dClosure_of_nbr hzB i).1
      · rw [sub_add_eq_add_sub]; exact (Flat.mem_dClosure_of_nbr hzB i).2
    rw [heq, lapR_comp_add]
    exact hlap _ hzB
  have hmem : y - x₀ ∈ ballZ0 (d := d) (1 / 2 * (r / 2)) := by
    refine MuLipschitz.mem_ballZ0.2 ?_
    rw [MuLipschitz.toE_sub]; linarith
  have hH := hC (r / 2) f hf0 hf00 hlapf (y - x₀) hmem
  have hyB : y ∈ B := MuLipschitz.mem_ballZ0.2 (by
    have := norm_sub_norm_le (toE y) (toE x₀)
    linarith)
  rw [hfz (y - x₀) (by rw [sub_add_cancel]; exact subset_dClosure _ hyB), sub_add_cancel,
    MuLipschitz.toE_sub] at hH
  calc g y ≤ C * ‖toE y - toE x₀‖ ^ 2 := hH
    _ ≤ max C 0 * ‖toE y - toE x₀‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)

end SingleSourceD2

end RandomSandpile

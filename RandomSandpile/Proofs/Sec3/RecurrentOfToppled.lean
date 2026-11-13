import RandomSandpile.Steps.Sec3.RecurrentOfToppled
import RandomSandpile.Proofs.Sec3.Burning

/-!
# Proof of Proposition 3.4 (a sandpile in which every site has toppled is recurrent)

Proofs of the steps of `RandomSandpile/Steps/Sec3/RecurrentOfToppled.lean` and of
`RandomSandpile.RecurrentOfToppledStmt`.

* `toppledFinite`: `A` lies in the range of the toppling sequence of the legal part of `w`.
* `toppledNoForbidden`: by induction on the legal part `u` of `w`, `Δ_{ℤ^d} u + τ` has no forbidden
  subconfiguration on the set `{u ≥ 1}` of toppled sites. Appending a toppling at the unstable site
  `x` adds `x` to that set (`NoForbiddenSubconfig.insert`, `x` is unstable) and then topples `x`
  (`NoForbiddenSubconfig.topple`). This is the last-toppling argument of the hidden proof
 in inductive form.
* `legalOfNoForbidden`: greedy toppling, by induction on `∑_A (φ - ψ)`, `ψ` the topplings done. On
  the set `B` where `φ - ψ` attains its maximum `M ≥ 1`, `φ - ψ ≤ 1_B + M - 1` with equality on `B`,
  so `Δ_{ℤ^d}(φ - ψ) ≤ Δ_{ℤ^d} 1_B` on `B`; the site of `B` given by the absence of forbidden
  subconfigurations is unstable in `η - Δ_{ℤ^d} φ + Δ_{ℤ^d} ψ`.
* `superharmonicBarrier`: the barrier `C (R - x₀²)` on `A`, `0` off `A` (the proof of
  `RandomSandpile.stabilizingOpen_nonempty`, `RandomSandpile/Defs/Odometer.lean:196`, with `C`
  given).
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- The absence of forbidden subconfigurations passes to subsets. -/
theorem NoForbiddenSubconfig.subset {η : Site d → ℤ} {A A' : Set (Site d)}
    (hη : NoForbiddenSubconfig η A) (h : A' ⊆ A) : NoForbiddenSubconfig η A' :=
  fun B hB hBf hBne => hη B (hB.trans h) hBf hBne

/-- Adding an unstable site to `A` preserves the absence of forbidden subconfigurations: an
unstable site `x` has `η x ≥ 2d ≥ deg_B x`. -/
theorem NoForbiddenSubconfig.insert {η : Site d → ℤ} {A : Set (Site d)}
    (hη : NoForbiddenSubconfig η A) {x : Site d} (hx : 2 * (d : ℤ) ≤ η x) :
    NoForbiddenSubconfig η (insert x A) := by
  intro B hB hBf hBne
  by_cases hxB : x ∈ B
  · refine ⟨x, hxB, ?_⟩
    have h := lap_le_lap_of_le (u := B.indicator fun _ => (1 : ℤ)) (w := fun _ => 1)
      (fun y => by by_cases hy : y ∈ B <;> simp [hy]) (x := x) (by simp [hxB])
    rw [Burning.lap_const_apply] at h
    linarith
  · exact hη B (fun y hy => (Set.mem_insert_iff.1 (hB hy)).resolve_left fun h => hxB (h ▸ hy))
      hBf hBne

namespace RecurrentOfToppled

/-- After legal toppling `u` from `τ` (in any set `W`), the sandpile `τ + Δ_{ℤ^d} u` has no
forbidden subconfiguration on the set of sites toppled at least once. -/
theorem noForbidden_toppled {τ u : Site d → ℤ} {W : Set (Site d)} (hu : IsLegal τ W u) :
    NoForbiddenSubconfig (fun x => τ x + lap u x) {z | 1 ≤ u z} := by
  refine IsLegal.induction
    (fun u => NoForbiddenSubconfig (fun x => τ x + lap u x) {z | 1 ≤ u z}) ?_ ?_ hu
  · intro B hB _ hBne
    obtain ⟨z, hz⟩ := hBne
    exact absurd (hB hz) (by simp)
  · intro u x _ ih _ hx
    have hx' : 2 * (d : ℤ) ≤ τ x + lap u x := by linarith
    have h := (ih.insert (x := x) hx').topple (x := x) hx'
    refine (h.subset fun z hz => ?_).mono fun z _ => ?_
    · by_cases hzx : z = x
      · exact Set.mem_insert_iff.2 (Or.inl hzx)
      · refine Set.mem_insert_iff.2 (Or.inr ?_)
        have hz' : 1 ≤ u z + dirac x z := hz
        rw [dirac_of_ne hzx, add_zero] at hz'
        exact hz'
    · show τ z + lap u z + lap (dirac x) z ≤ τ z + lap (u + dirac x) z
      rw [Burning.lap_pi_add_apply]
      linarith

private theorem unit_apply_sq' (i i₀ : Fin d) :
    (unit i : Site d) i₀ ^ 2 = if i = i₀ then 1 else 0 := by
  by_cases h : i = i₀
  · subst h; simp [unit]
  · simp [unit, Ne.symm h, h]

end RecurrentOfToppled

open RecurrentOfToppled

/-- **Step 1 of Proposition 3.4**: the set `A` of toppled sites is finite. -/
theorem toppledFinite : ToppledFiniteStmt := by
  intro d A W η w hAW hw h1
  obtain ⟨wb, uh, -, -, rfl, hwbW, -, n, xs, -, -, rfl⟩ := hw
  refine (Set.finite_range xs).subset fun x hx => ?_
  have h := h1 x hx
  simp only [Pi.add_apply, hwbW x (hAW hx), zero_add] at h
  by_contra hne
  have h0 : ∑ i : Fin n, dirac (xs i) x = 0 :=
    Finset.sum_eq_zero fun i _ => dirac_of_ne fun h => hne ⟨i, h.symm⟩
  omega

/-- **Step 2 of Proposition 3.4**: `Δ_{ℤ^d} w + η` has no forbidden subconfiguration
in `A`. -/
theorem toppledNoForbidden : ToppledNoForbiddenStmt := by
  intro d A W η w hAW hw h1
  obtain ⟨wb, uh, -, -, rfl, hwbW, -, hleg⟩ := hw
  refine ((noForbidden_toppled hleg).subset fun x hx => ?_).mono fun x _ => ?_
  · have h := h1 x hx
    simp only [Pi.add_apply, hwbW x (hAW hx), zero_add] at h
    exact h
  · show lap wb x + η x + lap uh x ≤ lap (wb + uh) x + η x
    rw [Burning.lap_pi_add_apply]
    linarith

/-- **Step 3 of Proposition 3.4**, the generalized burning algorithm. -/
theorem legalOfNoForbidden : LegalOfNoForbiddenStmt := by
  classical
  intro d A hA η φ hη hφ0 hφA
  have key : ∀ n : ℕ, ∀ ψ, IsLegal (fun x => η x - lap φ x) A ψ → (∀ x, ψ x ≤ φ x) →
      ∑ x ∈ hA.toFinset, (φ x - ψ x) = n → IsLegal (fun x => η x - lap φ x) A φ := by
    intro n
    induction n with
    | zero =>
      intro ψ hψ hle hsum
      have h0 : ∀ x ∈ hA.toFinset, φ x - ψ x = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun x _ => sub_nonneg.2 (hle x)).1 (by simpa using hsum)
      have he : ψ = φ := by
        funext x
        by_cases hx : x ∈ A
        · have := h0 x (hA.mem_toFinset.2 hx); linarith
        · rw [hψ.eq_zero_of_notMem hx, hφA x hx]
      rw [he] at hψ
      exact hψ
    | succ n ih =>
      intro ψ hψ hle hsum
      have hne : ∑ x ∈ hA.toFinset, (φ x - ψ x) ≠ 0 := by rw [hsum]; omega
      obtain ⟨x, hxS, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      obtain ⟨z₀, hz₀S, hz₀⟩ := hA.toFinset.exists_max_image (fun y => φ y - ψ y) ⟨x, hxS⟩
      have hz₀' : ∀ y ∈ hA.toFinset, φ y - ψ y ≤ φ z₀ - ψ z₀ := hz₀
      obtain ⟨M, hM⟩ : ∃ M, M = φ z₀ - ψ z₀ := ⟨_, rfl⟩
      have hM1 : 1 ≤ M := by
        have h1 := hz₀' x hxS; have h2 := hle x
        have h3 : φ x - ψ x ≠ 0 := hx
        omega
      let B : Set (Site d) := {y | y ∈ A ∧ φ y - ψ y = M}
      have hBA : B ⊆ A := fun y hy => hy.1
      obtain ⟨z, ⟨hzA, hzM⟩, hz⟩ :=
        hη B hBA (hA.subset hBA) ⟨z₀, hA.mem_toFinset.1 hz₀S, hM.symm⟩
      -- `φ - ψ ≤ 1_B + (M - 1)`, with equality at `z`
      have hcmp : ∀ y, φ y - ψ y ≤ B.indicator (fun _ => (1 : ℤ)) y + (M - 1) := by
        intro y
        by_cases hyB : y ∈ B
        · rw [Set.indicator_of_mem hyB, hyB.2]; omega
        · rw [Set.indicator_of_notMem hyB]
          by_cases hyA : y ∈ A
          · have h1 := hz₀' y (hA.mem_toFinset.2 hyA)
            have h2 : φ y - ψ y ≠ M := fun h => hyB ⟨hyA, h⟩
            omega
          · rw [hψ.eq_zero_of_notMem hyA, hφA y hyA]; omega
      have hzB : z ∈ B := ⟨hzA, hzM⟩
      have hlap := lap_le_lap_of_le (u := fun y => φ y - ψ y)
        (w := fun y => B.indicator (fun _ => (1 : ℤ)) y + (M - 1)) hcmp (x := z)
        (by simp only [Set.indicator_of_mem hzB, hzM]; ring)
      rw [Burning.lap_sub_apply', Burning.lap_add_apply', Burning.lap_const_apply] at hlap
      have hψ' : IsLegal (fun x => η x - lap φ x) A (ψ + dirac z) := hψ.snoc hzA (by
        show 2 * (d : ℤ) ≤ lap ψ z + (η z - lap φ z)
        linarith)
      refine ih (ψ + dirac z) hψ' (fun y => ?_) ?_
      · by_cases hyz : y = z
        · subst hyz
          simp only [Pi.add_apply, dirac_self]
          omega
        · simp only [Pi.add_apply, dirac_of_ne hyz, add_zero]
          exact hle y
      · have hzS : z ∈ hA.toFinset := hA.mem_toFinset.2 hzA
        have hs : ∀ y, φ y - (ψ + dirac z) y = (φ y - ψ y) - dirac z y := fun y => by
          simp only [Pi.add_apply]; ring
        have hd1 : ∑ y ∈ hA.toFinset, dirac z y = 1 := by
          rw [Finset.sum_eq_single z (fun b _ hb => dirac_of_ne hb) (fun h => absurd hzS h)]
          exact dirac_self z
        rw [Finset.sum_congr rfl fun y _ => hs y, Finset.sum_sub_distrib, hsum, hd1]
        push_cast
        ring
  refine key (∑ x ∈ hA.toFinset, φ x).toNat 0 (IsLegal.zero _ A) hφ0 ?_
  simp only [Pi.zero_apply, sub_zero]
  exact (Int.toNat_of_nonneg (Finset.sum_nonneg fun x _ => hφ0 x)).symm

/-- **Step 4 of Proposition 3.4**, the barrier `C (R - x₀²)` on `A`. The proof is that of
`RandomSandpile.stabilizingOpen_nonempty` (`RandomSandpile/Defs/Odometer.lean:196`) with the constant
`C` given. -/
theorem superharmonicBarrier : SuperharmonicBarrierStmt := by
  classical
  intro d hd A hA C hC0
  let i₀ : Fin d := ⟨0, hd⟩
  obtain ⟨K, hK⟩ := (hA.image fun x : Site d => |x i₀|).bddAbove
  have hK' : ∀ x ∈ A, |x i₀| ≤ K := fun x hx => hK ⟨x, hx, rfl⟩
  set R : ℤ := (|K| + 1) ^ 2 with hR
  -- the quadratic `g = C (R - x_{i₀}²)` dominates the barrier at `x ∈ A` and its neighbours
  have hsq : ∀ y : Site d, |y i₀| ≤ |K| + 1 → 0 ≤ R - y i₀ ^ 2 := by
    intro y hy
    have h0 : 0 ≤ |y i₀| := abs_nonneg _
    have : y i₀ ^ 2 ≤ (|K| + 1) ^ 2 := by
      rw [← sq_abs (y i₀)]; exact pow_le_pow_left₀ h0 hy 2
    linarith
  have hnb : ∀ x ∈ A, ∀ (i : Fin d) (s : ℤ), |s| ≤ 1 →
      |(x + s • unit i) i₀| ≤ |K| + 1 := by
    intro x hx i s hs
    have hu : |s * (unit i : Site d) i₀| ≤ 1 := by
      rw [abs_mul]
      have : |(unit i : Site d) i₀| ≤ 1 := by
        by_cases h : i = i₀
        · subst h; simp [unit]
        · simp [unit, Ne.symm h]
      nlinarith [abs_nonneg s, abs_nonneg ((unit i : Site d) i₀)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |x i₀ + s * (unit i : Site d) i₀| ≤ |x i₀| + |s * (unit i : Site d) i₀| := abs_add_le _ _
      _ ≤ |K| + 1 := add_le_add ((hK' x hx).trans (le_abs_self K)) hu
  let u : Site d → ℤ := fun y => if y ∈ A then C * (R - y i₀ ^ 2) else 0
  have hule : ∀ x ∈ A, ∀ (i : Fin d) (s : ℤ), |s| ≤ 1 →
      u (x + s • unit i) ≤ C * (R - (x + s • unit i) i₀ ^ 2) := by
    intro x hx i s hs
    simp only [u]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hC0 (hsq _ (hnb x hx i s hs))
  refine ⟨u, fun y => ?_, fun y hy => ?_, fun x hx => ?_⟩
  · simp only [u]
    split_ifs with h
    · exact mul_nonneg hC0 (hsq y (by
        have := hK' y h; linarith [le_abs_self K]))
    · exact le_rfl
  · simp only [u, ite_eq_right hy]
  · -- `Δ u (x) ≤ ∑_i (g(x+e_i) + g(x-e_i) - 2 g(x)) = -2C`
    have hux : u x = C * (R - x i₀ ^ 2) := by simp [u, hx]
    have hplus : ∀ i : Fin d, u (x + unit i) ≤ C * (R - (x + unit i) i₀ ^ 2) := fun i => by
      simpa using hule x hx i 1 (by simp)
    have hminus : ∀ i : Fin d, u (x - unit i) ≤ C * (R - (x - unit i) i₀ ^ 2) := fun i => by
      simpa [sub_eq_add_neg] using hule x hx i (-1) (by simp)
    rw [lap_eq_sum_second_diff]
    calc ∑ i : Fin d, (-2 * u x + u (x + unit i) + u (x - unit i))
        ≤ ∑ i : Fin d, (if i = i₀ then -2 * C else 0) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h2 : -2 * C * (unit i : Site d) i₀ ^ 2 = if i = i₀ then -2 * C else 0 := by
            rw [unit_apply_sq']; split_ifs <;> ring
          rw [← h2, hux]
          have hp := hplus i
          have hm := hminus i
          simp only [Pi.add_apply, Pi.sub_apply] at hp hm
          nlinarith [hp, hm]
      _ = -2 * C := by simp [i₀]

/-- The forbidden-subconfiguration criterion for recurrence . -/
theorem noForbiddenRecurrent : NoForbiddenRecurrentStmt :=
  noForbiddenRecurrent_of_steps legalOfNoForbidden superharmonicBarrier

/-- **Proposition 3.4** (recurrent). -/
theorem recurrentOfToppled : RecurrentOfToppledStmt :=
  recurrentOfToppled_of_steps toppledFinite toppledNoForbidden noForbiddenRecurrent

end RandomSandpile

import RandomSandpile.Steps.Sec3.Burning
import RandomSandpile.Proofs.Sec3.LeastAction
import LatticeProb.Sandpile.LeastAction

/-!
# Proof of Proposition 3.3 (burning: maximum and comparison principles)

Proofs of the four steps of `RandomSandpile/Steps/Sec3/Burning.lean` and of
`RandomSandpile.BurningStmt` (Proposition 3.3, `paper/random_piles-corrected.tex`).

* `stableMaxPrinciple` (eq:stable): if `v x₀ > f` on `∂A`, put `M = v x₀ - 1 ≥ 0`. The
  truncation `min v M` is again stabilizing for `s` (where `v ≤ M` it lies below `v` and touches
  it; where `v > M` it touches the constant `M`, and `s` is stable), so `min v M - w` is a
  stabilizing toppling function for `Δ_{ℤ^d} w + s` vanishing on `∂A`, where `v = w + û` is the
  decomposition of `v ∈ 𝓛(s, A)`. The least action principle (`legalLeStabilizing`) gives
  `û ≤ min v M - w`, so `v x₀ = û x₀ ≤ M`, a contradiction.
* `recurrentNoForbidden` (burning algorithm): the sandpile `t + 2d - 1` with `t ≥ 0` has no
  forbidden subconfiguration (a finite nonempty `B` has a site with a neighbour outside `B`), and
  a legal toppling preserves this (`NoForbiddenSubconfig.topple`, using
  `1_B = 1_{B ∖ {x}} + 1_x`).
* `noForbiddenLocLegal`: boundary topplings add chips in `A` (`Δ_{ℤ^d} w ≥ 0` in `A`), then
  legal topplings preserve the property.
* `supersolutionMinPrinciple`: if `z > z x₀ ≥ min_A z` on `∂A`, let `B` be the set where `z`
  attains its minimum over `A`. A site `y₀ ∈ B` given by the absence of forbidden
  subconfigurations has `Δ_{ℤ^d}(z + 1_B)(y₀) ≤ -1`, while `z + 1_B` has a local minimum at `y₀`.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

namespace Burning

variable {d : ℕ}

/-- `x + eᵢ` is a neighbour of `x` (as `LatticeProb.Sandpile.adj_add_unit`,
`LatticeProb/Sandpile/Waves.lean:25`, whose module is not imported here). -/
theorem adj_add_unit' (x : Site d) (i : Fin d) : (lattice d).Adj (x + unit i) x :=
  ⟨i, Or.inr rfl⟩

/-- `x - eᵢ` is a neighbour of `x` (as `LatticeProb.Sandpile.adj_sub_unit`,
`LatticeProb/Sandpile/Waves.lean:29`). -/
theorem adj_sub_unit' (x : Site d) (i : Fin d) : (lattice d).Adj (x - unit i) x :=
  ⟨i, Or.inl (by abel)⟩

theorem dirac_nonneg' (z x : Site d) : 0 ≤ dirac z x := by
  unfold dirac; split_ifs <;> norm_num

/-- The integer Laplacian of a constant vanishes. -/
theorem lap_const_apply (c : ℤ) (x : Site d) : lap (fun _ => c) x = 0 := by
  simp only [lap, nbrSumZ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A function with a local minimum at `x` over the `2d` neighbours of `x` has
`Δ_{ℤ^d} g (x) ≥ 0`. -/
theorem lap_nonneg_of_le_nbr {g : Site d → ℤ} {x : Site d}
    (h : ∀ i, g x ≤ g (x + unit i) ∧ g x ≤ g (x - unit i)) : 0 ≤ lap g x := by
  rw [lap_eq_sum_second_diff]
  exact Finset.sum_nonneg fun i _ => by linarith [(h i).1, (h i).2]

/-- The neighbour `x + eᵢ` of a site `x ∈ A` lies in `A` or in `∂A`. -/
theorem add_unit_mem {A : Set (Site d)} {x : Site d} (hx : x ∈ A) (i : Fin d) :
    x + unit i ∈ A ∨ x + unit i ∈ bdry A := by
  by_cases h : x + unit i ∈ A
  · exact Or.inl h
  · exact Or.inr (mem_bdry.2 ⟨h, x, hx, adj_add_unit' x i⟩)

/-- The neighbour `x - eᵢ` of a site `x ∈ A` lies in `A` or in `∂A`. -/
theorem sub_unit_mem {A : Set (Site d)} {x : Site d} (hx : x ∈ A) (i : Fin d) :
    x - unit i ∈ A ∨ x - unit i ∈ bdry A := by
  by_cases h : x - unit i ∈ A
  · exact Or.inl h
  · exact Or.inr (mem_bdry.2 ⟨h, x, hx, adj_sub_unit' x i⟩)

theorem self_ne_add_unit (z : Site d) (i : Fin d) : z ≠ z + unit i := by
  intro h
  apply unit_ne_zero i
  have := congrArg (fun y => y - z) h
  simpa using this.symm

/-- A finite nonempty set of sites contains a site whose `+e₀` neighbour lies outside it. -/
theorem exists_add_unit_notMem (hd : 0 < d) {B : Set (Site d)} (hB : B.Finite)
    (hne : B.Nonempty) : ∃ z ∈ B, z + unit ⟨0, hd⟩ ∉ B := by
  obtain ⟨z, hz, hmax⟩ := Set.exists_max_image B (fun x => x ⟨0, hd⟩) hB hne
  refine ⟨z, hz, fun h => ?_⟩
  have h1 := hmax _ h
  simp [unit] at h1

/-- The outer boundary of a finite nonempty set of sites is nonempty. -/
theorem bdry_nonempty (hd : 0 < d) {A : Set (Site d)} (hA : A.Finite) (hne : A.Nonempty) :
    (bdry A).Nonempty := by
  obtain ⟨z, hz, hzn⟩ := exists_add_unit_notMem hd hA hne
  exact ⟨_, mem_bdry.2 ⟨hzn, z, hz, adj_add_unit' z _⟩⟩

/-- A unit toppling at the neighbour `z + eᵢ` sends at least one chip to `z`. -/
theorem one_le_lap_dirac_add_unit (z : Site d) (i : Fin d) :
    1 ≤ lap (dirac (z + unit i)) z := by
  rw [lap, dirac_of_ne (self_ne_add_unit z i), mul_zero, sub_zero]
  have h1 : (1 : ℤ) ≤ dirac (z + unit i) (z + unit i) + dirac (z + unit i) (z - unit i) := by
    rw [dirac_self]; linarith [dirac_nonneg' (z + unit i) (z - unit i)]
  exact h1.trans (Finset.single_le_sum
    (f := fun j => dirac (z + unit i) (z + unit j) + dirac (z + unit i) (z - unit j))
    (fun j _ => add_nonneg (dirac_nonneg' _ _) (dirac_nonneg' _ _)) (Finset.mem_univ i))

/-- `1_B = 1_{B ∖ {x}} + 1_x` for `x ∈ B`. -/
theorem indicator_eq_diff_add_dirac {B : Set (Site d)} {x : Site d} (hx : x ∈ B) :
    (B.indicator fun _ => (1 : ℤ)) =
      fun y => ((B \ {x}).indicator fun _ => (1 : ℤ)) y + dirac x y := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [hx, dirac]
  · by_cases hyB : y ∈ B <;> simp [Set.indicator, hyB, hy, dirac]

/-- The absence of forbidden subconfigurations is monotone in the sandpile. -/
theorem _root_.RandomSandpile.NoForbiddenSubconfig.mono {η η' : Site d → ℤ} {A : Set (Site d)}
    (hη : NoForbiddenSubconfig η A) (h : ∀ x ∈ A, η x ≤ η' x) : NoForbiddenSubconfig η' A := by
  intro B hBA hBf hBne
  obtain ⟨z, hz, hle⟩ := hη B hBA hBf hBne
  exact ⟨z, hz, by linarith [h z (hBA hz)]⟩

/-- Toppling an unstable site preserves the absence of forbidden subconfigurations. -/
theorem _root_.RandomSandpile.NoForbiddenSubconfig.topple {η : Site d → ℤ} {A : Set (Site d)}
    (hη : NoForbiddenSubconfig η A) {x : Site d} (hx : 2 * (d : ℤ) ≤ η x) :
    NoForbiddenSubconfig (fun y => η y + lap (dirac x) y) A := by
  intro B hBA hBf hBne
  by_cases hxB : x ∈ B
  · have hlap : ∀ y, lap (B.indicator fun _ => (1 : ℤ)) y =
        lap ((B \ {x}).indicator fun _ => (1 : ℤ)) y + lap (dirac x) y := fun y => by
      rw [indicator_eq_diff_add_dirac hxB, lap_add_apply']
    rcases (B \ {x}).eq_empty_or_nonempty with h | h
    · refine ⟨x, hxB, ?_⟩
      rw [hlap, h, Set.indicator_empty, lap_const_apply]
      linarith
    · obtain ⟨z, hz, hle⟩ := hη (B \ {x}) (Set.sdiff_subset.trans hBA)
        (hBf.subset Set.sdiff_subset) h
      refine ⟨z, hz.1, ?_⟩
      rw [hlap]
      linarith
  · obtain ⟨z, hz, hle⟩ := hη B hBA hBf hBne
    have hzx : z ≠ x := fun h => hxB (h ▸ hz)
    have h0 := lap_le_lap_of_le (u := 0) (w := dirac x) (fun y => dirac_nonneg' x y) (x := z)
      (by simp [dirac_of_ne hzx])
    rw [lap_zero_apply] at h0
    exact ⟨z, hz, by linarith⟩

/-- Legal toppling preserves the absence of forbidden subconfigurations. -/
theorem _root_.RandomSandpile.NoForbiddenSubconfig.of_isLegal {η u : Site d → ℤ} {A : Set (Site d)}
    (hη : NoForbiddenSubconfig η A) (hu : IsLegal η A u) :
    NoForbiddenSubconfig (fun y => η y + lap u y) A := by
  refine IsLegal.induction (fun u => NoForbiddenSubconfig (fun y => η y + lap u y) A) ?_ ?_ hu
  · exact hη.mono fun x _ => by simp [lap_zero_apply]
  · intro u x _ hP _ hleg
    refine (hP.topple (x := x) (by linarith)).mono fun y _ => ?_
    rw [lap_pi_add_apply]
    linarith

/-- The sandpile `t + 2d - 1` with `t ≥ 0` in `A` has no forbidden subconfiguration in `A`. -/
theorem noForbiddenSubconfig_base (hd : 0 < d) {t : Site d → ℤ} {A : Set (Site d)}
    (ht : ∀ x ∈ A, 0 ≤ t x) : NoForbiddenSubconfig (fun y => t y + (2 * (d : ℤ) - 1)) A := by
  intro B hBA hBf hBne
  obtain ⟨z, hz, hzn⟩ := exists_add_unit_notMem hd hBf hBne
  refine ⟨z, hz, ?_⟩
  have hle : ∀ y, (B.indicator fun _ => (1 : ℤ)) y ≤
      (fun y => (1 : ℤ) - dirac (z + unit ⟨0, hd⟩) y) y := by
    intro y
    by_cases hy : y = z + unit ⟨0, hd⟩
    · subst hy; simp [hzn]
    · by_cases hyB : y ∈ B <;> simp [hyB, dirac_of_ne hy]
  have heq : (B.indicator fun _ => (1 : ℤ)) z =
      (fun y => (1 : ℤ) - dirac (z + unit ⟨0, hd⟩) y) z := by
    simp [hz, dirac_of_ne (self_ne_add_unit z _)]
  have h1 := lap_le_lap_of_le hle heq
  rw [lap_sub_apply', lap_const_apply] at h1
  have h2 := one_le_lap_dirac_add_unit z ⟨0, hd⟩
  have h3 := ht z (hBA hz)
  linarith

end Burning

open Burning

/-- Step 1 of Proposition 3.3, (eq:stable): the maximum principle for stable `s`. -/
theorem stableMaxPrinciple : StableMaxPrincipleStmt := by
  intro d hd A hA f s v hf hv hvf hst x₀ hx₀
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  obtain ⟨y₀, hy₀⟩ := bdry_nonempty hd hA ⟨x₀, hx₀⟩
  have hM0 : 0 ≤ v x₀ - 1 := by have := hf y₀ hy₀; have := hcon y₀ hy₀; omega
  obtain ⟨⟨w, uh, hw, huh, hvwu, hwA, huhB, hleg⟩, hvT, hvS⟩ := hv
  have hv_apply : ∀ y, v y = w y + uh y := fun y => by rw [hvwu]; rfl
  have huh0 : ∀ y ∉ A, uh y = 0 := fun y hy => by
    by_cases hyb : y ∈ bdry A
    · exact huhB y hyb
    · exact huh.2 y (by rw [dClosure_eq]; exact fun h => h.elim hy hyb)
  -- off `A`, `v = w ≤ M`
  have hoff : ∀ y ∉ A, v y = w y ∧ w y ≤ v x₀ - 1 := fun y hy => by
    refine ⟨by rw [hv_apply, huh0 y hy, add_zero], ?_⟩
    by_cases hyb : y ∈ bdry A
    · have h1 := hvf y hyb; have h2 := hcon y hyb; rw [hv_apply, huh0 y hy] at h1; omega
    · rw [hw.2 y (by rw [dClosure_eq]; exact fun h => h.elim hy hyb)]; exact hM0
  let zf : Site d → ℤ := fun y => min (v y) (v x₀ - 1) - w y
  have hzoff : ∀ y ∉ A, zf y = 0 := fun y hy => by
    obtain ⟨h1, h2⟩ := hoff y hy
    simp only [zf, h1, min_eq_left h2, sub_self]
  have hzS : zf ∈ stabilizing (fun y => lap w y + s y) A := by
    refine ⟨⟨fun y => ?_, fun y hy => hzoff y fun h => hy (subset_dClosure A h)⟩, fun x hx => ?_⟩
    · by_cases hyA : y ∈ A
      · simp only [zf, hwA y hyA, sub_zero]; exact le_min (hvT.1 y) hM0
      · rw [hzoff y hyA]
    · have hsub : lap zf x = lap (fun y => min (v y) (v x₀ - 1)) x - lap w x :=
        lap_sub_apply' _ w x
      have hmv : lap (fun y => min (v y) (v x₀ - 1)) x + s x ≤ 2 * (d : ℤ) - 1 := by
        by_cases hvx : v x ≤ v x₀ - 1
        · have := lap_le_lap_of_le (u := fun y => min (v y) (v x₀ - 1)) (w := v)
            (fun y => min_le_left _ _) (x := x) (min_eq_left hvx)
          linarith [hvS x hx]
        · have := lap_le_lap_of_le (u := fun y => min (v y) (v x₀ - 1)) (w := fun _ => v x₀ - 1)
            (fun y => min_le_right _ _) (x := x) (min_eq_right (by omega))
          rw [lap_const_apply] at this
          linarith [hst x hx]
      rw [hsub]
      linarith
  have hle : uh x₀ ≤ zf x₀ := legalLeStabilizing d A _ uh zf hleg hzS x₀
  have hz0 : zf x₀ ≤ v x₀ - 1 := by
    simp only [zf, hwA x₀ hx₀, sub_zero]; exact min_le_right _ _
  have hv0 : v x₀ = uh x₀ := by rw [hv_apply, hwA x₀ hx₀, zero_add]
  omega

/-- Step 2 of Proposition 3.3, the burning algorithm: recurrent sandpiles have no forbidden
subconfiguration. -/
theorem recurrentNoForbidden : RecurrentNoForbiddenStmt := by
  rintro d hd A η ⟨t, u, ht, hu, hub, hη⟩
  have h := (noForbiddenSubconfig_base hd ht).of_isLegal (isLegal_of_mem_locLegal hu hub)
  refine h.mono fun x hx => ?_
  rw [hη x hx]
  linarith

/-- Step 3 of Proposition 3.3: locally legal topplings preserve the absence of forbidden
subconfigurations. -/
theorem noForbiddenLocLegal : NoForbiddenLocLegalStmt := by
  intro d A η v hη hv
  obtain ⟨w, uh, hw, -, rfl, hwA, -, hleg⟩ := hv
  have h0 : NoForbiddenSubconfig (fun y => lap w y + η y) A := hη.mono fun x hx => by
    have := lap_le_lap_of_le (u := 0) (w := w) (fun y => hw.1 y) (x := x) (by simp [hwA x hx])
    rw [lap_zero_apply] at this
    linarith
  refine (h0.of_isLegal hleg).mono fun x _ => ?_
  rw [lap_pi_add_apply]
  linarith

/-- Step 4 of Proposition 3.3: the minimum principle for supersolutions. -/
theorem supersolutionMinPrinciple : SupersolutionMinPrincipleStmt := by
  intro d A hA η z hη hz x₀ hx₀
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  obtain ⟨x₁, hx₁, hmin⟩ := Set.exists_min_image A z hA ⟨x₀, hx₀⟩
  let B : Set (Site d) := {y | y ∈ A ∧ z y = z x₁}
  have hBA : B ⊆ A := fun y hy => hy.1
  obtain ⟨y₀, hy₀, hle⟩ := hη B hBA (hA.subset hBA) ⟨x₁, hx₁, rfl⟩
  have key : ∀ n, n ∈ A ∨ n ∈ bdry A → z x₁ + 1 ≤ z n + B.indicator (fun _ => (1 : ℤ)) n := by
    intro n hn
    by_cases hnB : n ∈ B
    · rw [Set.indicator_of_mem hnB, hnB.2]
    · rw [Set.indicator_of_notMem hnB, add_zero]
      rcases hn with hnA | hnb
      · have h1 := hmin n hnA
        have h2 : z n ≠ z x₁ := fun h => hnB ⟨hnA, h⟩
        omega
      · have h1 := hcon n hnb
        have h2 := hmin x₀ hx₀
        omega
  have hval : z y₀ + B.indicator (fun _ => (1 : ℤ)) y₀ = z x₁ + 1 := by
    rw [Set.indicator_of_mem hy₀, hy₀.2]
  have hnn : 0 ≤ lap (fun y => z y + B.indicator (fun _ => (1 : ℤ)) y) y₀ :=
    lap_nonneg_of_le_nbr fun i =>
      ⟨by rw [hval]; exact key _ (add_unit_mem hy₀.1 i),
        by rw [hval]; exact key _ (sub_unit_mem hy₀.1 i)⟩
  rw [lap_add_apply'] at hnn
  have := hz y₀ hy₀.1
  linarith

/-- **Proposition 3.3** (burning): the maximum principle (eq:stable), the minimum
principle (eq:rec) and the comparison principle for the discrete sandpile PDE. -/
theorem burning : BurningStmt :=
  burning_of_steps stableMaxPrinciple recurrentNoForbidden noForbiddenLocLegal
    supersolutionMinPrinciple

end RandomSandpile

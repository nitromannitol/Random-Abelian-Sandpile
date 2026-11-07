import RandomSandpile.Proofs.Sec9.SingleSourceFlatnessStar
import RandomSandpile.Proofs.Sec7.LimitObstacleGamma
import RandomSandpile.Proofs.Sec5.MuBounded

/-!
# Theorem 9.2, `F*`-variant: the finite comparison at a contact point

Finite ingredients of the subsolution step at Peano points (with the leastness of the single-source odometer `v_n` (least stabilizing
toppling of `η + n δ_0`) in place of recurrence (Propositions 3.3-3.4):

* `false_of_competitor`: an integer `Y` with `Δ Y + η ≤ 2d - 1` and `Y ≥ 0` on `A ∌ 0`,
  `Y ≥ v_n` on the outer boundary of `A` and `Y < v_n` somewhere in `A` cannot exist:
  `min(Y, v_n)` on `A`, `v_n` elsewhere, would be a smaller stabilizing toppling.
* `exists_int_affine`: an integer affine function (zero lattice Laplacian) within
  `(d + 1)|y - z₀| + 1` of a given real affine function.
* `exists_contact_of_lt_muStar`: if `μ*(A, η, l, M)` exceeds the site bound of Lemma 5.4 times
  `|A ∖ I|`, some stabilizing `X` has a subgradient of `X - q_l - q_M` (relative to `Ā`) at a site
  of `A ∩ I`.
* `false_of_contact`: route_star §4.3. A contact point `x_c ∈ A` of a stabilizing `X` and a
  splitting `q - T = G + affine` with `|v_n - T| ≤ e` on `Ā`, `0 ≤ G`, `G(x_c) ≤ γ₊`, `G ≥ γ₋` on the
  outer boundary, `γ₋ - γ₊` larger than the errors and `v_n` large on `A`, is impossible.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric

namespace RandomSandpile

namespace SingleSourceFstar

variable {d : ℕ}

/-! ### Lattice Laplacians -/

/-- Copied from `Proofs/Sec7/PegdenSmartRegularityTranslates.lean`
(`PegdenSmartRegularity.lap_le_lap_of_nbr`). -/
theorem lap_le_lap_of_nbr' {u v : Site d → ℤ} {x : Site d} (hx : u x = v x)
    (hnb : ∀ i, u (x + unit i) ≤ v (x + unit i) ∧ u (x - unit i) ≤ v (x - unit i)) :
    lap u x ≤ lap v x := by
  simp only [lap, nbrSumZ, hx]
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => add_le_add (hnb i).1 (hnb i).2
  linarith

/-- Copied from `Proofs/Sec7/MainTheoremUExteriorSub.lean` (`ExteriorSub.inner_toE_eq_sum`). -/
theorem inner_toE_eq_sum' (γ : Rd d) (h : Site d) :
    inner ℝ γ (toE h) = ∑ i, γ i * (h i : ℝ) := by
  simp [toE, PiLp.inner_apply, mul_comm]

/-- An integer affine function has zero lattice Laplacian. -/
theorem lap_linear_add_const (k : Site d) (c : ℤ) (x : Site d) :
    lap (fun y => (∑ i, k i * y i) + c) x = 0 := by
  have h1 := PegdenSmartRegularity.lap_add_const (fun y : Site d => ∑ i, k i * y i) c x
  have h2 := PegdenSmartRegularity.lap_of_additive (f := fun y : Site d => ∑ i, k i * y i)
    (fun y z => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]) x
  exact h1.trans h2

/-- **Integer rounding of an affine function**: `μ(y) = ⌊g⌋·y + ⌊c'⌋` is integer affine and within
`(d + 1)|y - z₀| + 1` of `c + g·y`. -/
theorem exists_int_affine (g : Rd d) (c : ℝ) (z0 : Rd d) :
    ∃ μ : Site d → ℤ, (∀ x, lap μ x = 0) ∧
      ∀ y : Site d, |(μ y : ℝ) - (c + inner ℝ g (toE y))| ≤ ((d : ℝ) + 1) * ‖toE y - z0‖ + 1 := by
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = c + inner ℝ (g - toE (latticeRound g)) z0 := ⟨_, rfl⟩
  refine ⟨fun y => (∑ i, latticeRound g i * y i) + ⌊c'⌋, fun x => lap_linear_add_const _ _ x,
    fun y => ?_⟩
  show |((((∑ i, latticeRound g i * y i) + ⌊c'⌋ : ℤ)) : ℝ) - (c + inner ℝ g (toE y))| ≤
    ((d : ℝ) + 1) * ‖toE y - z0‖ + 1
  have hcast : ((((∑ i, latticeRound g i * y i) + ⌊c'⌋ : ℤ)) : ℝ) =
      inner ℝ (toE (latticeRound g)) (toE y) + (⌊c'⌋ : ℝ) := by
    rw [inner_toE_eq_sum']
    push_cast
    simp only [toE_apply]
  have e : ((((∑ i, latticeRound g i * y i) + ⌊c'⌋ : ℤ)) : ℝ) - (c + inner ℝ g (toE y)) =
      inner ℝ (toE (latticeRound g) - g) (toE y - z0) + ((⌊c'⌋ : ℝ) - c') := by
    rw [hcast, inner_sub_left, inner_sub_right, inner_sub_right]
    rw [inner_sub_left] at hc'
    linear_combination hc'
  rw [e]
  have h1 := abs_real_inner_le_norm (toE (latticeRound g) - g) (toE y - z0)
  have h2 := norm_toE_latticeRound_sub_le g
  have h3 : |(⌊c'⌋ : ℝ) - c'| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Int.floor_le c', Int.lt_floor_add_one c']
  have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (toE y - z0))
  calc |inner ℝ (toE (latticeRound g) - g) (toE y - z0) + ((⌊c'⌋ : ℝ) - c')|
      ≤ |inner ℝ (toE (latticeRound g) - g) (toE y - z0)| + |(⌊c'⌋ : ℝ) - c'| := abs_add_le _ _
    _ ≤ ((d : ℝ) + 1) * ‖toE y - z0‖ + 1 := by linarith

/-! ### The competitor `min(Y, v_n)` -/

/-- **Leastness of the single-source odometer against a local competitor.** If `Y` is integer,
`Δ Y + η ≤ 2d - 1` and `Y ≥ 0` on `A ∌ 0`, and `Y ≥ v_n` on the outer boundary of `A`, then
`Y ≥ v_n` on `A`: otherwise `min(Y, v_n)` on `A`, `v_n` elsewhere, is a stabilizing toppling for
`η + n δ_0` smaller than `v_n`. -/
theorem false_of_competitor {η : Site d → ℤ} {n : ℕ}
    (hne : (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty)
    {A : Set (Site d)} (h0 : (0 : Site d) ∉ A) {Y : Site d → ℤ}
    (hY : ∀ x ∈ A, lap Y x + η x ≤ 2 * (d : ℤ) - 1) (hY0 : ∀ x ∈ A, 0 ≤ Y x)
    (hbd : ∀ y ∈ bdry A, singleSourceOdometer η n y ≤ Y y)
    {x₀ : Site d} (hx₀ : x₀ ∈ A) (hlt : Y x₀ < singleSourceOdometer η n x₀) : False := by
  classical
  have hVs := (isLeast_singleSourceOdometer hne).1
  simp only [mem_stabilizing_univ] at hVs
  set Z : Site d → ℤ := fun x =>
    if x ∈ A then min (Y x) (singleSourceOdometer η n x) else singleSourceOdometer η n x
    with hZ
  have hZV : ∀ x, Z x ≤ singleSourceOdometer η n x := fun x => by
    simp only [hZ]
    split_ifs
    · exact min_le_right _ _
    · exact le_rfl
  have hZY : ∀ y ∈ dClosure A, Z y ≤ Y y := by
    intro y hy
    rw [dClosure_eq] at hy
    simp only [hZ]
    split_ifs with hyA
    · exact min_le_left _ _
    · rcases hy with hy | hy
      · exact absurd hy hyA
      · exact hbd y hy
  have hZs : Z ∈ stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ := by
    simp only [mem_stabilizing_univ]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · simp only [hZ]
      split_ifs with hxA
      · exact le_min (hY0 x hxA) (hVs.1 x)
      · exact hVs.1 x
    · by_cases hxA : x ∈ A
      · by_cases hYV : Y x ≤ singleSourceOdometer η n x
        · have hZx : Z x = Y x := by simp only [hZ, if_pos hxA, min_eq_left hYV]
          have hl := lap_le_lap_of_nbr' hZx fun i =>
            ⟨hZY _ (add_unit_mem_dClosure hxA i), hZY _ (sub_unit_mem_dClosure hxA i)⟩
          have hx0 : x ≠ 0 := fun h => h0 (h ▸ hxA)
          have hδ : dirac (0 : Site d) x = 0 := by simp [dirac, hx0]
          rw [hδ, mul_zero, add_zero]
          linarith [hY x hxA]
        · have hZx : Z x = singleSourceOdometer η n x := by
            simp only [hZ, if_pos hxA, min_eq_right (not_le.1 hYV).le]
          have hl := lap_le_lap_of_nbr' hZx fun i => ⟨hZV _, hZV _⟩
          linarith [hVs.2 x]
      · have hZx : Z x = singleSourceOdometer η n x := by simp only [hZ, if_neg hxA]
        have hl := lap_le_lap_of_nbr' hZx fun i => ⟨hZV _, hZV _⟩
        linarith [hVs.2 x]
  have hle : singleSourceOdometer η n x₀ ≤ Z x₀ := singleSourceOdometer_le hZs x₀
  have hZx₀ : Z x₀ ≤ Y x₀ := hZY x₀ (by rw [dClosure_eq]; exact Or.inl hx₀)
  omega

/-! ### A contact point from the `μ*` mass -/

/-- **Contact point in a subset.** If `μ*(A, η, l, M)` exceeds the site bound of Lemma 5.4 times
`|A ∖ I|`, then some stabilizing `X` on `A` has a subgradient of `X - q_l - q_M` (tested on `Ā`) at
a site of `A ∩ I`: the sites of `A ∖ I` carry at most that much subgradient volume. -/
theorem exists_contact_of_lt_muStar (hd : 1 ≤ d) {A I : Set (Site d)} (hA : A.Finite)
    {η : Site d → ℤ} {ηmin : ℤ} (hη : ∀ x ∈ A, ηmin ≤ η x) (l : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hlt : ENNReal.ofReal ((max ((2 * (d : ℝ) - 1) - (ηmin : ℝ) - l - M.trace) 0 / d) ^ d *
        ((A \ I).ncard : ℝ)) < muStar A η l M) :
    ∃ X ∈ stabilizing η A, ∃ x ∈ A ∩ I, ∃ p : Rd d,
      p ∈ subGrad (fun y => (X y : ℝ) - (qlZ l y + qMZ M y)) x A := by
  by_contra hcon
  have h : ∀ X ∈ stabilizing η A, ∀ x ∈ A ∩ I, ∀ p : Rd d,
      p ∉ subGrad (fun y => (X y : ℝ) - (qlZ l y + qMZ M y)) x A :=
    fun X hX x hx p hp => hcon ⟨X, hX, x, hx, p, hp⟩
  have hle : muStar A η l M ≤ ENNReal.ofReal
      ((max ((2 * (d : ℝ) - 1) - (ηmin : ℝ) - l - M.trace) 0 / d) ^ d *
        ((A \ I).ncard : ℝ)) := by
    refine iSup₂_le fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := mem_perturbedSuper.1 hw
    have hsub : subGradSet (fun x => (v x : ℝ) - (qlZ l x + qMZ M x)) A ⊆
        ⋃ x ∈ A \ I, subGrad (fun x => (v x : ℝ) - (qlZ l x + qMZ M x)) x A := by
      intro p hp
      simp only [subGradSet, Set.mem_iUnion] at hp ⊢
      obtain ⟨x, hxA, hpx⟩ := hp
      exact ⟨x, ⟨hxA, fun hxI => h v hv x ⟨hxA, hxI⟩ p hpx⟩, hpx⟩
    refine (measure_mono hsub).trans ?_
    refine volume_biUnion_le_ncard (hA.subset Set.sdiff_subset) _ (by positivity)
      fun x hx => (supGradVolumeLe d A _ x hx.1).2.trans ?_
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ d)
    refine div_le_div_of_nonneg_right (max_le_max_right _ ?_) (Nat.cast_nonneg d)
    rw [lapR_sub', lapR_intCast, lapQuadratic d hd]
    have h1 := hv.2 x hx.1
    have h2 := hη x hx.1
    have h3 : (lap v x : ℝ) ≤ 2 * (d : ℝ) - 1 - (ηmin : ℝ) := by
      have : lap v x ≤ 2 * (d : ℤ) - 1 - ηmin := by omega
      exact_mod_cast this
    linarith
  exact absurd hlt (not_lt.2 hle)

/-! ### The comparison at a contact point -/

/-- **The comparison of route_star §4.3** (leastness form). Let `X` be stabilizing on `A ∌ 0` with
a subgradient `p` of `X - q` at `x_c ∈ A`, and split `q - T = G + (c₀ + g·y)` on `Ā`, where `T` is
within `e` of the odometer `v_n` on `Ā`. If `G ≥ 0` on `Ā`, `G(x_c) ≤ γ₊`, `G ≥ γ₋` on the outer
boundary, `|y - z₀| ≤ D` on `Ā`, the gap `γ₋ - γ₊` exceeds `2e + 2((d + 1)D + 1) + 1` and `v_n`
exceeds `γ₊` plus the same errors on `A`, then `X` minus an integer affine function minus an integer
constant is a competitor contradicting `false_of_competitor`. -/
theorem false_of_contact {η : Site d → ℤ} {n : ℕ}
    (hne : (stabilizing (fun x => η x + (n : ℤ) * dirac 0 x) Set.univ).Nonempty)
    {A : Set (Site d)} (h0 : (0 : Site d) ∉ A) {X : Site d → ℤ} (hX : X ∈ stabilizing η A)
    {q : Site d → ℝ} {xc : Site d} (hxc : xc ∈ A) {p : Rd d}
    (hp : p ∈ subGrad (fun y => (X y : ℝ) - q y) xc A)
    {T G : Site d → ℝ} {g z0 : Rd d} {c₀ e γm γp D : ℝ}
    (hid : ∀ y ∈ dClosure A, q y - T y = G y + (c₀ + inner ℝ g (toE y)))
    (happ : ∀ y ∈ dClosure A, |(singleSourceOdometer η n y : ℝ) - T y| ≤ e)
    (hG0 : ∀ y ∈ dClosure A, 0 ≤ G y) (hGb : ∀ y ∈ bdry A, γm ≤ G y) (hGc : G xc ≤ γp)
    (hD : ∀ y ∈ dClosure A, ‖toE y - z0‖ ≤ D)
    (hgap : γp + 2 * e + 2 * (((d : ℝ) + 1) * D + 1) + 1 ≤ γm)
    (hpos : ∀ y ∈ A, γp + 2 * e + 2 * (((d : ℝ) + 1) * D + 1) + 1 ≤
      (singleSourceOdometer η n y : ℝ)) : False := by
  have hxcl : xc ∈ dClosure A := by rw [dClosure_eq]; exact Or.inl hxc
  obtain ⟨μ, hμ, herr⟩ := exists_int_affine (-(g + p))
    (-(c₀ + ((X xc : ℝ) - q xc) - inner ℝ p (toE xc))) z0
  -- `-μ` approximates `ℓ'(y) = c₀ + g·y + w₀ + p·(y - x_c)`, `w₀ = X(x_c) - q(x_c)`
  have hℓ : ∀ y : Site d, -(c₀ + ((X xc : ℝ) - q xc) - inner ℝ p (toE xc)) +
      inner ℝ (-(g + p)) (toE y) =
      -((c₀ + inner ℝ g (toE y)) + ((X xc : ℝ) - q xc) + inner ℝ p (toE y - toE xc)) := by
    intro y
    rw [inner_neg_left, inner_add_left, inner_sub_right]
    ring
  have hE : ∀ y ∈ dClosure A, ((d : ℝ) + 1) * ‖toE y - z0‖ + 1 ≤ ((d : ℝ) + 1) * D + 1 := by
    intro y hy
    have := mul_le_mul_of_nonneg_left (hD y hy) (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)
    linarith
  -- `X + μ - v_n ≥ G - errors` on `Ā`, `≤ G(x_c) + errors` at `x_c`
  have hlow : ∀ y ∈ dClosure A, G y - (((d : ℝ) + 1) * D + 1) - e ≤
      (X y : ℝ) + μ y - singleSourceOdometer η n y := by
    intro y hy
    have h1 : (X xc : ℝ) - q xc + inner ℝ p (toE y - toE xc) ≤ (X y : ℝ) - q y := hp y hy
    have h2 := hid y hy
    have h3 := abs_le.1 (happ y hy)
    have h4 := abs_le.1 (herr y)
    have h5 := hE y hy
    have h6 := hℓ y
    linarith [h4.1, h4.2, h3.1, h3.2]
  have hup : (X xc : ℝ) + μ xc - singleSourceOdometer η n xc ≤
      G xc + (((d : ℝ) + 1) * D + 1) + e := by
    have h2 := hid xc hxcl
    have h3 := abs_le.1 (happ xc hxcl)
    have h4 := abs_le.1 (herr xc)
    have h5 := hE xc hxcl
    have h6 := hℓ xc
    have h7 : inner ℝ p (toE xc - toE xc) = 0 := by rw [sub_self, inner_zero_right]
    linarith [h4.1, h4.2, h3.1, h3.2]
  -- the competitor `Y = X + μ - k₀`
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, k₀ = X xc + μ xc - singleSourceOdometer η n xc + 1 := ⟨_, rfl⟩
  have hk₀r : (k₀ : ℝ) = ((X xc + μ xc - singleSourceOdometer η n xc + 1 : ℤ) : ℝ) := by
    rw [hk₀]
  push_cast at hk₀r
  refine false_of_competitor hne h0 (Y := fun y => (X y + μ y) + -k₀) ?_ ?_ ?_ hxc ?_
  · intro x hx
    have h3 : lap (fun y => (X y + μ y) + -k₀) x = lap X x := by
      have h := (PegdenSmartRegularity.lap_add_const (fun y => X y + μ y) (-k₀) x).trans
        (PegdenSmartRegularity.lap_fun_add X μ x)
      rw [hμ x, add_zero] at h
      exact h
    rw [h3]
    exact hX.2 x hx
  · intro y hy
    show 0 ≤ X y + μ y + -k₀
    have hyc : y ∈ dClosure A := by rw [dClosure_eq]; exact Or.inl hy
    have h1 := hlow y hyc
    have h2 := hG0 y hyc
    have h3 := hpos y hy
    have h4 : (0 : ℝ) ≤ ((X y + μ y + -k₀ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h4
  · intro y hy
    show singleSourceOdometer η n y ≤ X y + μ y + -k₀
    have hyc : y ∈ dClosure A := by rw [dClosure_eq]; exact Or.inr hy
    have h1 := hlow y hyc
    have h2 := hGb y hy
    have h4 : ((singleSourceOdometer η n y : ℤ) : ℝ) ≤ ((X y + μ y + -k₀ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  · show X xc + μ xc + -k₀ < singleSourceOdometer η n xc
    omega

end SingleSourceFstar

end RandomSandpile

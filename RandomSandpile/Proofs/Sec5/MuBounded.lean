import RandomSandpile.Steps.Sec5.MuBounded
import RandomSandpile.Proofs.Sec3.LeastAction

/-!
# Proof of Lemma 5.4 (bounds on `μ` and `μ*`)

Proofs of the three steps of `RandomSandpile/Steps/Sec5/MuBounded.lean`, of the support lemmas on
every finite set (`mu_le_ncard`, `muStar_le_ncard`), and of `RandomSandpile.MuBoundedStmt`
(Lemma 5.4, `paper/random_piles-corrected.tex`).

* `legal_lap_lower`: a legal toppling function satisfies `Δ_{ℤ^d} u + η ≥ min(0, η)`
  everywhere: a site that never topples only receives chips, and a site that toppled had at least
  `2d` chips before its last toppling and only receives chips afterwards.
  `locLegalLapLower` (Step 1) deduces the bound in `A` for `u = w + û ∈ 𝓛(η, A)`, since
  `Δ_{ℤ^d} w ≥ 0` in `A`.
* `lapQuadratic` (Step 2): `Δ_i q_l = l / d` and `Δ_i q_M = M_{ii}` on the lattice.
* `supGradVolumeLe` (Step 3): the supergradient (resp. subgradient) set at `x ∈ A` lies in the box
  `∏_i [w(x + e_i) - w(x), w(x) - w(x - e_i)]` (resp. `∏_i [w(x) - w(x - e_i), w(x + e_i) - w(x)]`),
  whose Lebesgue measure is bounded by the arithmetic-geometric mean inequality.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal Matrix

namespace RandomSandpile

variable {d : ℕ}

/-! ### Step 1: the legality lower bound -/

theorem lap_add' (u v : Site d → ℤ) (x : Site d) : lap (u + v) x = lap u x + lap v x := by
  simp only [lap, nbrSumZ, Pi.add_apply, Finset.sum_add_distrib]
  ring

/-- A unit toppling at `z` lowers the Laplacian by at most `2d` at `z` and nowhere else. -/
theorem lap_dirac_ge (z x : Site d) : -(2 * (d : ℤ)) * dirac z x ≤ lap (dirac z) x := by
  have h : 0 ≤ nbrSumZ (dirac z) x :=
    Finset.sum_nonneg fun i _ => add_nonneg (by unfold dirac; split_ifs <;> norm_num)
      (by unfold dirac; split_ifs <;> norm_num)
  rw [lap]
  linarith

/-- **Tex 238.** A legal toppling function `u` for `η` in `A` satisfies
`Δ_{ℤ^d} u + η ≥ min(0, η)` at every site. -/
theorem legal_lap_lower {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (hu : IsLegal η A u) (y : Site d) : min 0 (η y) ≤ lap u y + η y := by
  revert y
  refine IsLegal.induction (fun u => ∀ y, min 0 (η y) ≤ lap u y + η y) ?_ ?_ hu
  · intro y
    have : lap (0 : Site d → ℤ) y = 0 := by simp [lap, nbrSumZ]
    rw [this, zero_add]
    exact min_le_right _ _
  · intro u x _ hP _ hx y
    have h1 := lap_dirac_ge x y
    rw [lap_add']
    by_cases hy : y = x
    · subst hy
      rw [dirac_self] at h1
      have := min_le_left 0 (η y)
      linarith
    · rw [dirac_of_ne hy] at h1
      have := hP y
      linarith

/-- **Step 1** (683). -/
theorem locLegalLapLower : LocLegalLapLowerStmt := by
  intro d η A u hu x hx
  obtain ⟨w, uh, hw, -, rfl, hw0, -, hleg⟩ := hu
  have h1 := legal_lap_lower hleg x
  have h2 : 0 ≤ lap w x := by
    rw [lap, hw0 x hx, mul_zero, sub_zero]
    exact Finset.sum_nonneg fun i _ => add_nonneg (hw.1 _) (hw.1 _)
  rw [lap_add']
  have : min 0 (η x) ≤ min 0 (lap w x + η x) := min_le_min_left _ (by linarith)
  linarith

/-! ### Step 2: the Laplacian of the parabola -/

theorem ofLp_toE_add_unit (x : Site d) (i : Fin d) :
    WithLp.ofLp (toE (x + unit i)) = WithLp.ofLp (toE x) + Pi.single i (1 : ℝ) := by
  funext j
  by_cases h : j = i
  · subst h; simp [toE, unit]
  · simp [toE, unit, Pi.single_apply, h]

theorem ofLp_toE_sub_unit (x : Site d) (i : Fin d) :
    WithLp.ofLp (toE (x - unit i)) = WithLp.ofLp (toE x) - Pi.single i (1 : ℝ) := by
  funext j
  by_cases h : j = i
  · subst h; simp [toE, unit]
  · simp [toE, unit, Pi.single_apply, h]

theorem quad_secondDiff (N : Matrix (Fin d) (Fin d) ℝ) (g e : Fin d → ℝ) :
    (g + e) ⬝ᵥ N *ᵥ (g + e) + (g - e) ⬝ᵥ N *ᵥ (g - e) - 2 * (g ⬝ᵥ N *ᵥ g) =
      2 * (e ⬝ᵥ N *ᵥ e) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, add_dotProduct,
    dotProduct_sub, sub_dotProduct]
  ring

theorem single_quad (N : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    Pi.single i (1 : ℝ) ⬝ᵥ N *ᵥ Pi.single i 1 = N i i := by
  rw [single_dotProduct, Matrix.mulVec_single]
  simp

theorem norm_toE_sq (x : Site d) :
    ‖toE x‖ ^ 2 = WithLp.ofLp (toE x) ⬝ᵥ (1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ WithLp.ofLp (toE x) := by
  rw [EuclideanSpace.norm_sq_eq, Matrix.one_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [toE, sq]

/-- `Δ_i q_M = M_{ii}` on the lattice. -/
theorem secondDiff_qMZ (M : Matrix (Fin d) (Fin d) ℝ) (x : Site d) (i : Fin d) :
    secondDiff i (qMZ M) x = M i i := by
  have h := quad_secondDiff M (WithLp.ofLp (toE x)) (Pi.single i (1 : ℝ))
  rw [single_quad] at h
  simp only [secondDiff, qMZ, qM, ofLp_toE_add_unit, ofLp_toE_sub_unit]
  linarith

/-- `Δ_i q_l = l / d` on the lattice. -/
theorem secondDiff_qlZ (hd : 1 ≤ d) (l : ℝ) (x : Site d) (i : Fin d) :
    secondDiff i (qlZ l) x = l / d := by
  have h := quad_secondDiff 1 (WithLp.ofLp (toE x)) (Pi.single i (1 : ℝ))
  rw [single_quad, Matrix.one_apply_eq] at h
  have hd' : (d : ℝ) ≠ 0 := by positivity
  simp only [secondDiff, qlZ, ql, norm_toE_sq, ofLp_toE_add_unit, ofLp_toE_sub_unit]
  field_simp
  linear_combination l * h

/-- **Step 2**. -/
theorem lapQuadratic : LapQuadraticStmt := by
  intro d hd l M x
  have hd' : (d : ℝ) ≠ 0 := by positivity
  have hsum : ∀ i, secondDiff i (fun y => qlZ l y + qMZ M y) x = l / d + M i i := fun i => by
    rw [← secondDiff_qlZ hd l x i, ← secondDiff_qMZ M x i]
    simp only [secondDiff]; ring
  rw [lapR_eq_sum_secondDiff, Finset.sum_congr rfl fun i _ => hsum i, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.trace]
  simp only [Matrix.diag]
  field_simp

/-! ### Step 3: the discrete Monge-Ampère bound at one site -/

/-- **AM-GM**, power form: `∏_i z_i ≤ ((∑_i z_i) / d)^d` for `z : Fin d → ℝ≥0`. -/
theorem prod_le_sum_div_pow (z : Fin d → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / d) ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) z (fun _ _ => zero_le_one)
    (by simp [hd]) (fun i _ => hz i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul] at h
  calc ∏ i, z i = ((∏ i, z i) ^ ((d : ℝ)⁻¹)) ^ d :=
        (Real.rpow_inv_natCast_pow (Finset.prod_nonneg fun i _ => hz i) hd.ne').symm
    _ ≤ ((∑ i, z i) / d) ^ d :=
        pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg fun i _ => hz i) _) h d

/-- A set of `ℝ^d` inside the box `∏_i [a_i, b_i]` with `∑_i (b_i - a_i) ≤ c` has measure at most
`d^{-d} (c⁺)^d`. -/
theorem volume_le_of_subset_box (S : Set (Rd d)) (a b : Fin d → ℝ)
    (hS : ∀ p ∈ S, ∀ i, a i ≤ p i ∧ p i ≤ b i) {c : ℝ} (hc : ∑ i, (b i - a i) ≤ c) :
    volume S ≤ ENNReal.ofReal ((max c 0 / d) ^ d) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  have hab : ∀ i, 0 ≤ b i - a i := fun i => by
    have := hS p hp i; linarith
  have hsub : S ⊆ WithLp.ofLp ⁻¹' Set.Icc a b := fun q hq =>
    ⟨fun i => (hS q hq i).1, fun i => (hS q hq i).2⟩
  refine (measure_mono hsub).trans ?_
  rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi, ← ENNReal.ofReal_prod_of_nonneg fun i _ => hab i]
  refine ENNReal.ofReal_le_ofReal ((prod_le_sum_div_pow _ hab).trans ?_)
  refine pow_le_pow_left₀ (div_nonneg (Finset.sum_nonneg fun i _ => hab i) (Nat.cast_nonneg d)) ?_ d
  exact div_le_div_of_nonneg_right (hc.trans (le_max_left _ _)) (Nat.cast_nonneg d)

theorem add_unit_mem_dClosure {A : Set (Site d)} {x : Site d} (hx : x ∈ A) (i : Fin d) :
    x + unit i ∈ dClosure A := by
  rw [dClosure_eq]
  by_cases h : x + unit i ∈ A
  · exact Or.inl h
  · exact Or.inr (mem_bdry.2 ⟨h, x, hx, ⟨i, Or.inr rfl⟩⟩)

theorem sub_unit_mem_dClosure {A : Set (Site d)} {x : Site d} (hx : x ∈ A) (i : Fin d) :
    x - unit i ∈ dClosure A := by
  rw [dClosure_eq]
  by_cases h : x - unit i ∈ A
  · exact Or.inl h
  · exact Or.inr (mem_bdry.2 ⟨h, x, hx, ⟨i, Or.inl (by abel)⟩⟩)

theorem inner_toE_add_unit (p : Rd d) (x : Site d) (i : Fin d) :
    inner ℝ p (toE (x + unit i) - toE x) = p i := by
  have : toE (x + unit i) - toE x = WithLp.toLp 2 (Pi.single i (1 : ℝ)) := by
    ext1 j
    by_cases h : j = i
    · subst h; simp [toE, unit]
    · simp [toE, unit, Pi.single_apply, h]
  rw [this, PiLp.inner_apply]
  simp [Pi.single_apply]

theorem inner_toE_sub_unit (p : Rd d) (x : Site d) (i : Fin d) :
    inner ℝ p (toE (x - unit i) - toE x) = -p i := by
  have : toE (x - unit i) - toE x = -WithLp.toLp 2 (Pi.single i (1 : ℝ)) := by
    ext1 j
    by_cases h : j = i
    · subst h; simp [toE, unit]
    · simp [toE, unit, Pi.single_apply, h]
  rw [this, inner_neg_right, PiLp.inner_apply]
  simp [Pi.single_apply]

/-- **Step 3**. -/
theorem supGradVolumeLe : SupGradVolumeLeStmt := by
  intro d A w x hx
  constructor
  · refine volume_le_of_subset_box _ (fun i => w (x + unit i) - w x) (fun i => w x - w (x - unit i))
      (fun p hp i => ?_) (le_of_eq ?_)
    · have h1 := hp _ (add_unit_mem_dClosure hx i)
      have h2 := hp _ (sub_unit_mem_dClosure hx i)
      rw [inner_toE_add_unit] at h1
      rw [inner_toE_sub_unit] at h2
      constructor <;> linarith
    · rw [lapR_eq_sum_secondDiff, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [secondDiff]; ring
  · refine volume_le_of_subset_box _ (fun i => w x - w (x - unit i)) (fun i => w (x + unit i) - w x)
      (fun p hp i => ?_) (le_of_eq ?_)
    · have h1 := hp _ (add_unit_mem_dClosure hx i)
      have h2 := hp _ (sub_unit_mem_dClosure hx i)
      rw [inner_toE_add_unit] at h1
      rw [inner_toE_sub_unit] at h2
      constructor <;> linarith
    · rw [lapR_eq_sum_secondDiff]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [secondDiff]; ring

/-! ### Lemma 5.4 and the support lemmas -/

/-- **Support lemma for `μ`**: for `d ≥ 1`, a finite `A ⊂ ℤ^d` and `η ≤ η_max` in
`A`, `μ(A, η, l, M) ≤ d^{-d} ((max(η_max, 0) + l + Tr(M))⁺)^d |A|`. -/
theorem mu_le_ncard (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) {η : Site d → ℤ} {ηmax : ℤ}
    (hη : ∀ x ∈ A, η x ≤ ηmax) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    mu A η l M ≤ ENNReal.ofReal
      ((max (((max ηmax 0 : ℤ) : ℝ) + l + M.trace) 0 / d) ^ d * (A.ncard : ℝ)) :=
  mu_le_of_steps locLegalLapLower lapQuadratic supGradVolumeLe hd hA hη l M

/-- **Support lemma for `μ*`**: for `d ≥ 1`, a finite `A ⊂ ℤ^d` and `η ≥ η_min` in
`A`, `μ*(A, η, l, M) ≤ d^{-d} (((2d - 1) - η_min - l - Tr(M))⁺)^d |A|`. -/
theorem muStar_le_ncard (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) {η : Site d → ℤ}
    {ηmin : ℤ} (hη : ∀ x ∈ A, ηmin ≤ η x) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStar A η l M ≤ ENNReal.ofReal
      ((max ((2 * (d : ℝ) - 1) - (ηmin : ℝ) - l - M.trace) 0 / d) ^ d * (A.ncard : ℝ)) :=
  muStar_le_of_steps lapQuadratic supGradVolumeLe hd hA hη l M

/-- **Lemma 5.4** (mu-is-bounded, with the drafted correction of the vanishing range
of `μ`). -/
theorem muBounded : MuBoundedStmt :=
  muBounded_of_steps locLegalLapLower lapQuadratic supGradVolumeLe

end RandomSandpile

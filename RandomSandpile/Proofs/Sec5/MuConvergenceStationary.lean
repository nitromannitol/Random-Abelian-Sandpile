import RandomSandpile.Steps.Sec5.MuConvergence

/-!
# Lemma 5.5, Step 2: stationarity of `μ` and `μ*` under translation

Proof of `MuStationaryStmt`: `μ(A, T_y η, l, M) = μ(y + A, η, l, M)` and the same for `μ*`.

* The translate `τ_y u(z) = u(z - y)` commutes with the Laplacian (`lap_transl`) and maps
  `∂A`, `Ā` to `∂(y + A)`, `y + Ā` (`mem_bdry_vadd`, `mem_dClosure_vadd`), hence maps legal,
  locally legal and stabilizing topplings for `T_y η` in `A` to those for `η` in `y + A`
  (`isLegal_transl`, `transl_mem_locLegal`, `transl_mem_stabilizing`).
* The parabola changes by an affine function: `(q_l + q_M)(z - y) = (q_l + q_M)(z) + p₀ · z + c`
  (`parabola_transl`, no symmetry of `M` needed), so the supergradient (resp. subgradient) set of
  the translated perturbed subsolution is a translate of the original one (`supGradSet_vadd`,
  `subGradSet_vadd`), with the same Lebesgue measure.
* This gives `μ(A, T_y η) ≤ μ(y + A, η)`; the reverse inequality is the same one for `-y`.
-/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal Pointwise Matrix
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- The translate `τ_y u (z) = u (z - y)` of a function on the lattice. -/
def transl {α : Type*} (y : Site d) (u : Site d → α) : Site d → α := fun z => u (z - y)

@[simp] theorem transl_apply {α : Type*} (y : Site d) (u : Site d → α) (z : Site d) :
    transl y u z = u (z - y) := rfl

theorem lap_transl (y : Site d) (u : Site d → ℤ) (x : Site d) :
    lap (transl y u) x = lap u (x - y) := by
  have h1 : ∀ i : Fin d, x + unit i - y = x - y + unit i := fun i => by abel
  have h2 : ∀ i : Fin d, x - unit i - y = x - y - unit i := fun i => by abel
  simp only [lap, nbrSumZ, transl_apply, h1, h2]

theorem dirac_transl (a y : Site d) : transl y (dirac a) = dirac (a + y) := by
  funext z
  simp only [transl_apply, dirac, sub_eq_iff_eq_add]

theorem mem_vadd_set_sub {y z : Site d} {A : Set (Site d)} : z ∈ y +ᵥ A ↔ z - y ∈ A := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]

theorem adj_sub_sub_iff {x x' y : Site d} : Adj (x - y) (x' - y) ↔ Adj x x' := by
  simp only [adj_iff_sum_abs, Pi.sub_apply, sub_sub_sub_cancel_right]

theorem mem_bdry_vadd {y z : Site d} {A : Set (Site d)} : z ∈ bdry (y +ᵥ A) ↔ z - y ∈ bdry A := by
  simp only [mem_bdry, mem_vadd_set_sub]
  refine and_congr Iff.rfl ⟨fun ⟨x, hx, hadj⟩ => ⟨x - y, hx, adj_sub_sub_iff.2 hadj⟩,
    fun ⟨x, hx, hadj⟩ => ⟨x + y, by simpa using hx, ?_⟩⟩
  rw [← adj_sub_sub_iff (y := y)]
  simpa using hadj

theorem mem_dClosure_vadd {y z : Site d} {A : Set (Site d)} :
    z ∈ dClosure (y +ᵥ A) ↔ z - y ∈ dClosure A := by
  simp only [dClosure_eq, Set.mem_union, mem_vadd_set_sub, mem_bdry_vadd]


theorem isTopplingFn_transl {A : Set (Site d)} {u : Site d → ℤ} (y : Site d)
    (hu : IsTopplingFn A u) : IsTopplingFn (y +ᵥ A) (transl y u) :=
  ⟨fun _ => hu.1 _, fun _ hz => hu.2 _ (fun h => hz (mem_dClosure_vadd.2 h))⟩

theorem isLegal_transl {ξ : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ} (y : Site d)
    (hu : IsLegal ξ A u) : IsLegal (transl y ξ) (y +ᵥ A) (transl y u) := by
  refine IsLegal.induction (η := ξ) (A := A) (fun u => IsLegal (transl y ξ) (y +ᵥ A) (transl y u))
    ?_ ?_ hu
  · exact IsLegal.zero _ _
  · intro u x _ hP hx hlap
    have h : transl y (u + dirac x) = transl y u + dirac (x + y) := by
      rw [← dirac_transl]; rfl
    rw [h]
    refine IsLegal.snoc hP (mem_vadd_set_sub.2 (by simpa using hx)) ?_
    rw [lap_transl]
    simpa using hlap

theorem transl_mem_locLegal {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ} (y : Site d)
    (hu : u ∈ locLegal (shift y η) A) : transl y u ∈ locLegal η (y +ᵥ A) := by
  obtain ⟨w, uh, hw, huh, rfl, hw0, huh0, hleg⟩ := hu
  refine ⟨transl y w, transl y uh, isTopplingFn_transl y hw, isTopplingFn_transl y huh, rfl,
    fun x hx => hw0 _ (mem_vadd_set_sub.1 hx), fun x hx => huh0 _ (mem_bdry_vadd.1 hx), ?_⟩
  have h := isLegal_transl y hleg
  convert h using 2
  simp [lap_transl, transl]

theorem transl_mem_stabilizing {η : Site d → ℤ} {A : Set (Site d)} {v : Site d → ℤ} (y : Site d)
    (hv : v ∈ stabilizing (shift y η) A) : transl y v ∈ stabilizing η (y +ᵥ A) := by
  refine ⟨isTopplingFn_transl y hv.1, fun x hx => ?_⟩
  have h := hv.2 _ (mem_vadd_set_sub.1 hx)
  rw [lap_transl]
  simpa using h


/-! ### The parabola changes by an affine function under translation -/

theorem toE_add (z y : Site d) : toE (z + y) = toE z + toE y := by
  ext i
  simp

theorem toE_sub (z y : Site d) : toE (z - y) = toE z - toE y := by
  ext i
  simp

theorem ql_add (l : ℝ) (e f : Rd d) :
    ql l (e + f) = ql l e + inner ℝ ((l / d) • f) e + ql l f := by
  unfold ql
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_comm]
  ring

theorem qM_add (M : Matrix (Fin d) (Fin d) ℝ) (e f : Rd d) :
    qM M (e + f) = qM M e +
      inner ℝ (WithLp.toLp 2 ((1 / 2 : ℝ) • (M *ᵥ WithLp.ofLp f + Mᵀ *ᵥ WithLp.ofLp f))) e +
      qM M f := by
  have h : WithLp.ofLp f ⬝ᵥ M *ᵥ WithLp.ofLp e = (Mᵀ *ᵥ WithLp.ofLp f) ⬝ᵥ WithLp.ofLp e := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [qM, WithLp.ofLp_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    star_trivial, dotProduct_smul, smul_eq_mul]
  rw [h, dotProduct_comm (WithLp.ofLp e) (Mᵀ *ᵥ WithLp.ofLp f)]
  ring

theorem parabola_transl (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (y : Site d) :
    ∃ (p₀ : Rd d) (c : ℝ), ∀ z : Site d,
      qlZ l (z + y) + qMZ M (z + y) = (qlZ l z + qMZ M z) + inner ℝ p₀ (toE z) + c := by
  refine ⟨(l / d) • toE y + WithLp.toLp 2 ((1 / 2 : ℝ) •
    (M *ᵥ WithLp.ofLp (toE y) + Mᵀ *ᵥ WithLp.ofLp (toE y))), qlZ l y + qMZ M y, fun z => ?_⟩
  simp only [qlZ, qMZ, toE_add, ql_add, qM_add, inner_add_left]
  ring


/-! ### Translation of supergradient and subgradient sets -/

theorem mem_supGrad_vadd {w w' : Site d → ℝ} {y x : Site d} {A : Set (Site d)} {b : Rd d}
    {c : ℝ} (hw : ∀ z, w' (z + y) = w z + inner ℝ b (toE z) + c) {p : Rd d} :
    p ∈ supGrad w' (x + y) (y +ᵥ A) ↔ p + -b ∈ supGrad w x A := by
  have hE : ∀ z, toE (z + y) - toE (x + y) = toE z - toE x := fun z => by
    rw [toE_add, toE_add]; abel
  constructor
  · intro h z hz
    have h1 := h (z + y) (mem_dClosure_vadd.2 (by simpa using hz))
    rw [hw, hw, hE] at h1
    rw [inner_add_left, inner_neg_left]
    have e1 := inner_sub_right (𝕜 := ℝ) b (toE z) (toE x)
    linarith
  · intro h y' hy'
    obtain ⟨z, rfl⟩ : ∃ z, y' = z + y := ⟨y' - y, (sub_add_cancel _ _).symm⟩
    have h1 := h z (by simpa using mem_dClosure_vadd.1 hy')
    rw [hw, hw, hE]
    rw [inner_add_left, inner_neg_left] at h1
    have e1 := inner_sub_right (𝕜 := ℝ) b (toE z) (toE x)
    linarith

theorem mem_subGrad_vadd {w w' : Site d → ℝ} {y x : Site d} {A : Set (Site d)} {b : Rd d}
    {c : ℝ} (hw : ∀ z, w' (z + y) = w z + inner ℝ b (toE z) + c) {p : Rd d} :
    p ∈ subGrad w' (x + y) (y +ᵥ A) ↔ p + -b ∈ subGrad w x A := by
  have hE : ∀ z, toE (z + y) - toE (x + y) = toE z - toE x := fun z => by
    rw [toE_add, toE_add]; abel
  constructor
  · intro h z hz
    have h1 := h (z + y) (mem_dClosure_vadd.2 (by simpa using hz))
    rw [hw, hw, hE] at h1
    rw [inner_add_left, inner_neg_left]
    have e1 := inner_sub_right (𝕜 := ℝ) b (toE z) (toE x)
    linarith
  · intro h y' hy'
    obtain ⟨z, rfl⟩ : ∃ z, y' = z + y := ⟨y' - y, (sub_add_cancel _ _).symm⟩
    have h1 := h z (by simpa using mem_dClosure_vadd.1 hy')
    rw [hw, hw, hE]
    rw [inner_add_left, inner_neg_left] at h1
    have e1 := inner_sub_right (𝕜 := ℝ) b (toE z) (toE x)
    linarith

theorem supGradSet_vadd {w w' : Site d → ℝ} {y : Site d} {A : Set (Site d)} {b : Rd d} {c : ℝ}
    (hw : ∀ z, w' (z + y) = w z + inner ℝ b (toE z) + c) :
    supGradSet w' (y +ᵥ A) = (fun p => p + -b) ⁻¹' supGradSet w A := by
  ext p
  simp only [supGradSet, Set.mem_iUnion, Set.mem_preimage, exists_prop]
  constructor
  · rintro ⟨x', hx', h⟩
    obtain ⟨x, rfl⟩ : ∃ x, x' = x + y := ⟨x' - y, (sub_add_cancel _ _).symm⟩
    exact ⟨x, by simpa [mem_vadd_set_sub] using hx', (mem_supGrad_vadd hw).1 h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x + y, mem_vadd_set_sub.2 (by simpa using hx), (mem_supGrad_vadd hw).2 h⟩

theorem subGradSet_vadd {w w' : Site d → ℝ} {y : Site d} {A : Set (Site d)} {b : Rd d} {c : ℝ}
    (hw : ∀ z, w' (z + y) = w z + inner ℝ b (toE z) + c) :
    subGradSet w' (y +ᵥ A) = (fun p => p + -b) ⁻¹' subGradSet w A := by
  ext p
  simp only [subGradSet, Set.mem_iUnion, Set.mem_preimage, exists_prop]
  constructor
  · rintro ⟨x', hx', h⟩
    obtain ⟨x, rfl⟩ : ∃ x, x' = x + y := ⟨x' - y, (sub_add_cancel _ _).symm⟩
    exact ⟨x, by simpa [mem_vadd_set_sub] using hx', (mem_subGrad_vadd hw).1 h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x + y, mem_vadd_set_sub.2 (by simpa using hx), (mem_subGrad_vadd hw).2 h⟩

theorem volume_supGradSet_vadd {w w' : Site d → ℝ} {y : Site d} {A : Set (Site d)} {b : Rd d}
    {c : ℝ} (hw : ∀ z, w' (z + y) = w z + inner ℝ b (toE z) + c) :
    volume (supGradSet w' (y +ᵥ A)) = volume (supGradSet w A) := by
  rw [supGradSet_vadd hw]
  exact measure_preimage_add_right _ _ _

theorem volume_subGradSet_vadd {w w' : Site d → ℝ} {y : Site d} {A : Set (Site d)} {b : Rd d}
    {c : ℝ} (hw : ∀ z, w' (z + y) = w z + inner ℝ b (toE z) + c) :
    volume (subGradSet w' (y +ᵥ A)) = volume (subGradSet w A) := by
  rw [subGradSet_vadd hw]
  exact measure_preimage_add_right _ _ _


/-! ### Stationarity -/

theorem mu_shift_le (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (y : Site d)
    (A : Set (Site d)) : mu A (shift y η) l M ≤ mu (y +ᵥ A) η l M := by
  refine iSup₂_le fun w hw => ?_
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.1 hw
  obtain ⟨p₀, c, hp⟩ := parabola_transl l M y
  have hmem : (fun z => ((transl y u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)) ∈ perturbedSub (y +ᵥ A) η l M :=
    mem_perturbedSub.2 ⟨_, transl_mem_locLegal y hu, rfl⟩
  have hw' : ∀ z, (fun z => ((transl y u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)) (z + y) =
      (fun x => (u x : ℝ) - (qlZ l x + qMZ M x)) z + inner ℝ (-p₀) (toE z) + (-c) := by
    intro z
    simp only [transl_apply, add_sub_cancel_right, inner_neg_left, hp z]
    ring
  rw [← volume_supGradSet_vadd (w := fun x => ((u x : ℤ) : ℝ) - (qlZ l x + qMZ M x))
    (w' := fun z => ((transl y u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)) (y := y) hw']
  exact le_iSup₂_of_le _ hmem le_rfl

theorem muStar_shift_le (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (y : Site d)
    (A : Set (Site d)) : muStar A (shift y η) l M ≤ muStar (y +ᵥ A) η l M := by
  refine iSup₂_le fun w hw => ?_
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSuper.1 hw
  obtain ⟨p₀, c, hp⟩ := parabola_transl l M y
  have hmem : (fun z => ((transl y u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)) ∈
      perturbedSuper (y +ᵥ A) η l M :=
    mem_perturbedSuper.2 ⟨_, transl_mem_stabilizing y hu, rfl⟩
  have hw' : ∀ z, (fun z => ((transl y u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)) (z + y) =
      (fun x => (u x : ℝ) - (qlZ l x + qMZ M x)) z + inner ℝ (-p₀) (toE z) + (-c) := by
    intro z
    simp only [transl_apply, add_sub_cancel_right, inner_neg_left, hp z]
    ring
  rw [← volume_subGradSet_vadd (w := fun x => ((u x : ℤ) : ℝ) - (qlZ l x + qMZ M x))
    (w' := fun z => ((transl y u z : ℤ) : ℝ) - (qlZ l z + qMZ M z)) (y := y) hw']
  exact le_iSup₂_of_le _ hmem le_rfl

theorem mu_shift_eq (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (y : Site d)
    (A : Set (Site d)) : mu A (shift y η) l M = mu (y +ᵥ A) η l M := by
  refine le_antisymm (mu_shift_le η l M y A) ?_
  have h := mu_shift_le (shift y η) l M (-y) (y +ᵥ A)
  rwa [← shift_add, neg_add_cancel, shift_zero, id_eq, vadd_vadd, neg_add_cancel, zero_vadd] at h

theorem muStar_shift_eq (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (y : Site d)
    (A : Set (Site d)) : muStar A (shift y η) l M = muStar (y +ᵥ A) η l M := by
  refine le_antisymm (muStar_shift_le η l M y A) ?_
  have h := muStar_shift_le (shift y η) l M (-y) (y +ᵥ A)
  rwa [← shift_add, neg_add_cancel, shift_zero, id_eq, vadd_vadd, neg_add_cancel, zero_vadd] at h

/-- **Lemma 5.5, Step 2.** `μ(A, T_y η) = μ(y + A, η)` and `μ*(A, T_y η) = μ*(y + A, η)`. -/
theorem muStationary : MuStationaryStmt :=
  fun _ η l M y A => ⟨mu_shift_eq η l M y A, muStar_shift_eq η l M y A⟩

end RandomSandpile

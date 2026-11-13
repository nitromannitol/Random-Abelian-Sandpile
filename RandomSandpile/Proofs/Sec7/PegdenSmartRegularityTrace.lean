import RandomSandpile.Steps.Sec7.PegdenSmartRegularity
import RandomSandpile.Infra.Rossin
import RandomSandpile.Proofs.Sec5.MuBounded

/-!
# Lemma 7.6(3): matrices of trace less than `d` are integer superharmonic

Proof of `IntegerSuperharmonicOfTraceStmt` (`RandomSandpile/Steps/Sec7/PegdenSmartRegularity.lean`),
the role of Rossin's observation, together with the lattice algebra of the quadratics
`q_M(z) = ½ zᵀ M z` used by Lemma 7.6.

Proof. Let `B` be symmetric with `tr B < d`. Choose a symmetric `A` with rational entries, `N A`
integral, `q_A ≥ q_B` and `tr A < d` (`exists_rat_approx` applied to `B + θ I`). With `L = 2N`,
`q_A(z + L m) - q_A(z)` is an integer, affine in `z`, for every `m ∈ ℤ^d`. Hence `u₀ = ⌊q_A⌋`
satisfies `u₀(z + L m) = u₀(z) + (affine)`, its Laplacian `s = Δ_{ℤ^d} u₀` is `L`-periodic, and
`q_A - u₀ ∈ [0, 1)` is `L`-periodic, so the sum of `s` over a period is `L^d tr A < d L^d`, fewer
chips than the `d L^d` edges of the torus `ℤ^d / L ℤ^d`. Rossin's observation
(`rossinStabilizable`) gives `w ≥ 0` with `Δ_{ℤ^d} w + s ≤ 2d - 1`, and `u = u₀ + w + 1` has
`Δ_{ℤ^d} u ≤ 2d - 1` and `u > q_A ≥ q_B`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped Matrix

namespace RandomSandpile

namespace PegdenSmartRegularity

variable {d : ℕ}

/-! ### Quadratic and bilinear forms on the lattice -/

/-- The bilinear form `zᵀ M y` on `ℤ^d`. -/
def bilinZ (M : Matrix (Fin d) (Fin d) ℝ) (z y : Site d) : ℝ :=
  ∑ i, ∑ j, (z i : ℝ) * M i j * (y j : ℝ)

theorem qMZ_eq_sum (M : Matrix (Fin d) (Fin d) ℝ) (z : Site d) :
    qMZ M z = (1 / 2) * ∑ i, ∑ j, (z i : ℝ) * M i j * (z j : ℝ) := by
  simp only [qMZ, qM, toE, dotProduct, Matrix.mulVec]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem norm_toE_sq_eq_sum (z : Site d) : ‖toE z‖ ^ 2 = ∑ i, ((z i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [toE]

theorem bilinZ_self (M : Matrix (Fin d) (Fin d) ℝ) (y : Site d) :
    bilinZ M y y = 2 * qMZ M y := by
  rw [qMZ_eq_sum, bilinZ]; ring

theorem bilinZ_symm {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (z y : Site d) :
    bilinZ M y z = bilinZ M z y := by
  unfold bilinZ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hM.apply i j]; ring

theorem bilinZ_add_left (M : Matrix (Fin d) (Fin d) ℝ) (z z' y : Site d) :
    bilinZ M (z + z') y = bilinZ M z y + bilinZ M z' y := by
  simp only [bilinZ, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

theorem bilinZ_sub_left (M : Matrix (Fin d) (Fin d) ℝ) (z z' y : Site d) :
    bilinZ M (z - z') y = bilinZ M z y - bilinZ M z' y := by
  simp only [bilinZ, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

theorem qMZ_add {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (z y : Site d) :
    qMZ M (z + y) = qMZ M z + bilinZ M z y + qMZ M y := by
  have expand : ∑ i, ∑ j, ((z + y) i : ℝ) * M i j * ((z + y) j : ℝ) =
      ∑ i, ∑ j, (z i : ℝ) * M i j * (z j : ℝ) + bilinZ M z y + bilinZ M y z +
        ∑ i, ∑ j, (y i : ℝ) * M i j * (y j : ℝ) := by
    simp only [bilinZ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, Int.cast_add]; ring
  rw [qMZ_eq_sum, expand, bilinZ_symm hM, qMZ_eq_sum, qMZ_eq_sum]; ring

theorem qMZ_sub {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (z y : Site d) :
    qMZ M (z - y) = qMZ M z - bilinZ M z y + qMZ M y := by
  have h := qMZ_add hM (z - y) y
  rw [sub_add_cancel, bilinZ_sub_left, bilinZ_self] at h
  linarith

theorem qMZ_add_left (M M' : Matrix (Fin d) (Fin d) ℝ) (z : Site d) :
    qMZ (M + M') z = qMZ M z + qMZ M' z := by
  simp only [qMZ_eq_sum, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem qMZ_sub_left (M M' : Matrix (Fin d) (Fin d) ℝ) (z : Site d) :
    qMZ (M - M') z = qMZ M z - qMZ M' z := by
  simp only [qMZ_eq_sum, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem qMZ_smul_left (c : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (z : Site d) :
    qMZ (c • M) z = c * qMZ M z := by
  simp only [qMZ_eq_sum, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qMZ_one (z : Site d) : qMZ (1 : Matrix (Fin d) (Fin d) ℝ) z = ‖toE z‖ ^ 2 / 2 := by
  rw [qMZ_eq_sum, norm_toE_sq_eq_sum]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [sq]; ring

/-- `|q_M(z)| ≤ (d c / 2) |z|²` when all entries of `M` are bounded by `c ≥ 0`. -/
theorem abs_qMZ_le {M : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hM : ∀ i j, |M i j| ≤ c) (z : Site d) : |qMZ M z| ≤ d * c / 2 * ‖toE z‖ ^ 2 := by
  rw [qMZ_eq_sum, norm_toE_sq_eq_sum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 : |∑ i, ∑ j, (z i : ℝ) * M i j * (z j : ℝ)| ≤ c * (∑ i, |(z i : ℝ)|) ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_mul]
    have h0 : 0 ≤ |(z i : ℝ)| * |(z j : ℝ)| := by positivity
    rw [show |(z i : ℝ)| * |M i j| * |(z j : ℝ)| = |M i j| * (|(z i : ℝ)| * |(z j : ℝ)|) by ring]
    exact mul_le_mul_of_nonneg_right (hM i j) h0
  have h2 : (∑ i, |(z i : ℝ)|) ^ 2 ≤ d * ∑ i, ((z i : ℝ)) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => |(z i : ℝ)|)
    simpa [sq_abs] using this
  have h3 : c * (∑ i, |(z i : ℝ)|) ^ 2 ≤ c * (d * ∑ i, ((z i : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hc
  nlinarith

/-- **Rational approximation of a symmetric matrix**: a symmetric `A` with `N A` integral,
`|q_{A - Y}(z)| ≤ θ |z|²` and `|tr A - tr Y| ≤ θ`. -/
theorem exists_rat_approx {Y : Matrix (Fin d) (Fin d) ℝ} (hY : Y.IsSymm) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (N : ℕ) (K : Matrix (Fin d) (Fin d) ℤ) (A : Matrix (Fin d) (Fin d) ℝ), 0 < N ∧ A.IsSymm ∧
      (∀ i j, (N : ℝ) * A i j = K i j) ∧ (∀ z : Site d, |qMZ (A - Y) z| ≤ θ * ‖toE z‖ ^ 2) ∧
      |A.trace - Y.trace| ≤ θ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (((d : ℝ) + 1) / θ)
  have hNpos' : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNpos : 0 < N := by exact_mod_cast hNpos'
  have hNθ : (d : ℝ) + 1 < N * θ := by rwa [div_lt_iff₀ hθ] at hN
  set K : Matrix (Fin d) (Fin d) ℤ := fun i j => ⌊(N : ℝ) * Y i j⌋ with hK
  set A : Matrix (Fin d) (Fin d) ℝ := fun i j => (K i j : ℝ) / N with hA
  have hent : ∀ i j, |(A - Y) i j| ≤ 1 / N := by
    intro i j
    change |(⌊(N : ℝ) * Y i j⌋ : ℝ) / N - Y i j| ≤ 1 / N
    have h1 := Int.floor_le ((N : ℝ) * Y i j)
    have h2 := Int.lt_floor_add_one ((N : ℝ) * Y i j)
    have hrw : (⌊(N : ℝ) * Y i j⌋ : ℝ) / N - Y i j =
        ((⌊(N : ℝ) * Y i j⌋ : ℝ) - N * Y i j) / N := by field_simp
    rw [hrw, abs_div, abs_of_pos hNpos', div_le_div_iff_of_pos_right hNpos', abs_le]
    constructor <;> linarith
  refine ⟨N, K, A, hNpos, ?_, ?_, ?_, ?_⟩
  · refine Matrix.IsSymm.ext fun i j => ?_
    simp only [hA, hK, hY.apply i j]
  · intro i j
    simp only [hA]
    field_simp
  · intro z
    refine (abs_qMZ_le (by positivity) hent z).trans ?_
    have : (d : ℝ) * (1 / N) / 2 ≤ θ := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), mul_one_div, div_le_iff₀ hNpos']
      nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  · rw [← Matrix.trace_sub, Matrix.trace]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hent i i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_le_iff₀ hNpos']
    nlinarith

/-- `zᵀ A (N m)` is an integer when `N A` is integral. -/
theorem bilinZ_smul_eq_int {A : Matrix (Fin d) (Fin d) ℝ} {N : ℕ} {K : Matrix (Fin d) (Fin d) ℤ}
    (hK : ∀ i j, (N : ℝ) * A i j = K i j) (z m : Site d) :
    bilinZ A z ((N : ℤ) • m) = ((∑ i, ∑ j, z i * K i j * m j : ℤ) : ℝ) := by
  simp only [bilinZ, Int.cast_sum, Int.cast_mul, Pi.smul_apply, smul_eq_mul, Int.cast_natCast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hK i j]; ring

/-! ### Lattice Laplacians -/

theorem lap_of_additive {f : Site d → ℤ} (hf : ∀ x y, f (x + y) = f x + f y) (x : Site d) :
    lap f x = 0 := by
  have hsub : ∀ x y, f (x - y) = f x - f y := fun x y => by
    have := hf (x - y) y; rw [sub_add_cancel] at this; linarith
  have : nbrSumZ f x = ∑ _i : Fin d, 2 * f x :=
    Finset.sum_congr rfl fun i _ => by rw [hf, hsub]; ring
  rw [lap_eq, this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `z ↦ ∑ᵢⱼ zᵢ Kᵢⱼ mⱼ` is additive, hence harmonic. -/
theorem lap_intBilin (K : Matrix (Fin d) (Fin d) ℤ) (m x : Site d) :
    lap (fun z => ∑ i, ∑ j, z i * K i j * m j) x = 0 :=
  lap_of_additive (f := fun z : Site d => ∑ i, ∑ j, z i * K i j * m j) (fun z z' => by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]) x

theorem lap_comp_add (f : Site d → ℤ) (y x : Site d) :
    lap (fun z => f (z + y)) x = lap f (x + y) := by
  have h : ∀ i, f (x + unit i + y) + f (x - unit i + y) = f (x + y + unit i) + f (x + y - unit i) :=
    fun i => by rw [add_right_comm, sub_add_eq_add_sub]
  simp only [lap, nbrSumZ, h]

theorem lap_comp_sub (f : Site d → ℤ) (y x : Site d) :
    lap (fun z => f (z - y)) x = lap f (x - y) := by
  simp only [sub_eq_add_neg]
  exact lap_comp_add f (-y) x

theorem lap_fun_add (f g : Site d → ℤ) (x : Site d) :
    lap (fun z => f z + g z) x = lap f x + lap g x := by
  simp only [lap, nbrSumZ, Finset.sum_add_distrib]; ring

theorem lap_add_const (f : Site d → ℤ) (c : ℤ) (x : Site d) :
    lap (fun z => f z + c) x = lap f x := by
  simp only [lap, nbrSumZ, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]; ring

/-- `Δ_{ℤ^d} q_M = tr M`. -/
theorem lapR_qMZ (M : Matrix (Fin d) (Fin d) ℝ) (x : Site d) : lapR (qMZ M) x = M.trace := by
  rw [lapR_eq_sum_secondDiff, Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => secondDiff_qMZ M x i

theorem lapR_sub (f g : Site d → ℝ) (x : Site d) :
    lapR (fun z => f z - g z) x = lapR f x - lapR g x := by
  simp only [lapR, nbrSum, sub_add_sub_comm, Finset.sum_sub_distrib]; ring

/-! ### Sums over a period of real periodic functions -/

theorem sum_box_add_real {N : ℕ} {f : Site d → ℝ} (hN : 0 < N)
    (hf : ∀ x z : Site d, f (x + (N : ℤ) • z) = f x) (z : Site d) :
    ∑ x ∈ periodBox d N, f (x + z) = ∑ x ∈ periodBox d N, f x := by
  have hred : ∀ x, f (Rossin.red N x) = f x := fun x => by
    conv_rhs => rw [← Rossin.red_add_smul N x]
    exact (hf _ _).symm
  rw [show ∑ x ∈ periodBox d N, f (x + z) = ∑ x ∈ periodBox d N, f (Rossin.red N (x + z)) from
    Finset.sum_congr rfl fun x _ => (hred _).symm]
  refine Finset.sum_nbij' (fun x => Rossin.red N (x + z)) (fun x => Rossin.red N (x + -z))
    (fun x _ => Rossin.red_mem hN _) (fun x _ => Rossin.red_mem hN _) ?_ ?_ (fun x _ => rfl)
  · intro x hx
    rw [Rossin.red_red_add, add_neg_cancel_right, Rossin.red_of_mem hx]
  · intro x hx
    rw [Rossin.red_red_add, neg_add_cancel_right, Rossin.red_of_mem hx]

theorem sum_box_lapR {N : ℕ} {f : Site d → ℝ} (hN : 0 < N)
    (hf : ∀ x z : Site d, f (x + (N : ℤ) • z) = f x) :
    ∑ x ∈ periodBox d N, lapR f x = 0 := by
  simp only [lapR, nbrSum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, sub_eq_add_neg, sum_box_add_real hN hf]
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ### The proof -/

end PegdenSmartRegularity

open PegdenSmartRegularity

/-- **Matrices of trace less than `d` are integer superharmonic** (Rossin's observation). -/
theorem integerSuperharmonicOfTrace : IntegerSuperharmonicOfTraceStmt := by
  intro d B hB htr
  set θ : ℝ := ((d : ℝ) - B.trace) / (2 * ((d : ℝ) + 1)) with hθ
  have hθpos : 0 < θ := div_pos (by linarith) (by positivity)
  have hθd : θ * (2 * ((d : ℝ) + 1)) = (d : ℝ) - B.trace := by
    rw [hθ]; field_simp
  set Y := B + θ • (1 : Matrix (Fin d) (Fin d) ℝ) with hYdef
  have hY : Y.IsSymm := hB.add (Matrix.isSymm_one.smul θ)
  obtain ⟨N, K, A, hN, hA, hK, happ, htrA⟩ := exists_rat_approx hY (half_pos hθpos)
  -- `q_A ≥ q_B` and `tr A < d`
  have hqA : ∀ z, qMZ B z ≤ qMZ A z := fun z => by
    have h1 := (abs_le.1 (happ z)).1
    have h2 : qMZ A z = qMZ (A - Y) z + qMZ B z + θ * (‖toE z‖ ^ 2 / 2) := by
      rw [qMZ_sub_left, hYdef, qMZ_add_left, qMZ_smul_left, qMZ_one]; ring
    have : 0 ≤ ‖toE z‖ ^ 2 := by positivity
    nlinarith
  have htrA' : A.trace < d := by
    have h1 := (abs_le.1 htrA).2
    have h2 : Y.trace = B.trace + θ * d := by
      rw [hYdef, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
        smul_eq_mul]
    nlinarith
  -- the period `L = 2N` and the shifts of `q_A`
  set L : ℕ := 2 * N with hL
  have hLpos : 0 < L := by omega
  set ι : Site d → Site d → ℤ := fun m z => ∑ i, ∑ j, z i * K i j * ((2 : ℤ) • m) j with hι
  set κ : Site d → ℤ := fun m => ∑ i, ∑ j, 2 * (N : ℤ) * m i * K i j * m j with hκ
  have hLm : ∀ m : Site d, (L : ℤ) • m = (N : ℤ) • ((2 : ℤ) • m) := fun m => by
    rw [smul_smul, hL]; push_cast; ring_nf
  have hκval : ∀ m : Site d, qMZ A ((L : ℤ) • m) = ((κ m : ℤ) : ℝ) := by
    intro m
    rw [qMZ_eq_sum]
    simp only [hκ, Int.cast_sum, Int.cast_mul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hK i j]; simp only [hL]; push_cast; ring
  have hqshift : ∀ z m : Site d, qMZ A (z + (L : ℤ) • m) = qMZ A z + ((ι m z + κ m : ℤ) : ℝ) := by
    intro z m
    rw [qMZ_add hA, hκval, Int.cast_add, ← add_assoc]
    congr 2
    rw [hLm, bilinZ_smul_eq_int hK]
  set u₀ : Site d → ℤ := fun z => ⌊qMZ A z⌋ with hu₀
  have hu₀shift : ∀ z m : Site d, u₀ (z + (L : ℤ) • m) = u₀ z + (ι m z + κ m) := by
    intro z m
    simp only [hu₀, hqshift, Int.floor_add_intCast]
  set s : Site d → ℤ := lap u₀ with hs
  have hper : IsPeriodic L s := by
    intro x m
    simp only [hs]
    rw [← lap_comp_add u₀ ((L : ℤ) • m) x]
    simp only [hu₀shift]
    rw [show (fun z => u₀ z + (ι m z + κ m)) = fun z => (u₀ z + ι m z) + κ m from
      funext fun z => by ring, lap_add_const, lap_fun_add, hι, lap_intBilin, add_zero]
  -- the sum of `s` over a period is `L^d tr A`
  set F : Site d → ℝ := fun z => qMZ A z - u₀ z with hF
  have hFper : ∀ x m : Site d, F (x + (L : ℤ) • m) = F x := by
    intro x m
    simp only [hF, hqshift, hu₀shift]; push_cast; ring
  have hsumR : ((∑ x ∈ periodBox d L, s x : ℤ) : ℝ) = (L : ℝ) ^ d * A.trace := by
    have h1 : ∀ x, (s x : ℝ) = A.trace - lapR F x := fun x => by
      rw [hs, ← lapR_intCast]
      have : (fun y => (u₀ y : ℝ)) = fun y => qMZ A y - F y := funext fun y => by
        simp only [hF]; ring
      rw [this, lapR_sub, lapR_qMZ]
    push_cast
    simp only [h1, Finset.sum_sub_distrib, sum_box_lapR hLpos hFper, Finset.sum_const,
      Rossin.card_periodBox, nsmul_eq_mul]
    push_cast; ring
  have hsum : ∑ x ∈ periodBox d L, s x < (d : ℤ) * (L : ℤ) ^ d := by
    have : ((∑ x ∈ periodBox d L, s x : ℤ) : ℝ) < (((d : ℤ) * (L : ℤ) ^ d : ℤ) : ℝ) := by
      rw [hsumR]; push_cast
      have : (0 : ℝ) < (L : ℝ) ^ d := by positivity
      nlinarith
    exact_mod_cast this
  -- Rossin's observation
  obtain ⟨-, w, -, -, -, hwL⟩ := rossinStabilizable d L s hLpos hper hsum
  obtain ⟨-, hw⟩ := mem_stabilizing_univ.1 hwL.1
  refine ⟨fun z => u₀ z + w z + 1, fun x => ?_, fun x => ?_⟩
  · rw [lap_add_const, lap_fun_add]
    have := hw x
    simp only [hs] at this
    linarith
  · have h1 := Int.lt_floor_add_one (qMZ A x)
    have h2 := hqA x
    obtain ⟨hw0, -⟩ := mem_stabilizing_univ.1 hwL.1
    have h3 : (0 : ℝ) ≤ w x := by exact_mod_cast hw0 x
    push_cast
    simp only [hu₀] at h1 ⊢
    linarith

end RandomSandpile

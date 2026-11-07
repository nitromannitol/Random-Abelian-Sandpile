import RandomSandpile.Draft.Section7
import LatticeProb.Walk.SRWGreenGrad
import LatticeProb.Walk.Ball
import LatticeProb.Walk.GreenTwoSided.PointwiseBounds
import LatticeProb.ParticleHoleLemmas

/-!
# Step of Lemma 7.2: discrete gradient estimate from a bounded Laplacian

`lapGradientBound_core`: for `d ≥ 2`, a function `u : ℤ^d → ℤ` vanishing off the open cube
`{|x|_∞ < R}` with `|Δ_{ℤ^d} u| ≤ M` has nearest-neighbour increments `≤ C M (R + 1)`. This is the
regularity input (cited there to Kuo–Trudinger 2005).

Route: the Green representation `u(x) = ∑_y P^m(0, y - x) u(y) - (2d)⁻¹ ∑_y g_m(y - x) Δu(y)`
(`LapGradient.greenRep_tsum`, induction on `m`), the gradient bound of the truncated Green function
`|∇ g_m(z)| ≤ C (1 + |z|)^{1-d}` uniform in `m` (`LatticeProb.exists_srwGreen_gradient`), the
on-diagonal heat-kernel bound `P^m ≤ C m^{-d/2}` for the first term, and the radial sum
`∑_{|z|_∞ ≤ N} (1 + |z|)^{1-d} = O(N)` (`LapGradient.sum_box_one_add_graphNorm_rpow_le`).
-/
noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
namespace LapGradient

variable {d : ℕ}

/-- A function on the lattice with finite support is summable. -/
lemma summable_of_finite_supp {f : Site d → ℝ} (hf : (Function.support f).Finite) :
    Summable f :=
  summable_of_ne_finset_zero (s := hf.toFinset) (fun b hb => by simpa using hb)

/-- Multiplying by an arbitrary weight keeps the support finite. -/
lemma finite_supp_mul {f : Site d → ℝ} (c : Site d → ℝ) (hf : (Function.support f).Finite) :
    (Function.support fun y => c y * f y).Finite :=
  hf.subset (fun y hy => by
    simp only [Function.mem_support] at hy ⊢
    exact right_ne_zero_of_mul hy)

/-- Translating the argument by `+ e` keeps the support finite. -/
lemma finite_supp_comp_add {f : Site d → ℝ} (e : Site d) (hf : (Function.support f).Finite) :
    (Function.support fun y => f (y + e)).Finite :=
  Set.Finite.preimage (f := fun y => y + e) (add_left_injective e).injOn hf

/-- Translating the argument by `- e` keeps the support finite. -/
lemma finite_supp_comp_sub {f : Site d → ℝ} (e : Site d) (hf : (Function.support f).Finite) :
    (Function.support fun y => f (y - e)).Finite :=
  Set.Finite.preimage (f := fun y => y - e) (sub_left_injective).injOn hf

/-- Summation by translation `y ↦ y + e`. -/
lemma tsum_shift_add (p U : Site d → ℝ) (x e : Site d) :
    ∑' y, p (y - x + e) * U y = ∑' y, p (y - x) * U (y - e) := by
  have h := Equiv.tsum_eq (Equiv.addRight e) (fun y => p (y - x) * U (y - e))
  rw [← h]
  refine tsum_congr fun y => ?_
  simp [add_sub_right_comm]

/-- Summation by translation `y ↦ y - e`. -/
lemma tsum_shift_sub (p U : Site d → ℝ) (x e : Site d) :
    ∑' y, p (y - x - e) * U y = ∑' y, p (y - x) * U (y + e) := by
  have h := Equiv.tsum_eq (Equiv.subRight e) (fun y => p (y - x) * U (y + e))
  rw [← h]
  refine tsum_congr fun y => ?_
  simp [sub_right_comm]


/-- One step of the heat kernel against a finitely supported function:
`∑ P^{m+1}(y - x) U y = (2d)⁻¹ ∑ P^m(y - x) (nbrSum U) y`. -/
lemma tsum_walkOp_nbr (p U : Site d → ℝ) (hU : (Function.support U).Finite)
    (x : Site d) :
    ∑' y, walkOp p (y - x) * U y
      = (2 * d : ℝ)⁻¹ * ∑' y, p (y - x) * nbrSum U y := by
  have hs1 : ∀ i : Fin d, Summable fun y => p (y - x + unit i) * U y := fun i =>
    summable_of_finite_supp (hU.subset (fun y hy => by
      simp only [Function.mem_support] at hy ⊢
      exact right_ne_zero_of_mul hy))
  have hs2 : ∀ i : Fin d, Summable fun y => p (y - x - unit i) * U y := fun i =>
    summable_of_finite_supp (hU.subset (fun y hy => by
      simp only [Function.mem_support] at hy ⊢
      exact right_ne_zero_of_mul hy))
  have hs3 : ∀ i : Fin d, Summable fun y => p (y - x) * U (y - unit i) := fun i =>
    summable_of_finite_supp (finite_supp_mul _ (finite_supp_comp_sub (unit i) hU))
  have hs4 : ∀ i : Fin d, Summable fun y => p (y - x) * U (y + unit i) := fun i =>
    summable_of_finite_supp (finite_supp_mul _ (finite_supp_comp_add (unit i) hU))
  have hL : ∀ y, walkOp p (y - x) * U y
      = (2 * d : ℝ)⁻¹ * ∑ i : Fin d,
          (p (y - x + unit i) * U y + p (y - x - unit i) * U y) := by
    intro y
    rw [walkOp, nbrSum, div_eq_inv_mul, mul_assoc, Finset.sum_mul]
    simp only [add_mul]
  have hR : ∀ y, p (y - x) * nbrSum U y
      = ∑ i : Fin d, (p (y - x) * U (y + unit i) + p (y - x) * U (y - unit i)) := by
    intro y
    rw [nbrSum, Finset.mul_sum]
    simp only [mul_add]
  simp_rw [hL, hR]
  rw [Summable.tsum_mul_left _ (summable_sum fun i _ => (hs1 i).add (hs2 i))]
  congr 1
  rw [Summable.tsum_finsetSum fun i _ => (hs1 i).add (hs2 i),
    Summable.tsum_finsetSum fun i _ => (hs4 i).add (hs3 i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hs1 i).tsum_add (hs2 i), (hs4 i).tsum_add (hs3 i), tsum_shift_add, tsum_shift_sub]
  ring


/-- The Green representation in `tsum` form, for finitely supported `U` with finitely
supported Laplacian `F`. -/
lemma greenRep_tsum (hd : 0 < d) (U F : Site d → ℝ)
    (hF : ∀ y, F y = nbrSum U y - 2 * d * U y)
    (hU : (Function.support U).Finite) (hFs : (Function.support F).Finite) (x : Site d) :
    ∀ m : ℕ, U x = ∑' y, srwHeat d m (y - x) * U y
        - (2 * d : ℝ)⁻¹ * ∑' y, srwGreen d m (y - x) * F y := by
  intro m
  induction m with
  | zero =>
    have h0 : ∑' y, srwHeat d 0 (y - x) * U y = U x := by
      rw [tsum_eq_single x]
      · simp
      · intro y hy
        simp [sub_eq_zero, hy]
    rw [h0]
    simp
  | succ m ih =>
    have hd2 : (2 * d : ℝ) ≠ 0 := by positivity
    have hsU : Summable fun y => srwHeat d m (y - x) * U y :=
      summable_of_finite_supp (finite_supp_mul _ hU)
    have hsF : Summable fun y => srwHeat d m (y - x) * F y :=
      summable_of_finite_supp (finite_supp_mul _ hFs)
    have hsG : Summable fun y => srwGreen d m (y - x) * F y :=
      summable_of_finite_supp (finite_supp_mul _ hFs)
    have hA : ∑' y, srwHeat d (m + 1) (y - x) * U y
        = ∑' y, srwHeat d m (y - x) * U y
          + (2 * d : ℝ)⁻¹ * ∑' y, srwHeat d m (y - x) * F y := by
      have h1 : ∑' y, srwHeat d (m + 1) (y - x) * U y
          = (2 * d : ℝ)⁻¹ * ∑' y, srwHeat d m (y - x) * nbrSum U y :=
        tsum_walkOp_nbr (srwHeat d m) U hU x
      have h2 : ∀ y, srwHeat d m (y - x) * nbrSum U y
          = srwHeat d m (y - x) * F y + 2 * d * (srwHeat d m (y - x) * U y) := by
        intro y
        rw [hF y]
        ring
      simp_rw [h2] at h1
      rw [h1, hsF.tsum_add (hsU.mul_left _), hsU.tsum_mul_left]
      field_simp
      ring
    have hG : ∑' y, srwGreen d (m + 1) (y - x) * F y
        = ∑' y, srwGreen d m (y - x) * F y + ∑' y, srwHeat d m (y - x) * F y := by
      simp_rw [srwGreen_succ, add_mul]
      exact hsG.tsum_add hsF
    rw [hA, hG]
    linear_combination ih

/-- The Green representation of a function supported in the finite set `S`, whose Laplacian
`F` is also supported in `S`: for every `m` and `x`,
`U x = ∑_{y ∈ S} P^m(y - x) U y - (2d)⁻¹ ∑_{y ∈ S} g_m(y - x) F y`. -/
lemma greenRep (hd : 0 < d) (S : Finset (Site d)) (U F : Site d → ℝ)
    (hF : ∀ y, F y = nbrSum U y - 2 * d * U y)
    (hUS : ∀ y, y ∉ S → U y = 0) (hFS : ∀ y, y ∉ S → F y = 0) (x : Site d) (m : ℕ) :
    U x = ∑ y ∈ S, srwHeat d m (y - x) * U y
        - (2 * d : ℝ)⁻¹ * ∑ y ∈ S, srwGreen d m (y - x) * F y := by
  have hU : (Function.support U).Finite :=
    S.finite_toSet.subset (fun y hy => by
      by_contra hyS
      exact hy (hUS y hyS))
  have hFs : (Function.support F).Finite :=
    S.finite_toSet.subset (fun y hy => by
      by_contra hyS
      exact hy (hFS y hyS))
  rw [greenRep_tsum hd U F hF hU hFs x m,
    tsum_eq_sum (s := S) (fun y hy => by simp [hUS y hy]),
    tsum_eq_sum (s := S) (fun y hy => by simp [hFS y hy])]


/-- `|unit i j| ≤ 1`. -/
lemma abs_unit_le (i j : Fin d) : |(unit i : Site d) j| ≤ 1 := by
  by_cases h : j = i <;> simp [unit, h]

/-- The shell weight is dominated by `2 ^ (d - 1)`: `(2k+1)^{d-1} (1+k)^{1-d} ≤ 2^{d-1}`. -/
lemma shell_weight_le (hd : 1 ≤ d) (k : ℕ) :
    (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) ≤ 2 ^ (d - 1) := by
  have ha : (0 : ℝ) < 1 + k := by positivity
  have h1 : (1 + (k : ℝ)) ^ (1 - (d : ℝ)) = ((1 + (k : ℝ)) ^ (d - 1))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ha.le]
    congr 1
    rw [Nat.cast_sub hd]
    push_cast
    ring
  rw [h1, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  calc (2 * (k : ℝ) + 1) ^ (d - 1) ≤ (2 * (1 + (k : ℝ))) ^ (d - 1) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = 2 ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1) := mul_pow _ _ _

/-- The radial sum of `(1 + |z|_∞)^{1-d}` over a box of radius `n`. -/
lemma sum_box_one_add_supNorm_rpow_le (hd : 1 ≤ d) (n : ℕ) :
    ∑ z ∈ boxFinset (0 : Site d) n, (1 + (supNorm z : ℝ)) ^ (1 - (d : ℝ))
      ≤ 1 + n * (2 * d * 2 ^ (d - 1)) := by
  have h := sum_box_radial_le (d := d) (fun k : ℕ => (1 + (k : ℝ)) ^ (1 - (d : ℝ)))
    (fun k => by positivity) n
  refine h.trans ?_
  simp only [Nat.cast_zero, add_zero, Real.one_rpow]
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (1 - (d : ℝ))
        ≤ 2 * d * 2 ^ (d - 1) := by
    intro k _
    have := shell_weight_le hd k
    have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
    calc 2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (1 - (d : ℝ))
        = 2 * d * ((2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (1 - (d : ℝ))) := by ring
      _ ≤ 2 * d * 2 ^ (d - 1) := mul_le_mul_of_nonneg_left this hd0
  have := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
  simp only [add_tsub_cancel_right] at this
  linarith

/-- The graph-norm version of the radial sum bound. -/
lemma sum_box_one_add_graphNorm_rpow_le (hd : 1 ≤ d) (n : ℕ) :
    ∑ z ∈ boxFinset (0 : Site d) n, (1 + (graphNorm z : ℝ)) ^ (1 - (d : ℝ))
      ≤ 1 + n * (2 * d * 2 ^ (d - 1)) := by
  refine le_trans (Finset.sum_le_sum fun z _ => ?_) (sum_box_one_add_supNorm_rpow_le hd n)
  have hle : (supNorm z : ℝ) ≤ graphNorm z := by exact_mod_cast supNorm_le_graphNorm z
  have hexp : (1 - (d : ℝ)) ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hexp

/-- The shifted sum over the box `S = [-R, R]^d`: for `x` in the box of radius `R + 1` and `e` a
unit step, `∑_{y ∈ S} (1 + |y - (x + e)|_1)^{1-d}` is at most `1 + (2R + 2) · 2d · 2^{d-1}`. -/
lemma sum_shifted_box_le (hd : 1 ≤ d) (R : ℕ) (x : Site d)
    (hx : x ∈ boxFinset (0 : Site d) (R + 1)) (i : Fin d) :
    ∑ y ∈ boxFinset (0 : Site d) R, (1 + (graphNorm (y - (x + unit i)) : ℝ)) ^ (1 - (d : ℝ))
      ≤ 1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)) := by
  have hinj : Function.Injective fun y : Site d => y - (x + unit i) := sub_left_injective
  have hsub : (boxFinset (0 : Site d) R).image (fun y => y - (x + unit i))
      ⊆ boxFinset (0 : Site d) (2 * R + 2) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    rw [mem_boxFinset_iff] at hy hx ⊢
    intro j
    have h1 := abs_le.mp (hy j)
    have h2 := abs_le.mp (hx j)
    have h3 := abs_le.mp (abs_unit_le i j)
    simp only [Pi.zero_apply, sub_zero, Pi.sub_apply, Pi.add_apply] at h1 h2 ⊢
    rw [abs_le]
    push_cast at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  calc ∑ y ∈ boxFinset (0 : Site d) R, (1 + (graphNorm (y - (x + unit i)) : ℝ)) ^ (1 - (d : ℝ))
      = ∑ z ∈ (boxFinset (0 : Site d) R).image (fun y => y - (x + unit i)),
          (1 + (graphNorm z : ℝ)) ^ (1 - (d : ℝ)) :=
        (Finset.sum_image (f := fun z : Site d => (1 + (graphNorm z : ℝ)) ^ (1 - (d : ℝ)))
          (fun a _ b _ h => hinj h)).symm
    _ ≤ ∑ z ∈ boxFinset (0 : Site d) (2 * R + 2), (1 + (graphNorm z : ℝ)) ^ (1 - (d : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => by positivity)
    _ ≤ _ := sum_box_one_add_graphNorm_rpow_le hd (2 * R + 2)


/-- The Green-function difference sum against a bounded Laplacian, by the gradient bound and
the shifted box sum. -/
lemma green_diff_sum_le {Cg : ℝ} (hCg : 0 < Cg)
    (hgrad : ∀ (m : ℕ) (y z : Site d), z ∈ nbrFinset y →
      |srwGreen d m y - srwGreen d m z| ≤ Cg * (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)))
    (hd : 1 ≤ d) (R : ℕ) (x : Site d) (hx : x ∈ boxFinset (0 : Site d) (R + 1)) (i : Fin d)
    (F : Site d → ℝ) (M : ℝ) (hM0 : 0 ≤ M) (hFM : ∀ y, |F y| ≤ M) (m : ℕ) :
    |∑ y ∈ boxFinset (0 : Site d) R,
        (srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) * F y|
      ≤ Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1))) := by
  calc |∑ y ∈ boxFinset (0 : Site d) R,
        (srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) * F y|
      ≤ ∑ y ∈ boxFinset (0 : Site d) R,
        |(srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) * F y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ boxFinset (0 : Site d) R,
          Cg * M * (1 + (graphNorm (y - (x + unit i)) : ℝ)) ^ (1 - (d : ℝ)) := by
        refine Finset.sum_le_sum fun y _ => ?_
        have hmem : y - x ∈ nbrFinset (y - (x + unit i)) := by
          rw [nbrFinset, Finset.mem_biUnion]
          refine ⟨i, Finset.mem_univ _, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton]
          left
          abel
        have h1 := hgrad m (y - (x + unit i)) (y - x) hmem
        rw [abs_mul]
        calc |srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)| * |F y|
            ≤ (Cg * (1 + (graphNorm (y - (x + unit i)) : ℝ)) ^ (1 - (d : ℝ))) * M :=
              mul_le_mul h1 (hFM y) (abs_nonneg _) (by positivity)
          _ = Cg * M * (1 + (graphNorm (y - (x + unit i)) : ℝ)) ^ (1 - (d : ℝ)) := by ring
    _ = Cg * M * ∑ y ∈ boxFinset (0 : Site d) R,
          (1 + (graphNorm (y - (x + unit i)) : ℝ)) ^ (1 - (d : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_shifted_box_le hd R x hx i) (by positivity)

/-- The heat-kernel difference sum is small for large times. -/
lemma heat_diff_sum_le {Ch : ℝ}
    (hheat : ∀ k : ℕ, 1 ≤ k → ∀ w : Site d, srwHeat d k w ≤ Ch * (k : ℝ) ^ (-(d : ℝ) / 2))
    (S : Finset (Site d)) (U : Site d → ℝ) (x e : Site d) (m : ℕ) (hm : 1 ≤ m) :
    |∑ y ∈ S, (srwHeat d m (y - (x + e)) - srwHeat d m (y - x)) * U y|
      ≤ Ch * (m : ℝ) ^ (-(d : ℝ) / 2) * ∑ y ∈ S, |U y| := by
  calc |∑ y ∈ S, (srwHeat d m (y - (x + e)) - srwHeat d m (y - x)) * U y|
      ≤ ∑ y ∈ S, |(srwHeat d m (y - (x + e)) - srwHeat d m (y - x)) * U y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ S, Ch * (m : ℝ) ^ (-(d : ℝ) / 2) * |U y| := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have h1 := hheat m hm (y - (x + e))
        have h2 := hheat m hm (y - x)
        have h3 := srwHeat_nonneg (d := d) m (y - (x + e))
        have h4 := srwHeat_nonneg (d := d) m (y - x)
        rw [abs_sub_le_iff]
        constructor <;> linarith
    _ = _ := by rw [Finset.mul_sum]


/-- Moving by at most one unit step lowers the modulus by at most one. -/
lemma le_abs_add_of_le_abs {R : ℕ} {a b : ℤ} (hb : |b| ≤ 1) (h : (R : ℤ) + 1 ≤ |a|) :
    (R : ℤ) ≤ |a + b| ∧ (R : ℤ) ≤ |a - b| := by
  have hb' := abs_le.mp hb
  constructor
  · rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (a + b) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      linarith [hb'.1, hb'.2]
  · rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (a - b) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      linarith [hb'.1, hb'.2]

/-- The Laplacian of an integer function vanishing outside the box `[-R, R]^d` also vanishes
outside this box. -/
lemma lap_eq_zero_of_not_mem_box (u : Site d → ℤ) (R : ℕ)
    (hu : ∀ x : Site d, (∃ i, (R : ℤ) ≤ |x i|) → u x = 0) (y : Site d)
    (hy : y ∉ boxFinset (0 : Site d) R) : lap u y = 0 := by
  rw [mem_boxFinset_iff] at hy
  push Not at hy
  obtain ⟨j, hj⟩ := hy
  simp only [Pi.zero_apply, sub_zero] at hj
  have hj' : (R : ℤ) + 1 ≤ |y j| := hj
  have hy0 : u y = 0 := hu y ⟨j, by linarith⟩
  have hp : ∀ k : Fin d, u (y + unit k) = 0 := fun k =>
    hu _ ⟨j, by
      have := (le_abs_add_of_le_abs (abs_unit_le k j) hj').1
      simpa using this⟩
  have hn : ∀ k : Fin d, u (y - unit k) = 0 := fun k =>
    hu _ ⟨j, by
      have := (le_abs_add_of_le_abs (abs_unit_le k j) hj').2
      simpa using this⟩
  rw [lap_eq, hy0, nbrSumZ]
  simp [hp, hn]


end LapGradient

open LapGradient in
/-- **The discrete interior gradient estimate**: a finitely supported integer function `u`
(vanishing where some coordinate has modulus at least `R`) with `|Δu| ≤ M` has
`|u(x + e_i) - u(x)| ≤ C M (R + 1)`, with `C` depending only on `d ≥ 2`. -/
theorem lapGradientBound_core (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, 0 < C ∧ ∀ (u : Site d → ℤ) (M : ℝ) (R : ℕ),
    (∀ x : Site d, (∃ i, (R : ℤ) ≤ |x i|) → u x = 0) → (∀ x, |(lap u x : ℝ)| ≤ M) →
      ∀ (x : Site d) (i : Fin d), |(u (x + unit i) : ℝ) - u x| ≤ C * M * ((R : ℝ) + 1) := by
  have hd0 : 0 < d := by omega
  obtain ⟨Cg, hCg, hgrad⟩ := exists_srwGreen_gradient d hd
  obtain ⟨Ch, hCh, hheat⟩ := GreenTwoSided.srwHeat_le_mul_rpow_neg_half (d := d) (by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  refine ⟨(2 * d : ℝ)⁻¹ * Cg * (1 + 4 * d * 2 ^ (d - 1)), by positivity, ?_⟩
  intro u M R hu hM x i
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  by_cases hfar : ∃ j, (R : ℤ) + 2 ≤ |x j|
  · obtain ⟨j, hj⟩ := hfar
    have h0 : u x = 0 := hu x ⟨j, by linarith⟩
    have h1 : u (x + unit i) = 0 :=
      hu _ ⟨j, by
        have := (le_abs_add_of_le_abs (abs_unit_le i j) (R := R) (a := x j) (by linarith)).1
        simpa using this⟩
    rw [h0, h1]
    simp only [Int.cast_zero, sub_self, abs_zero]
    positivity
  · push Not at hfar
    have hx : x ∈ boxFinset (0 : Site d) (R + 1) := by
      rw [mem_boxFinset_iff]
      intro j
      have := hfar j
      simp only [Pi.zero_apply, sub_zero]
      push_cast
      linarith
    set S : Finset (Site d) := boxFinset (0 : Site d) R with hS
    set U : Site d → ℝ := fun y => (u y : ℝ) with hUdef
    set F : Site d → ℝ := fun y => (lap u y : ℝ) with hFdef
    have hFeq : ∀ y, F y = nbrSum U y - 2 * d * U y := by
      intro y
      simp only [hFdef, hUdef, lap, nbrSumZ, nbrSum]
      push_cast
      ring
    have hUS : ∀ y, y ∉ S → U y = 0 := by
      intro y hy
      rw [hS, mem_boxFinset_iff] at hy
      push Not at hy
      obtain ⟨j, hj⟩ := hy
      simp only [Pi.zero_apply, sub_zero] at hj
      simp only [hUdef]
      rw [hu y ⟨j, by linarith⟩]
      simp
    have hFS : ∀ y, y ∉ S → F y = 0 := by
      intro y hy
      simp only [hFdef]
      rw [lap_eq_zero_of_not_mem_box u R hu y hy]
      simp
    have hFM : ∀ y, |F y| ≤ M := fun y => hM y
    -- the bound for each finite time
    have hbound : ∀ m : ℕ, 1 ≤ m →
        |U (x + unit i) - U x| ≤ Ch * (m : ℝ) ^ (-(d : ℝ) / 2) * ∑ y ∈ S, |U y|
          + (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))) := by
      intro m hm
      have e1 := greenRep hd0 S U F hFeq hUS hFS (x + unit i) m
      have e2 := greenRep hd0 S U F hFeq hUS hFS x m
      have hdiff : U (x + unit i) - U x
          = (∑ y ∈ S, (srwHeat d m (y - (x + unit i)) - srwHeat d m (y - x)) * U y)
            - (2 * d : ℝ)⁻¹ * ∑ y ∈ S,
              (srwGreen d m (y - (x + unit i)) - srwGreen d m (y - x)) * F y := by
        simp only [sub_mul, Finset.sum_sub_distrib]
        linarith [e1, e2]
      have hA := heat_diff_sum_le hheat S U x (unit i) m hm
      have hB := green_diff_sum_le hCg hgrad (by omega : 1 ≤ d) R x hx i F M hM0 hFM m
      rw [hdiff]
      refine (abs_sub _ _).trans ?_
      refine add_le_add hA ?_
      rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity))]
      exact mul_le_mul_of_nonneg_left hB (by positivity)
    -- pass to the limit `m → ∞`
    have hlim : Tendsto (fun m : ℕ => Ch * (m : ℝ) ^ (-(d : ℝ) / 2) * ∑ y ∈ S, |U y|
          + (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))))
        atTop (𝓝 (Ch * 0 * ∑ y ∈ S, |U y|
          + (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))))) := by
      have hpow : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(d : ℝ) / 2)) atTop (𝓝 0) := by
        have h := (tendsto_rpow_neg_atTop (y := (d : ℝ) / 2) (by positivity)).comp
          tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, neg_div] using h
      exact ((hpow.const_mul Ch).mul_const _).add_const _
    have hfinal := ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun m hm => hbound m hm⟩)
    have hcons : |U (x + unit i) - U x| ≤ (2 * d : ℝ)⁻¹ *
        (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1)))) := by
      simpa using hfinal
    refine hcons.trans ?_
    have hT : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
    have hRn : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have hkey : (2 * d : ℝ)⁻¹ * Cg * (1 + 4 * d * 2 ^ (d - 1)) * M * ((R : ℝ) + 1)
        - (2 * d : ℝ)⁻¹ * (Cg * M * (1 + ((2 * R + 2 : ℕ) : ℝ) * (2 * d * 2 ^ (d - 1))))
        = (2 * d : ℝ)⁻¹ * Cg * M * R := by
      push_cast
      ring
    have hpos : 0 ≤ (2 * d : ℝ)⁻¹ * Cg * M * R := by positivity
    show _ ≤ (2 * d : ℝ)⁻¹ * Cg * (1 + 4 * d * 2 ^ (d - 1)) * M * ((R : ℝ) + 1)
    linarith

end RandomSandpile

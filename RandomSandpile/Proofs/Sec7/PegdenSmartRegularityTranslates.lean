import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTrace
import RandomSandpile.Proofs.Sec5.MuConvergenceStationary
import RandomSandpile.Steps.Sec7.OdometerLowerBound
import RandomSandpile.Defs.Divisible

/-!
# Lemma 7.6(2): Pegden-Smart's minimum of integer-corrected translates

Proof of `PegdenSmartIntegerSuperharmonicStmt` (Pegden-Smart, *Convergence of the Abelian
sandpile*, Lemma 4.1, local form; `RandomSandpile/Inputs/Proposed.lean`, marked PROVABLE), following
the sketch in its docstring.

* `exists_local_quadratic_approx`: from the uniform convergence `n_k⁻² v_k([n_k x]) → v₀` on
  `B_r(a)` and the second-order Peano expansion of `v₀` at `a` with matrix `X`: for every `θ > 0` and
  `R₀` there are `k`, `R ≥ R₀`, a lattice point `c₀ ≈ n_k a` and an affine function
  `ℓ(w) = P·w + C` with `|v_k(c₀ + w) - q_X(w) - ℓ(w)| ≤ θ R²` and `(c₀ + w) / n_k ∈ B_r(a)` for
  `|w| < R` (`R = ρ n_k`).
* `exists_min_translates`: the lattice construction. Let `A` be symmetric with `N A` integral and
  `q_{X - A} ≥ δ |·|²`. For `m ∈ ℤ^d` put `y_m = N m` and
  `φ_m(z) = V(z - y_m) + zᵀ A y_m + c_m`, an integer function (`zᵀ A y_m = ∑ zᵢ Kᵢⱼ mⱼ`, `K = N A`),
  with `c_m = ⌊P·y_m - q_A(y_m)⌋`, so that
  `φ_m(z) = q_A(z) + ℓ(z) + q_{X-A}(z - y_m) + O(θ R²) + O(1)` for `|z - y_m| < R`. The minimum `u(z)`
  of `φ_m(z)` over the window `|z - y_m| < R` is attained with `|z - y_m| < R/2` (quadratic gap), so
  `u ≤ φ_m` at the neighbours of `z` and `Δ_{ℤ^d} u(z) ≤ Δ_{ℤ^d} φ_m(z) = Δ_{ℤ^d} V(z - y_m)`,
  while `u ≥ q_A + ℓ - O(θ R²) - 1`.
* `pegdenSmartIntegerSuperharmonic`: with `A` rational, `X - (ε/2) I - (ε/8)|·|² ≤ A ≤ ...`, so that
  `q_A ≥ q_{X - εI} + (ε/8)|·|²`, the affine term is absorbed and an integer constant is added.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped Matrix

namespace RandomSandpile

namespace PegdenSmartRegularity

variable {d : ℕ}

/-! ### Small facts -/

theorem lap_le_lap_of_nbr {u v : Site d → ℤ} {x : Site d} (hx : u x = v x)
    (hnb : ∀ i, u (x + unit i) ≤ v (x + unit i) ∧ u (x - unit i) ≤ v (x - unit i)) :
    lap u x ≤ lap v x := by
  simp only [lap, nbrSumZ, hx]
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => add_le_add (hnb i).1 (hnb i).2
  linarith

theorem norm_toE_add_unit_sub (x y : Site d) (i : Fin d) :
    ‖toE (x + unit i - y)‖ ≤ ‖toE (x - y)‖ + 1 := by
  rw [show x + unit i - y = (x - y) + unit i by abel, OdometerLowerBound.toE_add,
    ← OdometerLowerBound.norm_toE_unit i]
  exact norm_add_le _ _

theorem norm_toE_sub_unit_sub (x y : Site d) (i : Fin d) :
    ‖toE (x - unit i - y)‖ ≤ ‖toE (x - y)‖ + 1 := by
  rw [show x - unit i - y = (x - y) - unit i by abel, OdometerLowerBound.toE_sub,
    ← OdometerLowerBound.norm_toE_unit i]
  exact norm_sub_le _ _

/-- The remainder of `z` modulo `N ℤ^d` has `|z - N ⌊z / N⌋|² ≤ d N²`. -/
theorem norm_toE_sub_smul_div_sq_le {N : ℕ} (hN : 0 < N) (z : Site d) :
    ‖toE (z - (N : ℤ) • fun i => z i / (N : ℤ))‖ ^ 2 ≤ d * (N : ℝ) ^ 2 := by
  rw [norm_toE_sq_eq_sum]
  have h : ∀ i, (((z - (N : ℤ) • fun i => z i / (N : ℤ)) i : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    intro i
    have he : (z - (N : ℤ) • fun i => z i / (N : ℤ)) i = z i % (N : ℤ) := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact (Int.emod_def (z i) N).symm
    rw [he]
    have h0 : (0 : ℤ) ≤ z i % (N : ℤ) := Int.emod_nonneg _ (by omega)
    have h1 : z i % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
    have h0' : (0 : ℝ) ≤ ((z i % (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast h0
    have h1' : ((z i % (N : ℤ) : ℤ) : ℝ) ≤ N := by exact_mod_cast h1.le
    nlinarith
  calc ∑ i, (((z - (N : ℤ) • fun i => z i / (N : ℤ)) i : ℤ) : ℝ) ^ 2
      ≤ ∑ _i : Fin d, (N : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = d * (N : ℝ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem abs_entry_le_sum (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    |M i j| ≤ ∑ i, ∑ j, |M i j| :=
  (Finset.single_le_sum (f := fun j => |M i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))

theorem qM_smul_vec (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (x : Rd d) :
    qM M (c • x) = c ^ 2 * qM M x := by
  simp only [qM, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

theorem qMZ_eq_qM (M : Matrix (Fin d) (Fin d) ℝ) (z : Site d) : qMZ M z = qM M (toE z) := rfl

/-! ### The lattice construction -/

/-- **Pegden-Smart's construction.** The minimum of the integer-corrected translates
`φ_m(z) = V(z - N m) + zᵀ A (N m) + c_m` over the window `|z - N m| < R`. -/
theorem exists_min_translates {V : Site d → ℤ} {X A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsSymm) {N : ℕ} (hN : 0 < N) {K : Matrix (Fin d) (Fin d) ℤ}
    (hK : ∀ i j, (N : ℝ) * A i j = K i j) {δ Λ : ℝ} (hδ : 0 ≤ δ) (hΛ : 0 ≤ Λ)
    (hlow : ∀ w : Site d, δ * ‖toE w‖ ^ 2 ≤ qMZ (X - A) w)
    (hup : ∀ w : Site d, qMZ (X - A) w ≤ Λ * ‖toE w‖ ^ 2)
    {P : Rd d} {C R η₀ : ℝ} (hR : 2 ≤ R) (hcov : (d : ℝ) * N ^ 2 < (R / 2) ^ 2)
    (hgap : Λ * (d * N ^ 2) + 2 * η₀ + 1 < δ * (R / 2) ^ 2)
    (happrox : ∀ w : Site d, ‖toE w‖ < R →
      |(V w : ℝ) - (qMZ X w + inner ℝ P (toE w) + C)| ≤ η₀) :
    ∃ u : Site d → ℤ, (∀ z, ∃ w : Site d, ‖toE w‖ < R ∧ lap u z ≤ lap V w) ∧
      ∀ z, qMZ A z + inner ℝ P (toE z) + C - η₀ - 1 ≤ u z := by
  classical
  set y : Site d → Site d := fun m => (N : ℤ) • m with hy
  set c : Site d → ℤ := fun m => ⌊inner ℝ P (toE (y m)) - qMZ A (y m)⌋ with hc
  set ι : Site d → Site d → ℤ := fun m z => ∑ i, ∑ j, z i * K i j * m j with hι
  set φ : Site d → Site d → ℤ := fun m z => V (z - y m) + ι m z + c m with hφ
  set base : Site d → ℝ := fun z => qMZ A z + inner ℝ P (toE z) + C with hbase
  -- the real expansion of `φ_m`
  have hexp : ∀ m z, ‖toE (z - y m)‖ < R →
      base z + qMZ (X - A) (z - y m) - 1 - η₀ < φ m z ∧
        (φ m z : ℝ) ≤ base z + qMZ (X - A) (z - y m) + η₀ := by
    intro m z hz
    have h1 := abs_le.1 (happrox _ hz)
    have hι' : (ι m z : ℝ) = bilinZ A z (y m) := (bilinZ_smul_eq_int hK z m).symm
    have hq := qMZ_sub hA z (y m)
    have hP : inner ℝ P (toE (z - y m)) = inner ℝ P (toE z) - inner ℝ P (toE (y m)) := by
      rw [OdometerLowerBound.toE_sub, inner_sub_right]
    have hXA := qMZ_sub_left X A (z - y m)
    have hc1 : ((c m : ℤ) : ℝ) ≤ inner ℝ P (toE (y m)) - qMZ A (y m) := Int.floor_le _
    have hc2 : inner ℝ P (toE (y m)) - qMZ A (y m) < ((c m : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hφz : (φ m z : ℝ) = V (z - y m) + ι m z + c m := by simp only [hφ]; push_cast; ring
    simp only [hbase]
    constructor <;> nlinarith
  -- the window and its minimum
  set S : Site d → Set ℤ := fun z => {k | ∃ m, ‖toE (z - y m)‖ < R ∧ φ m z = k} with hS
  set m₀ : Site d → Site d := fun z => fun i => z i / (N : ℤ) with hm₀
  have hR0 : 0 < R := by linarith
  have hm₀sq : ∀ z, ‖toE (z - y (m₀ z))‖ ^ 2 ≤ d * (N : ℝ) ^ 2 := fun z =>
    norm_toE_sub_smul_div_sq_le hN z
  have hm₀R : ∀ z, ‖toE (z - y (m₀ z))‖ < R / 2 := fun z => by
    have := hm₀sq z
    have h2 : ‖toE (z - y (m₀ z))‖ ^ 2 < (R / 2) ^ 2 := lt_of_le_of_lt this hcov
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hne : ∀ z, (S z).Nonempty := fun z => ⟨_, m₀ z, by linarith [hm₀R z], rfl⟩
  have hbdd : ∀ z, BddBelow (S z) := by
    intro z
    refine ⟨⌊base z - 1 - η₀⌋, ?_⟩
    rintro k ⟨m, hm, rfl⟩
    have h := (hexp m z hm).1
    have h0 : 0 ≤ qMZ (X - A) (z - y m) :=
      le_trans (mul_nonneg hδ (by positivity)) (hlow _)
    have : (⌊base z - 1 - η₀⌋ : ℝ) ≤ φ m z := by
      linarith [Int.floor_le (base z - 1 - η₀)]
    exact_mod_cast this
  set u : Site d → ℤ := fun z => sInf (S z) with hu
  have hule : ∀ z m, ‖toE (z - y m)‖ < R → u z ≤ φ m z := fun z m hm =>
    csInf_le (hbdd z) ⟨m, hm, rfl⟩
  have hmin : ∀ z, ∃ m, ‖toE (z - y m)‖ < R / 2 ∧ u z = φ m z := by
    intro z
    obtain ⟨m, hm, hmz⟩ := Int.csInf_mem (hne z) (hbdd z)
    refine ⟨m, ?_, hmz.symm⟩
    by_contra hfar
    push Not at hfar
    have hlo := (hexp m z hm).1
    have hhi := (hexp (m₀ z) z (by linarith [hm₀R z])).2
    have hle : (u z : ℝ) ≤ φ (m₀ z) z := by exact_mod_cast hule z (m₀ z) (by linarith [hm₀R z])
    have hfar2 : (R / 2) ^ 2 ≤ ‖toE (z - y m)‖ ^ 2 := pow_le_pow_left₀ (by positivity) hfar 2
    have hl := hlow (z - y m)
    have hh := hup (z - y (m₀ z))
    have hmz' : (u z : ℝ) = φ m z := by exact_mod_cast hmz.symm
    have h3 : Λ * ‖toE (z - y (m₀ z))‖ ^ 2 ≤ Λ * (d * N ^ 2) :=
      mul_le_mul_of_nonneg_left (hm₀sq z) hΛ
    have h4 : δ * (R / 2) ^ 2 ≤ δ * ‖toE (z - y m)‖ ^ 2 := mul_le_mul_of_nonneg_left hfar2 hδ
    linarith
  refine ⟨u, fun z => ?_, fun z => ?_⟩
  · obtain ⟨m, hm, hmz⟩ := hmin z
    refine ⟨z - y m, by linarith, ?_⟩
    have hlapφ : lap (φ m) z = lap V (z - y m) := by
      have : φ m = fun z => (V (z - y m) + ι m z) + c m := rfl
      rw [this, lap_add_const, lap_fun_add, lap_comp_sub, hι, lap_intBilin, add_zero]
    rw [← hlapφ]
    refine lap_le_lap_of_nbr hmz fun i => ⟨hule _ _ ?_, hule _ _ ?_⟩
    · linarith [norm_toE_add_unit_sub z (y m) i]
    · linarith [norm_toE_sub_unit_sub z (y m) i]
  · obtain ⟨m, hm, hmz⟩ := hmin z
    have h := (hexp m z (by linarith)).1
    have h0 : 0 ≤ qMZ (X - A) (z - y m) := le_trans (mul_nonneg hδ (by positivity)) (hlow _)
    have hmz' : (u z : ℝ) = φ m z := by exact_mod_cast hmz
    simp only [hbase] at h
    linarith

/-! ### Local quadratic approximation of the odometers -/

/-- `|[x] - x|² ≤ d` for the coordinatewise floor. -/
theorem norm_toE_latticeRound_sub_sq_le (x : Rd d) : ‖toE (latticeRound x) - x‖ ^ 2 ≤ d := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖(toE (latticeRound x) - x) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [toE, latticeRound, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
        have h1 := Int.floor_le (x i)
        have h2 := Int.lt_floor_add_one (x i)
        nlinarith
    _ = d := by simp

theorem exists_local_quadratic_approx {n : ℕ → ℕ} (hn : StrictMono n) {v : ℕ → Site d → ℤ}
    {v₀ : Rd d → ℝ} {a : Rd d} {r : ℝ} (hr : 0 < r)
    (hconv : TendstoUniformlyOn (fun k => rescaleOdo (v k) (n k)) v₀ atTop (Metric.ball a r))
    {p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ} (hTay : HasSecondOrderTaylorAt v₀ a p X)
    {θ : ℝ} (hθ : 0 < θ) (R₀ : ℝ) :
    ∃ (k : ℕ) (R : ℝ) (c₀ : Site d) (P : Rd d) (C : ℝ), R₀ ≤ R ∧ ∀ w : Site d, ‖toE w‖ < R →
      ‖((n k : ℝ))⁻¹ • toE (c₀ + w) - a‖ < r ∧
      |(v k (c₀ + w) : ℝ) - (qMZ X w + inner ℝ P (toE w) + C)| ≤ θ * R ^ 2 := by
  -- Taylor at scale `ε₁`
  obtain ⟨ε₁, hε₁, hTε⟩ := Metric.eventually_nhds_iff.1 (hTay.def (c := θ / 8) (by positivity))
  set ρ : ℝ := min ε₁ r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρ2 : 2 * ρ ≤ ε₁ ∧ 2 * ρ ≤ r := ⟨by rw [hρ]; linarith [min_le_left ε₁ r],
    by rw [hρ]; linarith [min_le_right ε₁ r]⟩
  -- `k` large
  obtain ⟨M, hM⟩ := exists_nat_gt (max (R₀ / ρ) (((d : ℝ) + 1) / ρ))
  have hev := (hn.tendsto_atTop.eventually_ge_atTop (M + 1)).and
    (Metric.tendstoUniformlyOn_iff.1 hconv (θ * ρ ^ 2 / 8) (by positivity))
  obtain ⟨k, hkM, hkU⟩ := hev.exists
  set nn : ℝ := (n k : ℝ) with hnn
  have hnk0 : n k ≠ 0 := by omega
  have hnnpos : 0 < nn := by rw [hnn]; exact_mod_cast Nat.pos_of_ne_zero hnk0
  have hMnn : (M : ℝ) < nn := by
    rw [hnn]; exact_mod_cast (show M < n k by omega)
  have hR₀ : R₀ ≤ ρ * nn := by
    have h1 : R₀ / ρ < nn := lt_trans (lt_of_le_of_lt (le_max_left _ _) hM) hMnn
    rw [div_lt_iff₀ hρpos] at h1; linarith
  have hdnn : ((d : ℝ) + 1) / nn < ρ := by
    have h1 : ((d : ℝ) + 1) / ρ < nn := lt_trans (lt_of_le_of_lt (le_max_right _ _) hM) hMnn
    rw [div_lt_iff₀ hρpos] at h1
    rw [div_lt_iff₀ hnnpos]; linarith
  -- the base point and the affine part
  set c₀ : Site d := latticeRound (nn • a) with hc₀
  set e₀ : Rd d := nn⁻¹ • toE c₀ - a with he₀
  have he₀ρ : ‖e₀‖ < ρ := by
    have h1 : e₀ = nn⁻¹ • (toE c₀ - nn • a) := by
      rw [he₀, smul_sub, smul_smul, inv_mul_cancel₀ hnnpos.ne', one_smul]
    have h2 := norm_toE_latticeRound_sub_sq_le (nn • a)
    have h3 : ‖toE c₀ - nn • a‖ ≤ (d : ℝ) + 1 := by
      have h0 : 0 ≤ ‖toE c₀ - nn • a‖ := norm_nonneg _
      rw [← hc₀] at h2
      nlinarith
    rw [h1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnnpos]
    calc nn⁻¹ * ‖toE c₀ - nn • a‖ ≤ nn⁻¹ * ((d : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ((d : ℝ) + 1) / nn := by ring
      _ < ρ := hdnn
  set g : Rd d := WithLp.toLp 2 ((1 / 2 : ℝ) • (X *ᵥ WithLp.ofLp e₀ + Xᵀ *ᵥ WithLp.ofLp e₀))
    with hg
  refine ⟨k, ρ * nn, c₀, nn • p + nn • g, nn ^ 2 * (v₀ a + inner ℝ p e₀ + qM X e₀), hR₀,
    fun w hw => ?_⟩
  set x : Rd d := nn⁻¹ • toE (c₀ + w) with hx
  have hxa : x - a = nn⁻¹ • toE w + e₀ := by
    rw [hx, he₀, OdometerLowerBound.toE_add, smul_add]; abel
  have hw' : ‖nn⁻¹ • toE w‖ < ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnnpos, inv_mul_lt_iff₀ hnnpos]
    linarith
  have hxa2 : ‖x - a‖ < 2 * ρ := by
    rw [hxa]; linarith [norm_add_le (nn⁻¹ • toE w) e₀]
  have hxr : ‖x - a‖ < r := by linarith [hρ2.2]
  refine ⟨hxr, ?_⟩
  -- the three approximations
  have hxball : x ∈ Metric.ball a r := by rwa [Metric.mem_ball, dist_eq_norm]
  have hU := hkU x hxball
  rw [Real.dist_eq] at hU
  have hresc : rescaleOdo (v k) (n k) x = (v k (c₀ + w) : ℝ) / nn ^ 2 := by
    simp only [rescaleOdo, hx, hnn]
    rw [latticeRound_smul_inv_smul_toE hnk0]
  rw [hresc] at hU
  have hT := hTε (show dist x a < ε₁ by rw [dist_eq_norm]; linarith [hρ2.1])
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x - a‖ ^ 2)] at hT
  have hxa_sq : ‖x - a‖ ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith [norm_nonneg (x - a)]
  -- the polynomial identity
  have hpoly : nn ^ 2 * (v₀ a + inner ℝ p (x - a) + qM X (x - a)) =
      qMZ X w + inner ℝ (nn • p + nn • g) (toE w) + nn ^ 2 * (v₀ a + inner ℝ p e₀ + qM X e₀) := by
    rw [hxa, qM_add, ← hg, qM_smul_vec, inner_add_right, inner_smul_right, inner_smul_right,
      inner_add_left, inner_smul_left, inner_smul_left, qMZ_eq_qM]
    simp only [RCLike.conj_to_real]
    field_simp
    ring
  have hvk : (v k (c₀ + w) : ℝ) = nn ^ 2 * ((v k (c₀ + w) : ℝ) / nn ^ 2) := by field_simp
  rw [← hpoly, hvk, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  have key : |(v k (c₀ + w) : ℝ) / nn ^ 2 - (v₀ a + inner ℝ p (x - a) + qM X (x - a))| ≤
      θ * ρ ^ 2 := by
    have h8 : θ / 8 * ‖x - a‖ ^ 2 ≤ θ / 8 * (4 * ρ ^ 2) :=
      mul_le_mul_of_nonneg_left hxa_sq (by positivity)
    rw [abs_le] at hT ⊢
    rw [abs_lt] at hU
    constructor <;> linarith
  calc nn ^ 2 * |(v k (c₀ + w) : ℝ) / nn ^ 2 - (v₀ a + inner ℝ p (x - a) + qM X (x - a))|
      ≤ nn ^ 2 * (θ * ρ ^ 2) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = θ * (ρ * nn) ^ 2 := by ring

end PegdenSmartRegularity

open PegdenSmartRegularity

/-- **Pegden-Smart, Lemma 4.1 (local form)**: `PegdenSmartIntegerSuperharmonicStmt`. -/
theorem pegdenSmartIntegerSuperharmonic : PegdenSmartIntegerSuperharmonicStmt := by
  intro d hd n hn v v₀ a r hr hlap hconv p X hX hTay ε hε
  -- a rational `A` strictly between `X - εI` and `X`
  obtain ⟨N, K, A, hN, hA, hK, happ, -⟩ :=
    exists_rat_approx (isSymm_sub_smul_one hX (ε / 2)) (θ := ε / 8) (by positivity)
  have hdecomp : ∀ z : Site d, qMZ A z =
      qMZ (A - (X - (ε / 2) • 1)) z + qMZ X z - ε / 2 * (‖toE z‖ ^ 2 / 2) := fun z => by
    rw [qMZ_sub_left, qMZ_sub_left, qMZ_smul_left, qMZ_one]; ring
  have hlow : ∀ w : Site d, ε / 8 * ‖toE w‖ ^ 2 ≤ qMZ (X - A) w := fun w => by
    have h1 := (abs_le.1 (happ w)).2
    rw [qMZ_sub_left, hdecomp]
    nlinarith
  have hAbig : ∀ z : Site d, qMZ (X - ε • 1) z + ε / 8 * ‖toE z‖ ^ 2 ≤ qMZ A z := fun z => by
    have h1 := (abs_le.1 (happ z)).1
    rw [hdecomp, qMZ_sub_left, qMZ_smul_left, qMZ_one]
    nlinarith
  set c : ℝ := ∑ i, ∑ j, |(X - A) i j| with hcdef
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set Λ : ℝ := d * c / 2 with hΛ
  have hΛpos : 0 ≤ Λ := by positivity
  have hup : ∀ w : Site d, qMZ (X - A) w ≤ Λ * ‖toE w‖ ^ 2 := fun w =>
    (le_abs_self _).trans (abs_qMZ_le hc (abs_entry_le_sum _) w)
  -- the scale
  set θ₀ : ℝ := ε / 128 with hθ₀
  set R₀ : ℝ := 2 + 64 * (Λ * (d * N ^ 2) + 1) / ε + 4 * d * N ^ 2 with hR₀
  obtain ⟨k, R, c₀, P, C, hRR₀, happrox⟩ :=
    exists_local_quadratic_approx hn hr hconv hTay (θ := θ₀) (by positivity) R₀
  have hR2 : 2 ≤ R := by
    have : 0 ≤ 64 * (Λ * (d * N ^ 2) + 1) / ε + 4 * d * N ^ 2 := by positivity
    linarith
  have hRsq : R ≤ R ^ 2 := by nlinarith
  have hcov : (d : ℝ) * N ^ 2 < (R / 2) ^ 2 := by
    have : 0 ≤ 64 * (Λ * (d * N ^ 2) + 1) / ε := by positivity
    nlinarith
  have hgap : Λ * (d * N ^ 2) + 2 * (θ₀ * R ^ 2) + 1 < ε / 8 * (R / 2) ^ 2 := by
    have h1 : 64 * (Λ * (d * N ^ 2) + 1) / ε < R ^ 2 := by
      have : 0 ≤ 4 * (d : ℝ) * N ^ 2 := by positivity
      linarith
    rw [div_lt_iff₀ hε] at h1
    rw [hθ₀]; nlinarith
  obtain ⟨u, hulap, hulow⟩ := exists_min_translates (V := fun w => v k (c₀ + w)) (X := X) hA hN hK
    (by positivity) hΛpos hlow hup hR2 hcov hgap (fun w hw => (happrox w hw).2)
  -- absorb the affine part
  set D : ℝ := 2 * ‖P‖ ^ 2 / ε - C + θ₀ * R ^ 2 + 1 with hD
  refine ⟨fun z => u z + ⌈D⌉, fun x => ⟨?_, ?_⟩⟩
  · rw [lap_add_const]
    obtain ⟨w, hw, hle⟩ := hulap x
    have hlv : lap (fun w => v k (c₀ + w)) w = lap (v k) (c₀ + w) := by
      have : (fun w => v k (c₀ + w)) = fun w => v k (w + c₀) := funext fun w => by rw [add_comm]
      rw [this, lap_comp_add, add_comm]
    rw [hlv] at hle
    exact hle.trans (hlap k (c₀ + w) (happrox w hw).1)
  · have h1 := hulow x
    have h2 := hAbig x
    have h3 : -(‖P‖ * ‖toE x‖) ≤ inner ℝ P (toE x) := (abs_le.1 (abs_real_inner_le_norm P (toE x))).1
    have h4 : -(2 * ‖P‖ ^ 2 / ε) ≤ ε / 8 * ‖toE x‖ ^ 2 - ‖P‖ * ‖toE x‖ := by
      have : 0 ≤ ε / 8 * (‖toE x‖ - 4 * ‖P‖ / ε) ^ 2 := by positivity
      have hexp : ε / 8 * (‖toE x‖ - 4 * ‖P‖ / ε) ^ 2 =
          ε / 8 * ‖toE x‖ ^ 2 - ‖P‖ * ‖toE x‖ + 2 * ‖P‖ ^ 2 / ε := by
        field_simp; ring
      linarith
    have h5 := Int.le_ceil D
    push_cast
    linarith

end RandomSandpile

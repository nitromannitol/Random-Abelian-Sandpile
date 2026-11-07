import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityTranslates
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityFinite
import RandomSandpile.Proofs.Sec7.PegdenSmartRegularityBoxes
import RandomSandpile.Proofs.Sec7.DivisibleHomogenize

/-!
# Lemma 7.6(3): the Hessian trace bound in `W`

Proof of `FreeOdometerLimitHessianTraceStmt` (`freeOdometerLimitHessianTrace`): almost surely, if
a uniform limit `v` of rescaled free odometers of `η` on `W` has a second-order Peano expansion at
`a ∈ W` with symmetric `X = D²v(a)`, then `tr X ≤ 2d - 1 - E η(0)` (the homogenized form of
`Δ_{ℤ^d} v_n + η ≤ 2d - 1` in `W_n`).

Almost sure event: `η` is bounded and the normalised sums of `η - E η(0)` over all dyadic cubes
tend to `0` (`cubeErgodic`, the pointwise ergodic theorem). Suppose `tr X = 2d - 1 - E η(0) + 4γ`
with `γ > 0`. Near `c₀ ≈ n_k a`, at scale `R = ρ n_k`,
`F(w) = v_k(c₀ + w) - q_X(w) - P·w - C` has `|F| ≤ θ R²` (`exists_local_quadratic_approx_scale`) and
`Δ_{ℤ^d} F(w) ≤ E η(0) - η(c₀ + w) - 4γ` (the free sandpile is stable, `c₀ + w ∈ W_n`). Sum against
the tent product `w_L` (`L ≈ R/(d+1)`) and sum by parts:
`-θR² ∑|Δ w_L| ≤ ∑ F Δ w_L = ∑ w_L Δ F ≤ -∑ w_L (η(c₀ + ·) - E η(0)) - 4γ ∑ w_L`. The middle sum is a
sum of `L^d` box sums, each `≤ ε n_k^d` (`uniform_box_sum`), `∑ |Δ w_L| ≤ 4d L^{2d-2}` and
`∑ w_L = L^{2d}`, so `4γ ≤ 3γ` for `θ`, `ε` small.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology
open scoped Matrix

namespace RandomSandpile

namespace PegdenSmartRegularity

variable {d : ℕ}

/-- `exists_local_quadratic_approx` with the scale `R = ρ n_k` exposed: `ρ` is chosen before `k`. -/
theorem exists_local_quadratic_approx_scale {n : ℕ → ℕ} (hn : StrictMono n)
    {v : ℕ → Site d → ℤ} {v₀ : Rd d → ℝ} {a : Rd d} {r : ℝ} (hr : 0 < r)
    (hconv : TendstoUniformlyOn (fun k => rescaleOdo (v k) (n k)) v₀ atTop (Metric.ball a r))
    {p : Rd d} {X : Matrix (Fin d) (Fin d) ℝ} (hTay : HasSecondOrderTaylorAt v₀ a p X)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ᶠ k in atTop, ∃ (c₀ : Site d) (P : Rd d) (C : ℝ),
      ∀ w : Site d, ‖toE w‖ < ρ * n k →
        ‖((n k : ℝ))⁻¹ • toE (c₀ + w) - a‖ < r ∧
        |(v k (c₀ + w) : ℝ) - (qMZ X w + inner ℝ P (toE w) + C)| ≤ θ * (ρ * n k) ^ 2 := by
  -- Taylor at scale `ε₁`
  obtain ⟨ε₁, hε₁, hTε⟩ := Metric.eventually_nhds_iff.1 (hTay.def (c := θ / 8) (by positivity))
  set ρ : ℝ := min ε₁ r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρ2 : 2 * ρ ≤ ε₁ ∧ 2 * ρ ≤ r := ⟨by rw [hρ]; linarith [min_le_left ε₁ r],
    by rw [hρ]; linarith [min_le_right ε₁ r]⟩
  refine ⟨ρ, hρpos, by linarith [hρ2.2], ?_⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (((d : ℝ) + 1) / ρ)
  filter_upwards [hn.tendsto_atTop.eventually_ge_atTop (M + 1),
    Metric.tendstoUniformlyOn_iff.1 hconv (θ * ρ ^ 2 / 8) (by positivity)] with k hkM hkU
  set nn : ℝ := (n k : ℝ) with hnn
  have hnk0 : n k ≠ 0 := by omega
  have hnnpos : 0 < nn := by rw [hnn]; exact_mod_cast Nat.pos_of_ne_zero hnk0
  have hMnn : (M : ℝ) < nn := by
    rw [hnn]; exact_mod_cast (show M < n k by omega)
  have hdnn : ((d : ℝ) + 1) / nn < ρ := by
    have h1 : ((d : ℝ) + 1) / ρ < nn := lt_trans hM hMnn
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
  refine ⟨c₀, nn • p + nn • g, nn ^ 2 * (v₀ a + inner ℝ p e₀ + qM X e₀), fun w hw => ?_⟩
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

theorem lapR_of_additive {f : Site d → ℝ} (hf : ∀ y z, f (y + z) = f y + f z) (x : Site d) :
    lapR f x = 0 := by
  have hs : ∀ y z, f (y - z) = f y - f z := fun y z => by
    have := hf (y - z) z; rw [sub_add_cancel] at this; linarith
  rw [lapR_eq_sum_secondDiff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [secondDiff, hf, hs]; ring

theorem lapR_fun_add (f g : Site d → ℝ) (x : Site d) :
    lapR (fun z => f z + g z) x = lapR f x + lapR g x := by
  simp only [lapR, nbrSum, Finset.sum_add_distrib]; ring

theorem lapR_const (c : ℝ) (x : Site d) : lapR (fun _ : Site d => c) x = 0 := by
  simp only [lapR, nbrSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `Δ_{ℤ^d}` of the quadratic-plus-affine function `q_X + P·z + C` is `tr X`. -/
theorem lapR_quadAffine (X : Matrix (Fin d) (Fin d) ℝ) (P : Rd d) (C : ℝ) (x : Site d) :
    lapR (fun w => qMZ X w + inner ℝ P (toE w) + C) x = X.trace := by
  rw [lapR_fun_add (fun w => qMZ X w + inner ℝ P (toE w)), lapR_const, lapR_fun_add,
    lapR_qMZ, lapR_of_additive (f := fun w => inner ℝ P (toE w)) (fun y z => by
      rw [OdometerLowerBound.toE_add, inner_add_right])]
  ring

theorem sum_tentBox_add (k : Fin d → ℕ) (c : Site d) (g : Site d → ℝ) :
    ∑ z ∈ tentBox k, g (c + z) =
      ∑ y ∈ intBox (fun i => c i - k i) (fun i => c i + k i + 1), g y := by
  have hset : intBox (fun i => c i - k i) (fun i => c i + k i + 1) =
      (tentBox k).map (Equiv.addLeft c).toEmbedding := by
    ext y
    simp only [Finset.mem_map, intBox, Fintype.mem_piFinset, Finset.mem_Ico, tentBox,
      Finset.mem_Icc, Equiv.coe_toEmbedding, Equiv.coe_addLeft]
    constructor
    · intro hy
      refine ⟨y - c, fun i => ?_, by abel⟩
      simp only [Pi.sub_apply]; have := hy i; omega
    · rintro ⟨z, hz, rfl⟩ i
      simp only [Pi.add_apply]; have := hz i; omega
  rw [hset, Finset.sum_map]
  simp

theorem abs_coord_le_norm (z : Site d) (i : Fin d) : |(z i : ℝ)| ≤ ‖toE z‖ := by
  have h : ((z i : ℝ)) ^ 2 ≤ ‖toE z‖ ^ 2 := by
    rw [norm_toE_sq_eq_sum]
    exact Finset.single_le_sum (f := fun i => ((z i : ℝ)) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at this

end PegdenSmartRegularity

open PegdenSmartRegularity

/-- **The Hessian trace bound in `W`** (Lemma 7.6(3)). -/
theorem freeOdometerLimitHessianTrace : FreeOdometerLimitHessianTraceStmt := by
  intro d hd E W hW
  have hd1 : 1 ≤ d := by omega
  set m : ℝ := meanEta E.P with hm
  set Ω₁ : Set (Config d) := {η | (∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax) ∧
    ∀ (j : ℕ) (k : Site d), Tendsto (fun N : ℕ =>
      (∑ y ∈ dyadicCube j k N, ((η y : ℝ) - m)) / (N : ℝ) ^ d) atTop (𝓝 0)} with hΩ₁
  refine ⟨Ω₁, ?_, ?_⟩
  · have h1 : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
    have h2 := cubeErgodic d hd E
    have h3 : ∀ᵐ η ∂E.P, η ∈ Ω₁ := by
      filter_upwards [h1, h2] with η h1 h2 using ⟨h1, h2⟩
    rw [ae_iff] at h3
    simpa only [Set.compl_def] using h3
  intro η hη nk hnk v hv a ha p X hX hTay
  by_contra hcon
  push Not at hcon
  set γ : ℝ := (X.trace - (2 * (d : ℝ) - 1 - m)) / 4 with hγ
  have hγpos : 0 < γ := by rw [hγ]; linarith
  have htrX : 2 * (d : ℝ) - 1 - X.trace = m - 4 * γ := by rw [hγ]; ring
  -- the bounded centred environment
  set Mb : ℝ := |(E.ηmin : ℝ)| + |(E.ηmax : ℝ)| + |m| with hMb
  have hfb : ∀ y, |(η y : ℝ) - m| ≤ Mb := fun y => by
    have e1 : (E.ηmin : ℝ) ≤ η y := by exact_mod_cast (hη.1 y).1
    have e2 : (η y : ℝ) ≤ E.ηmax := by exact_mod_cast (hη.1 y).2
    have := neg_abs_le (E.ηmin : ℝ); have := le_abs_self (E.ηmax : ℝ)
    have := neg_abs_le m; have := le_abs_self m
    have := abs_nonneg (E.ηmin : ℝ); have := abs_nonneg (E.ηmax : ℝ)
    rw [abs_le]; constructor <;> linarith
  -- scales
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW.2.1 a ha
  set θ : ℝ := γ / (8 * d * ((d : ℝ) + 1) ^ 2) with hθ
  have hθpos : 0 < θ := by positivity
  obtain ⟨ρ, hρ, hρr, hevk⟩ := exists_local_quadratic_approx_scale
    (v := fun k => freeOdometer η (discretize W (nk k))) hnk hr hv.tendstoUniformlyOn hTay hθpos
  set ε : ℝ := γ * (ρ / (2 * ((d : ℝ) + 1))) ^ d with hε
  have hεpos : 0 < ε := by positivity
  set K : ℝ := ‖a‖ + 2 * r + 2 with hK
  have hK1 : 1 ≤ K := by have := norm_nonneg a; linarith
  obtain ⟨N₀, hN₀⟩ := uniform_box_sum (fun y => (η y : ℝ) - m) Mb hfb hη.2 hd1 hεpos hK1
  obtain ⟨M', hM'⟩ := exists_nat_gt (2 * ((d : ℝ) + 1) / ρ)
  have hM'1 : 1 ≤ M' := by
    have : (0 : ℝ) < M' := lt_trans (by positivity) hM'
    exact_mod_cast this
  obtain ⟨k, hk, c₀, P, C, happ⟩ :=
    ((hnk.tendsto_atTop.eventually_ge_atTop (N₀ + M')).and hevk).exists
  set nn : ℝ := (nk k : ℝ) with hnn
  have hnk0 : nk k ≠ 0 := by omega
  have hnn1 : (1 : ℝ) ≤ nn := by rw [hnn]; exact_mod_cast (show 1 ≤ nk k by omega)
  have hnnpos : 0 < nn := by linarith
  have hnnM : (M' : ℝ) ≤ nn := by rw [hnn]; exact_mod_cast (show M' ≤ nk k by omega)
  have hx2 : 2 ≤ ρ * nn / ((d : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have := lt_of_lt_of_le hM' hnnM
    rw [div_lt_iff₀ hρ] at this; linarith
  -- the tent size
  set L : ℕ := ⌊ρ * nn / ((d : ℝ) + 1)⌋₊ with hL
  have hLup : (L : ℝ) ≤ ρ * nn / ((d : ℝ) + 1) := Nat.floor_le (by positivity)
  have hLlow : ρ * nn / (2 * ((d : ℝ) + 1)) ≤ L := by
    have h1 := Nat.lt_floor_add_one (ρ * nn / ((d : ℝ) + 1))
    have h2 : ρ * nn / (2 * ((d : ℝ) + 1)) = ρ * nn / ((d : ℝ) + 1) / 2 := by
      rw [div_div, mul_comm ((d : ℝ) + 1) 2]
    rw [h2]; linarith
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ L := by
      have : (1 : ℝ) ≤ ρ * nn / (2 * ((d : ℝ) + 1)) := by
        rw [le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ (by positivity)] at hx2; linarith
      linarith
    exact_mod_cast this
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hρnL : ρ * nn ≤ 2 * ((d : ℝ) + 1) * L := by
    rw [div_le_iff₀ (by positivity)] at hLlow; linarith
  have hLρ : (L : ℝ) * ((d : ℝ) + 1) ≤ ρ * nn := by
    rwa [le_div_iff₀ (by positivity)] at hLup
  set B : Finset (Site d) := bigBox d L with hB
  have hBnorm : ∀ w ∈ B, ‖toE w‖ < ρ * nn := by
    intro w hw
    simp only [hB, bigBox, Fintype.mem_piFinset, Finset.mem_Icc] at hw
    have hsq : ‖toE w‖ ^ 2 ≤ d * (L : ℝ) ^ 2 := by
      rw [norm_toE_sq_eq_sum]
      calc ∑ i, ((w i : ℝ)) ^ 2 ≤ ∑ _i : Fin d, (L : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => by
            have h1 : (-(L : ℝ)) ≤ w i := by exact_mod_cast (hw i).1
            have h2 : (w i : ℝ) ≤ L := by exact_mod_cast (hw i).2
            nlinarith
        _ = d * (L : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : ((L : ℝ) * ((d : ℝ) + 1)) ^ 2 ≤ (ρ * nn) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hLρ 2
    have h4 : (d : ℝ) * (L : ℝ) ^ 2 < (ρ * nn) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (lt_of_le_of_lt hsq h4)
  -- the function `F`
  set V : Site d → ℤ := freeOdometer η (discretize W (nk k)) with hV
  set F : Site d → ℝ := fun w => (V (c₀ + w) : ℝ) - (qMZ X w + inner ℝ P (toE w) + C) with hF
  have hFb : ∀ w ∈ B, |F w| ≤ θ * (ρ * nn) ^ 2 := fun w hw => (happ w (hBnorm w hw)).2
  have hlapF : ∀ w ∈ B, lapR F w ≤ (m - (η (c₀ + w) : ℝ)) - 4 * γ := by
    intro w hw
    have hV' := lapR_intCast (fun w => V (c₀ + w)) w
    have h1 : lapR F w = (lap V (c₀ + w) : ℝ) - X.trace := by
      rw [hF, lapR_sub (fun w => ((V (c₀ + w) : ℤ) : ℝ))
        (fun w => qMZ X w + inner ℝ P (toE w) + C), lapR_quadAffine, hV']
      congr 2
      rw [show (fun w => V (c₀ + w)) = fun w => V (w + c₀) from funext fun w => by
        rw [add_comm], lap_comp_add, add_comm]
    have h2 := lap_freeOdometer_add_indicator_le hd1 η hW.1 (nk k) (c₀ + w)
    have hmem : c₀ + w ∈ discretize W (nk k) := by
      rw [mem_discretize_iff hnk0]
      exact hball (by rw [Metric.mem_ball, dist_eq_norm]; exact (happ w (hBnorm w hw)).1)
    rw [Set.indicator_of_mem hmem] at h2
    have h3 : ((lap V (c₀ + w) : ℤ) : ℝ) ≤ 2 * d - 1 - η (c₀ + w) := by
      have : lap V (c₀ + w) ≤ 2 * (d : ℤ) - 1 - η (c₀ + w) := by linarith
      exact_mod_cast this
    rw [h1]; linarith
  -- the base point is at distance `O(n_k)`
  have hc₀ : ‖toE c₀‖ ≤ nn * (‖a‖ + r) := by
    have h0 := (happ 0 (by rw [OdometerLowerBound.toE_zero, norm_zero]; positivity)).1
    rw [add_zero] at h0
    have h1 : ‖nn⁻¹ • toE c₀‖ ≤ ‖a‖ + r := by
      have := norm_le_insert' (nn⁻¹ • toE c₀) a
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnnpos, inv_mul_le_iff₀ hnnpos] at h1
    exact h1
  have hboxes : ∀ k' ∈ Fintype.piFinset (fun _ : Fin d => Finset.range L),
      |∑ z ∈ tentBox k', ((η (c₀ + z) : ℝ) - m)| ≤ ε * nn ^ d := by
    intro k' hk'
    have hk'i : ∀ i, (k' i : ℝ) < L := fun i => by
      simp only [Fintype.mem_piFinset, Finset.mem_range] at hk'
      exact_mod_cast hk' i
    rw [sum_tentBox_add k' c₀ (fun y => (η y : ℝ) - m)]
    refine hN₀ (nk k) (by omega) _ _ fun i => ?_
    have hci := (abs_le.1 ((abs_coord_le_norm c₀ i).trans hc₀))
    have hLr : (L : ℝ) ≤ r * nn := by
      have : ρ * nn / ((d : ℝ) + 1) ≤ ρ * nn := div_le_self (by positivity) (by linarith)
      nlinarith
    have hk0 : (0 : ℝ) ≤ k' i := Nat.cast_nonneg _
    have := hk'i i
    have hKn : K * nn = nn * (‖a‖ + r) + r * nn + 2 * nn := by rw [hK]; ring
    push_cast
    constructor <;> linarith [hci.1, hci.2]
  -- summation by parts
  have hsum1 : ∑ z ∈ B, tentW L z * lapR F z = ∑ z ∈ B, F z * lapR (tentW L) z :=
    sum_tentW_mul_lapR hL1 F
  have hlow : -(θ * (ρ * nn) ^ 2 * (4 * d * ((L : ℝ) ^ 2) ^ (d - 1))) ≤
      ∑ z ∈ B, F z * lapR (tentW L) z := by
    have hpt : ∀ z ∈ B, -(θ * (ρ * nn) ^ 2 * |lapR (tentW L) z|) ≤ F z * lapR (tentW L) z :=
      fun z hz => by
        have h := hFb z hz
        have : |F z * lapR (tentW L) z| ≤ θ * (ρ * nn) ^ 2 * |lapR (tentW L) z| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
        linarith [neg_abs_le (F z * lapR (tentW L) z)]
    have hS := sum_abs_lapR_tentW_le (d := d) hL1
    have hc : 0 ≤ θ * (ρ * nn) ^ 2 := by positivity
    calc -(θ * (ρ * nn) ^ 2 * (4 * d * ((L : ℝ) ^ 2) ^ (d - 1)))
        ≤ -(θ * (ρ * nn) ^ 2 * ∑ z ∈ B, |lapR (tentW L) z|) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hS hc)
      _ = ∑ z ∈ B, -(θ * (ρ * nn) ^ 2 * |lapR (tentW L) z|) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum hpt
  have hup : ∑ z ∈ B, tentW L z * lapR F z ≤
      -(∑ z ∈ B, tentW L z * ((η (c₀ + z) : ℝ) - m)) - 4 * γ * ((L : ℝ) ^ 2) ^ d := by
    have hpt : ∀ z ∈ B, tentW L z * lapR F z ≤
        -(tentW L z * ((η (c₀ + z) : ℝ) - m)) - 4 * γ * tentW L z := fun z hz => by
      have := mul_le_mul_of_nonneg_left (hlapF z hz) (tentW_nonneg L z); linarith
    refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hB, sum_tentW]
  have hmid : |∑ z ∈ B, tentW L z * ((η (c₀ + z) : ℝ) - m)| ≤ (L : ℝ) ^ d * (ε * nn ^ d) := by
    have h := sum_tentW_mul (d := d) L (fun z => (η (c₀ + z) : ℝ) - m)
    rw [hB, h]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hboxes).trans (le_of_eq ?_))
    rw [Finset.sum_const, Fintype.card_piFinset, Finset.prod_const, Finset.card_range,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  -- the contradiction
  set S : ℝ := ((L : ℝ) ^ 2) ^ d with hS
  have hSpos : 0 < S := by positivity
  have hA : θ * (ρ * nn) ^ 2 * (4 * d * ((L : ℝ) ^ 2) ^ (d - 1)) ≤ 2 * γ * S := by
    have h1 : (ρ * nn) ^ 2 ≤ (2 * ((d : ℝ) + 1) * L) ^ 2 := pow_le_pow_left₀ (by positivity) hρnL 2
    have hpow : (L : ℝ) ^ 2 * ((L : ℝ) ^ 2) ^ (d - 1) = S := by
      rw [hS, ← pow_succ', Nat.sub_add_cancel hd1]
    have h2 : θ * (2 * ((d : ℝ) + 1) * L) ^ 2 * (4 * d * ((L : ℝ) ^ 2) ^ (d - 1)) = 2 * γ * S := by
      rw [← hpow, hθ]; field_simp; ring
    have h3 : 0 ≤ θ * (4 * d * ((L : ℝ) ^ 2) ^ (d - 1)) := by positivity
    calc θ * (ρ * nn) ^ 2 * (4 * d * ((L : ℝ) ^ 2) ^ (d - 1))
        = (ρ * nn) ^ 2 * (θ * (4 * d * ((L : ℝ) ^ 2) ^ (d - 1))) := by ring
      _ ≤ (2 * ((d : ℝ) + 1) * L) ^ 2 * (θ * (4 * d * ((L : ℝ) ^ 2) ^ (d - 1))) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ = θ * (2 * ((d : ℝ) + 1) * L) ^ 2 * (4 * d * ((L : ℝ) ^ 2) ^ (d - 1)) := by ring
      _ = 2 * γ * S := h2
  have hBnd : (L : ℝ) ^ d * (ε * nn ^ d) ≤ γ * S := by
    have h1 : nn ≤ 2 * ((d : ℝ) + 1) * L / ρ := by rw [le_div_iff₀ hρ]; linarith
    have h2 : nn ^ d ≤ (2 * ((d : ℝ) + 1) * L / ρ) ^ d := pow_le_pow_left₀ hnnpos.le h1 d
    have h3 : ε * (2 * ((d : ℝ) + 1) * L / ρ) ^ d = γ * (L : ℝ) ^ d := by
      rw [hε, mul_assoc, ← mul_pow]
      congr 2
      field_simp
    have h4 : (L : ℝ) ^ d * (L : ℝ) ^ d = S := by rw [hS, ← mul_pow, sq]
    calc (L : ℝ) ^ d * (ε * nn ^ d) ≤ (L : ℝ) ^ d * (ε * (2 * ((d : ℝ) + 1) * L / ρ) ^ d) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hεpos.le) (by positivity)
      _ = γ * S := by rw [h3, ← h4]; ring
  have hm1 := (abs_le.1 hmid).1
  have : γ * S ≤ 0 := by linarith
  exact absurd this (not_le.2 (mul_pos hγpos hSpos))

end RandomSandpile

import RandomSandpile.Proofs.Sec8.DivisibleHomogenizeDomainExit
import RandomSandpile.Proofs.Sec9.OpenBoundaryLapLipschitz
import LatticeProb.Walk.GreenTwoSided.UpperBound

/-!
# The Green mass of a thin layer around `∂W` inside a larger box

For the confinement radius of Theorem 1.1 the Green potential is taken in a box `D_n` containing
`W_n`, and the boundary layer of `W_n` lies inside `D_n`. This file shows that the killed Green
function of `D_n` gives the layer `{y ∈ W_n : dist(y, ℤ^d ∖ W_n) ≤ γ n}` mass at most `δ n²` once
`γ` is small (`layerMass`). The mass is split into the diagonal term, the sites within distance
`θ n` of the pole, bounded by the weighted occupation estimate `weightedSum_le`, and the remaining
sites, bounded pointwise by the killed Green function bound `killedGreenReal_le_box`
of Lattice-Probability times the number of sites in the layer. The number of sites is at most
`n^d |F_r|` with `F_r = W̄^r ∩ (Wᶜ)‾^r` (`card_layer_le`), by disjoint scaled unit cubes, and
`|F_r| → |∂W| = 0` as `r → 0`.
-/

noncomputable section

open MeasureTheory LatticeProb Filter Topology Metric Set

namespace RandomSandpile

variable {d : ℕ}

/-! ### The diagonal and the split of the Green mass -/

theorem toE_injective_conf : Function.Injective (toE (d := d)) := fun x y h => funext fun i => by
  have := congrArg (fun w : Rd d => w i) h
  simpa [toE] using this

theorem toE_zero_conf : toE (0 : Site d) = 0 := by
  ext i
  simp [toE]

theorem greenKilled_symm (hd : 1 ≤ d) (B : Finset (Site d)) (x y : Site d) :
    greenKilled (B : Set (Site d)) x y = greenKilled (B : Set (Site d)) y x := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := exists_not_mem_finset hd B
  exact Network.killedGreenReal_symm (Graph.Zd.latticeConnected d) B hq x y

/-- The weighted occupation bound, one site at a time. -/
theorem greenKilled_mul_inv_le (hd : 2 ≤ d) {B : Finset (Site d)} {ρ : ℝ}
    (hBρ : ∀ y ∈ B, ‖toE y‖ ≤ ρ) {x z : Site d} (hx : x ∈ B) (hz : z ≠ x) :
    greenKilled (B : Set (Site d)) x z * ‖toE (z - x)‖⁻¹ ≤ 3 * (ρ + 1) := by
  have hw := DivisibleHomogenizeDomain.weightedSum_le hd B.finite_toSet (fun y hy => hBρ y hy) (x := x) hx
  rw [greenPotential_coe_finset] at hw
  by_cases hzB : z ∈ B
  · refine le_trans ?_ hw
    have hterm : greenKilled (B : Set (Site d)) x z * ‖toE (z - x)‖⁻¹ =
        greenKilled (B : Set (Site d)) x z * (if z = x then 0 else ‖toE (z - x)‖⁻¹) := by
      rw [ite_eq_right hz]
    rw [hterm]
    refine Finset.single_le_sum (f := fun y => greenKilled (B : Set (Site d)) x y *
      (if y = x then 0 else ‖toE (y - x)‖⁻¹)) (fun y _ => ?_) hzB
    refine mul_nonneg (greenKilled_nonneg _ _ _) ?_
    split_ifs
    · exact le_rfl
    · positivity
  · rw [greenKilled_eq_zero_of_not_mem_right (by omega) B.finite_toSet x (by exact_mod_cast hzB),
      zero_mul]
    have : (0 : ℝ) ≤ ρ := (norm_nonneg _).trans (hBρ x hx)
    positivity

theorem norm_toE_unit (i : Fin d) : ‖toE (LatticeProb.unit i : Site d)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hu : (LatticeProb.unit i : Site d) = Pi.single i 1 := rfl
  have : ∀ j, ‖(toE (LatticeProb.unit i : Site d)) j‖ ^ 2 = if j = i then 1 else 0 := by
    intro j
    rw [hu]
    by_cases hj : j = i
    · subst hj
      simp [toE]
    · simp [toE, Pi.single_apply, hj]
  rw [Finset.sum_congr rfl fun j _ => this j]
  simp

/-- The diagonal of the killed Green function: `g_B(x, x) ≤ 1 + 3 (ρ + 1)`. -/
theorem greenKilled_self_le (hd : 2 ≤ d) {B : Finset (Site d)} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hBρ : ∀ y ∈ B, ‖toE y‖ ≤ ρ) (x : Site d) :
    greenKilled (B : Set (Site d)) x x ≤ 1 + 3 * (ρ + 1) := by
  have hd1 : 1 ≤ d := by omega
  by_cases hx : x ∈ B
  · have heq := lapR_greenKilled hd1 B.finite_toSet (by exact_mod_cast hx) x
    rw [ite_eq_left rfl, lapR] at heq
    have hnb : ∀ z : Site d, z ≠ x → greenKilled (B : Set (Site d)) z x ≤ 3 * (ρ + 1) *
        ‖toE (z - x)‖ := by
      intro z hz
      have h1 := greenKilled_mul_inv_le hd hBρ hx hz
      rw [greenKilled_symm hd1 B z x]
      have hpos : 0 < ‖toE (z - x)‖ := by
        rw [norm_pos_iff]
        intro h
        exact hz (by simpa [sub_eq_zero] using toE_injective_conf (h.trans toE_zero_conf.symm))
      rwa [← div_eq_mul_inv, div_le_iff₀ hpos] at h1
    have hplus : ∀ i : Fin d, greenKilled (B : Set (Site d)) (x + unit i) x ≤ 3 * (ρ + 1) := by
      intro i
      have h := hnb (x + unit i) (fun h => unit_ne_zero i (by simpa using h))
      rwa [add_sub_cancel_left, norm_toE_unit, mul_one] at h
    have hminus : ∀ i : Fin d, greenKilled (B : Set (Site d)) (x - unit i) x ≤ 3 * (ρ + 1) := by
      intro i
      have h := hnb (x - unit i) (fun h => unit_ne_zero i (by
        have := congrArg (fun z => x - z) h
        simpa using this))
      have e : toE (x - unit i - x) = -toE (unit i : Site d) := by
        rw [show x - unit i - x = -(unit i : Site d) by abel]
        simp [toE]
        rfl
      rwa [e, norm_neg, norm_toE_unit, mul_one] at h
    have hsum : nbrSum (fun z => greenKilled (B : Set (Site d)) z x) x ≤ 2 * d * (3 * (ρ + 1)) := by
      simp only [nbrSum]
      calc ∑ i : Fin d, (greenKilled (B : Set (Site d)) (x + unit i) x +
            greenKilled (B : Set (Site d)) (x - unit i) x)
          ≤ ∑ _i : Fin d, (3 * (ρ + 1) + 3 * (ρ + 1)) :=
            Finset.sum_le_sum fun i _ => add_le_add (hplus i) (hminus i)
        _ = 2 * d * (3 * (ρ + 1)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have h2d : 0 < 2 * (d : ℝ) := by positivity
    have hg : 2 * d * greenKilled (B : Set (Site d)) x x ≤ 1 + 2 * d * (3 * (ρ + 1)) := by
      linarith
    have hg0 := greenKilled_nonneg (B : Set (Site d)) x x
    nlinarith
  · rw [greenKilled_eq_zero_of_not_mem_left _ (by exact_mod_cast hx)]
    positivity

/-- The split of the Green mass of a finite set `S`: the diagonal, the sites within distance `r`
of the pole (weighted occupation), and the far sites, where `g_B(x, ·) ≤ G`. -/
theorem sum_greenKilled_le (hd : 2 ≤ d) {B : Finset (Site d)} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hBρ : ∀ y ∈ B, ‖toE y‖ ≤ ρ) {r G : ℝ} (hr : 0 < r) (hG0 : 0 ≤ G)
    (hG : ∀ x y : Site d, x ≠ y → r < ‖toE (y - x)‖ → greenKilled (B : Set (Site d)) x y ≤ G)
    (S : Finset (Site d)) (x : Site d) :
    ∑ y ∈ S, greenKilled (B : Set (Site d)) x y ≤
      (1 + 3 * (ρ + 1)) + r * (3 * (ρ + 1)) + S.card * G := by
  classical
  set g : Site d → ℝ := fun y => greenKilled (B : Set (Site d)) x y with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => greenKilled_nonneg _ _ _
  by_cases hx : x ∈ B
  · set w : Site d → ℝ := fun y => if y = x then 0 else ‖toE (y - x)‖⁻¹ with hw
    have hw0 : ∀ y, 0 ≤ w y := fun y => by
      simp only [hw]
      split_ifs
      · exact le_rfl
      · positivity
    have hgw : ∑ y ∈ B, g y * w y ≤ 3 * (ρ + 1) := by
      have := DivisibleHomogenizeDomain.weightedSum_le hd B.finite_toSet (fun y hy => hBρ y hy) (x := x) hx
      rwa [greenPotential_coe_finset] at this
    set S₁ := S.filter (fun y => y = x)
    set S₂ := S.filter (fun y => y ≠ x ∧ ‖toE (y - x)‖ ≤ r)
    set S₃ := S.filter (fun y => y ≠ x ∧ r < ‖toE (y - x)‖)
    have hsplit : ∑ y ∈ S, g y ≤ ∑ y ∈ S₁, g y + ∑ y ∈ S₂, g y + ∑ y ∈ S₃, g y := by
      rw [← Finset.sum_union, ← Finset.sum_union]
      · refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) (fun y _ _ => hg0 y)
        simp only [Finset.mem_union, Finset.mem_filter, S₁, S₂, S₃]
        by_cases hyx : y = x
        · exact Or.inl (Or.inl ⟨hy, hyx⟩)
        · rcases le_or_gt ‖toE (y - x)‖ r with h | h
          · exact Or.inl (Or.inr ⟨hy, hyx, h⟩)
          · exact Or.inr ⟨hy, hyx, h⟩
      · refine Finset.disjoint_left.2 fun y hy1 hy2 => ?_
        simp only [Finset.mem_union, Finset.mem_filter, S₁, S₂, S₃] at hy1 hy2
        rcases hy1 with h | h
        · exact hy2.2.1 h.2
        · exact absurd hy2.2.2 (not_lt.2 h.2.2)
      · refine Finset.disjoint_left.2 fun y hy1 hy2 => ?_
        simp only [Finset.mem_filter, S₁, S₂] at hy1 hy2
        exact hy2.2.1 hy1.2
    have h1 : ∑ y ∈ S₁, g y ≤ 1 + 3 * (ρ + 1) := by
      have hsub : S₁ ⊆ {x} := fun y hy => by
        simp only [Finset.mem_filter, S₁] at hy
        simp [hy.2]
      calc ∑ y ∈ S₁, g y ≤ ∑ y ∈ ({x} : Finset (Site d)), g y :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => hg0 y
        _ = g x := Finset.sum_singleton _ _
        _ ≤ 1 + 3 * (ρ + 1) := greenKilled_self_le hd hρ hBρ x
    have h2 : ∑ y ∈ S₂, g y ≤ r * (3 * (ρ + 1)) := by
      have hterm : ∀ y ∈ S₂, g y ≤ r * (g y * w y) := by
        intro y hy
        simp only [Finset.mem_filter, S₂] at hy
        have hpos : 0 < ‖toE (y - x)‖ := by
          rw [norm_pos_iff]
          intro h
          exact hy.2.1 (by simpa [sub_eq_zero] using toE_injective_conf (h.trans toE_zero_conf.symm))
        simp only [hw, ite_eq_right hy.2.1]
        have : 1 ≤ r * ‖toE (y - x)‖⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
          exact hy.2.2
        nlinarith [hg0 y]
      calc ∑ y ∈ S₂, g y ≤ ∑ y ∈ S₂, r * (g y * w y) := Finset.sum_le_sum hterm
        _ = r * ∑ y ∈ S₂, g y * w y := by rw [Finset.mul_sum]
        _ ≤ r * ∑ y ∈ B, g y * w y := by
            refine mul_le_mul_of_nonneg_left ?_ hr.le
            calc ∑ y ∈ S₂, g y * w y = ∑ y ∈ S₂.filter (· ∈ B), g y * w y := by
                  refine (Finset.sum_filter_of_ne fun y _ h => ?_).symm
                  by_contra hyB
                  exact h (by
                    rw [show g y = 0 from greenKilled_eq_zero_of_not_mem_right (by omega)
                      B.finite_toSet x (by exact_mod_cast hyB), zero_mul])
              _ ≤ ∑ y ∈ B, g y * w y :=
                  Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => (Finset.mem_filter.1 hy).2)
                    fun y _ _ => mul_nonneg (hg0 y) (hw0 y)
        _ ≤ r * (3 * (ρ + 1)) := mul_le_mul_of_nonneg_left hgw hr.le
    have h3 : ∑ y ∈ S₃, g y ≤ S.card * G := by
      calc ∑ y ∈ S₃, g y ≤ ∑ _y ∈ S₃, G := Finset.sum_le_sum fun y hy => by
              simp only [Finset.mem_filter, S₃] at hy
              exact hG x y (Ne.symm hy.2.1) hy.2.2
        _ = S₃.card * G := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ S.card * G := mul_le_mul_of_nonneg_right
            (by exact_mod_cast Finset.card_filter_le _ _) hG0
    linarith
  · have h0 : ∑ y ∈ S, g y = 0 := Finset.sum_eq_zero fun y _ =>
      greenKilled_eq_zero_of_not_mem_left _ (by exact_mod_cast hx) y
    rw [h0]
    positivity

/-! ### Counting lattice sites by disjoint cubes -/

/-- The scaled unit cube `n⁻¹ (y + [0, 1)^d)`. -/
def scaledCube (n : ℕ) (y : Site d) : Set (Rd d) :=
  {z | ∀ i, (y i : ℝ) ≤ n * z i ∧ n * z i < y i + 1}

theorem scaledCube_eq_preimage (n : ℕ) (hn : 1 ≤ n) (y : Site d) :
    scaledCube n y = (WithLp.ofLp (p := 2) (V := Fin d → ℝ)) ⁻¹'
      Set.pi Set.univ (fun i => Set.Ico ((y i : ℝ) / n) (((y i : ℝ) + 1) / n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  ext z
  simp only [scaledCube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    true_implies, Set.mem_Ico, div_le_iff₀ hn0, lt_div_iff₀ hn0]
  constructor
  · intro h i
    exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩
  · intro h i
    exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩

/-- **Counting.** If the cubes of the sites of `S` lie in a measurable `U` of finite measure, then
`|S| ≤ n^d |U|`. -/
theorem card_le_volume {S : Finset (Site d)} {n : ℕ} (hn : 1 ≤ n) {U : Set (Rd d)}
    (hU : ∀ y ∈ S, scaledCube n y ⊆ U) (hUf : volume U ≠ ⊤) :
    (S.card : ℝ) ≤ (n : ℝ) ^ d * volume.real U := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hvol : ∀ y : Site d, volume (scaledCube n y) = ENNReal.ofReal ((n : ℝ)⁻¹) ^ d := by
    intro y
    rw [scaledCube_eq_preimage n hn y,
      (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet,
      Real.volume_pi_Ico]
    rw [Finset.prod_congr rfl fun i _ => show ENNReal.ofReal (((y i : ℝ) + 1) / n - (y i : ℝ) / n) =
      ENNReal.ofReal ((n : ℝ)⁻¹) by congr 1; ring]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmeas : ∀ y : Site d, MeasurableSet (scaledCube n y) := fun y => by
    rw [scaledCube_eq_preimage n hn y]
    exact (PiLp.volume_preserving_ofLp (Fin d)).measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
  have hdisj : Set.PairwiseDisjoint (S : Set (Site d)) (scaledCube n) := by
    intro y _ y' _ hyy'
    refine Set.disjoint_left.2 fun z hz hz' => hyy' (funext fun i => ?_)
    obtain ⟨h1, h2⟩ := hz i
    obtain ⟨h1', h2'⟩ := hz' i
    have a : y i ≤ y' i := by
      have : (y i : ℝ) < y' i + 1 := lt_of_le_of_lt h1 h2'
      exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast this)
    have b : y' i ≤ y i := by
      have : (y' i : ℝ) < y i + 1 := lt_of_le_of_lt h1' h2
      exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast this)
    exact le_antisymm a b
  have hU' : (⋃ y ∈ S, scaledCube n y) ⊆ U := Set.iUnion₂_subset fun y hy => hU y hy
  have hsum := measure_biUnion_finset (μ := volume) hdisj fun y _ => hmeas y
  have hle : volume (⋃ y ∈ S, scaledCube n y) ≤ volume U := measure_mono hU'
  rw [hsum] at hle
  simp only [hvol, Finset.sum_const, nsmul_eq_mul] at hle
  have hreal := ENNReal.toReal_mono hUf hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_natCast] at hreal
  have hnd : (0 : ℝ) < (n : ℝ) ^ d := by positivity
  calc (S.card : ℝ) = (n : ℝ) ^ d * ((S.card : ℝ) * ((n : ℝ)⁻¹) ^ d) := by
        rw [mul_left_comm, ← mul_pow, mul_inv_cancel₀ hn0.ne', one_pow, mul_one]
    _ ≤ (n : ℝ) ^ d * volume.real U := mul_le_mul_of_nonneg_left hreal hnd.le

/-! ### The neighbourhood of the frontier -/

/-- The points within distance `r` of both `W` and its complement. -/
def frontierNbhd (W : Set (Rd d)) (r : ℝ) : Set (Rd d) := cthickening r W ∩ cthickening r Wᶜ

theorem tendsto_volume_frontierNbhd {W : Set (Rd d)} (hb : Bornology.IsBounded W)
    (hf : volume (frontier W) = 0) :
    Tendsto (fun r => volume (frontierNbhd W r)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_measure_biInter_gt (μ := volume) (s := frontierNbhd W) (a := (0 : ℝ))
    (fun r _ => (isClosed_cthickening.inter isClosed_cthickening).measurableSet.nullMeasurableSet)
    (fun i j _ hij => inter_subset_inter (cthickening_mono hij W) (cthickening_mono hij Wᶜ))
    ⟨1, one_pos, ((measure_mono inter_subset_left).trans_lt
      (hb.cthickening (δ := 1)).measure_lt_top).ne⟩
  have hI : (⋂ r > (0 : ℝ), frontierNbhd W r) = frontier W := by
    rw [frontier_eq_closure_inter_closure, closure_eq_iInter_cthickening,
      closure_eq_iInter_cthickening]
    ext z
    simp only [frontierNbhd, mem_iInter, mem_inter_iff]
    exact ⟨fun h => ⟨fun r hr => (h r hr).1, fun r hr => (h r hr).2⟩,
      fun h r hr => ⟨h.1 r hr, h.2 r hr⟩⟩
  rw [hI, hf] at h
  exact h

/-- The norm of a point of `[0, 1)^d` is less than `√d`. -/
theorem norm_lt_sqrt_of_mem_unitCube (hd : 1 ≤ d) {c : Rd d} (hc : ∀ i, 0 ≤ c i ∧ c i < 1) :
    ‖c‖ < Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_lt_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  calc ∑ i, ‖c i‖ ^ 2 < ∑ _i : Fin d, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty hne fun i _ => by
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [(hc i).1, (hc i).2]
    _ = d := by simp

/-- The cube of a site of the layer of width `γ n` lies in `frontierNbhd W (γ + √d / n)`. -/
theorem scaledCube_subset_frontierNbhd (hd : 1 ≤ d) {W : Set (Rd d)} {n : ℕ} (hn : 1 ≤ n)
    {γ : ℝ} {y : Site d} (hyW : y ∈ discretize W n)
    (hyL : y ∈ nearCompl (discretize W n) (γ * n)) :
    scaledCube n y ⊆ frontierNbhd W (γ + Real.sqrt d / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnz : (n : ℝ) ≠ 0 := hn0.ne'
  obtain ⟨z, hz, hzy⟩ := hyL
  have ha : (n : ℝ)⁻¹ • toE y ∈ W := (Set.mem_smul_set_iff_inv_smul_mem₀ hnz _ _).1 hyW
  have hb : (n : ℝ)⁻¹ • toE z ∉ W := fun h => hz ((Set.mem_smul_set_iff_inv_smul_mem₀ hnz _ _).2 h)
  have hsub : toE z - toE y = toE (z - y) := by
    ext i
    simp [toE]
  have hab : dist ((n : ℝ)⁻¹ • toE y) ((n : ℝ)⁻¹ • toE z) ≤ γ := by
    rw [dist_comm, dist_eq_norm, ← smul_sub, hsub, norm_smul, norm_inv, Real.norm_natCast,
      inv_mul_le_iff₀ hn0]
    linarith [hzy]
  intro c hc
  have hcd : dist c ((n : ℝ)⁻¹ • toE y) ≤ Real.sqrt d / n := by
    have hcoord : ∀ i, ((n : ℝ) • c - toE y) i = n * c i - y i := fun i => by simp [toE]
    have hmem : ∀ i, 0 ≤ ((n : ℝ) • c - toE y) i ∧ ((n : ℝ) • c - toE y) i < 1 := fun i => by
      rw [hcoord]
      obtain ⟨h1, h2⟩ := hc i
      constructor <;> linarith
    have hlt := norm_lt_sqrt_of_mem_unitCube hd hmem
    rw [dist_eq_norm, le_div_iff₀ hn0]
    have : (n : ℝ) • c - toE y = (n : ℝ) • (c - (n : ℝ)⁻¹ • toE y) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hnz, one_smul]
    rw [this, norm_smul, Real.norm_natCast] at hlt
    linarith
  have hγ : 0 ≤ γ := le_trans dist_nonneg hab
  refine ⟨mem_cthickening_of_dist_le c _ _ _ ha (by linarith [Real.sqrt_nonneg (d : ℝ)]),
    mem_cthickening_of_dist_le c _ _ _ hb ?_⟩
  calc dist c ((n : ℝ)⁻¹ • toE z) ≤ dist c ((n : ℝ)⁻¹ • toE y) +
        dist ((n : ℝ)⁻¹ • toE y) ((n : ℝ)⁻¹ • toE z) := dist_triangle _ _ _
    _ ≤ γ + Real.sqrt d / n := by linarith

/-! ### The layer mass -/

theorem norm_toE_le_of_abs_lt {y : Site d} {M : ℝ} (hM : 0 ≤ M) (hy : ∀ i, |(y i : ℝ)| ≤ M) :
    ‖toE y‖ ≤ Real.sqrt d * M := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hM, ← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖toE y i‖ ^ 2 ≤ ∑ _i : Fin d, M ^ 2 := Finset.sum_le_sum fun i _ => by
        have : ‖toE y i‖ = |(y i : ℝ)| := by simp [toE]
        rw [this, sq_abs]
        nlinarith [hy i, abs_nonneg (y i : ℝ), sq_abs (y i : ℝ)]
    _ = d * M ^ 2 := by simp

/-- **The layer mass.** Let `W` be bounded with null frontier. For every `δ > 0` there are `γ > 0`
and `n₀` such that for `n ≥ n₀`, every finite `D ⊆ {‖x‖_∞ < 2an}` and every finite set `L` of
sites of `W_n` within distance `γ n` of `ℤ^d ∖ W_n`, the killed Green function of `D` gives `L`
mass at most `δ n²` from every pole. -/
theorem layerMass (hd : 2 ≤ d) {W : Set (Rd d)} (hb : Bornology.IsBounded W)
    (hf : volume (frontier W) = 0) {a : ℕ} (ha : 1 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ D L : Finset (Site d),
      (∀ y ∈ D, ∀ i, |y i| < 2 * a * n) →
      (∀ y ∈ L, y ∈ discretize W n ∧
        y ∈ nearCompl (discretize W n) (γ * n)) →
      ∀ x : Site d, ∑ y ∈ L, greenKilled (D : Set (Site d)) x y ≤ δ * (n : ℝ) ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC0, hC⟩ := GreenTwoSided.killedGreenReal_le_box (d := d) hd1
  set A : ℝ := (a : ℝ) with hAdef
  have hA : (1 : ℝ) ≤ A := by simp only [hAdef]; exact_mod_cast ha
  set sd : ℝ := Real.sqrt d with hsd
  have hs : 0 ≤ sd := Real.sqrt_nonneg _
  set c₁ : ℝ := 3 * (2 * A * sd + 2) with hc₁def
  have hc₁ : 0 < c₁ := by positivity
  set θ : ℝ := δ / (3 * c₁) with hθdef
  have hθ : 0 < θ := by positivity
  set c₂ : ℝ := C * (9 * A ^ 2) * (1 / θ ^ d + 1) with hc₂def
  have hc₂ : 0 < c₂ := by positivity
  have hlim := tendsto_volume_frontierNbhd hb hf
  have hev := hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity :
    (0 : ℝ) < δ / (3 * c₂))))
  obtain ⟨r₀, hr₀, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  set γ : ℝ := r₀ / 4 with hγdef
  have hγ : 0 < γ := div_pos hr₀ (by norm_num)
  refine ⟨γ, hγ, max (max 1 ⌈sd / γ⌉₊) ⌈3 * (4 + 6 * A * sd) / δ⌉₊, ?_⟩
  intro n hn D L hD hL x
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) (le_of_max_le_left hn)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hmax1 : ⌈sd / γ⌉₊ ≤ n := le_trans (le_max_right _ _) (le_of_max_le_left hn)
  have hnγ : sd / γ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hmax1)
  have hmax2 : ⌈3 * (4 + 6 * A * sd) / δ⌉₊ ≤ n := le_of_max_le_right hn
  have hnδ : 3 * (4 + 6 * A * sd) / δ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hmax2)
  -- The geometry of `D`.
  set ρ : ℝ := sd * (2 * A * n) with hρdef
  have hρ : 0 ≤ ρ := by positivity
  have hDρ : ∀ y ∈ D, ‖toE y‖ ≤ ρ := fun y hy => norm_toE_le_of_abs_lt (by positivity)
    fun i => by
      have h1 := hD y hy i
      have h2 : ((|y i| : ℤ) : ℝ) < (((2 * a * n : ℕ) : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      have h' : |(y i : ℝ)| < 2 * A * n := by simpa only [hAdef] using h2
      exact h'.le
  set Lb : ℕ := 2 * a * n with hLb
  have hDbox : ∀ z ∈ D, z ∈ box d Lb := fun z hz i => by
    have := hD z hz i
    simp only [hLb]
    push_cast
    omega
  set G : ℝ := C * ((Lb : ℝ) + 1) ^ 2 * (1 / (θ * n) ^ d + 1 / ((Lb : ℝ) + 1) ^ d) with hGdef
  have hG0 : 0 ≤ G := by positivity
  have hGfar : ∀ x y : Site d, x ≠ y → θ * n < ‖toE (y - x)‖ →
      greenKilled (D : Set (Site d)) x y ≤ G := by
    intro x y hxy hfar
    refine (hC Lb D hDbox x y hxy).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (by positivity)
    have hnorm : ‖toE (y - x)‖ ≤ (graphNorm (x - y) : ℝ) := by
      have h := OpenBoundaryLapLipschitz.norm_toE_le_graphNorm (x - y)
      have e : toE (x - y) = -toE (y - x) := by
        ext i
        simp [toE]
      rwa [e, norm_neg] at h
    have hpos : 0 < θ * n := by positivity
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ hpos.le (hfar.le.trans hnorm) d)
  have hsplit := sum_greenKilled_le hd hρ hDρ (by positivity : (0 : ℝ) < θ * n) hG0 hGfar L x
  -- The number of sites of the layer.
  have hcube : ∀ y ∈ L, scaledCube n y ⊆ frontierNbhd W (γ + sd / n) := fun y hy =>
    scaledCube_subset_frontierNbhd hd1 hn1 (hL y hy).1 (hL y hy).2
  have hFfin : volume (frontierNbhd W (γ + sd / n)) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt (hb.cthickening).measure_lt_top).ne
  have hcard := card_le_volume hn1 hcube hFfin
  have hsdn : sd / n ≤ γ := by
    rw [div_le_iff₀ hn0]
    rw [div_le_iff₀ hγ] at hnγ
    linarith
  have hFvol : volume.real (frontierNbhd W (γ + sd / n)) ≤ δ / (3 * c₂) := by
    have hr : γ + sd / n ∈ Ioo 0 r₀ := ⟨by positivity, by linarith⟩
    have h := hsub hr
    have h' : volume (frontierNbhd W (γ + sd / n)) ≤ ENNReal.ofReal (δ / (3 * c₂)) := le_of_lt h
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h'
  -- The three terms.
  have hρ' : ρ = 2 * (A * sd) * n := by simp only [hρdef]; ring
  have hT1 : 1 + 3 * (ρ + 1) ≤ δ / 3 * (n : ℝ) ^ 2 := by
    have e1 : 1 + 3 * (ρ + 1) = 4 + 6 * (A * sd) * n := by rw [hρ']; ring
    have hAs : 0 ≤ A * sd := by positivity
    have h1 : 1 + 3 * (ρ + 1) ≤ (4 + 6 * A * sd) * n := by
      have e2 : (4 + 6 * A * sd) * n = 4 * n + 6 * (A * sd) * n := by ring
      rw [e1, e2]
      linarith only [hnR]
    have h2 : 4 + 6 * A * sd ≤ δ / 3 * n := by
      rw [div_le_iff₀ hδ] at hnδ
      linarith only [hnδ]
    calc 1 + 3 * (ρ + 1) ≤ (4 + 6 * A * sd) * n := h1
      _ ≤ (δ / 3 * n) * n := mul_le_mul_of_nonneg_right h2 hn0.le
      _ = δ / 3 * (n : ℝ) ^ 2 := by ring
  have hT2 : θ * n * (3 * (ρ + 1)) ≤ δ / 3 * (n : ℝ) ^ 2 := by
    have h1 : 3 * (ρ + 1) ≤ c₁ * n := by
      have e1 : 3 * (ρ + 1) = 6 * (A * sd) * n + 3 := by rw [hρ']; ring
      have e2 : c₁ * n = 6 * (A * sd) * n + 6 * n := by simp only [hc₁def]; ring
      rw [e1, e2]
      linarith only [hnR]
    have h2 : θ * c₁ = δ / 3 := by
      simp only [hθdef]
      field_simp
    calc θ * n * (3 * (ρ + 1)) ≤ θ * n * (c₁ * n) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = θ * c₁ * (n : ℝ) ^ 2 := by ring
      _ = δ / 3 * (n : ℝ) ^ 2 := by rw [h2]
  have hT3 : (L.card : ℝ) * G ≤ δ / 3 * (n : ℝ) ^ 2 := by
    have hLbR : (Lb : ℝ) = 2 * A * n := by simp only [hLb, hAdef]; push_cast; ring
    have hAn : (1 : ℝ) ≤ A * n := one_le_mul_of_one_le_of_one_le hA hnR
    have hLb1 : (Lb : ℝ) + 1 ≤ 3 * A * n := by
      rw [hLbR]
      have e : 3 * A * n = 2 * A * n + A * n := by ring
      rw [e]
      linarith only [hAn]
    have hnLb : (n : ℝ) ≤ (Lb : ℝ) + 1 := by
      rw [hLbR]
      have : (n : ℝ) ≤ A * n := le_mul_of_one_le_left hn0.le hA
      linarith only [this, hAn]
    have hnG : (n : ℝ) ^ d * G ≤ C * (9 * A ^ 2 * (n : ℝ) ^ 2) * (1 / θ ^ d + 1) := by
      have e1 : (n : ℝ) ^ d * (1 / (θ * n) ^ d) = 1 / θ ^ d := by
        rw [mul_pow]
        field_simp
      have e2 : (n : ℝ) ^ d * (1 / ((Lb : ℝ) + 1) ^ d) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        exact pow_le_pow_left₀ hn0.le hnLb d
      have hsq : ((Lb : ℝ) + 1) ^ 2 ≤ 9 * A ^ 2 * (n : ℝ) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hLb1 2
        calc ((Lb : ℝ) + 1) ^ 2 ≤ (3 * A * n) ^ 2 := this
          _ = 9 * A ^ 2 * (n : ℝ) ^ 2 := by ring
      calc (n : ℝ) ^ d * G = C * ((Lb : ℝ) + 1) ^ 2 * ((n : ℝ) ^ d * (1 / (θ * n) ^ d) +
            (n : ℝ) ^ d * (1 / ((Lb : ℝ) + 1) ^ d)) := by simp only [hGdef]; ring
        _ ≤ C * (9 * A ^ 2 * (n : ℝ) ^ 2) * (1 / θ ^ d + 1) := by
            rw [e1]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hsq hC0.le) (add_le_add le_rfl e2)
              (by positivity) (by positivity)
    calc (L.card : ℝ) * G ≤ ((n : ℝ) ^ d * (δ / (3 * c₂))) * G :=
          mul_le_mul_of_nonneg_right (hcard.trans (mul_le_mul_of_nonneg_left hFvol
            (by positivity))) hG0
      _ = δ / (3 * c₂) * ((n : ℝ) ^ d * G) := by ring
      _ ≤ δ / (3 * c₂) * (C * (9 * A ^ 2 * (n : ℝ) ^ 2) * (1 / θ ^ d + 1)) :=
          mul_le_mul_of_nonneg_left hnG (by positivity)
      _ = δ / 3 * (n : ℝ) ^ 2 := by
          simp only [hc₂def]
          field_simp
  linarith

end RandomSandpile

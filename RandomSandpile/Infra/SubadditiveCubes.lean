import RandomSandpile.Defs.Subadditive
import LatticeProb.Prob.AkcogluKrengelAE.Assembly
import LatticeProb.Prob.AkcogluKrengelAE.BoxTiling

/-! # The subadditive ergodic theorem on cubes and on rational boxes

This file proves the cube part of the multiparameter subadditive ergodic theorem (Proposition 5.3,
`SubadditiveErgodicStmt`) from Lattice-Probability's Akcoglu–Krengel theorem
`LatticeProb.akcoglu_krengel` (cubes `[0, n)^d`, random limit, subadditivity over box splits).

* `ae_eq_integral_of_ae_invariant`: on an ergodic `ℤ^d`-system an a.e. invariant integrable
  function is a.e. equal to its mean.
* `anchoredBoxErgodic`: the pointwise ergodic theorem along anchored boxes `∏ [0, ⌈N cᵢ⌉)` with a
  constant limit (`LatticeProb.AnchoredBoxErgodic`, left as hypotheses in the library), hence by
  `LatticeProb.RectangleErgodic_of_AnchoredBox` along the rectangles `∏ [⌈N aᵢ⌉, ⌈N bᵢ⌉)`,
  `0 ≤ a ≤ b`.
* `exists_ae_tendsto_cube`: a subadditive process `f` (`IsSubadditiveProcess`) satisfies the
  hypotheses of `akcoglu_krengel`, so `f(η, [0, n)^d) / n^d` converges almost surely.
* `exists_ae_tendsto_cube_const`: the limit is almost surely a constant `a ∈ [0, C]` (stationarity
  and ergodicity of the random environment).
* `subadditive_tiling_le`: tiling a finite set by translates of `[0, k)^d` along the `k^d` residue
  classes modulo `k`.
* `subadditiveOrthantBoxes`: almost surely, simultaneously for every half-open box `Q` with
  rational corners in the closed positive orthant, `f(nQ ∩ ℤ^d) / |nQ ∩ ℤ^d| → a`.

The lower bound for boxes that meet the coordinate hyperplanes on both sides (for instance
`[-1, 1)^d`) is not reached by this route: subadditivity gives a lower bound for `f(B)` only through
a set containing `B` whose value is controlled from below, and `akcoglu_krengel` controls only cubes
with a corner at the origin. See `SubadditiveRationalBoxesStmt`. -/

noncomputable section

open MeasureTheory Filter Topology LatticeProb
open scoped Pointwise

namespace RandomSandpile

/-! ### Ergodic lemmas for a `ℤ^d`-action -/

section Ergodic

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- On an ergodic `ℤ^d`-system, a measurable integrable function which is almost surely invariant
under each translation is almost surely equal to its mean. The event `{∀ y, G (σ y ω) ≤ ∫ G}` is
exactly invariant, and it agrees almost surely with `{G ≤ ∫ G}`. -/
theorem ae_eq_integral_of_ae_invariant (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Site d → Ω → Ω) (hσ : ∀ z, Measurable (σ z))
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    (herg : ∀ A : Set Ω, MeasurableSet A → (∀ z, σ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1)
    {G : Ω → ℝ} (hGm : Measurable G) (hGi : Integrable G μ)
    (hinv : ∀ z, ∀ᵐ ω ∂μ, G (σ z ω) = G ω) :
    ∀ᵐ ω ∂μ, G ω = ∫ ω, G ω ∂μ := by
  set c := ∫ ω, G ω ∂μ with hc
  set A : Set Ω := {ω | ∀ y, G (σ y ω) ≤ c} with hA
  have hAm : MeasurableSet A := by
    have : A = ⋂ y, σ y ⁻¹' {ω | G ω ≤ c} := by
      ext ω; simp [A]
    rw [this]
    exact MeasurableSet.iInter fun y => (hσ y) (measurableSet_le hGm measurable_const)
  have hAinv : ∀ z, σ z ⁻¹' A = A := by
    intro z
    ext ω
    simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · intro h y
      have := h (y - z)
      rwa [← hσadd, sub_add_cancel] at this
    · intro h y
      rw [← hσadd]
      exact h _
  have hall : ∀ᵐ ω ∂μ, ∀ y, G (σ y ω) = G ω := ae_all_iff.2 hinv
  have hAe : ∀ᵐ ω ∂μ, (ω ∈ A ↔ G ω ≤ c) := by
    filter_upwards [hall] with ω hω
    simp only [A, Set.mem_ofPred_eq, hω]
    exact ⟨fun h => h 0, fun h _ => h⟩
  have hci : Integrable (fun _ : Ω => c) μ := integrable_const c
  rcases herg A hAm hAinv with h0 | h1
  · have hnot : ∀ᵐ ω ∂μ, ω ∉ A := measure_eq_zero_iff_ae_notMem.1 h0
    have hle : (fun _ : Ω => c) ≤ᵐ[μ] G := by
      filter_upwards [hnot, hAe] with ω h1 h2
      exact le_of_lt (not_le.1 fun h => h1 (h2.2 h))
    have heq := (integral_eq_iff_of_ae_le hci hGi hle).1 (by simp [c])
    filter_upwards [heq] with ω hω
    exact hω.symm
  · have hin : ∀ᵐ ω ∂μ, ω ∈ A := mem_ae_iff.2 ((prob_compl_eq_zero_iff hAm).2 h1)
    have hle : G ≤ᵐ[μ] (fun _ : Ω => c) := by
      filter_upwards [hin, hAe] with ω h1 h2
      exact h2.1 h1
    have heq := (integral_eq_iff_of_ae_le hGi hci hle).1 (by simp [c])
    filter_upwards [heq] with ω hω
    exact hω

/-- Almost sure invariance under the translations by `y ≥ 0` gives almost sure invariance under
every translation: write `y = y⁺ - y⁻` and use that `σ y⁻` preserves the measure. -/
theorem ae_invariant_of_ae_invariant_nonneg (μ : Measure Ω) (σ : Site d → Ω → Ω)
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {G : Ω → ℝ} (hGm : Measurable G)
    (h : ∀ y : Site d, 0 ≤ y → ∀ᵐ ω ∂μ, G (σ y ω) = G ω) :
    ∀ y, ∀ᵐ ω ∂μ, G (σ y ω) = G ω := by
  intro y
  have hu := h y⁺ (posPart_nonneg y)
  have hv := h y⁻ (negPart_nonneg y)
  have hyv : y + y⁻ = y⁺ := (sub_eq_iff_eq_add.1 (posPart_sub_negPart y)).symm
  have key : ∀ᵐ ω ∂μ, G (σ y (σ y⁻ ω)) = G (σ y⁻ ω) := by
    filter_upwards [hu, hv] with ω h1 h2
    rw [← hσadd, hyv, h1, h2]
  have hmeas : MeasurableSet {ω | G (σ y ω) = G ω} :=
    measurableSet_eq_fun (hGm.comp (hσ y).measurable) hGm
  rw [← (hσ y⁻).map_eq, ae_map_iff (hσ y⁻).measurable.aemeasurable hmeas]
  exact key

end Ergodic

/-! ### The pointwise ergodic theorem along anchored boxes -/

section AnchoredBox

/-- **The anchored-box ergodic theorem** (`LatticeProb.AnchoredBoxErgodic`): for an ergodic
measure-preserving `ℤ^d`-action and a bounded measurable `h`,
`N^{-d} ∑_{x ∈ ∏ [0, ⌈N cᵢ⌉)} h(σ_x ω) → (∏ cᵢ) ∫ h` almost surely. The box limit `G` of
`exists_ae_tendsto_boxAvg` is invariant under the unit translations, hence under every
translation, so it is almost surely constant; it has the mean of `h` because it agrees with the
limit of `exists_ae_tendsto_anchoredBox_with_integral`. -/
theorem anchoredBoxErgodic {d : ℕ} (hd : 1 ≤ d) : AnchoredBoxErgodic d := by
  intro Ω _ μ _ σ hσ hσadd herg h hh hbdd c hc
  obtain ⟨M, hM, hb⟩ := hbdd
  by_cases hpos : ∀ i, 0 < c i
  · obtain ⟨G, hGm, hGb, hGconv, hGinv⟩ :=
      exists_ae_tendsto_boxAvg hσ hσadd hh hM hb Finset.univ
    obtain ⟨G', _hG'm, _hG'b, hG'int, hG'conv⟩ :=
      exists_ae_tendsto_anchoredBox_with_integral hσ hσadd hh hM hb hc
    have hmi : ∀ i, Tendsto (fun N : ℕ => ⌈(N : ℝ) * c i⌉.toNat) atTop atTop :=
      fun i => tendsto_ceil_toNat_atTop (hpos i)
    have hconv := hGconv (fun N i => ⌈(N : ℝ) * c i⌉.toNat) (fun i _ => hmi i)
    have hscale : Tendsto (fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) *
        ((N : ℝ) ^ (-(d : ℝ)))) atTop (𝓝 (∏ i, c i)) := by
      have h := tendsto_prod_ceil_toNat_div_pow hc
      have heq : (fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) *
          ((N : ℝ) ^ (-(d : ℝ)))) =
          fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) / (N : ℝ) ^ d := by
        funext N
        rw [Real.rpow_neg (Nat.cast_nonneg N) (d : ℝ), Real.rpow_natCast (N : ℝ) d,
          div_eq_mul_inv]
      rw [heq]; exact h
    have hconvG : ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
        ∑ x ∈ anchoredBox c N, h (σ x ω)) atTop (𝓝 ((∏ i, c i) * G ω)) := by
      filter_upwards [hconv] with ω hω
      have heq : (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, h (σ x ω)) =
          fun N : ℕ => (∏ i, (⌈(N : ℝ) * c i⌉.toNat : ℝ)) * ((N : ℝ) ^ (-(d : ℝ))) *
              boxAvg σ h Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω := by
        funext N
        rw [anchoredBox_eq_intBox hc N,
          ← sum_boxGridSet_eq_sum_intBox Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat)
              (fun x => h (σ x ω)),
          sum_boxGridSet_eq_boxAvg_mul σ h Finset.univ (fun i => ⌈(N : ℝ) * c i⌉.toNat) ω]
        ring
      rw [heq]
      exact hscale.mul hω
    have hprod : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hpos i).ne'
    have hGG' : ∀ᵐ ω ∂μ, G ω = G' ω := by
      filter_upwards [hconvG, hG'conv] with ω h1 h2
      exact mul_left_cancel₀ hprod (tendsto_nhds_unique h1 h2)
    have hGint : ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ := by rw [integral_congr_ae hGG', hG'int]
    -- `G` is invariant under every translation.
    let j0 : Fin d := ⟨0, hd⟩
    have hG0 : G ∘ σ 0 = G := by
      funext ω
      have h1 := congrFun (hGinv j0 (Finset.mem_univ _)) (σ 0 ω)
      have h2 := congrFun (hGinv j0 (Finset.mem_univ _)) ω
      simp only [Function.comp_apply] at h1 h2
      rw [Function.comp_apply, ← h1, ← hσadd, add_zero, h2]
    let Z : AddSubgroup (Site d) :=
      { carrier := {z | G ∘ σ z = G}
        zero_mem' := hG0
        add_mem' := by
          intro z w hz hw
          simp only [Set.mem_ofPred_eq] at hz hw ⊢
          funext ω
          have h1 := congrFun hz (σ w ω)
          have h2 := congrFun hw ω
          simp only [Function.comp_apply] at h1 h2 ⊢
          rw [hσadd, h1, h2]
        neg_mem' := by
          intro z hz
          simp only [Set.mem_ofPred_eq] at hz ⊢
          funext ω
          have h1 := congrFun hz (σ (-z) ω)
          have h2 := congrFun hG0 ω
          simp only [Function.comp_apply] at h1 h2 ⊢
          rw [← h1, ← hσadd, add_neg_cancel, h2] }
    have hunit : ∀ i, unit i ∈ Z := fun i => hGinv i (Finset.mem_univ _)
    have hall : ∀ z, z ∈ Z := by
      intro z
      have hz : z = ∑ i, (z i) • unit i := by
        ext j
        simp [unit, Pi.single_apply]
      rw [hz]
      exact Z.sum_mem fun i _ => Z.zsmul_mem (hunit i) _
    have hGi : Integrable G μ :=
      Integrable.of_bound hGm.aestronglyMeasurable M
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb x)
    have hconst := ae_eq_integral_of_ae_invariant μ σ (fun z => (hσ z).measurable) hσadd herg
      hGm hGi (fun z => Eventually.of_forall fun ω => congrFun (hall z) ω)
    filter_upwards [hconvG, hconst] with ω h1 h2
    rwa [h2, hGint] at h1
  · simp only [not_forall, not_lt] at hpos
    obtain ⟨i, hi⟩ := hpos
    have hci : c i = 0 := le_antisymm hi (hc i)
    filter_upwards with ω
    have hemp : ∀ N : ℕ, anchoredBox c N = ∅ := by
      intro N
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_anchoredBox] at hx
      have := hx i
      rw [hci, mul_zero, Int.ceil_zero, Finset.mem_Ico] at this
      omega
    have hprod : (∏ i, c i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hci
    have hconst : (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
        ∑ x ∈ anchoredBox c N, h (σ x ω)) = fun _ : ℕ => 0 := by
      funext N
      rw [hemp N, Finset.sum_empty, mul_zero]
    rw [hconst, hprod, zero_mul]
    exact tendsto_const_nhds

/-- **The rectangle ergodic theorem** (`LatticeProb.RectangleErgodic`): along the rectangles
`∏ [⌈N aᵢ⌉, ⌈N bᵢ⌉)` with `0 ≤ a ≤ b`. -/
theorem rectangleErgodic {d : ℕ} (hd : 1 ≤ d) : RectangleErgodic d :=
  RectangleErgodic_of_AnchoredBox (anchoredBoxErgodic hd)

end AnchoredBox

/-! ### Subadditive set functions on finite sets: tiling by cubes -/

section Tiling

variable {d : ℕ}

/-- The translate `z + [0, k)^d` of the cube `[0, k)^d`. -/
def cell (k : ℕ) (z : Site d) : Finset (Site d) :=
  (latticeCube d k).map (Equiv.addRight z).toEmbedding

theorem coe_map_addRight (A : Finset (Site d)) (z : Site d) :
    (↑(A.map (Equiv.addRight z).toEmbedding) : Set (Site d)) = z +ᵥ (↑A : Set (Site d)) := by
  ext x
  simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe,
    Equiv.coe_addRight, Set.mem_vadd_set, vadd_eq_add]
  constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, add_comm _ _⟩

theorem mem_cell {k : ℕ} {z x : Site d} : x ∈ cell k z ↔ ∀ i, z i ≤ x i ∧ x i < z i + k := by
  simp only [cell, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.coe_addRight, latticeCube,
    Finset.mem_Icc]
  constructor
  · rintro ⟨a, ⟨ha0, ha1⟩, rfl⟩ i
    have h0 := ha0 i
    have h1 := ha1 i
    simp only [Pi.zero_apply, Pi.add_apply] at h0 h1 ⊢
    omega
  · intro h
    refine ⟨x - z, ⟨fun i => ?_, fun i => ?_⟩, by simp⟩ <;>
      simp only [Pi.zero_apply, Pi.sub_apply] <;> have := h i <;> omega

theorem card_cell (k : ℕ) (z : Site d) : (cell k z).card = k ^ d := by
  rw [cell, Finset.card_map, card_latticeCube_eq_pow]

/-- Subadditivity over two disjoint finite sets. -/
theorem subadditive_union {g : Set (Site d) → ℝ} (hg : IsSubadditive g) {A B : Finset (Site d)}
    (hAB : Disjoint A B) : g ↑(A ∪ B) ≤ g ↑A + g ↑B := by
  have h := hg 2 ↑(A ∪ B) ![↑A, ↑B] (Finset.finite_toSet _)
    (by intro j; fin_cases j <;> exact Finset.finite_toSet _) ?_ ?_
  · simpa [Fin.sum_univ_two] using h
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [Function.onFun] using hAB
    · simpa [Function.onFun] using hAB.symm
    · exact absurd rfl hij
  · ext x
    simp [Fin.exists_fin_two]

/-- Subadditivity over pairwise disjoint cells inside `S`, with the remainder. -/
theorem subadditive_le_sum_cells {g : Set (Site d) → ℝ} (hg : IsSubadditive g)
    (S : Finset (Site d)) (k : ℕ) (G : Finset (Site d)) (hsub : ∀ z ∈ G, cell k z ⊆ S)
    (hdisj : ∀ z ∈ G, ∀ z' ∈ G, z ≠ z' → Disjoint (cell k z) (cell k z')) :
    g ↑S ≤ ∑ z ∈ G, g ↑(cell k z) + g ↑(S \ G.biUnion (cell k)) := by
  induction G using Finset.induction_on with
  | empty => simp
  | insert z₀ G hz₀ ih =>
    have ih' := ih (fun z hz => hsub z (Finset.mem_insert_of_mem hz))
      (fun z hz z' hz' => hdisj z (Finset.mem_insert_of_mem hz) z' (Finset.mem_insert_of_mem hz'))
    set R := S \ G.biUnion (cell k) with hR
    have hcR : cell k z₀ ⊆ R := by
      intro x hx
      rw [hR, Finset.mem_sdiff, Finset.mem_biUnion]
      refine ⟨hsub z₀ (Finset.mem_insert_self _ _) hx, ?_⟩
      rintro ⟨z, hz, hxz⟩
      have hne : z₀ ≠ z := fun h => hz₀ (h ▸ hz)
      exact Finset.disjoint_left.1
        (hdisj z₀ (Finset.mem_insert_self _ _) z (Finset.mem_insert_of_mem hz) hne) hx hxz
    have h2 := subadditive_union hg (Finset.disjoint_sdiff : Disjoint (cell k z₀) (R \ cell k z₀))
    rw [Finset.union_sdiff_of_subset hcR] at h2
    have hrem : S \ (insert z₀ G).biUnion (cell k) = R \ cell k z₀ := by
      ext x
      simp only [hR, Finset.mem_sdiff, Finset.biUnion_insert, Finset.mem_union]
      tauto
    rw [Finset.sum_insert hz₀, hrem]
    linarith

theorem card_sdiff_biUnion_cell (S : Finset (Site d)) (k : ℕ) (G : Finset (Site d))
    (hsub : ∀ z ∈ G, cell k z ⊆ S)
    (hdisj : ∀ z ∈ G, ∀ z' ∈ G, z ≠ z' → Disjoint (cell k z) (cell k z')) :
    ((S \ G.biUnion (cell k)).card : ℝ) = S.card - G.card * (k : ℝ) ^ d := by
  have hU : G.biUnion (cell k) ⊆ S := Finset.biUnion_subset.2 hsub
  have h1 := Finset.card_sdiff_add_card_eq_card hU
  have h2 : (G.biUnion (cell k)).card = G.card * k ^ d := by
    rw [Finset.card_biUnion (by intro z hz z' hz' hne; exact hdisj z hz z' hz' hne)]
    simp [card_cell]
  have h3 : ((S \ G.biUnion (cell k)).card : ℝ) + ((G.biUnion (cell k)).card : ℝ) = S.card := by
    exact_mod_cast h1
  rw [h2] at h3
  push_cast at h3
  linarith

/-- The sites `z ∈ S` whose cell `z + [0, k)^d` lies in `S`. -/
def innerSites (k : ℕ) (S : Finset (Site d)) : Finset (Site d) :=
  S.filter fun z => cell k z ⊆ S

/-- The residue of `z` modulo `k`, a point of `[0, k)^d`. -/
def residue (k : ℕ) (z : Site d) : Site d := fun i => z i % (k : ℤ)

theorem residue_mem_latticeCube {k : ℕ} (hk : 1 ≤ k) (z : Site d) :
    residue k z ∈ latticeCube d k := by
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  rw [latticeCube, Finset.mem_Icc]
  refine ⟨fun i => Int.emod_nonneg _ hkpos.ne', fun i => ?_⟩
  have := Int.emod_lt_of_pos (z i) hkpos
  simp only [residue]
  omega

theorem disjoint_cell_of_residue_eq {k : ℕ} (hk : 1 ≤ k) {z z' : Site d}
    (hzz : residue k z = residue k z') (hne : z ≠ z') : Disjoint (cell k z) (cell k z') := by
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  refine Finset.disjoint_left.2 fun x hx hx' => hne (funext fun i => ?_)
  have h1 := (mem_cell.1 hx) i
  have h2 := (mem_cell.1 hx') i
  have hr := congrFun hzz i
  simp only [residue] at hr
  have e1 := Int.mul_ediv_add_emod (z i) k
  have e2 := Int.mul_ediv_add_emod (z' i) k
  have hq : z i / k = z' i / k := by
    by_contra hq
    rcases lt_or_gt_of_ne hq with h | h
    · have h' : z i / k + 1 ≤ z' i / k := h
      nlinarith
    · have h' : z' i / k + 1 ≤ z i / k := h
      nlinarith
  rw [hq, hr] at e1
  linarith

/-- **Tiling inequality.** For `g ∈ 𝓜_C`, a finite `S` and `k ≥ 1`,
`k^d g(S) ≤ ∑_{z ∈ S_k} g(z + [0, k)^d) + C k^d (|S| - |S_k|)`, where `S_k` is the set of
`z ∈ S` with `z + [0, k)^d ⊆ S` (`innerSites`). For each residue `r` modulo `k`, the cells of
the points of `S_k` with residue `r` are pairwise disjoint; subadditivity over them and the
remainder, summed over the `k^d` residues, gives the bound. -/
theorem subadditive_tiling_le {C : ℝ} {g : Set (Site d) → ℝ} (hg : g ∈ subadditiveClass d C)
    (S : Finset (Site d)) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ d * g ↑S ≤ ∑ z ∈ innerSites k S, g ↑(cell k z) +
      C * (k : ℝ) ^ d * ((S.card : ℝ) - (innerSites k S).card) := by
  set I := innerSites k S with hI
  have hres : ∀ z ∈ I, residue k z ∈ latticeCube d k := fun z _ => residue_mem_latticeCube hk z
  have hr : ∀ r, g ↑S ≤ ∑ z ∈ I with residue k z = r, g ↑(cell k z) +
      C * ((S.card : ℝ) - (I.filter fun z => residue k z = r).card * (k : ℝ) ^ d) := by
    intro r
    have hsubc : ∀ z ∈ I.filter (fun z => residue k z = r), cell k z ⊆ S := by
      intro z hz
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 hz).1).2
    have hdisj : ∀ z ∈ I.filter (fun z => residue k z = r),
        ∀ z' ∈ I.filter (fun z => residue k z = r), z ≠ z' → Disjoint (cell k z) (cell k z') := by
      intro z hz z' hz' hne
      exact disjoint_cell_of_residue_eq hk
        ((Finset.mem_filter.1 hz).2.trans (Finset.mem_filter.1 hz').2.symm) hne
    have h1 := subadditive_le_sum_cells hg.1 S k _ hsubc hdisj
    have h2 := (hg.2 _ (Finset.finite_toSet (S \ (I.filter fun z => residue k z = r).biUnion
      (cell k)))).2
    rw [Set.ncard_coe_finset, card_sdiff_biUnion_cell S k _ hsubc hdisj] at h2
    linarith
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ latticeCube d k) => hr r)
  rw [Finset.sum_const, card_latticeCube_eq_pow, nsmul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_fiberwise_of_maps_to hres] at hsum
  have hcard : ∑ r ∈ latticeCube d k, ((I.filter fun z => residue k z = r).card : ℝ) =
      I.card := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise hres).symm
  have hC : ∑ r ∈ latticeCube d k,
      C * ((S.card : ℝ) - (I.filter fun z => residue k z = r).card * (k : ℝ) ^ d) =
      C * (k : ℝ) ^ d * ((S.card : ℝ) - I.card) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.sum_mul, hcard,
      card_latticeCube_eq_pow, nsmul_eq_mul]
    push_cast
    ring
  rw [hC] at hsum
  push_cast at hsum
  linarith

end Tiling

/-! ### Subadditive processes: the cube limit -/

section Process

variable {d : ℕ} {C : ℝ} {f : Config d → Set (Site d) → ℝ}

/-- A set function process restricted to finite sets, in the form used by
`LatticeProb.akcoglu_krengel`: `finsetProcess f A η = f(A, η)`. -/
def finsetProcess (f : Config d → Set (Site d) → ℝ) : Finset (Site d) → Config d → ℝ :=
  fun A η => f η ↑A

theorem finsetProcess_measurable (hf : IsSubadditiveProcess C f) (A : Finset (Site d)) :
    Measurable (finsetProcess f A) :=
  hf.measurable _ (Finset.finite_toSet A)

theorem finsetProcess_stat (hf : IsSubadditiveProcess C f) (A : Finset (Site d)) (z : Site d)
    (η : Config d) :
    finsetProcess f (A.map (Equiv.addRight z).toEmbedding) η = finsetProcess f A (shift z η) := by
  simp only [finsetProcess]
  rw [coe_map_addRight, hf.stationary z _ (Finset.finite_toSet A)]

theorem finsetProcess_bd (hf : IsSubadditiveProcess C f) (A : Finset (Site d)) (η : Config d) :
    0 ≤ finsetProcess f A η ∧ finsetProcess f A η ≤ C * A.card := by
  have h := (hf.mem η).2 ↑A (Finset.finite_toSet A)
  rwa [Set.ncard_coe_finset] at h

theorem finsetProcess_sub (hf : IsSubadditiveProcess C f) (B B₁ B₂ : Finset (Site d))
    (η : Config d) (h : IsBoxSplit B B₁ B₂) :
    finsetProcess f B η ≤ finsetProcess f B₁ η + finsetProcess f B₂ η := by
  obtain ⟨-, -, -, hdisj, hunion⟩ := h
  rw [← hunion]
  exact subadditive_union (hf.mem η).1 hdisj

/-- **Step (1).** A subadditive process satisfies the hypotheses of the Akcoglu–Krengel theorem
`LatticeProb.akcoglu_krengel` (`τ = shift`), so `f(η, [0, n)^d) / n^d` converges almost surely to
a random limit. -/
theorem exists_ae_tendsto_cube (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) :
    ∃ L : Config d → ℝ, ∀ᵐ η ∂E.P,
      Tendsto (fun n : ℕ => f η ↑(latticeCube d n) / (n : ℝ) ^ d) atTop (𝓝 (L η)) :=
  akcoglu_krengel E.P d hd shift E.stationary (fun z w η => shift_add z w η) (finsetProcess f)
    (finsetProcess_measurable hf) (fun A z η => finsetProcess_stat hf A z η)
    ⟨C, finsetProcess_bd hf⟩ (fun B B₁ B₂ η h => finsetProcess_sub hf B B₁ B₂ η h)

/-- The cube `[0, n + K)^d` contains `y + [0, n)^d` when `0 ≤ y` and `∑ yᵢ ≤ K`; subadditivity
then compares the two values. -/
theorem cube_le_shift_cube (hf : IsSubadditiveProcess C f) {y : Site d} (hy : 0 ≤ y)
    (η : Config d) (n : ℕ) :
    finsetProcess f (latticeCube d (n + ∑ i, (y i).toNat)) η ≤
      finsetProcess f (latticeCube d n) (shift y η) +
        C * (((n + ∑ i, (y i).toNat : ℕ) : ℝ) ^ d - (n : ℝ) ^ d) := by
  set K := ∑ i, (y i).toNat
  set T := (latticeCube d n).map (Equiv.addRight y).toEmbedding
  have hyK : ∀ i, y i ≤ K := by
    intro i
    have h1 : (y i).toNat ≤ K :=
      Finset.single_le_sum (f := fun i => (y i).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 := Int.self_le_toNat (y i)
    omega
  have hT : T ⊆ latticeCube d (n + K) := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [latticeCube, Finset.mem_Icc] at ha ⊢
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := ha.1 i; have := hy i
      simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight, Pi.add_apply, Pi.zero_apply] at *
      omega
    · have := ha.2 i; have := hyK i
      simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight, Pi.add_apply] at *
      push_cast
      omega
  have hsplit := subadditive_union (hf.mem η).1
    (Finset.disjoint_sdiff : Disjoint T (latticeCube d (n + K) \ T))
  rw [Finset.union_sdiff_of_subset hT] at hsplit
  have hrem := (finsetProcess_bd hf (latticeCube d (n + K) \ T) η).2
  have hcard : ((latticeCube d (n + K) \ T).card : ℝ) =
      ((n + K : ℕ) : ℝ) ^ d - (n : ℝ) ^ d := by
    have h1 := Finset.card_sdiff_add_card_eq_card hT
    have h2 : T.card = n ^ d := by rw [Finset.card_map, card_latticeCube_eq_pow]
    rw [card_latticeCube_eq_pow, h2] at h1
    have h3 : ((latticeCube d (n + K) \ T).card : ℝ) + ((n ^ d : ℕ) : ℝ) = ((n + K) ^ d : ℕ) := by
      exact_mod_cast h1
    push_cast at h3 ⊢
    linarith
  rw [hcard] at hrem
  have hstat := finsetProcess_stat hf (latticeCube d n) y η
  simp only [finsetProcess] at hsplit hrem hstat ⊢
  rw [← hstat]
  linarith

/-- **Step (2).** The cube limit is almost surely a constant `a ∈ [0, C]`. With
`L(η) = limsup_n f(η, [0, n)^d) / n^d`: for `y ≥ 0`, `y + [0, n)^d ⊆ [0, n + K)^d` gives
`L ≤ L ∘ T_y` almost surely (`cube_le_shift_cube`); both sides have the same mean because `T_y`
preserves `P`, so `L ∘ T_y = L` almost surely, for every `y` by
`ae_invariant_of_ae_invariant_nonneg`; ergodicity makes `L` almost surely equal to its mean. -/
theorem exists_ae_tendsto_cube_const (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ C ∧ ∀ᵐ η ∂E.P,
      Tendsto (fun n : ℕ => f η ↑(latticeCube d n) / (n : ℝ) ^ d) atTop (𝓝 a) := by
  set F := finsetProcess f with hF
  obtain ⟨L, hL⟩ := exists_ae_tendsto_cube hd E hf
  set Ls : Config d → ℝ := fun η => limsup (fun n => cubeRatio F n η) atTop with hLs
  have hLsm : Measurable Ls :=
    Measurable.limsup fun n => measurable_cubeRatio (finsetProcess_measurable hf) n
  have hconv : ∀ᵐ η ∂E.P, Tendsto (fun n => cubeRatio F n η) atTop (𝓝 (Ls η)) := by
    filter_upwards [hL] with η hη
    have h1 : Tendsto (fun n => cubeRatio F n η) atTop (𝓝 (L η)) := hη
    rw [show Ls η = L η from h1.limsup_eq]
    exact h1
  have hb : ∀ n η, 0 ≤ cubeRatio F n η ∧ cubeRatio F n η ≤ C :=
    fun n η => cubeRatio_nonneg_le hd (finsetProcess_bd hf) n η
  have hLsb : ∀ᵐ η ∂E.P, 0 ≤ Ls η ∧ Ls η ≤ C := by
    filter_upwards [hconv] with η hη
    exact ⟨ge_of_tendsto' hη fun n => (hb n η).1, le_of_tendsto' hη fun n => (hb n η).2⟩
  have hint_of : ∀ G : Config d → ℝ, AEStronglyMeasurable G E.P →
      (∀ᵐ η ∂E.P, 0 ≤ G η ∧ G η ≤ C) → Integrable G E.P := by
    intro G hG hGb
    refine Integrable.of_bound hG C ?_
    filter_upwards [hGb] with η h
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  have hLsi : Integrable Ls E.P := hint_of Ls hLsm.aestronglyMeasurable hLsb
  have hmono : ∀ y : Site d, 0 ≤ y → ∀ᵐ η ∂E.P, Ls η ≤ Ls (shift y η) := by
    intro y hy
    have hconv' : ∀ᵐ η ∂E.P, Tendsto (fun n => cubeRatio F n (shift y η)) atTop
        (𝓝 (Ls (shift y η))) := (E.stationary y).quasiMeasurePreserving.ae hconv
    filter_upwards [hconv, hconv'] with η h1 h2
    set K := ∑ i, (y i).toNat with hK
    have hr : Tendsto (fun n : ℕ => ((n + K : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) atTop (𝓝 1) := by
      have h3 : Tendsto (fun n : ℕ => (1 + (K : ℝ) / n) ^ d) atTop (𝓝 ((1 + 0) ^ d)) :=
        (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))).pow d
      rw [add_zero, one_pow] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      rw [← div_pow]
      congr 1
      push_cast
      field_simp
    have hlhs : Tendsto (fun n : ℕ => cubeRatio F (n + K) η *
        (((n + K : ℕ) : ℝ) ^ d / (n : ℝ) ^ d)) atTop (𝓝 (Ls η * 1)) :=
      ((tendsto_add_atTop_iff_nat K).2 h1).mul hr
    have hrhs : Tendsto (fun n : ℕ => cubeRatio F n (shift y η) +
        C * (((n + K : ℕ) : ℝ) ^ d / (n : ℝ) ^ d - 1)) atTop
        (𝓝 (Ls (shift y η) + C * (1 - 1))) :=
      h2.add (tendsto_const_nhds.mul (hr.sub tendsto_const_nhds))
    rw [mul_one] at hlhs
    rw [sub_self, mul_zero, add_zero] at hrhs
    refine le_of_tendsto_of_tendsto hlhs hrhs ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) < (n : ℝ) ^ d := by positivity
    have hpos' : (0 : ℝ) < ((n + K : ℕ) : ℝ) ^ d := by positivity
    have key := cube_le_shift_cube hf hy η n
    rw [← hK] at key
    simp only [cubeRatio]
    have e1 : F (latticeCube d (n + K)) η / ((n + K : ℕ) : ℝ) ^ d *
        (((n + K : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) = F (latticeCube d (n + K)) η / (n : ℝ) ^ d := by
      field_simp
    have e2 : F (latticeCube d n) (shift y η) / (n : ℝ) ^ d +
        C * (((n + K : ℕ) : ℝ) ^ d / (n : ℝ) ^ d - 1) =
        (F (latticeCube d n) (shift y η) + C * (((n + K : ℕ) : ℝ) ^ d - (n : ℝ) ^ d)) /
          (n : ℝ) ^ d := by
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right key hpos.le
  have hinv0 : ∀ y : Site d, 0 ≤ y → ∀ᵐ η ∂E.P, Ls (shift y η) = Ls η := by
    intro y hy
    have hb' : ∀ᵐ η ∂E.P, 0 ≤ Ls (shift y η) ∧ Ls (shift y η) ≤ C :=
      (E.stationary y).quasiMeasurePreserving.ae hLsb
    have hi' : Integrable (fun η => Ls (shift y η)) E.P :=
      hint_of _ (hLsm.comp (measurable_shift y)).aestronglyMeasurable hb'
    have hmap := integral_map (μ := E.P) (measurable_shift y).aemeasurable
      (f := Ls) (by rw [(E.stationary y).map_eq]; exact hLsm.aestronglyMeasurable)
    rw [(E.stationary y).map_eq] at hmap
    have heq := (integral_eq_iff_of_ae_le hLsi hi' (hmono y hy)).1 hmap
    filter_upwards [heq] with η h
    exact h.symm
  have hinv := ae_invariant_of_ae_invariant_nonneg E.P shift E.stationary
    (fun z w η => shift_add z w η) hLsm hinv0
  have hconst := ae_eq_integral_of_ae_invariant E.P shift measurable_shift
    (fun z w η => shift_add z w η) E.ergodic hLsm hLsi hinv
  refine ⟨∫ η, Ls η ∂E.P, integral_nonneg_of_ae (hLsb.mono fun η h => h.1), ?_, ?_⟩
  · have := integral_mono_ae hLsi (integrable_const C) (hLsb.mono fun η h => h.2)
    simpa using this
  · filter_upwards [hconv, hconst] with η h1 h2
    rw [h2] at h1
    exact h1

end Process

/-! ### Integer boxes -/

section Boxes

variable {d : ℕ}

/-- The integer box `∏ [lᵢ, uᵢ) ⊂ ℤ^d`. -/
def ibox (l u : Site d) : Finset (Site d) := Fintype.piFinset fun i => Finset.Ico (l i) (u i)

theorem mem_ibox {l u x : Site d} : x ∈ ibox l u ↔ ∀ i, l i ≤ x i ∧ x i < u i := by
  simp [ibox, Fintype.mem_piFinset, Finset.mem_Ico]

theorem rectBox_eq_ibox (a b : Fin d → ℝ) (N : ℕ) :
    rectBox a b N = ibox (fun i => ⌈(N : ℝ) * a i⌉) (fun i => ⌈(N : ℝ) * b i⌉) := rfl

theorem card_ibox (l u : Site d) :
    ((ibox l u).card : ℝ) = ∏ i, max ((u i - l i : ℤ) : ℝ) 0 := by
  rw [ibox, Fintype.card_piFinset]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Ico, ← Int.cast_natCast, Int.toNat_eq_max, Int.cast_max, Int.cast_zero, Int.cast_sub]

theorem ibox_zero_eq_latticeCube (n : ℕ) :
    ibox (fun _ => 0) (fun _ => (n : ℤ)) = latticeCube d n := by
  ext x
  rw [mem_ibox, latticeCube, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i => by have := (h i).2; simp only; omega⟩
  · rintro ⟨h0, h1⟩ i
    have := h0 i
    have := h1 i
    simp only [Pi.zero_apply] at *
    omega

/-- `z + [0, k)^d ⊆ ∏ [lᵢ, uᵢ)` for every `z ∈ ∏ [lᵢ, uᵢ - k + 1)`. -/
theorem ibox_add_subset_innerSites {k : ℕ} (hk : 1 ≤ k) (l u : Site d) :
    ibox l (fun i => u i + (1 - (k : ℤ))) ⊆ innerSites k (ibox l u) := by
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  intro z hz
  rw [mem_ibox] at hz
  rw [innerSites, Finset.mem_filter, mem_ibox]
  refine ⟨fun i => ⟨(hz i).1, ?_⟩, ?_⟩
  · have := (hz i).2
    omega
  · intro x hx
    rw [mem_cell] at hx
    rw [mem_ibox]
    intro i
    have := hz i
    have := hx i
    constructor <;> omega

/-- The sites of `A \ B` whose cell leaves `A \ B` lie within distance `k` of the boundary of `A`
or of `B`. -/
theorem card_sdiff_innerSites_sdiff_le {k : ℕ} (hk : 1 ≤ k) (lA uA lB uB : Site d) :
    ((ibox lA uA \ ibox lB uB).card : ℝ) - (innerSites k (ibox lA uA \ ibox lB uB)).card ≤
      (((ibox lA uA).card : ℝ) - (ibox lA (fun i => uA i + (1 - (k : ℤ)))).card) +
      (((ibox (fun i => lB i + (1 - (k : ℤ))) uB).card : ℝ) - (ibox lB uB).card) := by
  set A := ibox lA uA with hA
  set B := ibox lB uB with hB
  set T := A \ B with hT
  set A' := ibox lA (fun i => uA i + (1 - (k : ℤ))) with hA'
  set B' := ibox (fun i => lB i + (1 - (k : ℤ))) uB with hB'
  have hIT : innerSites k T ⊆ T := Finset.filter_subset _ _
  have hA'A : A' ⊆ innerSites k A := ibox_add_subset_innerSites hk lA uA
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hIA : innerSites k A ⊆ A := Finset.filter_subset _ _
  have hBB' : B ⊆ B' := by
    intro x hx
    rw [hB, mem_ibox] at hx
    rw [hB', mem_ibox]
    intro i
    have := hx i
    constructor <;> omega
  have hsub : T \ innerSites k T ⊆ (A \ innerSites k A) ∪ (B' \ B) := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    obtain ⟨hzT, hzI⟩ := hz
    have hzT' := Finset.mem_sdiff.1 hzT
    rw [innerSites, Finset.mem_filter, not_and] at hzI
    obtain ⟨x, hxc, hxT⟩ := Finset.not_subset.1 (hzI hzT)
    rw [Finset.mem_sdiff, not_and, not_not] at hxT
    rw [Finset.mem_union]
    by_cases hxA : x ∈ A
    · right
      have hxB := hxT hxA
      rw [Finset.mem_sdiff]
      refine ⟨?_, hzT'.2⟩
      rw [hB, mem_ibox] at hxB
      rw [hB', mem_ibox]
      rw [mem_cell] at hxc
      intro i
      have := hxB i
      have := hxc i
      constructor <;> omega
    · left
      rw [Finset.mem_sdiff]
      exact ⟨hzT'.1, fun hzIA => hxA ((Finset.mem_filter.1 hzIA).2 hxc)⟩
  have h1 : ((T \ innerSites k T).card : ℝ) + (innerSites k T).card = T.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hIT
  have h23 : ((T \ innerSites k T).card : ℝ) ≤ (A \ innerSites k A).card + (B' \ B).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h4 : ((A \ innerSites k A).card : ℝ) + (innerSites k A).card = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hIA
  have h4' : (A'.card : ℝ) ≤ (innerSites k A).card := by
    exact_mod_cast Finset.card_le_card hA'A
  have h5 : ((B' \ B).card : ℝ) + B.card = B'.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hBB'
  linarith

theorem tendsto_ceil_mul_div (c : ℝ) :
    Tendsto (fun N : ℕ => (⌈(N : ℝ) * c⌉ : ℝ) / N) atTop (𝓝 c) := by
  have hup : Tendsto (fun N : ℕ => c + 1 / (N : ℝ)) atTop (𝓝 (c + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [le_div_iff₀ hN']
    linarith [Int.le_ceil ((N : ℝ) * c)]
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hN', add_mul, one_div, inv_mul_cancel₀ hN'.ne']
    linarith [Int.ceil_lt_add_one ((N : ℝ) * c)]

/-- The volume of the box `∏ [⌈N pᵢ⌉ + α, ⌈N qᵢ⌉ + β)`, normalised by `N^d`, tends to
`∏ (qᵢ - pᵢ)`. -/
theorem tendsto_card_ibox_div_pow (p q : Fin d → ℝ) (hpq : ∀ i, p i ≤ q i) (α β : ℤ) :
    Tendsto (fun N : ℕ => ((ibox (fun i => ⌈(N : ℝ) * p i⌉ + α)
      (fun i => ⌈(N : ℝ) * q i⌉ + β)).card : ℝ) / (N : ℝ) ^ d) atTop
      (𝓝 (∏ i, (q i - p i))) := by
  have hfac : ∀ i, Tendsto (fun N : ℕ => max (((⌈(N : ℝ) * q i⌉ + β - (⌈(N : ℝ) * p i⌉ + α) : ℤ)
      : ℝ) / N) 0) atTop (𝓝 (q i - p i)) := by
    intro i
    have h1 : Tendsto (fun N : ℕ => (⌈(N : ℝ) * q i⌉ : ℝ) / N - (⌈(N : ℝ) * p i⌉ : ℝ) / N +
        ((β - α : ℤ) : ℝ) / N) atTop (𝓝 (q i - p i + 0)) :=
      ((tendsto_ceil_mul_div (q i)).sub (tendsto_ceil_mul_div (p i))).add
        (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [add_zero] at h1
    have h2 := h1.max (tendsto_const_nhds (x := (0 : ℝ)))
    rw [max_eq_left (sub_nonneg.2 (hpq i))] at h2
    refine h2.congr' (Eventually.of_forall fun N => ?_)
    congr 1
    push_cast
    ring
  have hprod := tendsto_finsetProd (Finset.univ : Finset (Fin d)) (fun i _ => hfac i)
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [card_ibox]
  calc ∏ i, max (((⌈(N : ℝ) * q i⌉ + β - (⌈(N : ℝ) * p i⌉ + α) : ℤ) : ℝ) / N) 0
      = ∏ i, (max (((⌈(N : ℝ) * q i⌉ + β - (⌈(N : ℝ) * p i⌉ + α) : ℤ) : ℝ)) 0 / N) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← max_div_div_right hN'.le, zero_div]
    _ = (∏ i, max (((⌈(N : ℝ) * q i⌉ + β - (⌈(N : ℝ) * p i⌉ + α) : ℤ) : ℝ)) 0) / (N : ℝ) ^ d := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Boxes

/-! ### Rational boxes in the positive orthant -/

section OrthantBoxes

variable {d : ℕ}

/-- A sequence squeezed, for every `k ≥ 1`, eventually below a sequence tending to `wU k` and above
one tending to `wL k`, where `wU k → L` and `wL k → L`, tends to `L`. -/
theorem tendsto_of_upper_lower {u : ℕ → ℝ} {L : ℝ} (wU wL : ℕ → ℝ)
    (hwU : Tendsto wU atTop (𝓝 L)) (hwL : Tendsto wL atTop (𝓝 L))
    (hU : ∀ k, 1 ≤ k → ∃ v : ℕ → ℝ, Tendsto v atTop (𝓝 (wU k)) ∧ ∀ᶠ N in atTop, u N ≤ v N)
    (hL : ∀ k, 1 ≤ k → ∃ v : ℕ → ℝ, Tendsto v atTop (𝓝 (wL k)) ∧ ∀ᶠ N in atTop, v N ≤ u N) :
    Tendsto u atTop (𝓝 L) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨k, hk, hk1⟩ := ((hwL.eventually (lt_mem_nhds hb)).and (eventually_ge_atTop 1)).exists
    obtain ⟨v, hv, hvu⟩ := hL k hk1
    filter_upwards [hv.eventually (lt_mem_nhds hk), hvu] with N h1 h2
    exact h1.trans_le h2
  · obtain ⟨k, hk, hk1⟩ := ((hwU.eventually (gt_mem_nhds hb)).and (eventually_ge_atTop 1)).exists
    obtain ⟨v, hv, hvu⟩ := hU k hk1
    filter_upwards [hv.eventually (gt_mem_nhds hk), hvu] with N h1 h2
    exact h2.trans_lt h1

theorem nonneg_of_mem_subadditiveClass {C : ℝ} {g : Set (Site d) → ℝ}
    (hg : g ∈ subadditiveClass d C) : 0 ≤ C := by
  have h := hg.2 {0} (Set.finite_singleton 0)
  rw [Set.ncard_singleton, Nat.cast_one] at h
  linarith [h.1, h.2]

/-- **Deterministic core of the box limit.** Let `g ∈ 𝓜_C` with `g([0, n)^d) / n^d → a`, let
`m k / k^d → a`, and let `0 ≤ p ≤ q ≤ K` with `K ≥ 1` an integer. Suppose that for every `k ≥ 1`
the cell sums `N^{-d} ∑_{x ∈ B} g(x + [0, k)^d)` over `B = ∏ [⌈N pᵢ⌉, ⌈N qᵢ⌉)` and over
`[0, NK)^d` tend to `|Q| m k` and `K^d m k`, `|Q| = ∏ (qᵢ - pᵢ)`. Then
`g(∏ [⌈N pᵢ⌉, ⌈N qᵢ⌉)) / N^d → |Q| a`.

Upper bound: the tiling inequality on `B`. Lower bound: subadditivity on
`[0, NK)^d = B ∪ ([0, NK)^d \ B)` and the tiling inequality on the complement. -/
theorem tendsto_rectBox_div_pow {C : ℝ} {g : Set (Site d) → ℝ} (hg : g ∈ subadditiveClass d C)
    {a : ℝ} (hcube : Tendsto (fun n : ℕ => g ↑(latticeCube d n) / (n : ℝ) ^ d) atTop (𝓝 a))
    {m : ℕ → ℝ} (hm : Tendsto (fun k : ℕ => m k / (k : ℝ) ^ d) atTop (𝓝 a))
    {p q : Fin d → ℝ} (hp : ∀ i, 0 ≤ p i) (hpq : ∀ i, p i ≤ q i) {K : ℕ} (hK : 1 ≤ K)
    (hqK : ∀ i, q i ≤ K)
    (hB : ∀ k, 1 ≤ k → Tendsto (fun N : ℕ => (∑ x ∈ rectBox p q N, g ↑(cell k x)) / (N : ℝ) ^ d)
      atTop (𝓝 ((∏ i, (q i - p i)) * m k)))
    (hA : ∀ k, 1 ≤ k → Tendsto (fun N : ℕ =>
      (∑ x ∈ ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ) * K), g ↑(cell k x)) / (N : ℝ) ^ d)
      atTop (𝓝 ((K : ℝ) ^ d * m k))) :
    Tendsto (fun N : ℕ => g ↑(rectBox p q N) / (N : ℝ) ^ d) atTop
      (𝓝 ((∏ i, (q i - p i)) * a)) := by
  set V := ∏ i, (q i - p i) with hV
  have hC0 := nonneg_of_mem_subadditiveClass hg
  have hg0 : ∀ A : Finset (Site d), 0 ≤ g ↑A ∧ g ↑A ≤ C * A.card := fun A => by
    have h := hg.2 ↑A (Finset.finite_toSet A)
    rwa [Set.ncard_coe_finset] at h
  have hceil : ∀ N : ℕ, ⌈(N : ℝ) * (K : ℝ)⌉ = (N : ℤ) * K := fun N => by
    rw [← Nat.cast_mul, Int.ceil_natCast]
    push_cast
    ring
  have hvol : ∀ α β : ℤ, Tendsto (fun N : ℕ => ((ibox (fun i => ⌈(N : ℝ) * p i⌉ + α)
      (fun i => ⌈(N : ℝ) * q i⌉ + β)).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 V) :=
    fun α β => tendsto_card_ibox_div_pow p q hpq α β
  have hvolB : Tendsto (fun N : ℕ => ((rectBox p q N).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 V) := by
    have h := hvol 0 0
    simp only [add_zero] at h
    exact h
  have hvolB1 : ∀ k : ℕ, Tendsto (fun N : ℕ => ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
      (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 V) := by
    intro k
    have h := hvol 0 (1 - (k : ℤ))
    simp only [add_zero] at h
    exact h
  have hvolB2 : ∀ k : ℕ, Tendsto (fun N : ℕ => ((ibox (fun i => ⌈(N : ℝ) * p i⌉ + (1 - (k : ℤ)))
      (fun i => ⌈(N : ℝ) * q i⌉)).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 V) := by
    intro k
    have h := hvol (1 - (k : ℤ)) 0
    simp only [add_zero] at h
    exact h
  have hvolA : ∀ β : ℤ, Tendsto (fun N : ℕ => ((ibox (d := d) (fun _ => 0)
      (fun _ => (N : ℤ) * K + β)).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 ((K : ℝ) ^ d)) := by
    intro β
    have h := tendsto_card_ibox_div_pow (d := d) (fun _ => 0) (fun _ => (K : ℝ))
      (fun _ => Nat.cast_nonneg K) 0 β
    simp only [mul_zero, Int.ceil_zero, add_zero, hceil, sub_zero, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hvolA0 : Tendsto (fun N : ℕ => ((ibox (d := d) (fun _ => 0)
      (fun _ => (N : ℤ) * K)).card : ℝ) / (N : ℝ) ^ d) atTop (𝓝 ((K : ℝ) ^ d)) := by
    have h := hvolA 0
    simp only [add_zero] at h
    exact h
  refine tendsto_of_upper_lower (fun k => V * (m k / (k : ℝ) ^ d))
    (fun k => (K : ℝ) ^ d * a - ((K : ℝ) ^ d - V) * (m k / (k : ℝ) ^ d)) ?_ ?_ ?_ ?_
  · exact tendsto_const_nhds.mul hm
  · have h := (tendsto_const_nhds (x := (K : ℝ) ^ d * a)).sub
      ((tendsto_const_nhds (x := (K : ℝ) ^ d - V)).mul hm)
    convert h using 2
    ring
  · -- upper bound: tiling of `B`
    intro k hk
    have hkpos : (0 : ℝ) < (k : ℝ) ^ d := by positivity
    refine ⟨fun N => (∑ x ∈ rectBox p q N, g ↑(cell k x)) / (N : ℝ) ^ d / (k : ℝ) ^ d +
      C * (((rectBox p q N).card : ℝ) / (N : ℝ) ^ d - ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
        (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ) / (N : ℝ) ^ d), ?_, ?_⟩
    · have h := ((hB k hk).div_const ((k : ℝ) ^ d)).add
        ((tendsto_const_nhds (x := C)).mul (hvolB.sub (hvolB1 k)))
      convert h using 2
      ring
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
      have ht := subadditive_tiling_le hg (rectBox p q N) hk
      have hsum : ∑ z ∈ innerSites k (rectBox p q N), g ↑(cell k z) ≤
          ∑ x ∈ rectBox p q N, g ↑(cell k x) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x _ _ => (hg0 _).1)
      have hsub : ibox (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ))) ⊆
          innerSites k (rectBox p q N) :=
        ibox_add_subset_innerSites hk (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉)
      have hin : ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
          (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ) ≤
          (innerSites k (rectBox p q N)).card := by
        exact_mod_cast Finset.card_le_card hsub
      have hCk := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ C * (k : ℝ) ^ d)
      have key : (k : ℝ) ^ d * g ↑(rectBox p q N) ≤ ∑ x ∈ rectBox p q N, g ↑(cell k x) +
          C * (k : ℝ) ^ d * (((rectBox p q N).card : ℝ) - ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
            (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ)) := by
        linarith
      have key' : g ↑(rectBox p q N) ≤ (∑ x ∈ rectBox p q N, g ↑(cell k x)) / (k : ℝ) ^ d +
          C * (((rectBox p q N).card : ℝ) - ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
            (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ)) := by
        rw [div_add' _ _ _ hkpos.ne', le_div_iff₀ hkpos]
        linarith
      calc g ↑(rectBox p q N) / (N : ℝ) ^ d
          ≤ ((∑ x ∈ rectBox p q N, g ↑(cell k x)) / (k : ℝ) ^ d +
            C * (((rectBox p q N).card : ℝ) - ((ibox (fun i => ⌈(N : ℝ) * p i⌉)
              (fun i => ⌈(N : ℝ) * q i⌉ + (1 - (k : ℤ)))).card : ℝ))) / (N : ℝ) ^ d :=
            div_le_div_of_nonneg_right key' hNpos.le
        _ = _ := by ring
  · -- lower bound: `[0, NK)^d = B ∪ ([0, NK)^d \ B)`
    intro k hk
    have hkpos : (0 : ℝ) < (k : ℝ) ^ d := by positivity
    have hK0 : (0 : ℝ) < (K : ℝ) ^ d := by positivity
    have hcubeK : Tendsto (fun N : ℕ => g ↑(latticeCube d (N * K)) / (N : ℝ) ^ d) atTop
        (𝓝 ((K : ℝ) ^ d * a)) := by
      have h1 : Tendsto (fun N : ℕ => N * K) atTop atTop :=
        tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_right N hK) tendsto_id
      have h2 := (hcube.comp h1).const_mul ((K : ℝ) ^ d)
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
      simp only [Function.comp_apply]
      push_cast
      rw [mul_pow]
      field_simp
    refine ⟨fun N => g ↑(latticeCube d (N * K)) / (N : ℝ) ^ d -
      ((∑ x ∈ ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ) * K), g ↑(cell k x)) / (N : ℝ) ^ d -
        (∑ x ∈ rectBox p q N, g ↑(cell k x)) / (N : ℝ) ^ d) / (k : ℝ) ^ d -
      C * ((((ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ) * K)).card : ℝ) / (N : ℝ) ^ d -
          ((ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ) * K + (1 - (k : ℤ)))).card : ℝ) /
            (N : ℝ) ^ d) +
        (((ibox (fun i => ⌈(N : ℝ) * p i⌉ + (1 - (k : ℤ))) (fun i => ⌈(N : ℝ) * q i⌉)).card
          : ℝ) / (N : ℝ) ^ d - ((rectBox p q N).card : ℝ) / (N : ℝ) ^ d)), ?_, ?_⟩
    · have h := (hcubeK.sub (((hA k hk).sub (hB k hk)).div_const ((k : ℝ) ^ d))).sub
        ((tendsto_const_nhds (x := C)).mul ((hvolA0.sub (hvolA (1 - (k : ℤ)))).add
          ((hvolB2 k).sub hvolB)))
      convert h using 2
      ring
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
      set A := ibox (d := d) (fun _ => (0 : ℤ)) (fun _ => (N : ℤ) * K) with hA_def
      have hAc : A = latticeCube d (N * K) := by
        rw [← ibox_zero_eq_latticeCube]
        push_cast
        rfl
      have hBA : rectBox p q N ⊆ A := by
        intro x hx
        rw [rectBox_eq_ibox, mem_ibox] at hx
        rw [hA_def, mem_ibox]
        intro i
        have h1 : (0 : ℤ) ≤ ⌈(N : ℝ) * p i⌉ :=
          Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg N) (hp i))
        have h2 : ⌈(N : ℝ) * q i⌉ ≤ (N : ℤ) * K := by
          rw [← hceil N]
          exact Int.ceil_mono (mul_le_mul_of_nonneg_left (hqK i) (Nat.cast_nonneg N))
        have := hx i
        constructor <;> omega
      have hsplit := subadditive_union hg.1
        (Finset.disjoint_sdiff : Disjoint (rectBox p q N) (A \ rectBox p q N))
      rw [Finset.union_sdiff_of_subset hBA] at hsplit
      have ht := subadditive_tiling_le hg (A \ rectBox p q N) hk
      have hsumT : ∑ z ∈ innerSites k (A \ rectBox p q N), g ↑(cell k z) ≤
          ∑ x ∈ A \ rectBox p q N, g ↑(cell k x) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x _ _ => (hg0 _).1)
      have hTsum : ∑ x ∈ A \ rectBox p q N, g ↑(cell k x) =
          ∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x) :=
        Finset.sum_sdiff_eq_sub hBA
      have hbd : ((A \ rectBox p q N).card : ℝ) -
          (innerSites k (A \ rectBox p q N)).card ≤
          (((A.card : ℝ) - (ibox (d := d) (fun _ => (0 : ℤ)) (fun _ => (N : ℤ) * K + (1 - (k : ℤ)))).card)
            + (((ibox (fun i => ⌈(N : ℝ) * p i⌉ + (1 - (k : ℤ))) (fun i => ⌈(N : ℝ) * q i⌉)).card
              : ℝ) - (rectBox p q N).card)) :=
        card_sdiff_innerSites_sdiff_le hk (fun _ => (0 : ℤ)) (fun _ => (N : ℤ) * K)
          (fun i => ⌈(N : ℝ) * p i⌉) (fun i => ⌈(N : ℝ) * q i⌉)
      have hCk := mul_le_mul_of_nonneg_left hbd (by positivity : (0 : ℝ) ≤ C * (k : ℝ) ^ d)
      set bd := ((A.card : ℝ) - (ibox (d := d) (fun _ => (0 : ℤ))
        (fun _ => (N : ℤ) * K + (1 - (k : ℤ)))).card) +
        (((ibox (fun i => ⌈(N : ℝ) * p i⌉ + (1 - (k : ℤ))) (fun i => ⌈(N : ℝ) * q i⌉)).card
          : ℝ) - (rectBox p q N).card) with hbd_def
      have key : (k : ℝ) ^ d * g ↑(A \ rectBox p q N) ≤
          (∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x)) +
            C * (k : ℝ) ^ d * bd := by
        rw [← hTsum]
        linarith
      have key' : g ↑(A \ rectBox p q N) ≤
          (∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x)) / (k : ℝ) ^ d +
            C * bd := by
        rw [div_add' _ _ _ hkpos.ne', le_div_iff₀ hkpos]
        linarith
      have hlow : g ↑A - (∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x)) /
          (k : ℝ) ^ d - C * bd ≤ g ↑(rectBox p q N) := by
        linarith
      rw [← hAc]
      calc _ = (g ↑A - (∑ x ∈ A, g ↑(cell k x) - ∑ x ∈ rectBox p q N, g ↑(cell k x)) /
            (k : ℝ) ^ d - C * bd) / (N : ℝ) ^ d := by
            rw [hbd_def]
            ring
        _ ≤ g ↑(rectBox p q N) / (N : ℝ) ^ d := div_le_div_of_nonneg_right hlow hNpos.le

end OrthantBoxes

/-! ### The almost sure limit on rational boxes -/

section RationalBoxes

variable {d : ℕ} {C : ℝ} {f : Config d → Set (Site d) → ℝ}

/-- The half-open box `∏ [pᵢ, qᵢ) ⊂ ℝ^d` with rational corners. -/
def ratBox (p q : Fin d → ℚ) : Set (Rd d) := {y | ∀ i, (p i : ℝ) ≤ y i ∧ y i < q i}

/-- `nQ ∩ ℤ^d = ∏ [⌈n pᵢ⌉, ⌈n qᵢ⌉)` for `Q = ∏ [pᵢ, qᵢ)` and `n ≥ 1`. -/
theorem discretize_ratBox (p q : Fin d → ℚ) {N : ℕ} (hN : 1 ≤ N) :
    discretize (ratBox p q) N = ↑(rectBox (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  ext x
  rw [discretize, Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ hNpos.ne',
    Finset.mem_coe, rectBox_eq_ibox, mem_ibox]
  simp only [ratBox, Set.mem_ofPred_eq, PiLp.smul_apply, smul_eq_mul, toE_apply]
  refine forall_congr' fun i => ?_
  rw [inv_mul_eq_div, le_div_iff₀ hNpos, div_lt_iff₀ hNpos, Int.ceil_le, Int.lt_ceil]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- The mean cube ratio converges to the constant `a` of the cube limit (dominated convergence). -/
theorem tendsto_integral_cube_div_pow (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) {a : ℝ}
    (hcube : ∀ᵐ η ∂E.P, Tendsto (fun n : ℕ => f η ↑(latticeCube d n) / (n : ℝ) ^ d) atTop (𝓝 a)) :
    Tendsto (fun k : ℕ => (∫ η, f η ↑(latticeCube d k) ∂E.P) / (k : ℝ) ^ d) atTop (𝓝 a) := by
  have h := tendsto_integral_of_dominated_convergence (μ := E.P) (fun _ => C)
    (F := fun (n : ℕ) η => f η ↑(latticeCube d n) / (n : ℝ) ^ d) (f := fun _ => a)
    (fun n => ((finsetProcess_measurable hf (latticeCube d n)).div_const _).aestronglyMeasurable)
    (integrable_const C)
    (fun n => Eventually.of_forall fun η => by
      have hb : 0 ≤ f η ↑(latticeCube d n) / (n : ℝ) ^ d ∧
          f η ↑(latticeCube d n) / (n : ℝ) ^ d ≤ C :=
        cubeRatio_nonneg_le hd (finsetProcess_bd hf) n η
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2)
    hcube
  have e : ∫ _ : Config d, a ∂E.P = a := by simp
  rw [e] at h
  refine h.congr fun k => ?_
  rw [integral_div]

/-- The rectangle ergodic theorem for the cube values `η ↦ f(η, [0, k)^d)`, in the form of cell
sums `∑_{x ∈ B} f(η, x + [0, k)^d)` (stationarity). -/
theorem ae_tendsto_sum_cell (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) (k : ℕ) (p q : Fin d → ℚ) :
    ∀ᵐ η ∂E.P, (∀ i, 0 ≤ p i) → (∀ i, p i ≤ q i) →
      Tendsto (fun N : ℕ => (∑ x ∈ rectBox (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) N,
        f η ↑(cell k x)) / (N : ℝ) ^ d) atTop
        (𝓝 ((∏ i, ((q i : ℝ) - p i)) * ∫ η, f η ↑(latticeCube d k) ∂E.P)) := by
  by_cases hp : ∀ i, 0 ≤ p i
  · by_cases hpq : ∀ i, p i ≤ q i
    · have hbk : ∀ η, 0 ≤ f η ↑(latticeCube d k) ∧
          f η ↑(latticeCube d k) ≤ C * ((latticeCube d k).card : ℝ) :=
        fun η => finsetProcess_bd hf (latticeCube d k) η
      have hbdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ η, |f η ↑(latticeCube d k)| ≤ M := by
        refine ⟨C * ((latticeCube d k).card : ℝ), (hbk 0).1.trans (hbk 0).2, fun η => ?_⟩
        rw [abs_of_nonneg (hbk η).1]
        exact (hbk η).2
      have h := rectangleErgodic hd E.P shift E.stationary (fun z w η => shift_add z w η)
        E.ergodic (fun η => f η ↑(latticeCube d k)) (finsetProcess_measurable hf _) hbdd
        (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) (fun i => by exact_mod_cast hp i)
        (fun i => by exact_mod_cast hpq i)
      filter_upwards [h] with η hη _ _
      refine hη.congr' (Eventually.of_forall fun N => ?_)
      rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, inv_mul_eq_div]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hf.stationary x _ (Finset.finite_toSet _), cell, coe_map_addRight]
    · exact Eventually.of_forall fun η _ h => absurd h hpq
  · exact Eventually.of_forall fun η h => absurd h hp

theorem rectBox_zero_nat_eq_ibox (K N : ℕ) :
    rectBox (d := d) (fun _ => (0 : ℝ)) (fun _ => (K : ℝ)) N =
      ibox (d := d) (fun _ => 0) (fun _ => (N : ℤ) * K) := by
  rw [rectBox_eq_ibox]
  congr 1 <;> funext i
  · simp
  · rw [← Nat.cast_mul, Int.ceil_natCast]
    push_cast
    ring

/-- **Step (3), lattice form.** Almost surely, simultaneously for every pair of rational vectors
`0 ≤ p ≤ q`, `f(η, ∏ [⌈N pᵢ⌉, ⌈N qᵢ⌉)) / N^d → ∏ (qᵢ - pᵢ) · a`, with `a` the constant of
`exists_ae_tendsto_cube_const`. The ergodic input is `ae_tendsto_sum_cell`, one full-measure
event for each `k` and each rational box. -/
theorem ae_tendsto_rectBox (hd : 1 ≤ d) (E : RandomEnvironment d)
    (hf : IsSubadditiveProcess C f) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ C ∧ ∀ᵐ η ∂E.P, ∀ p q : Fin d → ℚ, (∀ i, 0 ≤ p i) → (∀ i, p i ≤ q i) →
      Tendsto (fun N : ℕ => f η ↑(rectBox (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) N) /
        (N : ℝ) ^ d) atTop (𝓝 ((∏ i, ((q i : ℝ) - p i)) * a)) := by
  obtain ⟨a, ha0, haC, hcube⟩ := exists_ae_tendsto_cube_const hd E hf
  refine ⟨a, ha0, haC, ?_⟩
  have hm := tendsto_integral_cube_div_pow hd E hf hcube
  have hE : ∀ᵐ η ∂E.P, ∀ (k : ℕ) (p q : Fin d → ℚ), (∀ i, 0 ≤ p i) → (∀ i, p i ≤ q i) →
      Tendsto (fun N : ℕ => (∑ x ∈ rectBox (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) N,
        f η ↑(cell k x)) / (N : ℝ) ^ d) atTop
        (𝓝 ((∏ i, ((q i : ℝ) - p i)) * ∫ η, f η ↑(latticeCube d k) ∂E.P)) := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro p
    rw [ae_all_iff]
    intro q
    exact ae_tendsto_sum_cell hd E hf k p q
  filter_upwards [hcube, hE] with η hη hEη p q hp hpq
  obtain ⟨M, hM⟩ := Finite.exists_le (fun i => (q i : ℝ))
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge M
  have hK1 : 1 ≤ K₀ + 1 := by omega
  have hqK : ∀ i, (q i : ℝ) ≤ ((K₀ + 1 : ℕ) : ℝ) := fun i => by
    push_cast
    linarith [hM i]
  refine tendsto_rectBox_div_pow (hf.mem η) hη hm (fun i => by exact_mod_cast hp i)
    (fun i => by exact_mod_cast hpq i) hK1 hqK (fun k _ => hEη k p q hp hpq) (fun k _ => ?_)
  have h0 : ∀ i : Fin d, (fun _ => (0 : ℚ)) i ≤ (fun _ => ((K₀ + 1 : ℕ) : ℚ)) i :=
    fun _ => Nat.cast_nonneg _
  have h := hEη k (fun _ => 0) (fun _ => ((K₀ + 1 : ℕ) : ℚ)) (fun _ => le_rfl) h0
  simp only [Rat.cast_zero, Rat.cast_natCast, sub_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, rectBox_zero_nat_eq_ibox] at h
  exact h

/-- **Step (3).** Almost surely, simultaneously for every half-open box `Q = ∏ [pᵢ, qᵢ)` with
rational corners in the closed positive orthant (`0 ≤ pᵢ < qᵢ`),
`f(η, nQ ∩ ℤ^d) / |nQ ∩ ℤ^d| → a`, with a single constant `0 ≤ a ≤ C`. -/
def SubadditiveOrthantBoxesStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (E : RandomEnvironment d) (C : ℝ) (f : Config d → Set (Site d) → ℝ),
    IsSubadditiveProcess C f →
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ C ∧ ∀ᵐ η ∂E.P, ∀ p q : Fin d → ℚ, (∀ i, 0 ≤ p i) → (∀ i, p i < q i) →
      Tendsto (fun n : ℕ => f η (discretize (ratBox p q) n) /
        ((discretize (ratBox p q) n).ncard : ℝ)) atTop (𝓝 a)

/-- The same conclusion for every half-open box with rational corners (`pᵢ < qᵢ`, no sign
condition). Not proved here: for a box meeting both sides of a coordinate hyperplane through the
origin the almost sure lower bound is not reached from `akcoglu_krengel`, whose cubes all have a
corner at the origin (see the module docstring and `SubadditiveCentredCubesStmt`). -/
def SubadditiveRationalBoxesStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (E : RandomEnvironment d) (C : ℝ) (f : Config d → Set (Site d) → ℝ),
    IsSubadditiveProcess C f →
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ C ∧ ∀ᵐ η ∂E.P, ∀ p q : Fin d → ℚ, (∀ i, p i < q i) →
      Tendsto (fun n : ℕ => f η (discretize (ratBox p q) n) /
        ((discretize (ratBox p q) n).ncard : ℝ)) atTop (𝓝 a)

/-- The missing ingredient for `SubadditiveRationalBoxesStmt`: the Akcoglu–Krengel theorem along
the centred cubes `[-n, n)^d` (a regular family in the sense of Akcoglu–Krengel, not covered by
`LatticeProb.akcoglu_krengel`, which treats `[0, n)^d` only). -/
def SubadditiveCentredCubesStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (E : RandomEnvironment d) (C : ℝ) (f : Config d → Set (Site d) → ℝ),
    IsSubadditiveProcess C f →
    ∀ᵐ η ∂E.P, ∃ L : ℝ, Tendsto (fun n : ℕ =>
      f η ↑(ibox (d := d) (fun _ => -(n : ℤ)) (fun _ => (n : ℤ))) / ((2 * n : ℕ) : ℝ) ^ d) atTop
      (𝓝 L)

/-- **Step (3).** `SubadditiveOrthantBoxesStmt` holds. -/
theorem subadditiveOrthantBoxes : SubadditiveOrthantBoxesStmt := by
  intro d hd E C f hf
  obtain ⟨a, ha0, haC, h⟩ := ae_tendsto_rectBox hd E hf
  refine ⟨a, ha0, haC, ?_⟩
  filter_upwards [h] with η hη p q hp hpq
  have hlim := hη p q hp (fun i => (hpq i).le)
  have hVpos : 0 < ∏ i, ((q i : ℝ) - p i) :=
    Finset.prod_pos fun i _ => sub_pos.2 (by exact_mod_cast hpq i)
  have hvol := tendsto_card_ibox_div_pow (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
    (fun i => by exact_mod_cast (hpq i).le) 0 0
  simp only [add_zero] at hvol
  have h2 := hlim.div hvol hVpos.ne'
  rw [mul_div_cancel_left₀ _ hVpos.ne'] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  rw [discretize_ratBox p q hN, Set.ncard_coe_finset]
  exact div_div_div_cancel_right₀ hNpos.ne' _ _

end RationalBoxes

end RandomSandpile

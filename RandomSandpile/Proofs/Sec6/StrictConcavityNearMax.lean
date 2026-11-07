import RandomSandpile.Steps.Sec6.StrictConcavity
import RandomSandpile.Proofs.Sec6.MuLipschitzShell
import RandomSandpile.Proofs.Sec5.StabilizingLegal
import RandomSandpile.Proofs.Sec3.LeastAction
import RandomSandpile.Proofs.Sec6.StrictConcavityBall
import RandomSandpile.Proofs.Sec6.MuLipschitzAnnulusOff

/-! # Lemma 6.2': the probabilistic step `NearMaxSequenceStmt`

`NearMaxSequenceStmt` from Lemma 5.5 (`MuConvergenceStmt`), assuming that open balls are bounded
Lipschitz domains (`hball`).

* Replacement (Lemma 5.3). For finite `A` and `u ∈ 𝓛(η, A)`, the boundary toppling
  `w_b = u · 1_{∂A}` followed by the odometer of `η + Δ w_b` in `A` (`existsLegalStabilizing`) gives
  `h ∈ 𝓛(η, A) ∩ 𝒮(η, A)` with `h = u` on `∂A`. By Lemma 5.3 (`locLegalLeStabilizing`,
  `supGradSetMono`) the supergradient set only grows. Dually for `v ∈ 𝒮(η, A)`.
* Laplacian bound. For `h ∈ 𝓛 ∩ 𝒮`, `-max(ηmax, 0) ≤ Δh ≤ 2d - 1 - ηmin`, so
  `|Δ(h - q_l - q_M)| ≤ K`.
* Near-maximal selection. `w_n` is chosen within `δ_n = (|B_n| + 1)/(n + 1)` of
  `μ(B_n, η, l, M)`, and Lemma 5.5 on `B_1` gives `μ(B_n) / |B_n| → μ(l, M)`.
* Mass bounds. For `W` a sub-ball or the complement `B_1 \ B̄_ρ(c)` of a closed sub-ball, `nW ∩ ℤ^d ⊆ B_n`. The restriction lemma
  bounds the supergradient mass at `nW ∩ ℤ^d` by `μ(nW ∩ ℤ^d)`. Lemma 5.5 on `W` and lattice
  counting turn this into `≤ (α |W| / |B_1| + ε) |B_n|`. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric Module
open scoped Topology ENNReal Pointwise

namespace RandomSandpile

namespace NearMaxSequence

open MuLipschitz BallCount MuLipschitzShell

variable {d : ℕ}

/-! ### Replacement by a locally legal and stabilizing toppling -/

/-- A legal toppling function vanishes off `A`. -/
theorem isLegal_eq_zero_of_not_mem {η : Site d → ℤ} {A : Set (Site d)} {v : Site d → ℤ}
    (hv : IsLegal η A v) {y : Site d} (hy : y ∉ A) : v y = 0 := by
  obtain ⟨n, xs, hA, -, rfl⟩ := hv
  exact Finset.sum_eq_zero fun i _ => dirac_of_ne fun h => hy (h ▸ hA i)

theorem locLegal_isTopplingFn {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (hu : u ∈ locLegal η A) : IsTopplingFn A u := by
  obtain ⟨w, uh, hw, huh, rfl, -, -, -⟩ := hu
  exact ⟨fun x => add_nonneg (hw.1 x) (huh.1 x), fun x hx => by
    simp [hw.2 x hx, huh.2 x hx]⟩

/-- For finite `A` and a toppling function `u` on `Ā`, there is `h ∈ 𝓛(η, A) ∩ 𝒮(η, A)` with
`h = u` on `∂A`: topple the boundary as `u` does, then stabilize. -/
theorem exists_locLegal_stabilizing (hd : 0 < d) {A : Set (Site d)} (hA : A.Finite)
    (η : Site d → ℤ) {u : Site d → ℤ} (hu : IsTopplingFn A u) :
    ∃ h ∈ locLegal η A ∩ stabilizing η A, ∀ x ∈ bdry A, h x = u x := by
  classical
  set wb : Site d → ℤ := fun x => if x ∈ bdry A then u x else 0 with hwb
  have hwbT : IsTopplingFn A wb := by
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · simp only [hwb]
      split_ifs
      exacts [hu.1 x, le_rfl]
    · simp only [hwb]
      split_ifs with h
      · exact absurd (Or.inr h) hx
      · rfl
  have hwbA : ∀ x ∈ A, wb x = 0 := fun x hx => by
    simp only [hwb]
    split_ifs with h
    · exact absurd hx (mem_bdry.1 h).1
    · rfl
  obtain ⟨v, hvL, hvS⟩ := existsLegalStabilizing d hd A hA (fun y => lap wb y + η y)
  have hvT := hvL.isTopplingFn
  have hv0 : ∀ x ∈ bdry A, v x = 0 := fun x hx => isLegal_eq_zero_of_not_mem hvL (mem_bdry.1 hx).1
  refine ⟨wb + v, ⟨⟨wb, v, hwbT, hvT, rfl, hwbA, hv0, hvL⟩, ⟨?_, fun x hx => ?_⟩⟩, fun x hx => ?_⟩
  · exact ⟨fun x => add_nonneg (hwbT.1 x) (hvT.1 x), fun x hx => by
      simp [hwbT.2 x hx, hvT.2 x hx]⟩
  · rw [lap_add']
    obtain ⟨-, hvS2⟩ := hvS
    have := hvS2 x hx
    simp only at this
    linarith
  · simp only [Pi.add_apply, hwb, if_pos hx, hv0 x hx, add_zero]

/-- Replacement of a perturbed subsolution by one coming from `𝓛 ∩ 𝒮`. -/
theorem exists_replacement_sub (hd : 2 ≤ d) {A : Set (Site d)} (hA : A.Finite) {η : Site d → ℤ}
    {l : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {w : Site d → ℝ} (hw : w ∈ perturbedSub A η l M) :
    ∃ h ∈ locLegal η A ∩ stabilizing η A, volume (supGradSet w A) ≤
      volume (supGradSet (fun x => (h x : ℝ) - (qlZ l x + qMZ M x)) A) := by
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.1 hw
  obtain ⟨h, hh, hbd⟩ := exists_locLegal_stabilizing (by omega) hA η (locLegal_isTopplingFn hu)
  refine ⟨h, hh, measure_mono (supGradSetMono d A hA _ _ (fun y _ => ?_) (fun x hx => ?_))⟩
  · have h1 := locLegalLeStabilizing d A η u h hu hh.2 hbd y
    have h2 : (u y : ℝ) ≤ h y := by exact_mod_cast h1
    linarith
  · simp only [hbd x hx]

/-- Dual of `exists_replacement_sub`. -/
theorem exists_replacement_super (hd : 2 ≤ d) {A : Set (Site d)} (hA : A.Finite)
    {η : Site d → ℤ} {l : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {w : Site d → ℝ}
    (hw : w ∈ perturbedSuper A η l M) :
    ∃ h ∈ locLegal η A ∩ stabilizing η A, volume (subGradSet w A) ≤
      volume (subGradSet (fun x => (h x : ℝ) - (qlZ l x + qMZ M x)) A) := by
  obtain ⟨s, hs, rfl⟩ := mem_perturbedSuper.1 hw
  obtain ⟨h, hh, hbd⟩ := exists_locLegal_stabilizing (by omega) hA η hs.1
  refine ⟨h, hh, measure_mono (subGradSetMono d A hA _ _ (fun y _ => ?_) (fun x hx => ?_))⟩
  · have h1 := locLegalLeStabilizing d A η h s hh.1 hs (fun x hx => (hbd x hx).symm) y
    have h2 : (h y : ℝ) ≤ s y := by exact_mod_cast h1
    linarith
  · simp only [hbd x hx]

/-! ### The Laplacian bound -/

/-- The Laplacian bound `K` of Lemma 6.2'. -/
def lapBound (d : ℕ) (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ((|max ηmax 0| + |2 * (d : ℤ) - 1 - ηmin| : ℤ) : ℝ) + |l + M.trace|

theorem lapBound_nonneg (d : ℕ) (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    0 ≤ lapBound d ηmin ηmax l M := by
  unfold lapBound
  have : (0 : ℤ) ≤ |max ηmax 0| + |2 * (d : ℤ) - 1 - ηmin| := by positivity
  have : (0 : ℝ) ≤ ((|max ηmax 0| + |2 * (d : ℤ) - 1 - ηmin| : ℤ) : ℝ) := by exact_mod_cast this
  positivity

theorem abs_lapR_le (hd : 1 ≤ d) {η : Site d → ℤ} {ηmin ηmax : ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) {A : Set (Site d)} {h : Site d → ℤ}
    (hh : h ∈ locLegal η A ∩ stabilizing η A) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {x : Site d}
    (hx : x ∈ A) :
    |lapR (fun y => (h y : ℝ) - (qlZ l y + qMZ M y)) x| ≤ lapBound d ηmin ηmax l M := by
  rw [lapR_sub', lapR_intCast, lapQuadratic d hd]
  have h1 := locLegalLapLower d η A h hh.1 x hx
  obtain ⟨-, h2⟩ := hh.2
  have h2 := h2 x hx
  obtain ⟨hη1, hη2⟩ := hη x
  set B : ℤ := |max ηmax 0| + |2 * (d : ℤ) - 1 - ηmin|
  have hlo : -B ≤ Sandpile.lap h x := by
    have hm : min 0 (η x) - η x ≥ -max ηmax 0 := by
      rcases le_total 0 (η x) with h0 | h0
      · rw [min_eq_left h0]; have := le_max_left ηmax 0; linarith
      · rw [min_eq_right h0]; have := le_max_right ηmax 0; linarith
    have := le_abs_self (max ηmax 0)
    have := abs_nonneg (2 * (d : ℤ) - 1 - ηmin)
    linarith
  have hhi : Sandpile.lap h x ≤ B := by
    have := le_abs_self (2 * (d : ℤ) - 1 - ηmin)
    have := abs_nonneg (max ηmax 0)
    linarith
  have hlo' : -(B : ℝ) ≤ (Sandpile.lap h x : ℝ) := by exact_mod_cast hlo
  have hhi' : (Sandpile.lap h x : ℝ) ≤ B := by exact_mod_cast hhi
  unfold lapBound
  rw [abs_le]
  constructor <;> linarith [le_abs_self (l + M.trace), neg_abs_le (l + M.trace)]

/-! ### Near-maximal selection -/

theorem mu_ne_top (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) {η : Site d → ℤ} {ηmax : ℤ}
    (hη : ∀ x, η x ≤ ηmax) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : mu A η l M ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (mu_le_ncard hd hA (fun x _ => hη x) l M)

theorem muStar_ne_top (hd : 1 ≤ d) {A : Set (Site d)} (hA : A.Finite) {η : Site d → ℤ}
    {ηmin : ℤ} (hη : ∀ x, ηmin ≤ η x) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    muStar A η l M ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (muStar_le_ncard hd hA (fun x _ => hη x) l M)

theorem exists_nearMax_sub (hd : 2 ≤ d) {A : Set (Site d)} (hA : A.Finite) (η : Site d → ℤ)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {ηmax : ℤ} (hη : ∀ x, η x ≤ ηmax) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ h ∈ locLegal η A ∩ stabilizing η A, ENNReal.ofReal ((mu A η l M).toReal - δ) ≤
      volume (supGradSet (fun x => (h x : ℝ) - (qlZ l x + qMZ M x)) A) := by
  have hfin := mu_ne_top (by omega) hA hη l M
  obtain ⟨w, hw, hlt⟩ : ∃ w ∈ perturbedSub A η l M,
      ENNReal.ofReal ((mu A η l M).toReal - δ) ≤ volume (supGradSet w A) := by
    by_cases h0 : (mu A η l M).toReal - δ ≤ 0
    · obtain ⟨w, hw⟩ := perturbedSub_nonempty A η l M
      exact ⟨w, hw, by rw [ENNReal.ofReal_eq_zero.2 h0]; exact bot_le⟩
    · rw [not_le] at h0
      have hlt : ENNReal.ofReal ((mu A η l M).toReal - δ) < mu A η l M := by
        conv_rhs => rw [← ENNReal.ofReal_toReal hfin]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      rw [mu] at hlt
      obtain ⟨w, hw, hlt'⟩ := lt_biSup_iff.1 hlt
      exact ⟨w, hw, hlt'.le⟩
  obtain ⟨h, hh, hvol⟩ := exists_replacement_sub hd hA hw
  exact ⟨h, hh, hlt.trans hvol⟩

theorem exists_nearMax_super (hd : 2 ≤ d) {A : Set (Site d)} (hA : A.Finite) (η : Site d → ℤ)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) {ηmin : ℤ} (hη : ∀ x, ηmin ≤ η x) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ h ∈ locLegal η A ∩ stabilizing η A, ENNReal.ofReal ((muStar A η l M).toReal - δ) ≤
      volume (subGradSet (fun x => (h x : ℝ) - (qlZ l x + qMZ M x)) A) := by
  have hfin := muStar_ne_top (by omega) hA hη l M
  obtain ⟨w, hw, hlt⟩ : ∃ w ∈ perturbedSuper A η l M,
      ENNReal.ofReal ((muStar A η l M).toReal - δ) ≤ volume (subGradSet w A) := by
    by_cases h0 : (muStar A η l M).toReal - δ ≤ 0
    · obtain ⟨h, hh, -⟩ := exists_locLegal_stabilizing (by omega) hA η (u := 0)
        ⟨fun _ => le_rfl, fun _ _ => rfl⟩
      exact ⟨_, mem_perturbedSuper.2 ⟨h, hh.2, rfl⟩,
        by rw [ENNReal.ofReal_eq_zero.2 h0]; exact bot_le⟩
    · rw [not_le] at h0
      have hlt : ENNReal.ofReal ((muStar A η l M).toReal - δ) < muStar A η l M := by
        conv_rhs => rw [← ENNReal.ofReal_toReal hfin]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      rw [muStar] at hlt
      obtain ⟨w, hw, hlt'⟩ := lt_biSup_iff.1 hlt
      exact ⟨w, hw, hlt'.le⟩
  obtain ⟨h, hh, hvol⟩ := exists_replacement_super hd hA hw
  exact ⟨h, hh, hlt.trans hvol⟩

/-! ### Mass bounds on sub-domains -/

theorem discretize_subset_ballZ0 {W : Set (Rd d)} (hW : W ⊆ ball 0 1) {n : ℕ} (hn : 1 ≤ n) :
    discretize W n ⊆ ballZ0 (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  intro x hx
  have hx' : toE x ∈ (n : ℝ) • W := hx
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hn0.ne'] at hx'
  have h := hW hx'
  rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hn0] at h
  exact mem_ballZ0.2 (by linarith)

/-- For `W ⊆ B_1` with null frontier and `|W| = θ |B_1|`: a mass `F n` with
`F n / |nW ∩ ℤ^d| → α` is eventually `≤ (α θ + ε) |B_n|`, unless `nW ∩ ℤ^d = ∅`. -/
theorem eventually_le_of_tendsto (hd : 1 ≤ d) {W : Set (Rd d)} (hWsub : W ⊆ ball 0 1)
    (hWb : Bornology.IsBounded W) (hWm : MeasurableSet W) (hWf : volume (frontier W) = 0)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : volume.real W = θ * volume.real (ball (0 : Rd d) 1)) {α : ℝ}
    (hα : 0 ≤ α) {F : ℕ → ℝ≥0∞} (hF : ∀ n, F n ≠ ⊤)
    (hconv : Tendsto (fun n : ℕ => (F n).toReal / ((discretize W n).ncard : ℝ)) atTop (𝓝 α)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, discretize W n = ∅ ∨
      F n ≤ ENNReal.ofReal ((α * θ + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  intro ε hε
  have hvol1 : 0 < volume.real (ball (0 : Rd d) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hcnt := tendsto_ncard_discretize_div_ball hd hWb hWm hWf
  rw [hθ, mul_div_cancel_right₀ _ hvol1.ne'] at hcnt
  set ε₁ := ε / (4 * (θ + 1)) with hε₁
  set ε₂ := min 1 (ε / (4 * (α + 1))) with hε₂
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₂0 : 0 < ε₂ := lt_min one_pos (by positivity)
  have e1 := hconv.eventually (gt_mem_nhds (show α < α + ε₁ by linarith))
  have e2 := hcnt.eventually (gt_mem_nhds (show θ < θ + ε₂ by linarith))
  filter_upwards [e1, e2, eventually_ge_atTop 1] with n h1 h2 hn
  have hNpos : (0 : ℝ) < ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) :=
    Nat.cast_pos.2 (ncard_ballZ0_pos hn)
  by_cases hD0 : ((discretize W n).ncard : ℝ) = 0
  · left
    exact (Set.ncard_eq_zero ((ballZ0_finite _).subset (discretize_subset_ballZ0 hWsub hn))).1
      (by exact_mod_cast hD0)
  · right
    have hDpos : 0 < ((discretize W n).ncard : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hD0)
    rw [← ENNReal.ofReal_toReal (hF n)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm1 := (div_lt_iff₀ hDpos).1 h1
    have hc := (div_lt_iff₀ hNpos).1 h2
    have hαε₂ : α * ε₂ ≤ ε / 4 := by
      calc α * ε₂ ≤ α * (ε / (4 * (α + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hα
        _ ≤ ε / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
    have hε₁θ : ε₁ * θ ≤ ε / 4 := by
      rw [hε₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hε₁ε₂ : ε₁ * ε₂ ≤ ε / 4 := by
      have h1' : ε₁ ≤ ε / 4 := by
        rw [hε₁]
        exact div_le_div_of_nonneg_left hε.le (by norm_num) (by nlinarith)
      calc ε₁ * ε₂ ≤ ε₁ * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hε₁0.le
        _ ≤ ε / 4 := by linarith
    have key : (α + ε₁) * (θ + ε₂) ≤ α * θ + ε := by
      have : (α + ε₁) * (θ + ε₂) = α * θ + α * ε₂ + ε₁ * θ + ε₁ * ε₂ := by ring
      linarith
    calc (F n).toReal ≤ (α + ε₁) * (discretize W n).ncard := hm1.le
      _ ≤ (α + ε₁) * ((θ + ε₂) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) :=
          mul_le_mul_of_nonneg_left hc.le (by positivity)
      _ = (α + ε₁) * (θ + ε₂) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by ring
      _ ≤ (α * θ + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) :=
          mul_le_mul_of_nonneg_right key hNpos.le

/-- The data of Lemma 5.5 needed on a sub-domain `W ⊆ B_1`, at a fixed `η`. -/
structure SubdomainData (η : Site d → ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (W : Set (Rd d))
    (α α' θ : ℝ) : Prop where
  sub : W ⊆ ball 0 1
  bdd : Bornology.IsBounded W
  meas : MeasurableSet W
  front : volume (frontier W) = 0
  θ_nonneg : 0 ≤ θ
  vol : volume.real W = θ * volume.real (ball (0 : Rd d) 1)
  fin : ∀ n : ℕ, mu (discretize W n) η l M ≠ ⊤ ∧ muStar (discretize W n) η l M ≠ ⊤
  conv : Tendsto (fun n : ℕ => (mu (discretize W n) η l M).toReal / ((discretize W n).ncard : ℝ))
    atTop (𝓝 α)
  conv' : Tendsto (fun n : ℕ =>
    (muStar (discretize W n) η l M).toReal / ((discretize W n).ncard : ℝ)) atTop (𝓝 α')

theorem SubdomainData.mass_sub (hd : 1 ≤ d) {η : Site d → ℤ} {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {W : Set (Rd d)} {α α' θ : ℝ} (hW : SubdomainData η l M W α α' θ)
    (hα : 0 ≤ α) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M,
      volume (⋃ x ∈ discretize W n, supGrad w x (ballZ0 (n : ℝ))) ≤
        ENNReal.ofReal ((α * θ + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  filter_upwards [eventually_le_of_tendsto hd hW.sub hW.bdd hW.meas hW.front hW.θ_nonneg hW.vol hα
    (fun n => (hW.fin n).1) hW.conv ε hε, eventually_ge_atTop 1] with n hn hn1 w hw
  rcases hn with hD | hD
  · rw [hD]; simp
  · exact (volume_supGrad_le_mu (discretize_subset_ballZ0 hW.sub hn1) le_rfl hw).trans hD

theorem SubdomainData.mass_super (hd : 1 ≤ d) {η : Site d → ℤ} {l : ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {W : Set (Rd d)} {α α' θ : ℝ} (hW : SubdomainData η l M W α α' θ)
    (hα' : 0 ≤ α') (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M,
      volume (⋃ x ∈ discretize W n, subGrad w x (ballZ0 (n : ℝ))) ≤
        ENNReal.ofReal ((α' * θ + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
  filter_upwards [eventually_le_of_tendsto hd hW.sub hW.bdd hW.meas hW.front hW.θ_nonneg hW.vol hα'
    (fun n => (hW.fin n).2) hW.conv' ε hε, eventually_ge_atTop 1] with n hn hn1 w hw
  rcases hn with hD | hD
  · rw [hD]; simp
  · exact (volume_subGrad_le_muStar (discretize_subset_ballZ0 hW.sub hn1) le_rfl hw).trans hD

/-! ### The complement of a closed sub-ball -/

theorem volume_real_ball_sdiff_closedBall (c : Rd d) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hsub : closedBall c ρ ⊆ ball (0 : Rd d) 1) :
    volume.real (ball (0 : Rd d) 1 \ closedBall c ρ) = (1 - ρ ^ d) * volume.real (ball (0 : Rd d) 1) := by
  rw [measureReal_def, measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet
      measure_closedBall_lt_top.ne,
    ENNReal.toReal_sub_of_le (measure_mono hsub) measure_ball_lt_top.ne,
    Measure.addHaar_closedBall _ _ hρ0, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hρ0 d), measureReal_def]
  ring

theorem volume_frontier_ball_sdiff_closedBall (hd : 1 ≤ d) (c : Rd d) (ρ : ℝ) :
    volume (frontier (ball (0 : Rd d) 1 \ closedBall c ρ)) = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hopen : IsOpen (ball (0 : Rd d) 1 \ closedBall c ρ) := isOpen_ball.sdiff isClosed_closedBall
  have hcl : closure (ball (0 : Rd d) 1 \ closedBall c ρ) ⊆ closedBall 0 1 \ ball c ρ :=
    closure_minimal (Set.sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall)
      (isClosed_closedBall.sdiff isOpen_ball)
  refine measure_mono_null (t := sphere 0 1 ∪ sphere c ρ) ?_
    (measure_union_null (Measure.addHaar_sphere _ _ _) (Measure.addHaar_sphere _ _ _))
  intro x hx
  rw [hopen.frontier_eq] at hx
  obtain ⟨h1, h2⟩ := hcl hx.1
  have h3 := hx.2
  rw [mem_closedBall_zero_iff] at h1
  rw [mem_ball, not_lt] at h2
  simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall, not_and, not_not] at h3
  rcases lt_or_eq_of_le h1 with h | h
  · exact Or.inr (mem_sphere.2 (le_antisymm (h3 h) h2))
  · exact Or.inl (mem_sphere_zero_iff_norm.2 h)

end NearMaxSequence

open NearMaxSequence MuLipschitzShell MuLipschitz in
/-- **Step N1 of Lemma 6.2' from Lemma 5.5** (`NearMaxSequenceStmt`). -/
theorem nearMaxSequence_of_muConvergence (hconv : MuConvergenceStmt) : NearMaxSequenceStmt := by
  intro d hd ηmin ηmax l M
  have hd1 : 1 ≤ d := by omega
  haveI : NeZero d := ⟨by omega⟩
  refine ⟨lapBound d ηmin ηmax l M, lapBound_nonneg d ηmin ηmax l M, fun E hmin hmax => ?_⟩
  have hηae : ∀ᵐ η ∂E.P, ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax := by
    rw [← hmin, ← hmax]; exact ae_all_iff.2 E.bounded
  -- the sub-domains used: the unit ball, sub-balls and centred annuli
  have hdata : ∀ η : Site d → ℤ, (∀ W : Set (Rd d), IsLipschitzDomain W →
      (∀ n : ℕ, mu (discretize W n) η l (symmPart M) ≠ ⊤ ∧
        muStar (discretize W n) η l (symmPart M) ≠ ⊤) ∧
      Tendsto (fun n : ℕ => (mu (discretize W n) η l (symmPart M)).toReal /
        ((discretize W n).ncard : ℝ)) atTop (𝓝 (muBar E l (symmPart M))) ∧
      Tendsto (fun n : ℕ => (muStar (discretize W n) η l (symmPart M)).toReal /
        ((discretize W n).ncard : ℝ)) atTop (𝓝 (muStarBar E l (symmPart M)))) →
      ∀ (W : Set (Rd d)) (θ : ℝ), IsLipschitzDomain W → W ⊆ ball 0 1 → MeasurableSet W →
        volume (frontier W) = 0 → 0 ≤ θ → volume.real W = θ * volume.real (ball (0 : Rd d) 1) →
        SubdomainData η l M W (muBar E l M) (muStarBar E l M) θ := by
    intro η hη W θ hW hsub hm hf hθ0 hθ
    obtain ⟨hfin, hc, hc'⟩ := hη W hW
    simp only [mu_symmPart, muStar_symmPart, muBar_symmPart, muStarBar_symmPart] at hfin hc hc'
    exact ⟨hsub, hW.1, hm, hf, hθ0, hθ, hfin, hc, hc'⟩
  have hball : ∀ (z : Rd d) (r : ℝ), 0 < r →
      volume.real (ball z r) = r ^ d * volume.real (ball (0 : Rd d) 1) := by
    intro z r hr
    rw [measureReal_def, Measure.addHaar_ball _ _ hr.le, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le d), measureReal_def]
  have hballData : ∀ η, _ → ∀ (z : Rd d) (r : ℝ), 0 < r → ball z r ⊆ ball 0 1 →
      SubdomainData η l M (ball z r) (muBar E l M) (muStarBar E l M) (r ^ d) :=
    fun η hη z r hr hzr => hdata η hη _ _ (StrictConcavityBall.isLipschitzDomain_ball z hr) hzr
      measurableSet_ball (by rw [frontier_ball z hr.ne']; exact Measure.addHaar_sphere _ _ _)
      (pow_nonneg hr.le d) (hball z r hr)
  have hvol1 : 0 < volume.real (ball (0 : Rd d) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hannData : ∀ η, _ → ∀ (c : Rd d) (ρ : ℝ), 0 < ρ → closedBall c ρ ⊆ ball (0 : Rd d) 1 →
      SubdomainData η l M (ball (0 : Rd d) 1 \ closedBall c ρ) (muBar E l M) (muStarBar E l M)
        (1 - ρ ^ d) :=
    fun η hη c ρ hρ0 hcρ => hdata η hη _ _
      (MuLipschitzAnnulusOff.isLipschitzDomain_ball_sdiff_closedBall hd c hρ0 hcρ)
      Set.sdiff_subset (isOpen_ball.sdiff isClosed_closedBall).measurableSet
      (volume_frontier_ball_sdiff_closedBall hd1 c ρ)
      (by
        have h := volume_real_ball_sdiff_closedBall c hρ0.le hcρ
        have : 0 ≤ volume.real (ball (0 : Rd d) 1 \ closedBall c ρ) := measureReal_nonneg
        nlinarith)
      (volume_real_ball_sdiff_closedBall c hρ0.le hcρ)
  have hunit : ∀ η, _ → SubdomainData η l M (ball (0 : Rd d) 1) (muBar E l M) (muStarBar E l M) 1 :=
    fun η hη => hdata η hη _ _ (unitBallLipschitz d) le_rfl measurableSet_ball
      (by rw [frontier_ball 0 one_ne_zero]; exact Measure.addHaar_sphere _ _ _) zero_le_one
      (by ring)
  -- the slack `δ_n = (|B_n| + 1) / (n + 1)` of the near-maximal selection
  set δ : ℕ → ℝ := fun n => (((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) + 1) / ((n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      δ n ≤ ε / 2 * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (4 / ε)
    filter_upwards [eventually_ge_atTop (max m 1)] with n hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hN1 : (1 : ℝ) ≤ ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) := by
      exact_mod_cast ncard_ballZ0_pos hn1
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
    have h4 : 4 < ε * ((n : ℝ) + 1) := by
      have := (div_lt_iff₀ hε).1 (hm.trans_le (by linarith : (m : ℝ) ≤ n + 1))
      linarith
    simp only [δ]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- near-maximality from Lemma 5.5 on `B_1`
  have hconvB : ∀ (G : Set (Site d) → ℝ≥0∞) (α : ℝ),
      Tendsto (fun n : ℕ => (G (discretize (ball (0 : Rd d) 1) n)).toReal /
        ((discretize (ball (0 : Rd d) 1) n).ncard : ℝ)) atTop (𝓝 α) →
      Tendsto (fun n : ℕ => (G (ballZ0 (n : ℝ))).toReal / ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))
        atTop (𝓝 α) := fun G α h =>
    h.congr' ((eventually_ge_atTop 1).mono fun n hn => by rw [discretize_unitBall hn])
  have hnear : ∀ (F : ℕ → ℝ≥0∞) (α : ℝ),
      Tendsto (fun n : ℕ => (F n).toReal / ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) atTop
        (𝓝 α) → ∀ (V : ℕ → ℝ≥0∞), (∀ n, ENNReal.ofReal ((F n).toReal - δ n) ≤ V n) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ V n := by
    intro F α hF V hV ε hε
    filter_upwards [hF.eventually (lt_mem_nhds (show α - ε / 2 < α by linarith)), hδsmall ε hε,
      eventually_ge_atTop 1] with n h1 h2 hn
    have hNpos : (0 : ℝ) < ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ) :=
      Nat.cast_pos.2 (ncard_ballZ0_pos hn)
    have h1' := (lt_div_iff₀ hNpos).1 h1
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hV n)
    nlinarith
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · filter_upwards [(hconv d hd).1 E (symmPart M) (symmPart_isSymm M) l, hηae] with η hη hb
    choose h hh hvol using fun n : ℕ =>
      exists_nearMax_sub hd (ballZ0_finite (n : ℝ)) η l M (fun x => (hb x).2) (hδpos n)
    refine ⟨fun n x => (h n x : ℝ) - (qlZ l x + qMZ M x),
      fun n => ⟨mem_perturbedSub.2 ⟨h n, (hh n).1, rfl⟩, mem_perturbedSuper.2 ⟨h n, (hh n).2, rfl⟩⟩,
      fun n x hx => abs_lapR_le hd1 hb (hh n) l M hx,
      hnear (fun n => mu (ballZ0 (n : ℝ)) η l M) _
        (hconvB (fun A => mu A η l M) _ (hunit η hη).conv) _ hvol,
      fun z r hr hzr ε hε => ((hballData η hη z r hr hzr).mass_sub hd1 hα.le ε hε).mono
        fun n hn => hn _ (mem_perturbedSub.2 ⟨h n, (hh n).1, rfl⟩),
      fun c ρ hρ0 hcρ ε hε => ((hannData η hη c ρ hρ0 hcρ).mass_sub hd1 hα.le ε hε).mono
        fun n hn => hn _ (mem_perturbedSub.2 ⟨h n, (hh n).1, rfl⟩)⟩
  · filter_upwards [(hconv d hd).1 E (symmPart M) (symmPart_isSymm M) l, hηae] with η hη hb
    choose h hh hvol using fun n : ℕ =>
      exists_nearMax_super hd (ballZ0_finite (n : ℝ)) η l M (fun x => (hb x).1) (hδpos n)
    refine ⟨fun n x => (h n x : ℝ) - (qlZ l x + qMZ M x),
      fun n => ⟨mem_perturbedSub.2 ⟨h n, (hh n).1, rfl⟩, mem_perturbedSuper.2 ⟨h n, (hh n).2, rfl⟩⟩,
      fun n x hx => abs_lapR_le hd1 hb (hh n) l M hx,
      hnear (fun n => muStar (ballZ0 (n : ℝ)) η l M) _
        (hconvB (fun A => muStar A η l M) _ (hunit η hη).conv') _ hvol,
      fun z r hr hzr ε hε => ((hballData η hη z r hr hzr).mass_super hd1 hα.le ε hε).mono
        fun n hn => hn _ (mem_perturbedSuper.2 ⟨h n, (hh n).2, rfl⟩),
      fun c ρ hρ0 hcρ ε hε => ((hannData η hη c ρ hρ0 hcρ).mass_super hd1 hα.le ε hε).mono
        fun n hn => hn _ (mem_perturbedSuper.2 ⟨h n, (hh n).2, rfl⟩)⟩

/-- **Lemma 6.2' with a locally legal and stabilizing witness** (`NearMaxBendingStabilizingStmt`,
consumed by Lemma 7.5) from Lemma 5.5 and the deterministic core `AlmostMaximalBendingStmt`. -/
theorem nearMaxBendingStabilizing_of_core (hconv : MuConvergenceStmt)
    (hcore : AlmostMaximalBendingStmt) : NearMaxBendingStabilizingStmt :=
  nearMaxBendingStabilizing_of_steps (nearMaxSequence_of_muConvergence hconv) hcore

/-- **Lemma 6.3 from Lemma 5.5 and the deterministic core of Lemma 6.2'.** -/
theorem muLipschitz_of_core (hconv : MuConvergenceStmt) (hcore : AlmostMaximalBendingStmt) :
    MuLipschitzStmt :=
  muLipschitz_of_bending_of_muConvergence
    (nearMaxBending_of_steps (nearMaxSequence_of_muConvergence hconv) hcore) hconv

/-- **Lemma 6.2' with a locally legal and stabilizing witness from Lemma 5.5 and the limit object**
(`RescaledEnvelopeLimitStmt`, the analytic content). -/
theorem nearMaxBendingStabilizing_of_limit (hconv : MuConvergenceStmt)
    (hlim : RescaledEnvelopeLimitStmt) : NearMaxBendingStabilizingStmt :=
  nearMaxBendingStabilizing_of_core hconv (almostMaximalBending_of_limit hlim)

/-- **Lemma 6.3 from Lemma 5.5 and the limit object.** -/
theorem muLipschitz_of_limit (hconv : MuConvergenceStmt) (hlim : RescaledEnvelopeLimitStmt) :
    MuLipschitzStmt :=
  muLipschitz_of_core hconv (almostMaximalBending_of_limit hlim)

/-- **Lemma 6.2 with `C = C(β)` from Lemma 5.5 and the limit object.** -/
theorem strictConcavityBeta_of_limit (hconv : MuConvergenceStmt)
    (hlim : RescaledEnvelopeLimitStmt) : StrictConcavityBetaStmt :=
  strictConcavityBeta_of_bending_of_muConvergence
    (nearMaxBending_of_steps (nearMaxSequence_of_muConvergence hconv)
      (almostMaximalBending_of_limit hlim)) hconv

end RandomSandpile

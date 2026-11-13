import RandomSandpile.Steps.Sec5.HarnackQuadratic
import LatticeProb.Walk.Harnack

/-! # Proposition 5.2: the Harnack inequality for functions with bounded Laplacian on boxes

Proof of `BoxHarnackBddLapStmt`. For `f ≥ 0` on `box d (2r)` with `|Δ f| ≤ λ` on
`box d (2r - 1)`, write `f = h + w` on `box d (2r)`, where `h = harnackExt B K f` solves the
Dirichlet problem on `B \ K = box d (2r - 1)` with boundary data `f` on the shell
`K = box d (2r) \ box d (2r - 1)` (Lattice-Probability, `LatticeProb/Walk/Harnack/Dirichlet.lean`).
Then `h ≥ 0` is harmonic on `box d (2r - 1)`, so the discrete Harnack inequality
`LatticeProb.harnack` gives `h(y) ≤ C h(z)` on `box d r`. The remainder `w` vanishes off
`B \ K` and has charge `-Δ f` there, so by the Riesz representation
(`LatticeProb.eq_sum_harnackGreen_mul_laplacian`) `|w(x)| ≤ λ ∑_y G_{B \ K}(x, y) = λ E_x[τ]`, and the
expected exit time is at most `2r²` (compare with `4dr² - |y|²`, whose Laplacian is `-2d`). -/

open LatticeProb

namespace RandomSandpile

section BoxHarnack

variable {d : ℕ}

/-- `harnackGreen B x y ≥ 0` (Lattice-Probability proves it as a private lemma,
`LatticeProb/Walk/Harnack/Basics.lean`; same proof). -/
theorem harnackGreen_nonneg_of_one_le (hd : 1 ≤ d) (B : Finset (Site d)) (x y : Site d) :
    0 ≤ harnackGreen B x y := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
  unfold harnackGreen
  exact Network.killedGreenReal_nonneg (Graph.Zd.latticeConnected d) B hq y x

/-- The squared Euclidean norm `|v|² = ∑_i v_i²` of a lattice point. -/
def latticeSqNorm (v : Site d) : ℝ := ∑ i, ((v i : ℝ)) ^ 2

theorem latticeSqNorm_nonneg (v : Site d) : 0 ≤ latticeSqNorm v := by
  unfold latticeSqNorm; positivity

/-- `Δ |·|² = 2d`, direction by direction: `|y + e_j|² + |y - e_j|² = 2|y|² + 2`. -/
theorem latticeSqNorm_add_sub_unit (y : Site d) (j : Fin d) :
    latticeSqNorm (y + unit j) + latticeSqNorm (y - unit j) = 2 * latticeSqNorm y + 2 := by
  unfold latticeSqNorm
  rw [← Finset.sum_add_distrib]
  have h : ∀ i, (((y + unit j) i : ℤ) : ℝ) ^ 2 + (((y - unit j) i : ℤ) : ℝ) ^ 2
      = 2 * ((y i : ℤ) : ℝ) ^ 2 + 2 * (if j = i then 1 else 0) := by
    intro i
    by_cases hij : j = i
    · subst hij; simp [unit]; ring
    · have : i ≠ j := fun h => hij h.symm
      simp [unit, this, hij]; ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  simp

theorem latticeSqNorm_le_of_mem_box {v : Site d} {m : ℕ} (hv : v ∈ box d m) :
    latticeSqNorm v ≤ d * (m : ℝ) ^ 2 := by
  unfold latticeSqNorm
  calc ∑ i, ((v i : ℝ)) ^ 2 ≤ ∑ _i : Fin d, (m : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h : |(v i : ℝ)| ≤ m := by exact_mod_cast hv i
        have := pow_le_pow_left₀ (abs_nonneg _) h 2
        rwa [sq_abs] at this
    _ = d * (m : ℝ) ^ 2 := by simp

theorem boxHarnackBddLap : BoxHarnackBddLapStmt := by
  intro d hd
  obtain ⟨C, hC, hharn⟩ := harnack d hd
  refine ⟨2 * C + 2, by linarith, ?_⟩
  intro r hr lam f hf hlap y hy z hz
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hGnn := harnackGreen_nonneg_of_one_le hd
  have hlam0 : 0 ≤ lam := (abs_nonneg _).trans (hlap 0 (fun i => by simp))
  have hA'B : ∀ x, x ∈ box d (2 * r - 1) → x ∈ box d (2 * r) :=
    fun x hx => mem_box_mono (by omega) hx
  have hnbr : ∀ x ∈ box d (2 * r - 1), ∀ j : Fin d,
      x + unit j ∈ box d (2 * r) ∧ x - unit j ∈ box d (2 * r) := by
    intro x hx j
    have hj := unit_add_sub_mem_box_succ (2 * r - 1) x j hx
    rwa [show 2 * r - 1 + 1 = 2 * r by omega] at hj
  -- the box `B`, the shell `K`, and `B \ K = box d (2r - 1)`
  obtain ⟨B, hB⟩ : ∃ B : Finset (Site d), B = harnackBox d (2 * r) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Finset (Site d), K = B \ harnackBox d (2 * r - 1) := ⟨_, rfl⟩
  have hmemB : ∀ x, x ∈ B ↔ x ∈ box d (2 * r) := fun x => by
    rw [hB, mem_harnackBox_iff_mem_box]
  have hmemA : ∀ x, x ∈ B \ K ↔ x ∈ box d (2 * r - 1) := by
    intro x
    rw [hK, Finset.mem_sdiff, Finset.mem_sdiff, hmemB, mem_harnackBox_iff_mem_box]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra h3
      exact h2 ⟨h1, h3⟩
    · intro h
      exact ⟨hA'B x h, fun h' => h'.2 h⟩
  have hKB : K ⊆ B := by rw [hK]; exact Finset.sdiff_subset
  have hK_box : ∀ x ∈ K, x ∈ box d (2 * r) := fun x hx => (hmemB x).1 (hKB hx)
  -- the harmonic part `h`
  obtain ⟨h, hh⟩ : ∃ h : Site d → ℝ, h = harnackExt B K f := ⟨_, rfl⟩
  have hFK : ∀ x, 0 ≤ (if x ∈ K then f x else 0) := fun x => by
    split_ifs with h1
    · exact hf _ (hK_box _ h1)
    · exact le_rfl
  have h_nonneg : ∀ x, 0 ≤ h x := by
    intro x
    rw [hh]
    unfold harnackExt
    refine add_nonneg (hFK x) (Finset.sum_nonneg fun y _ => mul_nonneg (hGnn _ _ _) ?_)
    unfold nbrSum
    exact Finset.sum_nonneg fun j _ => add_nonneg (hFK _) (hFK _)
  have h_harm : ∀ x ∈ box d (2 * r - 1), nbrSum h x = 2 * (d : ℝ) * h x := by
    intro x hx
    have hx' := Finset.mem_sdiff.1 ((hmemA x).2 hx)
    rw [hh]
    exact nbrSum_harnackExt_eq_of_mem_sdiff hd B K f hx'.1 hx'.2
  have h_eqK : ∀ x ∈ K, h x = f x := fun x hx => by
    rw [hh]; exact harnackExt_eq_of_mem hd B K f hx
  have hHyz : h y ≤ C * h z := hharn r h hr (fun x _ => h_nonneg x) h_harm y hy z hz
  -- the remainder `w`, vanishing off `B \ K`
  obtain ⟨w, hw⟩ : ∃ w : Site d → ℝ, w = fun x => if x ∈ B \ K then f x - h x else 0 :=
    ⟨_, rfl⟩
  have hw_off : ∀ x, x ∉ B \ K → w x = 0 := fun x hx => by rw [hw]; simp only [ite_eq_right hx]
  have hw_B : ∀ x ∈ box d (2 * r), w x = f x - h x := by
    intro x hx
    rw [hw]
    dsimp only
    split_ifs with h1
    · rfl
    · have hxK : x ∈ K := by
        by_contra h2
        exact h1 (Finset.mem_sdiff.2 ⟨(hmemB x).2 hx, h2⟩)
      rw [h_eqK x hxK, sub_self]
  have hw_charge : ∀ x ∈ B \ K, 2 * (d : ℝ) * w x - nbrSum w x = -lapR f x := by
    intro x hx
    have hxA := (hmemA x).1 hx
    have hnb : nbrSum w x = nbrSum f x - nbrSum h x := by
      unfold nbrSum
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw_B _ (hnbr x hxA j).1, hw_B _ (hnbr x hxA j).2]
      ring
    rw [hnb, hw_B x (hA'B x hxA), h_harm x hxA, lapR]
    ring
  have hrep : ∀ x, w x = -∑ y ∈ B \ K, harnackGreen (B \ K) x y * lapR f y := by
    intro x
    rw [eq_sum_harnackGreen_mul_laplacian hd (B \ K) w hw_off x, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hw_charge y hy]
    ring
  -- the expected exit time from `box d (2r - 1)` is at most `2r²`
  have hexit : ∀ x, ∑ y ∈ B \ K, harnackGreen (B \ K) x y ≤ 2 * (r : ℝ) ^ 2 := by
    intro x
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (d : ℝ) * ((2 * r : ℕ) : ℝ) ^ 2 := ⟨_, rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : Site d → ℝ,
        φ = fun v => if v ∈ B \ K then m - latticeSqNorm v else 0 := ⟨_, rfl⟩
    have hm0 : 0 ≤ m := by rw [hm]; positivity
    have hφ_le : ∀ v ∈ box d (2 * r), φ v ≤ m - latticeSqNorm v := by
      intro v hv
      rw [hφ]
      dsimp only
      split_ifs
      · exact le_rfl
      · have := latticeSqNorm_le_of_mem_box hv
        rw [← hm] at this
        linarith
    have hφ_off : ∀ v, v ∉ B \ K → φ v = 0 := fun v hv => by rw [hφ]; simp only [ite_eq_right hv]
    have hφ_x : φ x ≤ m := by
      rw [hφ]
      dsimp only
      split_ifs
      · linarith [latticeSqNorm_nonneg x]
      · exact hm0
    have hcharge : ∀ v ∈ B \ K, 2 * (d : ℝ) ≤ 2 * (d : ℝ) * φ v - nbrSum φ v := by
      intro v hv
      have hvA := (hmemA v).1 hv
      have hφv : φ v = m - latticeSqNorm v := by rw [hφ]; simp only [ite_eq_left hv]
      have hnb : nbrSum φ v ≤
          ∑ j : Fin d, ((m - latticeSqNorm (v + unit j)) + (m - latticeSqNorm (v - unit j))) := by
        unfold nbrSum
        exact Finset.sum_le_sum fun j _ =>
          add_le_add (hφ_le _ (hnbr v hvA j).1) (hφ_le _ (hnbr v hvA j).2)
      have hsum : ∑ j : Fin d, ((m - latticeSqNorm (v + unit j)) + (m - latticeSqNorm (v - unit j)))
          = 2 * (d : ℝ) * m - 2 * (d : ℝ) * latticeSqNorm v - 2 * (d : ℝ) := by
        have hj : ∀ j : Fin d, (m - latticeSqNorm (v + unit j)) + (m - latticeSqNorm (v - unit j))
            = 2 * m - 2 * latticeSqNorm v - 2 := by
          intro j
          have := latticeSqNorm_add_sub_unit v j
          linarith
        rw [Finset.sum_congr rfl (fun j _ => hj j)]
        simp
        ring
      rw [hφv]
      linarith
    have hS : 2 * (d : ℝ) * ∑ y ∈ B \ K, harnackGreen (B \ K) x y ≤ φ x := by
      rw [eq_sum_harnackGreen_mul_laplacian hd (B \ K) φ hφ_off x, Finset.mul_sum]
      refine Finset.sum_le_sum fun y hy => ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hcharge y hy) (hGnn _ _ _)
    have hm' : m = 2 * (d : ℝ) * (2 * (r : ℝ) ^ 2) := by rw [hm]; push_cast; ring
    exact le_of_mul_le_mul_left (by linarith) (by positivity : (0 : ℝ) < 2 * d)
  have hw_bd : ∀ x, |w x| ≤ lam * (2 * (r : ℝ) ^ 2) := by
    intro x
    rw [hrep x, abs_neg]
    calc |∑ y ∈ B \ K, harnackGreen (B \ K) x y * lapR f y|
        ≤ ∑ y ∈ B \ K, |harnackGreen (B \ K) x y * lapR f y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ B \ K, harnackGreen (B \ K) x y * lam := by
          refine Finset.sum_le_sum fun y hy => ?_
          rw [abs_mul, abs_of_nonneg (hGnn _ _ _)]
          exact mul_le_mul_of_nonneg_left (hlap y ((hmemA y).1 hy)) (hGnn _ _ _)
      _ = lam * ∑ y ∈ B \ K, harnackGreen (B \ K) x y := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ lam * (2 * (r : ℝ) ^ 2) := mul_le_mul_of_nonneg_left (hexit x) hlam0
  -- conclusion: `f(y) = h(y) + w(y) ≤ C h(z) + 2λr² ≤ C f(z) + 2Cλr² + 2λr²`
  have hy2 : y ∈ box d (2 * r) := mem_box_mono (by omega) hy
  have hz2 : z ∈ box d (2 * r) := mem_box_mono (by omega) hz
  have hfy : f y = h y + w y := by rw [hw_B y hy2]; ring
  have hfz : f z = h z + w z := by rw [hw_B z hz2]; ring
  have hwy := (abs_le.mp (hw_bd y)).2
  have hwz := (abs_le.mp (hw_bd z)).1
  have hfz0 : 0 ≤ f z := hf z hz2
  have hCz : C * h z ≤ C * (f z + lam * (2 * (r : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC.le
  nlinarith [mul_nonneg hC.le hfz0, mul_nonneg hC.le hlam0]

end BoxHarnack

end RandomSandpile

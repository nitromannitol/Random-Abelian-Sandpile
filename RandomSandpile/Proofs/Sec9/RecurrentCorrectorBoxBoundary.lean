import RandomSandpile.Proofs.Sec9.RecurrentCorrectorAnnulus
import LatticeProb.Walk.Lazy

/-! # Macroscopic box boundary bounds for recurrent correctors -/

noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

theorem mem_originBox_iff_abs_le {d : ℕ} (L : ℕ) (z : Site d) :
    z ∈ originBox d L ↔ ∀ i, |z i| ≤ (L : ℤ) := by
  simp only [originBox, Fintype.mem_piFinset, Finset.mem_Icc]
  exact forall_congr' fun _ => (abs_le).symm

/-- A nearest-neighbor step from a box remains in its one-site enlargement. -/
theorem originBox_step_mem_succ {d : ℕ} {L : ℕ} {z : Site d}
    (hz : z ∈ originBox d L) (a : Dir d) : z + dirVec a ∈ originBox d (L + 1) := by
  rw [mem_originBox_iff_abs_le] at hz ⊢
  intro i
  have hcoord := hz i
  have hstep := abs_dirVec_le_one a i
  have hadd := abs_add_le (z i) (dirVec a i)
  change |z i + dirVec a i| ≤ ((L + 1 : ℕ) : ℤ)
  push_cast
  omega

/-- The normalized corrector is bounded on a one-site exterior shell of a
macroscopic box. -/
theorem recurrent_corrector_box_shell_bound_above {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (htail : SingleSourceVanishingTail η)
    (κ C Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ)))
    (m : ℝ) :
    ∃ r : ℝ, 0 < r ∧ m ≤ r ∧ ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ z : Site d, z ∉ originBox d ⌈r * ssScale d n⌉₊ →
        z ∈ originBox d (⌈r * ssScale d n⌉₊ + 1) →
        |(n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n z +
          (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n| ≤ B := by
  obtain ⟨r₀, hr₀, h⟩ := recurrent_lattice_corrector_annulus_bound hd η htail κ C Rg hRg hasymp
  let r := max r₀ m
  have hr : 0 < r := lt_of_lt_of_le hr₀ (le_max_left _ _)
  have hm : m ≤ r := le_max_right _ _
  obtain ⟨B, hB⟩ := h ((r + 2) * (Real.sqrt d + 1))
  refine ⟨r, hr, hm, B, ?_⟩
  filter_upwards [hB, eventually_ge_atTop 1] with n hn hn1
  intro z hzoutside hzinside
  let L := ⌈r * ssScale d n⌉₊
  have hs : 1 ≤ ssScale d n := one_le_ssScale hn1
  have hs0 : 0 ≤ ssScale d n := by linarith
  obtain ⟨i, hi⟩ : ∃ i, ¬ |z i| ≤ (L : ℤ) := by
    simpa only [mem_originBox_iff_abs_le, not_forall] using hzoutside
  have hcoord : (L : ℝ) ≤ |(z i : ℝ)| := by
    exact_mod_cast (le_of_lt (lt_of_not_ge hi))
  have hnorm : |(z i : ℝ)| ≤ ‖toE z‖ := by
    simpa [toE_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (toE z) i
  have hlo : r * ssScale d n ≤ ‖toE z‖ :=
    le_trans (Nat.le_ceil _) (le_trans hcoord hnorm)
  have hcoords : ∀ i, |(toE z) i| ≤ (L : ℝ) + 1 := by
    intro i
    have hzi : |z i| ≤ ((L + 1 : ℕ) : ℤ) := (mem_originBox_iff_abs_le _ _).1 hzinside i
    change |(z i : ℝ)| ≤ (L : ℝ) + 1
    exact_mod_cast hzi
  have hupper := norm_le_sqrt_mul_of_abs_le (toE z) (by positivity : 0 ≤ (L : ℝ) + 1) hcoords
  have hceil : (L : ℝ) < r * ssScale d n + 1 := Nat.ceil_lt_add_one (mul_nonneg hr.le hs0)
  have hL : (L : ℝ) + 1 ≤ (r + 2) * ssScale d n := by nlinarith
  have hscale : 0 ≤ (r + 2) * ssScale d n := by positivity
  apply hn z (le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hs0) hlo)
  calc
    ‖toE z‖ ≤ Real.sqrt d * ((L : ℝ) + 1) := hupper
    _ ≤ Real.sqrt d * ((r + 2) * ssScale d n) :=
      mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
    _ ≤ (Real.sqrt d + 1) * ((r + 2) * ssScale d n) := by nlinarith
    _ = ((r + 2) * (Real.sqrt d + 1)) * ssScale d n := by ring

/-- A sufficiently large macroscopic box has a bounded exterior shell. -/
theorem recurrent_corrector_box_shell_bound {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (htail : SingleSourceVanishingTail η)
    (κ C Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ))) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ z : Site d, z ∉ originBox d ⌈r * ssScale d n⌉₊ →
        z ∈ originBox d (⌈r * ssScale d n⌉₊ + 1) →
        |(n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n z +
          (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n| ≤ B := by
  obtain ⟨r, hr, _, B, hB⟩ :=
    recurrent_corrector_box_shell_bound_above hd η htail κ C Rg hRg hasymp 0
  exact ⟨r, hr, B, hB⟩

/-- The box can be chosen larger than any prescribed macroscopic radius. -/
theorem recurrent_corrector_box_boundary_bound_above {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (htail : SingleSourceVanishingTail η)
    (κ C Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ)))
    (m : ℝ) :
    ∃ r : ℝ, 0 < r ∧ m ≤ r ∧ ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ originBox d ⌈r * ssScale d n⌉₊, ∀ a : Dir d,
        z + dirVec a ∉ originBox d ⌈r * ssScale d n⌉₊ →
        |(n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n (z + dirVec a) +
          (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n| ≤ B := by
  obtain ⟨r, hr, hm, B, hB⟩ :=
    recurrent_corrector_box_shell_bound_above hd η htail κ C Rg hRg hasymp m
  refine ⟨r, hr, hm, B, ?_⟩
  filter_upwards [hB] with n hn
  intro z hz a houtside
  exact hn (z + dirVec a) houtside (originBox_step_mem_succ hz a)

/-- The normalized corrector is bounded on the external vertex boundary of a
macroscopic box. -/
theorem recurrent_corrector_box_boundary_bound {d : ℕ} (hd : 2 ≤ d)
    (η : Site d → ℤ) (htail : SingleSourceVanishingTail η)
    (κ C Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ C * ‖toE z‖ ^ (-(d : ℝ))) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ originBox d ⌈r * ssScale d n⌉₊, ∀ a : Dir d,
        z + dirVec a ∉ originBox d ⌈r * ssScale d n⌉₊ →
        |(n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n (z + dirVec a) +
          (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n| ≤ B := by
  obtain ⟨r, hr, B, hB⟩ := recurrent_corrector_box_shell_bound hd η htail κ C Rg hRg hasymp
  refine ⟨r, hr, B, ?_⟩
  filter_upwards [hB] with n hn
  intro z hz a houtside
  exact hn (z + dirVec a) houtside (originBox_step_mem_succ hz a)

end RandomSandpile
